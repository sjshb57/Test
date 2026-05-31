#!/usr/bin/env python3
# ============================================================================
# aggregate_avatars.py — 全站共享头像池汇总
# ----------------------------------------------------------------------------
# 扫描组织下所有存档仓库的 avatar/ 目录，按 pid 去重后汇总到 home/avatars/，
# 供 archive.py 下头像时优先命中（GitHub CDN 秒取，避免重复从 Wayback 下载）。
#
# 去重规则（同一个 avatar_{pid} 在多个仓库都有、且内容不同时）：
#   1. 优先“最新的”（该文件最近一次提交时间更晚的那份）
#   2. 若最新的仍并列，再取“文件体积较大”的那份
# 内容完全相同（git blob sha 一致）时不查提交时间，直接用，省 API 调用。
#
# 在 home 仓库的 Action 里运行，只写 home 自己（用默认 GITHUB_TOKEN 即可）。
# ============================================================================

import json
import os
import sys
import time
import urllib.parse

import requests

# ── 配置 ────────────────────────────────────────────────────────────────────
ORG = os.environ.get("AVATAR_POOL_ORG", "TwitterArchiver")
# 额外纳入的仓库（组织外的，owner/name 形式，逗号分隔）。
# 组织扫描已覆盖组织内全部仓库，默认留空；如需纳入组织外仓库再填。
EXTRA_REPOS = [
    r.strip() for r in os.environ.get(
        "AVATAR_POOL_EXTRA_REPOS",
        "",
    ).split(",") if r.strip()
]
# 不参与扫描的仓库名（home 自己）
EXCLUDE_REPO_NAMES = {"home"}

OUT_DIR = os.environ.get("AVATAR_POOL_OUT", "avatars")
MANIFEST_PATH = os.path.join(OUT_DIR, "_manifest.json")

TOKEN = os.environ.get("GITHUB_TOKEN", "")
API = "https://api.github.com"
SESSION = requests.Session()
SESSION.headers.update({
    "Accept": "application/vnd.github+json",
    "X-GitHub-Api-Version": "2022-11-28",
})
if TOKEN:
    SESSION.headers["Authorization"] = f"Bearer {TOKEN}"

_AVATAR_RE = __import__("re").compile(
    r"^avatar_(\d+)\.(?:jpg|jpeg|png|gif|webp)$", __import__("re").IGNORECASE
)


def log(*a):
    print(*a, flush=True)


def api_get(url, params=None):
    """带轻量重试的 GET（返回解析后的 JSON，404 返回 None）。"""
    for attempt in range(4):
        try:
            r = SESSION.get(url, params=params, timeout=30)
            if r.status_code == 404:
                return None
            if r.status_code in (403, 429):
                # rate limit / 限流：等一下再试
                reset = r.headers.get("X-RateLimit-Reset")
                wait = 5 * (attempt + 1)
                if reset:
                    try:
                        wait = max(wait, int(reset) - int(time.time()) + 2)
                    except ValueError:
                        pass
                wait = min(wait, 90)
                log(f"  [限流] 等 {wait}s 重试 …")
                time.sleep(wait)
                continue
            r.raise_for_status()
            return r.json()
        except requests.RequestException as e:
            if attempt == 3:
                log(f"  [警告] GET 失败 {url}: {e}")
                return None
            time.sleep(2 * (attempt + 1))
    return None


def list_org_repos(org):
    """列出组织下所有仓库（分页）。"""
    repos = []
    page = 1
    while True:
        data = api_get(f"{API}/orgs/{org}/repos",
                       params={"per_page": 100, "page": page, "type": "public"})
        if not data:
            break
        repos.extend(data)
        if len(data) < 100:
            break
        page += 1
    return [f"{org}/{r['name']}" for r in repos
            if r["name"] not in EXCLUDE_REPO_NAMES]


def list_contents(repo, path):
    """列目录内容（文件项含 name/sha/size/download_url）。目录不存在返回 []。"""
    data = api_get(f"{API}/repos/{repo}/contents/{urllib.parse.quote(path)}")
    if not isinstance(data, list):
        return []
    return data


def find_avatar_files(repo):
    """在一个仓库里找出所有账号的头像文件。
       返回 [(pid, fname, sha, size, download_url, repo, filepath), ...]"""
    found = []
    accounts = list_contents(repo, "accounts")
    acct_dirs = [c["name"] for c in accounts if c.get("type") == "dir"]
    for acct in acct_dirs:
        avatar_path = f"accounts/{acct}/wayback_snapshots/avatar"
        for f in list_contents(repo, avatar_path):
            if f.get("type") != "file":
                continue
            m = _AVATAR_RE.match(f["name"])
            if not m:
                continue
            found.append((
                m.group(1), f["name"], f["sha"], f.get("size", 0),
                f.get("download_url", ""), repo, f["path"],
            ))
    return found


def commit_date(repo, filepath):
    """该文件最近一次提交时间（epoch 秒）；查不到返回 0。"""
    data = api_get(f"{API}/repos/{repo}/commits",
                   params={"path": filepath, "per_page": 1})
    if not data:
        return 0
    try:
        iso = data[0]["commit"]["committer"]["date"]  # e.g. 2026-05-30T12:00:00Z
        return int(time.mktime(time.strptime(iso, "%Y-%m-%dT%H:%M:%SZ")))
    except (KeyError, IndexError, ValueError):
        return 0


def choose(pid, cands):
    """按规则从同 pid 的候选里选一个。cands: list of dict。"""
    if len(cands) == 1:
        return cands[0]
    shas = {c["sha"] for c in cands}
    if len(shas) == 1:
        # 内容完全一样，随便挑（取体积最大那个，反正都一样）
        return max(cands, key=lambda c: c["size"])
    # 内容不同：查提交时间（仅此罕见情形才花 API），按 (最新, 最大) 排序
    for c in cands:
        c["_ts"] = commit_date(c["repo"], c["path"])
    cands.sort(key=lambda c: (c["_ts"], c["size"]), reverse=True)
    log(f"  [冲突] pid={pid} 有 {len(shas)} 种内容，选最新+最大的 "
        f"(repo={cands[0]['repo']}, {cands[0]['size']}B)")
    return cands[0]


def load_manifest():
    try:
        with open(MANIFEST_PATH, encoding="utf-8") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def main():
    os.makedirs(OUT_DIR, exist_ok=True)
    manifest = load_manifest()  # pid -> {"file","sha","size","src"}

    repos = list_org_repos(ORG) + EXTRA_REPOS
    log(f"📋 待扫描仓库：{len(repos)} 个")

    # 收集：pid -> [候选...]
    by_pid = {}
    for i, repo in enumerate(repos, 1):
        files = find_avatar_files(repo)
        for pid, fname, sha, size, dl, rp, path in files:
            by_pid.setdefault(pid, []).append({
                "fname": fname, "sha": sha, "size": size,
                "download_url": dl, "repo": rp, "path": path,
            })
        log(f"  [{i}/{len(repos)}] {repo}: {len(files)} 个头像")

    log(f"\n🔢 全站去重后唯一头像：{len(by_pid)} 个")

    downloaded = skipped = removed = 0
    seen_pids = set()

    for pid, cands in by_pid.items():
        seen_pids.add(pid)
        winner = choose(pid, cands)
        prev = manifest.get(pid)
        # 未变化：sha 一致且文件还在 → 跳过
        if prev and prev.get("sha") == winner["sha"] and \
                os.path.exists(os.path.join(OUT_DIR, prev.get("file", ""))):
            skipped += 1
            continue
        # 下载入池
        if not winner["download_url"]:
            continue
        try:
            r = SESSION.get(winner["download_url"], timeout=60)
            r.raise_for_status()
        except requests.RequestException as e:
            log(f"  [警告] 下载失败 pid={pid}: {e}")
            continue
        # ext 变了的话，删掉旧扩展名的文件
        if prev and prev.get("file") and prev["file"] != winner["fname"]:
            old = os.path.join(OUT_DIR, prev["file"])
            if os.path.exists(old):
                os.remove(old)
        with open(os.path.join(OUT_DIR, winner["fname"]), "wb") as f:
            f.write(r.content)
        manifest[pid] = {
            "file": winner["fname"], "sha": winner["sha"],
            "size": winner["size"], "src": winner["repo"],
        }
        downloaded += 1

    # 清理：池子里有、但全站已不存在的 pid（账号删了等），从 manifest 和磁盘移除
    for pid in list(manifest.keys()):
        if pid not in seen_pids:
            old = os.path.join(OUT_DIR, manifest[pid].get("file", ""))
            if os.path.exists(old):
                os.remove(old)
                removed += 1
            del manifest[pid]

    with open(MANIFEST_PATH, "w", encoding="utf-8") as f:
        json.dump(manifest, f, ensure_ascii=False, indent=0)

    log(f"\n✅ 完成：新增/更新 {downloaded}，未变跳过 {skipped}，清理 {removed}")
    log(f"📦 池子现有头像：{len(manifest)} 个")
    return 0


if __name__ == "__main__":
    sys.exit(main())
