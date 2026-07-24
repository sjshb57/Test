#!/usr/bin/env python3
# ============================================================================
# aggregate_avatars.py — 全站共享头像池汇总
# ----------------------------------------------------------------------------
# 扫描组织下所有存档仓库的 avatar/ 目录，按 pid 去重后汇总到 home/avatars/，
# 供 archive.py 下头像时优先命中（GitHub CDN 秒取，避免重复从 Wayback 下载）。
#
# 选优规则（同一个 avatar_{pid} 在多个仓库都有、且内容不同时）：
#   同一个 pid 永远对应同一张图，差别只是 Wayback 存到的分辨率档位 /
#   压缩程度不同，因此「哪份更清晰」是唯一有意义的标准：
#     1. 像素面积（宽 × 高）大者胜 —— 真实解码测量，jpg/png 混存也能正确比较
#     2. 像素相同再比文件字节数（压缩更轻者胜）
#   池子里已有的旧版本也参与比较：新候选比现存的糊就保留现存的（防降级）。
#   无法解码的候选按 0×0 处理，自然落败；全员损坏时按字节数取大保底。
#
# 冲突候选的下载与测量多线程进行；决策与写盘串行。
# 在 home 仓库的 Action 里运行，只写 home 自己（默认 GITHUB_TOKEN 即可）。
# 依赖：requests pillow
# ============================================================================

import io
import json
import os
import re
import sys
import threading
import time
import urllib.parse
from concurrent.futures import ThreadPoolExecutor

import requests
from PIL import Image

# ── 配置 ────────────────────────────────────────────────────────────────────

ORG = os.environ.get("AVATAR_POOL_ORG", "TwitterArchiver")

# 额外纳入的仓库（组织外的，owner/name 形式，逗号分隔）。
EXTRA_REPOS = [
    r.strip() for r in os.environ.get("AVATAR_POOL_EXTRA_REPOS", "").split(",")
    if r.strip()
]

EXCLUDE_REPO_NAMES = {"home"}

OUT_DIR = os.environ.get("AVATAR_POOL_OUT", "avatars")
MANIFEST_PATH = os.path.join(OUT_DIR, "_manifest.json")

# 扫描仓库 / 下载测量 两个阶段的并发线程数
SCAN_WORKERS = int(os.environ.get("AVATAR_POOL_SCAN_WORKERS", "8"))
FETCH_WORKERS = int(os.environ.get("AVATAR_POOL_FETCH_WORKERS", "12"))

TOKEN = os.environ.get("GITHUB_TOKEN", "")
API = "https://api.github.com"

SESSION = requests.Session()
SESSION.headers.update({
    "Accept": "application/vnd.github+json",
    "X-GitHub-Api-Version": "2022-11-28",
})
if TOKEN:
    SESSION.headers["Authorization"] = f"Bearer {TOKEN}"

_adapter = requests.adapters.HTTPAdapter(
    pool_connections=FETCH_WORKERS * 2, pool_maxsize=FETCH_WORKERS * 2,
    max_retries=0,
)
SESSION.mount("https://", _adapter)

_AVATAR_RE = re.compile(r"^avatar_(\d+)\.(?:jpg|jpeg|png|gif|webp)$", re.IGNORECASE)

_log_lock = threading.Lock()


def log(*a):
    with _log_lock:
        print(*a, flush=True)


def api_get(url, params=None):
    """带轻量重试的 GET。返回 (状态, json)：
    状态 "ok" 正常 / "404" 不存在 / "err" 请求失败。线程安全。"""
    for attempt in range(4):
        try:
            r = SESSION.get(url, params=params, timeout=30)
            if r.status_code == 404:
                return "404", None
            if r.status_code in (403, 429):
                reset = r.headers.get("X-RateLimit-Reset")
                wait = 5 * (attempt + 1)
                if reset:
                    try:
                        wait = max(wait, int(reset) - int(time.time()) + 2)
                    except ValueError:
                        pass
                wait = min(wait, 90)
                log(f"   [限流] 等 {wait}s 重试 …")
                time.sleep(wait)
                continue
            r.raise_for_status()
            return "ok", r.json()
        except requests.RequestException as e:
            if attempt == 3:
                log(f"   [警告] GET 失败 {url}: {e}")
                return "err", None
            time.sleep(2 * (attempt + 1))
    return "err", None


# 扫描期间是否遇到过失败/截断（决定是否允许清理）
SCAN_ERRORS = [0]


def list_org_repos(org):
    """列出组织下所有公开仓库（分页）。返回 [(owner/name, 默认分支), ...]"""
    repos = []
    page = 1
    while True:
        st, data = api_get(f"{API}/orgs/{org}/repos",
                           params={"per_page": 100, "page": page, "type": "public"})
        if st == "err":
            SCAN_ERRORS[0] += 1
        if not data:
            break
        repos.extend(data)
        if len(data) < 100:
            break
        page += 1
    return [(f"{org}/{r['name']}", r.get("default_branch", "main"))
            for r in repos if r["name"] not in EXCLUDE_REPO_NAMES]


def list_contents(repo, path):
    """列目录内容。目录不存在返回 []；请求失败记入 SCAN_ERRORS。
    注意：此 API 单目录最多返回 1000 条，只可用于小目录。"""
    st, data = api_get(f"{API}/repos/{repo}/contents/{urllib.parse.quote(path)}")
    if st == "err":
        SCAN_ERRORS[0] += 1
    return data if isinstance(data, list) else []


def find_avatar_files(repo, branch):
    """在一个仓库里找出所有账号的头像文件。
    avatar 目录经常超过 1000 个文件，Contents API 会静默截断，
    因此用 Git Trees API 取全量（上限 10 万条，且有 truncated 标志）。
    返回 [{pid,fname,sha,size,download_url,repo,path}, ...]"""
    found = []
    accounts = list_contents(repo, "accounts")
    acct_dirs = [c["name"] for c in accounts if c.get("type") == "dir"]
    for acct in acct_dirs:
        snap_path = f"accounts/{acct}/wayback_snapshots"
        snap = list_contents(repo, snap_path)          # 小目录，不会截断
        av = next((c for c in snap
                   if c.get("name") == "avatar" and c.get("type") == "dir"), None)
        if not av:
            continue
        st, tree = api_get(f"{API}/repos/{repo}/git/trees/{av['sha']}")
        if st != "ok" or not tree:
            SCAN_ERRORS[0] += 1
            continue
        if tree.get("truncated"):
            log(f"   [警告] {repo} avatar 树被截断（>10 万条），本轮跳过清理")
            SCAN_ERRORS[0] += 1
        for e in tree.get("tree", []):
            if e.get("type") != "blob":
                continue
            m = _AVATAR_RE.match(e["path"])
            if not m:
                continue
            full = f"{snap_path}/avatar/{e['path']}"
            found.append({
                "pid": m.group(1), "fname": e["path"], "sha": e["sha"],
                "size": e.get("size", 0),
                "download_url":
                    f"https://raw.githubusercontent.com/{repo}/{branch}/"
                    + urllib.parse.quote(full),
                "repo": repo, "path": full,
            })
    return found


def measure(content: bytes):
    """返回 (宽, 高)；解码失败返回 (0, 0)。"""
    try:
        with Image.open(io.BytesIO(content)) as im:
            return int(im.width), int(im.height)
    except Exception:
        return 0, 0


def quality_key(c):
    """清晰度排序键：像素面积优先，字节数决胜。"""
    return (c.get("w", 0) * c.get("h", 0), c.get("bytes", 0))


def load_manifest():
    try:
        with open(MANIFEST_PATH, encoding="utf-8") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def backfill_dims(manifest):
    """老版本 manifest 没有 w/h：就地测量本地池文件补齐（一次性迁移）。"""
    filled = 0
    for pid, ent in manifest.items():
        if "w" in ent and "h" in ent:
            continue
        path = os.path.join(OUT_DIR, ent.get("file", ""))
        if not os.path.isfile(path):
            continue
        with open(path, "rb") as f:
            data = f.read()
        ent["w"], ent["h"] = measure(data)
        ent["size"] = len(data)
        filled += 1
    if filled:
        log(f"🧭 manifest 迁移：补齐 {filled} 条宽高信息")


def main():
    os.makedirs(OUT_DIR, exist_ok=True)
    manifest = load_manifest()   # pid -> {"file","sha","size","w","h","src"}
    backfill_dims(manifest)

    repos = list_org_repos(ORG) + [(r, "main") for r in EXTRA_REPOS]
    log(f"📋 待扫描仓库：{len(repos)} 个")

    # ── 扫各仓库（并发）────────────────────────────────────────────────────
    by_pid = {}          # pid -> [候选 dict]
    _scan_done = [0]

    def scan(item):
        repo, branch = item
        files = find_avatar_files(repo, branch)
        with _log_lock:
            _scan_done[0] += 1
            print(f"  [{_scan_done[0]}/{len(repos)}] {repo}: {len(files)} 个头像",
                  flush=True)
        return files

    with ThreadPoolExecutor(max_workers=SCAN_WORKERS) as ex:
        for files in ex.map(scan, repos):
            for c in files:
                by_pid.setdefault(c["pid"], []).append(c)

    log(f"\n🔢 全站唯一头像：{len(by_pid)} 个")

    # ── 分流：稳定项直接跳过，其余进入评估 ──────────────────────────────────
    # 稳定 = 所有候选 sha 都等于池子现存 sha，且池文件还在
    eval_pids = []
    stable = 0
    for pid, cands in by_pid.items():
        prev = manifest.get(pid)
        shas = {c["sha"] for c in cands}
        if prev and shas == {prev.get("sha")} and \
                os.path.isfile(os.path.join(OUT_DIR, prev.get("file", ""))):
            stable += 1
            continue
        eval_pids.append(pid)

    log(f"⚖️ 无变化 {stable} 个；需评估 {len(eval_pids)} 个")

    # ── 下载并测量候选（并发；同 sha 只下一次）─────────────────────────────
    tasks = []
    for pid in eval_pids:
        prev = manifest.get(pid)
        seen_sha = set()
        for c in by_pid[pid]:
            if c["sha"] in seen_sha:
                continue
            # 池子现存的那份不用下载，本地就有
            if prev and c["sha"] == prev.get("sha"):
                seen_sha.add(c["sha"])
                continue
            if not c["download_url"]:
                continue
            seen_sha.add(c["sha"])
            tasks.append(c)

    log(f"⬇️ 需下载测量的候选：{len(tasks)} 个（{FETCH_WORKERS} 线程）")
    fetch_failed = [0]

    def fetch(c):
        try:
            r = SESSION.get(c["download_url"], timeout=60)
            r.raise_for_status()
            c["content"] = r.content
            c["bytes"] = len(r.content)
            c["w"], c["h"] = measure(r.content)
        except requests.RequestException as e:
            c["content"] = None
            with _log_lock:
                fetch_failed[0] += 1
                print(f"   [警告] 下载失败 {c['repo']}/{c['fname']}: {e}", flush=True)

    with ThreadPoolExecutor(max_workers=FETCH_WORKERS) as ex:
        list(ex.map(fetch, tasks))

    # ── 决策 + 写盘（串行）─────────────────────────────────────────────────
    updated = kept = failed = 0
    for idx, pid in enumerate(eval_pids, 1):
        prev = manifest.get(pid)
        cands = [c for c in by_pid[pid] if c.get("content")]

        pool_entry = None
        if prev:
            pool_path = os.path.join(OUT_DIR, prev.get("file", ""))
            if os.path.isfile(pool_path):
                pool_entry = {
                    "is_pool": True, "fname": prev["file"], "sha": prev.get("sha"),
                    "bytes": prev.get("size", 0),
                    "w": prev.get("w", 0), "h": prev.get("h", 0),
                    "src": prev.get("src", ""),
                }

        contenders = cands + ([pool_entry] if pool_entry else [])
        if not contenders:
            failed += 1
            continue

        winner = max(contenders, key=quality_key)

        if winner.get("is_pool"):
            kept += 1          # 防降级：现存的最清晰，保留
            continue

        # 扩展名变了的话，删掉旧文件
        if prev and prev.get("file") and prev["file"] != winner["fname"]:
            old = os.path.join(OUT_DIR, prev["file"])
            if os.path.exists(old):
                try:
                    os.remove(old)
                except OSError:
                    pass

        with open(os.path.join(OUT_DIR, winner["fname"]), "wb") as f:
            f.write(winner["content"])
        manifest[pid] = {
            "file": winner["fname"], "sha": winner["sha"],
            "size": winner["bytes"], "w": winner["w"], "h": winner["h"],
            "src": winner["repo"],
        }
        updated += 1
        if updated % 200 == 0:
            log(f"   … 已更新 {updated} 张（进度 {idx}/{len(eval_pids)}）")

    # ── 清理：池子里有、但全站已不存在的 pid ────────────────────────────────
    # 双保险：扫描有失败/截断，或要删的数量异常多，都跳过清理。
    # 宁可池子里多留几张，也不能把还存在的头像误删
    # （Contents API 单目录静默截断到 1000 条就曾造成过误删）。
    removed = 0
    to_remove = [pid for pid in manifest if pid not in by_pid]
    allow_mass = os.environ.get("AVATAR_POOL_ALLOW_MASS_DELETE") == "1"
    if SCAN_ERRORS[0]:
        log(f"⚠️ 扫描期间有 {SCAN_ERRORS[0]} 次失败/截断，本轮跳过清理"
            f"（待删 {len(to_remove)} 个不动）")
    elif len(to_remove) > 30 and not allow_mass:
        log(f"⚠️ 待删数量异常（{len(to_remove)} > 30），跳过清理。"
            f"确认无误可设 AVATAR_POOL_ALLOW_MASS_DELETE=1 放行")
    else:
        for pid in to_remove:
            old = os.path.join(OUT_DIR, manifest[pid].get("file", ""))
            if os.path.exists(old):
                os.remove(old)
                removed += 1
            del manifest[pid]

    with open(MANIFEST_PATH, "w", encoding="utf-8") as f:
        json.dump(manifest, f, ensure_ascii=False, indent=0)

    log(f"\n✅ 完成：新增/更新 {updated}，无变化 {stable}，防降级保留 {kept}，"
        f"下载失败 {fetch_failed[0]}，无可用候选 {failed}，清理 {removed}")
    log(f"📦 池子现有头像：{len(manifest)} 个")
    return 0


if __name__ == "__main__":
    sys.exit(main())
