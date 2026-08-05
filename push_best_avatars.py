#!/usr/bin/env python3
# ============================================================================
# push_best_avatars.py — 把头像池里更清晰的版本推回各存档仓库
# ----------------------------------------------------------------------------
# 与 aggregate_avatars.py 配套、方向相反：
#   aggregate 把各仓库最清晰的头像收进池子；
#   本脚本把池子里的清晰版推回还拿着糊版的仓库，让全站立刻对齐，
#   不必等各仓库自己的更新周期从池子慢慢自愈。
#
# 该不该推 —— 对每个仓库里的 avatar_{pid} 文件：
#   1. pid 不在池子里                → 不推（池子没有更好的）
#   2. 文件名（含扩展名）和池子不一致 → 不推！清洗后的 HTML 和 index.json
#      里写死了带扩展名的文件名，换名字会把引用打断（此类会单独列出）
#   3. sha 和池子一致                → 不推（就是同一份）
#   4. 下载实测：仓库版像素 ≥ 池子版 → 不推（人家不比你差；
#      仓库版更清晰的情况留给 aggregate 下轮收编）
#   5. 仓库版像素 < 池子版（含仓库版损坏解不开）→ 推
#
# 推送用 Git Data API 按仓库合批：一个仓库一个 commit，不管修几张。
#
# 运行要求：
#   - 在 home 检出目录里跑（读本地 avatars/ 与 _manifest.json）
#   - 环境变量 PUSH_TOKEN：对组织仓库有 contents:write 权限的 PAT
#     （home 的默认 GITHUB_TOKEN 只能写 home 自己，不行）
#   - DRY_RUN=1 时只打印计划，不真推（默认 1，看清楚再来真的）
#   - 建议先跑一轮 aggregate_avatars 再跑本脚本，保证池子是最新的
# 依赖：requests pillow
# ============================================================================

import base64
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
EXCLUDE_REPO_NAMES = {"home"}
POOL_DIR = os.environ.get("AVATAR_POOL_OUT", "avatars")
MANIFEST_PATH = os.path.join(POOL_DIR, "_manifest.json")

SCAN_WORKERS = int(os.environ.get("AVATAR_POOL_SCAN_WORKERS", "8"))
FETCH_WORKERS = int(os.environ.get("AVATAR_POOL_FETCH_WORKERS", "12"))

DRY_RUN = os.environ.get("DRY_RUN", "1") != "0"

TOKEN = os.environ.get("PUSH_TOKEN", "")
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


def _request(method, url, payload=None, params=None):
    """带轻量重试的请求。404 返回 None；其余错误重试后抛出。"""
    for attempt in range(4):
        try:
            r = SESSION.request(method, url, json=payload, params=params, timeout=60)
            if r.status_code == 404:
                return None
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
            return r.json() if r.text else {}
        except requests.RequestException as e:
            if attempt == 3:
                raise
            time.sleep(2 * (attempt + 1))
    raise RuntimeError(f"{method} {url} 重试耗尽")


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
    """列出组织下所有仓库（含私有，分页）。返回 [(owner/name, 默认分支), ...]

    分页失败必须报错退出，不能 break：静默截断会让后面几百个仓库一次都没扫到，
    而日志上只表现为"待扫描仓库"数字偏小，极难发现。"""
    repos = []
    page = 1
    while True:
        data = None
        for attempt in range(3):
            st, data = api_get(f"{API}/orgs/{org}/repos",
                               params={"per_page": 100, "page": page, "type": "all"})
            if st != "err":
                break
            SCAN_ERRORS[0] += 1
            time.sleep(2 * (attempt + 1))
        else:
            raise RuntimeError(f"列举组织仓库第 {page} 页连续失败，中止以免只扫到一部分")
        if not data:
            break
        repos.extend(data)
        if len(data) < 100:
            break
        page += 1

    expected = api_get(f"{API}/orgs/{org}")[1] or {}
    total = (expected.get("public_repos") or 0) + (expected.get("total_private_repos") or 0)
    if total and len(repos) < total * 0.9:
        raise RuntimeError(f"只列出 {len(repos)} 个仓库，组织实际约 {total} 个，疑似分页截断")

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
    try:
        with Image.open(io.BytesIO(content)) as im:
            return int(im.width), int(im.height)
    except Exception:
        return 0, 0


def push_repo_batch(repo, items):
    """把若干文件以单个 commit 推进仓库。items: [{path, content(bytes)}]"""
    info = _request("GET", f"{API}/repos/{repo}")
    branch = info.get("default_branch", "main")
    ref = _request("GET", f"{API}/repos/{repo}/git/ref/heads/{branch}")
    head_sha = ref["object"]["sha"]
    head = _request("GET", f"{API}/repos/{repo}/git/commits/{head_sha}")
    base_tree = head["tree"]["sha"]

    entries = []
    for it in items:
        blob = _request("POST", f"{API}/repos/{repo}/git/blobs", {
            "content": base64.b64encode(it["content"]).decode(),
            "encoding": "base64",
        })
        entries.append({"path": it["path"], "mode": "100644",
                        "type": "blob", "sha": blob["sha"]})

    tree = _request("POST", f"{API}/repos/{repo}/git/trees",
                    {"base_tree": base_tree, "tree": entries})
    commit = _request("POST", f"{API}/repos/{repo}/git/commits", {
        "message": f"🖼️ 头像清晰度修复（{len(items)} 张，来自共享头像池）[skip ci]",
        "tree": tree["sha"], "parents": [head_sha],
    })
    _request("PATCH", f"{API}/repos/{repo}/git/refs/heads/{branch}",
             {"sha": commit["sha"]})


def main():
    if not TOKEN:
        log("❌ 缺少 PUSH_TOKEN（需要对组织仓库有 contents:write 权限的 PAT）")
        return 1

    try:
        with open(MANIFEST_PATH, encoding="utf-8") as f:
            manifest = json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        log(f"❌ 读不到 {MANIFEST_PATH}，请在 home 检出目录里运行")
        return 1

    # 池文件内容缓存（懒加载）；顺便兜底补测老 manifest 缺的 w/h
    pool_bytes = {}

    def pool_content(pid):
        if pid not in pool_bytes:
            path = os.path.join(POOL_DIR, manifest[pid]["file"])
            with open(path, "rb") as f:
                pool_bytes[pid] = f.read()
        return pool_bytes[pid]

    for pid, ent in manifest.items():
        if "w" not in ent or "h" not in ent:
            try:
                ent["w"], ent["h"] = measure(pool_content(pid))
            except OSError:
                ent["w"] = ent["h"] = 0

    log(f"📦 池子头像：{len(manifest)} 个   模式：{'试运行（只看不推）' if DRY_RUN else '实际推送'}")

    repos = list_org_repos(ORG)
    log(f"📋 待扫描仓库：{len(repos)} 个")

    # ── 扫描（并发）────────────────────────────────────────────────────────
    all_files = []
    _done = [0]

    def scan(item):
        repo, branch = item
        files = find_avatar_files(repo, branch)
        with _log_lock:
            _done[0] += 1
            print(f"  [{_done[0]}/{len(repos)}] {repo}: {len(files)} 个头像", flush=True)
        return files

    with ThreadPoolExecutor(max_workers=SCAN_WORKERS) as ex:
        for files in ex.map(scan, repos):
            all_files.extend(files)

    # ── 初筛（不需要下载的判断）─────────────────────────────────────────────
    ext_mismatch = []
    need_check = []
    same = not_in_pool = 0
    for f in all_files:
        ent = manifest.get(f["pid"])
        if not ent:
            not_in_pool += 1
            continue
        if f["sha"] == ent.get("sha"):
            same += 1
            continue
        if f["fname"] != ent["file"]:
            ext_mismatch.append(f)      # 扩展名不同：HTML/索引写死了文件名，不能换
            continue
        need_check.append(f)

    log(f"\n🔍 初筛：与池一致 {same}，池中没有 {not_in_pool}，"
        f"扩展名不一致(跳过) {len(ext_mismatch)}，需实测比较 {len(need_check)}")

    # ── 下载实测（并发）────────────────────────────────────────────────────
    def fetch(f):
        try:
            r = SESSION.get(f["download_url"], timeout=60)
            r.raise_for_status()
            f["w"], f["h"] = measure(r.content)
            f["bytes"] = len(r.content)
        except requests.RequestException:
            f["w"] = f["h"] = -1        # 下载失败：跳过，别当成损坏去修

    with ThreadPoolExecutor(max_workers=FETCH_WORKERS) as ex:
        list(ex.map(fetch, need_check))

    # ── 决断 ───────────────────────────────────────────────────────────────
    plan = {}                            # repo -> [file dict]
    repo_better = equal = fetch_fail = 0
    for f in need_check:
        if f.get("w", -1) < 0:
            fetch_fail += 1
            continue
        ent = manifest[f["pid"]]
        # 与 aggregate_avatars.py 的 quality_key 保持一致：(像素面积, 字节数)。
        # 之前这里只比面积，导致同尺寸但压缩更狠的糊图被判成"打平"永远换不掉——
        # 实测同为 400×400、仓库版 2.8KB 对池子版 31KB，那是缩略图拉伸的结果。
        pool_key = (ent.get("w", 0) * ent.get("h", 0), ent.get("size", 0))
        repo_key = (f["w"] * f["h"], f.get("bytes", 0))
        if repo_key > pool_key:
            repo_better += 1             # 仓库版更清晰：留给 aggregate 收编
        elif repo_key == pool_key:
            equal += 1                   # 完全一致：不折腾
        else:
            plan.setdefault(f["repo"], []).append(f)

    total_push = sum(len(v) for v in plan.values())
    log(f"⚖️ 决断：应推送 {total_push}（涉及 {len(plan)} 个仓库），"
        f"仓库版更优 {repo_better}，完全一致 {equal}，下载失败 {fetch_fail}")

    if repo_better:
        log("   ↑ 「仓库版更优」说明池子落后了，建议先重跑一轮汇总头像池")

    if ext_mismatch:
        log("\n📎 扩展名不一致清单（如需处理要连 HTML/索引一起改，本脚本不动）：")
        for f in ext_mismatch[:20]:
            log(f"   {f['repo']}/{f['path']}  vs 池内 {manifest[f['pid']]['file']}")
        if len(ext_mismatch) > 20:
            log(f"   … 共 {len(ext_mismatch)} 个")

    if not plan:
        log("\n✅ 没有需要推送的文件")
        return 0

    # ── 推送 / 试运行 ──────────────────────────────────────────────────────
    pushed_repos = pushed_files = failed_repos = 0
    for repo, items in sorted(plan.items()):
        heads = ", ".join(i["fname"] for i in items[:3])
        more = f" 等 {len(items)} 张" if len(items) > 3 else ""
        if DRY_RUN:
            log(f"   [试运行] {repo}: {heads}{more}")
            continue
        try:
            payload = [{"path": i["path"], "content": pool_content(i["pid"])}
                       for i in items]
            push_repo_batch(repo, payload)
            pushed_repos += 1
            pushed_files += len(items)
            log(f"   ✅ {repo}: 推送 {len(items)} 张")
        except Exception as e:
            failed_repos += 1
            log(f"   ❌ {repo}: {str(e)[:80]}")

    if DRY_RUN:
        log(f"\n👀 试运行结束：将推送 {total_push} 张到 {len(plan)} 个仓库。"
            f"确认无误后用 DRY_RUN=0 实际执行")
    else:
        log(f"\n✅ 推送完成：{pushed_files} 张 / {pushed_repos} 个仓库，"
            f"失败 {failed_repos} 个仓库")
    return 0


if __name__ == "__main__":
    sys.exit(main())
