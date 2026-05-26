#!/usr/bin/env python3
"""
archive.py — IncandescenceReader 一体化存档工具
================================================

合并了原本分散在 8 个脚本里的所有功能：
  fetch_json.py / 0037.py 的下载部分 → fetch-html
  fetch_media.py                    → fetch-media
  0037.py 的清洗部分                 → clean-html
  build_index.py                    → build-index
  fetch_avatars.py                  → fetch-avatars
  dedup_media.py                    → dedup
  _gen_list.py                      → gen-lists
  convert_ours.py                   → convert
  render_html_json.py               → render-html

依赖：
  pip install requests beautifulsoup4

用法：
  cd accounts/<username>
  python ../../archive.py <子命令> [选项]

公开账号工作流（Wayback）：
  python ../../archive.py fetch-cdx <username>
  python ../../archive.py fetch-html
  python ../../archive.py fetch-media
  python ../../archive.py clean-html
  python ../../archive.py build-index
  # 或一把梭（不含 fetch-cdx）：
  python ../../archive.py all

私密账号工作流（dump 转换）：
  python ../../archive.py convert <dump_dir>
  python ../../archive.py render-html
  python ../../archive.py fetch-media       # 补缺
  python ../../archive.py build-index

维护/修复：
  python ../../archive.py fetch-avatars [--retry]
  python ../../archive.py dedup [--execute] [--backup] [--delete-orphans]
  python ../../archive.py gen-lists

每个 fetch 子命令都支持 --retry [--file PATH]，读取失败清单只重跑失败项。
"""
from __future__ import annotations

import argparse
import html as html_module
import json
import os
import random
import re
import shutil
import signal
import sys
import threading
import time
from collections import defaultdict, Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from urllib.parse import parse_qsl, urlencode, urlparse, urlunparse

import requests
from bs4 import BeautifulSoup


# ============================================================================
# ── 配置 ────────────────────────────────────────────────────────────────────
# ============================================================================

# 工作目录布局（与 AnIncanescence 项目对齐）
OUTPUT_DIR  = "./wayback_snapshots"
HTML_DIR    = os.path.join(OUTPUT_DIR, "html")
JSON_DIR    = os.path.join(OUTPUT_DIR, "json")
IMAGE_DIR   = os.path.join(OUTPUT_DIR, "image")
VIDEO_DIR   = os.path.join(OUTPUT_DIR, "video")
AVATAR_DIR  = os.path.join(OUTPUT_DIR, "avatar")

INDEX_FILE = os.path.join(OUTPUT_DIR, "index.json")

# ── _log 目录：所有状态追踪文件 ─────────────────────────────────────────────
# 设计文档：DESIGN.md
# - archive_index.json: 主账本（单一真相源）
# - 18 个 .txt 文件: 人类可读视图（实时同步）
LOG_DIR = os.path.join(OUTPUT_DIR, "_log")
ARCHIVE_INDEX_FILE = os.path.join(LOG_DIR, "archive_index.json")

# 每类资源都有三个 .txt: done / failed (可救) / failed_all (含永久失败)
# 注意 failed.txt ⊂ failed_all.txt（包含关系）

# HTML 级（URL 粒度）
DONE_HTML            = os.path.join(LOG_DIR, "html_done.txt")
FAILED_HTML          = os.path.join(LOG_DIR, "html_failed.txt")
FAILED_HTML_ALL      = os.path.join(LOG_DIR, "html_failed_all.txt")

# Media 级（JSON 文件粒度，整条 JSON 全部成功才算 done）
DONE_MEDIA           = os.path.join(LOG_DIR, "media_done.txt")
FAILED_MEDIA         = os.path.join(LOG_DIR, "media_failed.txt")
FAILED_MEDIA_ALL     = os.path.join(LOG_DIR, "media_failed_all.txt")

# 图片级（URL 粒度）
DONE_IMAGE           = os.path.join(LOG_DIR, "image_done.txt")
FAILED_IMAGE         = os.path.join(LOG_DIR, "image_failed.txt")
FAILED_IMAGE_ALL     = os.path.join(LOG_DIR, "image_failed_all.txt")

# 视频级（URL 粒度）
DONE_VIDEO           = os.path.join(LOG_DIR, "video_done.txt")
FAILED_VIDEO         = os.path.join(LOG_DIR, "video_failed.txt")
FAILED_VIDEO_ALL     = os.path.join(LOG_DIR, "video_failed_all.txt")

# 头像级（URL 粒度）
DONE_AVATAR          = os.path.join(LOG_DIR, "avatar_done.txt")
FAILED_AVATAR        = os.path.join(LOG_DIR, "avatar_failed.txt")
FAILED_AVATAR_ALL    = os.path.join(LOG_DIR, "avatar_failed_all.txt")

# 所有 .txt 文件的列表（用于初始化时统一确保存在）
ALL_LOG_TXT_FILES = [
    DONE_HTML, FAILED_HTML, FAILED_HTML_ALL,
    DONE_MEDIA, FAILED_MEDIA, FAILED_MEDIA_ALL,
    DONE_IMAGE, FAILED_IMAGE, FAILED_IMAGE_ALL,
    DONE_VIDEO, FAILED_VIDEO, FAILED_VIDEO_ALL,
    DONE_AVATAR, FAILED_AVATAR, FAILED_AVATAR_ALL,
]


# 清单与备份
URL_LIST_FILE   = os.path.join(OUTPUT_DIR, "_url_list.txt")
MEDIA_LIST_FILE = os.path.join(OUTPUT_DIR, "_list_media.txt")
BACKUP_DIR      = os.path.join(OUTPUT_DIR, "html_backup")

# CDX 输入
CDX_LOCAL_FILE = "./cdx_data.json"

# 网络
HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/124.0.0.0 Safari/537.36"
    ),
    "Referer": "https://web.archive.org/",
}
HEADERS_TWITTER_REFERER = {**HEADERS, "Referer": "https://twitter.com/"}

## 重试 / 退避
REQUEST_ATTEMPTS   = 1   # 网络瞬断/超时/SSL 的最大重试次数；4xx 本身不重试
BACKOFF_BASE       = 0.4
BACKOFF_JITTER_MAX = 0.2
MAX_BACKOFF        = 15.0

# 媒体下载 timeout —— 元组形式 (connect_timeout, read_timeout)
# connect 给 5s（正常 TCP 握手远不需要这么久，超过说明服务器限速/不可达）
MEDIA_TIMEOUT_IMAGE  = (3, 10)   # 图片/头像
MEDIA_TIMEOUT_VIDEO  = (3, 12)   # 视频文件可能大
WAYBACK_HTML_TIMEOUT = (5, 10)   # wayback HTML

# 默认并发与延迟（每个子命令可用 CLI 覆盖）
DEFAULT_WORKERS_HTML   = 20
DEFAULT_WORKERS_MEDIA  = 35
DEFAULT_WORKERS_AVATAR = 30
DEFAULT_DELAY_HTML     = 0.4
DEFAULT_DELAY_MEDIA    = 0.2
DEFAULT_DELAY_AVATAR_RANGE = (0.03, 0.20)

# 索引/渲染
TEXT_MAX = 500

# 媒体短响应阈值（小于这个字节数视为限速 / 截断）
MEDIA_MIN_SIZE = 500
HTML_MIN_SIZE  = 200


# ============================================================================
# ── 全局共享状态（线程安全）─────────────────────────────────────────────────
# ============================================================================

_file_lock     = threading.Lock()
_print_lock    = threading.Lock()
_session_local = threading.local()


def safe_print(msg: str) -> None:
    with _print_lock:
        print(msg, flush=True)


def get_session() -> requests.Session:
    """每线程一个 Session，复用 TCP/TLS 连接（减少握手，降低被识别为爬虫的风险）。"""
    s = getattr(_session_local, "session", None)
    if s is None:
        s = requests.Session()
        s.headers.update(HEADERS)
        _session_local.session = s
    return s


def ensure_output_dirs() -> None:
    """确保所有输出目录存在，并确保 _log/ 下所有状态文件存在（哪怕 0 行）。"""
    for d in (OUTPUT_DIR, HTML_DIR, JSON_DIR, IMAGE_DIR, VIDEO_DIR, AVATAR_DIR, LOG_DIR):
        os.makedirs(d, exist_ok=True)
    # 所有 .txt 状态文件必须存在（用户能用 ls _log/ 看到全套状态被跟踪着）
    for path in ALL_LOG_TXT_FILES:
        if not os.path.exists(path):
            try:
                with open(path, "w", encoding="utf-8") as f:
                    pass  # 创建空文件
            except OSError:
                pass


# ============================================================================
# ── 文件名 / 文件状态 ───────────────────────────────────────────────────────
# ============================================================================

def safe_filename(timestamp: str, url: str, ext: str) -> str:
    """
    生成本地文件名的规则（所有子命令必须使用同一份规则，确保命名一致）。
      {timestamp}_{清洗后的URL前缀[:100]}{ext}
    例：20240710091620_twitter_com_AnIncandescence_status_1810966273943019850.json
    """
    url_no_query = url.split("?")[0]
    clean = re.sub(r"[^\w\-_]", "_", url_no_query.replace("https://", "").replace("http://", ""))
    return f"{timestamp}_{clean[:100]}{ext}"


def parse_wayback_line(line: str) -> tuple[str, str] | None:
    """从失败列表里的一行（wayback URL）解析出 (timestamp, original_url)。"""
    line = line.strip()
    if not line or line.startswith("#"):
        return None
    m = re.match(r"https?://web\.archive\.org/web/(\d+)(?:im_|if_)?/(.+)", line)
    if not m:
        return None
    return m.group(1), m.group(2)


# ============================================================================
# ── 退避 / 重试逻辑 ─────────────────────────────────────────────────────────
# ============================================================================

def _compute_backoff(attempt: int) -> float:
    """指数退避 + 随机抖动。attempt 从 1 起计。"""
    delay = BACKOFF_BASE * (2 ** (attempt - 1)) + random.uniform(0, BACKOFF_JITTER_MAX)
    return min(delay, MAX_BACKOFF)


def _parse_retry_after(value: str) -> float | None:
    if not value:
        return None
    raw = str(value).strip()
    if not raw:
        return None
    try:
        return max(0.0, float(raw))
    except ValueError:
        return None


def _rate_limit_wait_from_response(response: requests.Response | None) -> float | None:
    """
    429 时综合 Retry-After（相对秒）与 x-rate-limit-reset（Unix 时间戳），取较大值。
    """
    if response is None:
        return None
    retry_after = _parse_retry_after(response.headers.get("Retry-After", ""))
    reset_at    = _parse_retry_after(response.headers.get("x-rate-limit-reset", ""))
    reset_wait  = None
    if reset_at is not None:
        reset_wait = max(0.0, reset_at - time.time() + 1.0)
    candidates = [v for v in (retry_after, reset_wait) if v is not None]
    return max(candidates) if candidates else None


def _should_retry(exc: Exception) -> bool:
    # SSL 握手失败：wayback 场景下等于"该 URL 未归档"，直接试下一候选
    if isinstance(exc, requests.exceptions.SSLError):
        return False
    # ConnectTimeout：TCP 握手超时，通常是 wayback 限速拒绝连接，重试无意义
    if isinstance(exc, requests.exceptions.ConnectTimeout):
        return False
    if isinstance(exc, requests.HTTPError):
        if exc.response is not None:
            sc = exc.response.status_code
            # 4xx 一般不重试，但 408（超时）/ 429（限速）要重试
            if 400 <= sc < 500 and sc not in (408, 429):
                return False
        return True
    msg = str(exc)
    return any(k in msg for k in (
        "ConnectionError",
        "Timeout", "RemoteDisconnected", "ChunkedEncodingError", "EOF",
        "响应过短", "响应 Content-Type 异常",
    ))


def _retry_wait_for(exc: Exception, attempt: int) -> float:
    """根据异常计算等待时长（429 时尊重 Retry-After）。"""
    wait = _compute_backoff(attempt)
    if isinstance(exc, requests.HTTPError) and exc.response is not None and exc.response.status_code == 429:
        rl_wait = _rate_limit_wait_from_response(exc.response)
        if rl_wait is not None:
            wait = max(wait, rl_wait)
    return wait


# ============================================================================
# ── archive_index.json: 主账本系统 ──────────────────────────────────────────
# ============================================================================
#
# 设计文档：DESIGN.md
#
# 一份"单一真相源"，记录所有 URL 和 JSON 的精确状态。
# - 内存里维护 dict（_archive_index_data）
# - 每 30 秒 + SIGINT + 程序结束时 flush 到 _log/archive_index.json
# - .txt 文件作为人类可读视图，跟内存状态实时同步
#
# 三种状态：
#   done       成功（终态，只增不减）
#   failed     可救失败（408/429/5xx/超时/网络抖动 — 下次还会重试）
#   failed_all 永久失败（SSL / 4xx 除 408/429 — 默认跳过，--force 才重试）
#
# 包含关系：failed.txt ⊂ failed_all.txt
# ============================================================================

_archive_index_data: dict | None = None
_archive_index_dirty: bool = False
_archive_index_lock = threading.RLock()
_archive_index_flush_thread: threading.Thread | None = None
_archive_index_flush_stop = threading.Event()

# 每个 .txt 文件的内存 set（去重快）
_txt_sets: dict[str, set[str]] = {}
_txt_sets_lock = threading.RLock()

# 文件锁（防止 .txt 文件 append/remove 并发交错）
_log_file_lock = threading.RLock()

# 状态常量
STATUS_DONE       = "done"
STATUS_FAILED     = "failed"
STATUS_FAILED_ALL = "failed_all"

# 资源类型常量（对应 archive_index 里的顶级 key）
KIND_HTML   = "html"
KIND_IMAGE  = "images"
KIND_VIDEO  = "videos"
KIND_AVATAR = "avatars"
KIND_MEDIA  = "media"      # JSON 文件级

# kind → 三个 .txt 文件路径
KIND_TO_TXT_FILES: dict[str, tuple[str, str, str]] = {
    KIND_HTML:   (DONE_HTML,   FAILED_HTML,   FAILED_HTML_ALL),
    KIND_IMAGE:  (DONE_IMAGE,  FAILED_IMAGE,  FAILED_IMAGE_ALL),
    KIND_VIDEO:  (DONE_VIDEO,  FAILED_VIDEO,  FAILED_VIDEO_ALL),
    KIND_AVATAR: (DONE_AVATAR, FAILED_AVATAR, FAILED_AVATAR_ALL),
    KIND_MEDIA:  (DONE_MEDIA,  FAILED_MEDIA,  FAILED_MEDIA_ALL),
}


def _make_empty_archive_index() -> dict:
    """空骨架。"""
    return {
        "schema_version": 1,
        "last_updated": "",
        KIND_HTML:   {},
        KIND_IMAGE:  {},
        KIND_VIDEO:  {},
        KIND_AVATAR: {},
        KIND_MEDIA:  {},
    }


def load_archive_index() -> dict:
    """加载 archive_index.json 到内存。失败时返回空骨架并保留损坏文件备份。"""
    global _archive_index_data
    with _archive_index_lock:
        if _archive_index_data is not None:
            return _archive_index_data
        if not os.path.exists(ARCHIVE_INDEX_FILE):
            _archive_index_data = _make_empty_archive_index()
            return _archive_index_data
        try:
            with open(ARCHIVE_INDEX_FILE, encoding="utf-8") as f:
                data = json.load(f)
            # 简单验证
            if not isinstance(data, dict) or "schema_version" not in data:
                raise ValueError("结构无效")
            # 补齐缺失的 key
            empty = _make_empty_archive_index()
            for k in empty:
                if k not in data:
                    data[k] = empty[k]
            _archive_index_data = data
        except Exception as e:
            # 损坏 — 备份后用空骨架
            ts = time.strftime("%Y%m%d_%H%M%S")
            backup = ARCHIVE_INDEX_FILE + f".broken.{ts}"
            try:
                os.rename(ARCHIVE_INDEX_FILE, backup)
                safe_print(f"[archive_index] 文件损坏（{e}），已备份为 {backup}")
                safe_print(f"[archive_index] 建议跑 'archive.py rebuild-index' 重建")
            except OSError:
                pass
            _archive_index_data = _make_empty_archive_index()
        return _archive_index_data


def save_archive_index(force: bool = False) -> None:
    """把内存里的 archive_index 写回磁盘（原子替换）。"""
    global _archive_index_dirty
    with _archive_index_lock:
        if _archive_index_data is None:
            return
        if not force and not _archive_index_dirty:
            return
        _archive_index_data["last_updated"] = time.strftime("%Y-%m-%dT%H:%M:%S")
        os.makedirs(LOG_DIR, exist_ok=True)
        tmp_path = ARCHIVE_INDEX_FILE + ".tmp"
        try:
            with open(tmp_path, "w", encoding="utf-8") as f:
                json.dump(_archive_index_data, f, ensure_ascii=False, indent=2)
            os.replace(tmp_path, ARCHIVE_INDEX_FILE)
            _archive_index_dirty = False
        except Exception as e:
            safe_print(f"[archive_index] 写入失败：{e}")


def mark_index_dirty() -> None:
    """标记 archive_index 已修改，定时器/结束时会自动 flush。"""
    global _archive_index_dirty
    _archive_index_dirty = True


def _flush_loop():
    """后台线程：每 30 秒检查一次 dirty，dirty 就 flush。"""
    while not _archive_index_flush_stop.wait(30):
        try:
            save_archive_index(force=False)
        except Exception:
            pass


def start_archive_index_flush_thread() -> None:
    """启动后台 flush 线程（30s 周期）。"""
    global _archive_index_flush_thread
    if _archive_index_flush_thread is not None and _archive_index_flush_thread.is_alive():
        return
    _archive_index_flush_stop.clear()
    t = threading.Thread(target=_flush_loop, daemon=True, name="archive-index-flush")
    t.start()
    _archive_index_flush_thread = t


def stop_archive_index_flush_thread_and_save() -> None:
    """停止 flush 线程并做最后一次保存。"""
    _archive_index_flush_stop.set()
    if _archive_index_flush_thread is not None:
        _archive_index_flush_thread.join(timeout=2)
    save_archive_index(force=True)


def install_sigint_handler() -> None:
    """SIGINT (Ctrl+C) 处理：保存 archive_index 后正常退出。"""
    def _on_sigint(signum, frame):
        safe_print("\n[archive] 收到中断信号，正在保存状态...")
        try:
            stop_archive_index_flush_thread_and_save()
        except Exception as e:
            safe_print(f"[archive] 状态保存失败：{e}")
        else:
            safe_print(f"[archive] 状态已保存到 {ARCHIVE_INDEX_FILE}")
            safe_print(f"[archive] 可以下次跑相同命令接着继续")
        sys.exit(130)
    try:
        signal.signal(signal.SIGINT, _on_sigint)
    except (ValueError, AttributeError):
        # 不在主线程或平台不支持 — 忽略
        pass


# ============================================================================
# ── .txt 文件 set 管理 API ──────────────────────────────────────────────────
# ============================================================================
#
# 每个 .txt 文件在内存里维护一个 set（去重快）。状态变化时：
#   1. 更新内存 set
#   2. 立即把整个 set 重写到磁盘（如果改动）— 因为去重和"删除某行"必须重写
#
# 为了快速 append（不重写），常见操作是 _txt_add，它先查 set 决定要不要写。
# ============================================================================

def _load_txt_set(path: str) -> set[str]:
    """加载某个 .txt 文件到 set（带 # 注释和空行被过滤）。"""
    with _txt_sets_lock:
        if path in _txt_sets:
            return _txt_sets[path]
        s: set[str] = set()
        if os.path.exists(path):
            try:
                with open(path, encoding="utf-8") as f:
                    for line in f:
                        line = line.strip()
                        if line and not line.startswith("#"):
                            s.add(line)
            except OSError:
                pass
        _txt_sets[path] = s
        return s


def _txt_add(path: str, item: str) -> bool:
    """如果不在 set 里就 append 一行（fsync 立即落盘）。返回是否新增。"""
    with _txt_sets_lock:
        s = _load_txt_set(path)
        if item in s:
            return False
        s.add(item)
    with _log_file_lock:
        try:
            os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
            with open(path, "a", encoding="utf-8") as f:
                f.write(item + "\n")
                f.flush()
                try:
                    os.fsync(f.fileno())
                except OSError:
                    pass
            return True
        except OSError as e:
            safe_print(f"[txt] {path} 写入失败：{e}")
            return False


def _txt_remove(path: str, item: str) -> bool:
    """从 set 移除该行并重写整个文件。返回是否真删了。"""
    with _txt_sets_lock:
        s = _load_txt_set(path)
        if item not in s:
            return False
        s.discard(item)
        # 重写整个文件（保留行顺序：因为我们不存原顺序，这里就按字典序）
        # 实际上 set 本来无序，我们重写时按字典序产出稳定的输出
        items_sorted = sorted(s)
    with _log_file_lock:
        try:
            tmp = path + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                for x in items_sorted:
                    f.write(x + "\n")
                f.flush()
                try:
                    os.fsync(f.fileno())
                except OSError:
                    pass
            os.replace(tmp, path)
            return True
        except OSError as e:
            safe_print(f"[txt] {path} 重写失败：{e}")
            return False


def _txt_contains(path: str, item: str) -> bool:
    """O(1) 查询是否在文件里。"""
    s = _load_txt_set(path)
    with _txt_sets_lock:
        return item in s


# ============================================================================
# ── archive_index 状态变更 API ──────────────────────────────────────────────
# ============================================================================

def get_status(kind: str, key: str) -> str | None:
    """查某个 URL/JSON/HTML 的当前状态。不存在返回 None。"""
    idx = load_archive_index()
    with _archive_index_lock:
        rec = idx.get(kind, {}).get(key)
        if not isinstance(rec, dict):
            return None
        return rec.get("status")


def get_referenced_by(kind: str, url: str) -> list[str]:
    """查某个 URL 被哪些 JSON 引用（反向索引）。"""
    idx = load_archive_index()
    with _archive_index_lock:
        rec = idx.get(kind, {}).get(url)
        if not isinstance(rec, dict):
            return []
        return list(rec.get("referenced_by", []))


def get_depends_on(json_filename: str) -> dict[str, list[str]]:
    """查某个 JSON 引用了哪些 URL（正向引用）。"""
    idx = load_archive_index()
    with _archive_index_lock:
        rec = idx.get(KIND_MEDIA, {}).get(json_filename)
        if not isinstance(rec, dict):
            return {"images": [], "videos": [], "avatars": []}
        d = rec.get("depends_on", {})
        return {
            "images": list(d.get("images", [])),
            "videos": list(d.get("videos", [])),
            "avatars": list(d.get("avatars", [])),
        }


def add_dependency(json_filename: str, url_kind: str, url: str) -> None:
    """
    建立一条 JSON → URL 的引用关系，同时建立反向索引。
    url_kind ∈ {images, videos, avatars}
    """
    idx = load_archive_index()
    with _archive_index_lock:
        # 正向：media[json].depends_on[url_kind].append(url)
        media = idx[KIND_MEDIA]
        if json_filename not in media:
            media[json_filename] = {
                "status": "unknown",
                "depends_on": {"images": [], "videos": [], "avatars": []},
            }
        deps = media[json_filename].setdefault(
            "depends_on", {"images": [], "videos": [], "avatars": []}
        )
        if url not in deps[url_kind]:
            deps[url_kind].append(url)
        # 反向：<url_kind>[url].referenced_by.append(json)
        coll = idx[url_kind]
        if url not in coll:
            coll[url] = {"status": "unknown", "referenced_by": []}
        rb = coll[url].setdefault("referenced_by", [])
        if json_filename not in rb:
            rb.append(json_filename)
        mark_index_dirty()


def _now_iso() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%S")


def evaluate_media_status(json_filename: str) -> str:
    """
    根据 depends_on 里所有 URL 的状态推导 JSON 的状态。
      - 全部 done 或 failed_all → "done"（永久失败不阻止 JSON 算完成）
      - 任一 failed → "failed"（还有可救项）
      - 只剩 failed_all（且没有 done）→ "failed_all"
      - 没有任何依赖 → "done"（一条 JSON 引用了 0 个媒体也算完成）
    """
    deps = get_depends_on(json_filename)
    all_urls = [(KIND_IMAGE, u) for u in deps["images"]] + \
               [(KIND_VIDEO, u) for u in deps["videos"]] + \
               [(KIND_AVATAR, u) for u in deps["avatars"]]
    if not all_urls:
        return STATUS_DONE
    statuses = [get_status(k, u) for k, u in all_urls]
    has_unknown = any(s is None or s == "unknown" for s in statuses)
    has_failed = any(s == STATUS_FAILED for s in statuses)
    has_failed_all = any(s == STATUS_FAILED_ALL for s in statuses)
    has_done = any(s == STATUS_DONE for s in statuses)

    if has_unknown:
        return "unknown"
    if has_failed:
        return STATUS_FAILED
    if has_done and not has_failed_all:
        return STATUS_DONE
    if has_done and has_failed_all:
        return STATUS_DONE  # 永久失败的算已了结，整条算 done
    if has_failed_all and not has_done:
        return STATUS_FAILED_ALL
    return "unknown"


def _sync_txt_files_for(kind: str, key: str, new_status: str) -> None:
    """
    根据新状态同步该 (kind, key) 在三个 .txt 文件里的存在性。
    保证：
      done.txt          只在 status == done 时含
      failed.txt        只在 status == failed 时含
      failed_all.txt    在 status == failed 或 failed_all 时含
    """
    if kind not in KIND_TO_TXT_FILES:
        return
    done_p, failed_p, failed_all_p = KIND_TO_TXT_FILES[kind]
    if new_status == STATUS_DONE:
        _txt_add(done_p, key)
        _txt_remove(failed_p, key)
        _txt_remove(failed_all_p, key)
    elif new_status == STATUS_FAILED:
        _txt_remove(done_p, key)
        _txt_add(failed_p, key)
        _txt_add(failed_all_p, key)
    elif new_status == STATUS_FAILED_ALL:
        _txt_remove(done_p, key)
        _txt_remove(failed_p, key)
        _txt_add(failed_all_p, key)
    # 其它状态（unknown）：不做事


def set_status(kind: str, key: str, new_status: str,
               reason: str = "", trigger_media_sync: bool = True) -> None:
    """
    更新某个 (kind, key) 的状态。
    会自动：
      1. 更新 archive_index 内存
      2. 同步对应的三个 .txt 文件
      3. 若该 URL 是 image/video/avatar，触发引用它的 JSON 的状态重新评估

    注意：done 是终态，已 done 的不会被覆盖（除非显式 set 别的状态）。
    实际上现在的逻辑允许覆盖 — 比如 retry 时 done 不会被改回 failed，但失败状态可以升级到 done。
    """
    idx = load_archive_index()
    with _archive_index_lock:
        coll = idx.setdefault(kind, {})
        rec = coll.setdefault(key, {})
        old_status = rec.get("status")
        rec["status"] = new_status
        rec["last_updated"] = _now_iso()
        if reason:
            rec["last_reason"] = reason
        # miss_count 累计
        if new_status in (STATUS_FAILED, STATUS_FAILED_ALL):
            rec["miss_count"] = int(rec.get("miss_count", 0)) + 1
        mark_index_dirty()

    # 同步 .txt 文件
    _sync_txt_files_for(kind, key, new_status)

    # 反向同步 media 状态（如果改的是 URL）
    if trigger_media_sync and kind in (KIND_IMAGE, KIND_VIDEO, KIND_AVATAR):
        referenced_jsons = get_referenced_by(kind, key)
        for json_filename in referenced_jsons:
            new_media_status = evaluate_media_status(json_filename)
            if new_media_status == "unknown":
                continue
            # 直接更新 media 状态（避免递归）
            idx = load_archive_index()
            with _archive_index_lock:
                rec = idx[KIND_MEDIA].setdefault(json_filename, {})
                cur = rec.get("status")
                if cur != new_media_status:
                    rec["status"] = new_media_status
                    rec["last_updated"] = _now_iso()
                    mark_index_dirty()
                else:
                    continue
            _sync_txt_files_for(KIND_MEDIA, json_filename, new_media_status)


def classify_failure(exc: Exception) -> str:
    """
    把一个异常归类为 STATUS_FAILED（可救）或 STATUS_FAILED_ALL（永久）。

    永久失败：
      - SSL 错误（wayback 场景下等于"未归档"，重试无用）
      - HTTP 4xx 除 408/429
    可救失败：
      - ConnectTimeout（TCP 握手超时，通常是 wayback 限速，换时间/IP 可能成功）
      - HTTP 408/429/5xx
      - 超时 / 网络错误 / ChunkedEncodingError / 响应过短 / Content-Type 异常
    """
    if isinstance(exc, requests.exceptions.SSLError):
        return STATUS_FAILED_ALL
    if isinstance(exc, requests.exceptions.ConnectTimeout):
        return STATUS_FAILED
    if isinstance(exc, requests.HTTPError) and exc.response is not None:
        sc = exc.response.status_code
        if 400 <= sc < 500 and sc not in (408, 429):
            return STATUS_FAILED_ALL
    return STATUS_FAILED


# ============================================================================
# ── 底层网络下载 ────────────────────────────────────────────────────────────
# ============================================================================

def fetch_html_text(url: str, log=None, timeout: int = 30) -> str:
    """
    下载 HTML，强制 UTF-8 解码。带 Session 复用 + 指数退避重试。
    响应小于 HTML_MIN_SIZE 字节视为限速/截断，重试。
    """
    last_exc: Exception | None = None
    for attempt in range(1, REQUEST_ATTEMPTS + 1):
        try:
            with get_session().get(url, timeout=timeout) as resp:
                resp.raise_for_status()
                content = resp.content
                if len(content) < HTML_MIN_SIZE:
                    raise requests.RequestException(
                        f"响应过短（{len(content)} 字节），疑似限速或连接被截断"
                    )
                return content.decode("utf-8", errors="replace")
        except Exception as e:
            last_exc = e
            if not _should_retry(e):
                raise
            if attempt == REQUEST_ATTEMPTS:
                break
            wait = _retry_wait_for(e, attempt)
            if log:
                tag = "429" if (isinstance(e, requests.HTTPError) and e.response is not None
                                and e.response.status_code == 429) else type(e).__name__
                log(f"[重试 {attempt}/{REQUEST_ATTEMPTS-1}] {tag}，等待 {wait:.1f}s")
            time.sleep(wait)
    raise last_exc  # type: ignore[misc]


def download_stream(url: str, filepath: str, log=None, timeout: int = 60,
                    min_size: int = MEDIA_MIN_SIZE,
                    headers: dict | None = None) -> int:
    """
    流式下载到 filepath。带 Session 复用、指数退避、Content-Type / 短响应防御。
    成功返回字节数；失败抛出最后一次异常。
    """
    last_exc: Exception | None = None
    sess = get_session()
    if headers:
        # 临时合并 headers
        merged = {**sess.headers, **headers}
    else:
        merged = None

    for attempt in range(1, REQUEST_ATTEMPTS + 1):
        try:
            # 用 with 包住 response，确保异常路径上也能正确关闭底层 socket，
            # 否则 Python 3.12+ 会在 GC 时打印 "I/O operation on closed file" 警告
            with sess.get(url, timeout=timeout, stream=True, headers=merged) as resp:
                resp.raise_for_status()
                ctype = (resp.headers.get("Content-Type") or "").lower().strip()
                if ctype.startswith("text/") or "html" in ctype:
                    raise requests.RequestException(
                        f"响应 Content-Type 异常 ({ctype})，疑似错误页而非媒体"
                    )
                size = 0
                with open(filepath, "wb") as f:
                    for chunk in resp.iter_content(chunk_size=65536):
                        if chunk:
                            f.write(chunk)
                            size += len(chunk)
                if size < min_size:
                    if os.path.exists(filepath):
                        os.remove(filepath)
                    raise requests.RequestException(
                        f"响应过短（{size} 字节），疑似限速或连接被截断"
                    )
                return size
        except Exception as e:
            last_exc = e
            if os.path.exists(filepath):
                try:
                    os.remove(filepath)
                except OSError:
                    pass
            if not _should_retry(e):
                raise
            if attempt == REQUEST_ATTEMPTS:
                break
            wait = _retry_wait_for(e, attempt)
            if log:
                tag = "429" if (isinstance(e, requests.HTTPError) and e.response is not None
                                and e.response.status_code == 429) else type(e).__name__
                log(f"  [重试 {attempt}/{REQUEST_ATTEMPTS-1}] {tag}，等待 {wait:.1f}s")
            time.sleep(wait)
    raise last_exc  # type: ignore[misc]


def download_with_candidates(urls: list[str], filepath: str, log=None,
                             headers: dict | None = None,
                             timeout: int = 60) -> tuple[int, str]:
    """
    依次尝试每个候选 URL，任一成功即返回 (size, used_url)。
    候选 URL 一个都不跳过 — 即使前几个 4xx/SSL 错误，也继续往下试。
    这能覆盖"推特原站被封但 wayback 有存"的场景。

    每个 URL 自己的重试由 download_stream 控制：
      SSL / 4xx (除 408/429) → download_stream 不重试，直接抛 → 这里走下一个候选
      408/429/5xx/超时/网络抖动 → download_stream 重试 5 次

    """
    last_exc: Exception | None = None
    tried = 0

    for i, url in enumerate(urls, 1):
        tried += 1
        try:
            if log and tried > 1:
                log(f"  [候选 {i}/{len(urls)}] {url}")
            size = download_stream(url, filepath, log=log, headers=headers, timeout=timeout)
            return size, url
        except Exception as e:
            last_exc = e
            continue
    if last_exc:
        raise last_exc
    raise RuntimeError("候选 URL 列表为空")


# ============================================================================
# ── basename / pid 提取（共享给所有子命令）─────────────────────────────────
# ============================================================================

_IMG_BASENAME_NEW_RE = re.compile(
    r"_media_([A-Za-z0-9_\-]+?)_(?:jpg|png|gif|webp|jpeg)\.(?:jpg|png|gif|webp|jpeg)$",
    re.IGNORECASE,
)
_IMG_BASENAME_OLD_RE = re.compile(
    r"_media_([A-Za-z0-9_\-]+?)\.(?:jpg|png|gif|webp|jpeg)$",
    re.IGNORECASE,
)
_IMG_URL_BASENAME_RE = re.compile(
    r"pbs\.twimg\.com/media/([A-Za-z0-9_\-]+?)(?:\.(?:jpg|png|gif|webp|jpeg))?$",
)
_VIDEO_KEY_RE  = re.compile(r"(?:amplify_video|ext_tw_video|tweet_video)[/_](\d+)")
_AVATAR_PID_RE = re.compile(r"^avatar_(\d+)\.(?:jpg|png|gif|webp|jpeg)$", re.IGNORECASE)
_PROFILE_URL_PID_RE = re.compile(r"/profile_images/(\d+)/")
_TIMESTAMP_PREFIX_RE = re.compile(r"^(\d{14})_")


def extract_image_basename(s: str) -> str:
    """从本地文件名或 URL 提取 Twitter 图片 basename。"""
    no_query = s.split("?")[0]
    m = _IMG_BASENAME_NEW_RE.search(no_query)
    if m:
        return m.group(1)
    m = _IMG_BASENAME_OLD_RE.search(no_query)
    if m:
        return m.group(1)
    m = _IMG_URL_BASENAME_RE.search(no_query)
    if m:
        return m.group(1)
    return ""


def extract_video_media_key(s: str) -> str:
    m = _VIDEO_KEY_RE.search(s)
    return m.group(1) if m else ""


def extract_profile_image_id(url: str) -> str:
    m = _PROFILE_URL_PID_RE.search(url)
    return m.group(1) if m else ""


def extract_avatar_pid_from_filename(fname: str) -> str:
    m = _AVATAR_PID_RE.match(fname)
    return m.group(1) if m else ""


def extract_timestamp_from_filename(fname: str) -> str:
    m = _TIMESTAMP_PREFIX_RE.match(fname)
    return m.group(1) if m else ""


def ext_from_url(url: str) -> str:
    """从 URL 推断扩展名（图片/头像）。"""
    path = url.split("?")[0].lower()
    for e in (".png", ".gif", ".webp", ".jpeg", ".jpg"):
        if path.endswith(e):
            return ".jpeg" if e == ".jpeg" else e
    return ".jpg"


# ============================================================================
# ── 候选 URL 构造（原站直链 → wayback 回退）─────────────────────────────────
# ============================================================================

def build_pbs_image_variants(source_url: str) -> list[str]:
    """pbs.twimg.com 图片：orig → 4096x4096 → large → medium → small → 无参数。"""
    variants: list[str] = []
    seen: set[str] = set()

    def add(u: str) -> None:
        if u and u not in seen:
            seen.add(u)
            variants.append(u)

    parsed = urlparse(source_url)
    if parsed.netloc.endswith("pbs.twimg.com") and parsed.path.startswith("/media/"):
        query = dict(parse_qsl(parsed.query, keep_blank_values=True))
        suffix = os.path.splitext(parsed.path)[1].lower()
        format_hint = query.get("format", "")
        normalized_path = parsed.path

        if suffix in {".jpg", ".jpeg", ".png", ".gif", ".webp"}:
            format_hint = format_hint or suffix.lstrip(".")
            normalized_path = parsed.path[: -len(suffix)]

        if format_hint:
            for name_hint in ("orig", "4096x4096", "large", "medium", "small", "900x900"):
                new_q = dict(query)
                new_q["format"] = format_hint
                new_q["name"] = name_hint
                add(urlunparse(parsed._replace(path=normalized_path, query=urlencode(new_q))))

        add(source_url)
        add(urlunparse(parsed._replace(query="")))
    else:
        add(source_url)
        if parsed.query:
            add(urlunparse(parsed._replace(query="")))
    return variants


def build_image_candidate_urls(image_url: str, snapshot_timestamp: str) -> list[str]:
    """图片候选：原站画质回退 → wayback im_/if_/原始 三档回退。"""
    out: list[str] = []
    seen: set[str] = set()

    def add(u: str) -> None:
        if u and u not in seen:
            seen.add(u)
            out.append(u)

    for v in build_pbs_image_variants(image_url):
        add(v)
    if snapshot_timestamp:
        add(f"https://web.archive.org/web/{snapshot_timestamp}im_/{image_url}")
        add(f"https://web.archive.org/web/{snapshot_timestamp}if_/{image_url}")
        add(f"https://web.archive.org/web/{snapshot_timestamp}/{image_url}")
    return out


def build_video_candidate_urls(video_url: str, snapshot_timestamp: str) -> list[str]:
    """视频候选：原站直链 → 去query → wayback 回退。"""
    out: list[str] = []
    seen: set[str] = set()

    def add(u: str) -> None:
        if u and u not in seen:
            seen.add(u)
            out.append(u)

    add(video_url)
    parsed = urlparse(video_url)
    if parsed.netloc.endswith("video.twimg.com") and parsed.query:
        add(urlunparse(parsed._replace(query="")))
    if snapshot_timestamp:
        add(f"https://web.archive.org/web/{snapshot_timestamp}im_/{video_url}")
        add(f"https://web.archive.org/web/{snapshot_timestamp}if_/{video_url}")
        add(f"https://web.archive.org/web/{snapshot_timestamp}/{video_url}")
    return out


def build_avatar_candidate_urls(avatar_url: str, snapshot_timestamp: str) -> list[str]:
    """
    头像候选：原站 400x400（高画质）→ bigger → normal → 原样 → wayback 回退。
    """
    out: list[str] = []
    seen: set[str] = set()

    def add(u: str) -> None:
        if u and u not in seen:
            seen.add(u)
            out.append(u)

    if "_normal." in avatar_url:
        add(avatar_url.replace("_normal.", "_400x400."))
        add(avatar_url.replace("_normal.", "_bigger."))
    add(avatar_url)

    if snapshot_timestamp:
        if "_normal." in avatar_url:
            hq = avatar_url.replace("_normal.", "_400x400.")
            add(f"https://web.archive.org/web/{snapshot_timestamp}im_/{hq}")
        add(f"https://web.archive.org/web/{snapshot_timestamp}im_/{avatar_url}")
        add(f"https://web.archive.org/web/{snapshot_timestamp}if_/{avatar_url}")
    return out


# ============================================================================
# ── 媒体索引（启动时扫描本地建立）── 三类索引、含头像双向反射 ──────────────
# ============================================================================

class MediaIndex:
    """
    本地媒体的统一索引，三类共享：
      image_by_basename:  basename → 本地文件名（不含路径）
      video_by_key:       media_key 数字 → 本地文件名
      avatar_by_pid:      pid → 本地文件名
      avatar_by_name:     name → pid（指向最早建立此索引的 pid）
      avatar_by_username: username → pid

    头像的三路反射：同一用户换头像后 pid 变了，但 name / username 不变，
    通过任一匹配即可复用已有文件，避免重复下载。
    """

    def __init__(self) -> None:
        self.image_by_basename: dict[str, str] = {}
        self.video_by_key:      dict[str, str] = {}
        self.avatar_by_pid:     dict[str, str] = {}
        self.avatar_by_name:    dict[str, str] = {}
        self.avatar_by_username: dict[str, str] = {}
        self._lock = threading.Lock()

    # ── 图片 ───────────────────────────────────────────────────
    def register_image(self, basename: str, fname: str) -> None:
        if not basename:
            return
        with self._lock:
            self.image_by_basename.setdefault(basename, fname)

    def find_image(self, basename: str) -> str:
        with self._lock:
            return self.image_by_basename.get(basename, "")

    # ── 视频 ───────────────────────────────────────────────────
    def register_video(self, key: str, fname: str) -> None:
        if not key:
            return
        with self._lock:
            self.video_by_key.setdefault(key, fname)

    def find_video(self, key: str) -> str:
        with self._lock:
            return self.video_by_key.get(key, "")

    # ── 头像 ───────────────────────────────────────────────────
    def register_avatar(self, pid: str, name: str, username: str, fname: str) -> None:
        """登记一个新下载的头像到三路索引。"""
        with self._lock:
            if pid:
                self.avatar_by_pid.setdefault(pid, fname)
            if name and name not in self.avatar_by_name:
                self.avatar_by_name[name] = pid
            if username and username not in self.avatar_by_username:
                self.avatar_by_username[username] = pid

    def find_avatar(self, pid: str = "", name: str = "", username: str = "",
                    avatar_dir: str = AVATAR_DIR) -> tuple[str, str]:
        """
        按 username → name → pid 顺序查找已下载的头像。
        返回 (文件名, 命中方式)；找不到则返回 ("", "")。
        每次返回前检查实际文件存在，避免索引过期。
        """
        with self._lock:
            if username:
                p = self.avatar_by_username.get(username)
                if p:
                    fn = self.avatar_by_pid.get(p, "")
                    if fn and os.path.exists(os.path.join(avatar_dir, fn)):
                        return fn, "username"
            if name:
                p = self.avatar_by_name.get(name)
                if p:
                    fn = self.avatar_by_pid.get(p, "")
                    if fn and os.path.exists(os.path.join(avatar_dir, fn)):
                        return fn, "name"
            if pid:
                fn = self.avatar_by_pid.get(pid, "")
                if fn and os.path.exists(os.path.join(avatar_dir, fn)):
                    return fn, "pid"
        return "", ""


def _sort_key_image_naming(fname: str) -> tuple[int, str]:
    """优先索引新命名（pbs.twimg.com 原站直链下载），旧 wayback 包装放后面。"""
    return (0 if "_pbs_twimg_com_" in fname else 1, fname)


def _sort_key_video_naming(fname: str) -> tuple[int, str]:
    return (0 if "_video_twimg_com_" in fname else 1, fname)


def build_media_index(scan_json: bool = True, verbose: bool = True) -> MediaIndex:
    """
    扫描 image/ video/ avatar/ 建立索引；可选扫 json/ 补建头像 name/username 反向映射。
    """
    idx = MediaIndex()

    img_count = 0
    if os.path.isdir(IMAGE_DIR):
        for fname in sorted(os.listdir(IMAGE_DIR), key=_sort_key_image_naming):
            basename = extract_image_basename(fname)
            if basename and basename not in idx.image_by_basename:
                idx.image_by_basename[basename] = fname
                img_count += 1

    vid_count = 0
    if os.path.isdir(VIDEO_DIR):
        for fname in sorted(os.listdir(VIDEO_DIR), key=_sort_key_video_naming):
            key = extract_video_media_key(fname)
            if key and key not in idx.video_by_key:
                idx.video_by_key[key] = fname
                vid_count += 1

    av_count = 0
    if os.path.isdir(AVATAR_DIR):
        for fname in os.listdir(AVATAR_DIR):
            pid = extract_avatar_pid_from_filename(fname)
            if pid and pid not in idx.avatar_by_pid:
                idx.avatar_by_pid[pid] = fname
                av_count += 1

    name_link = user_link = 0
    if scan_json and os.path.isdir(JSON_DIR):
        for jname in os.listdir(JSON_DIR):
            if not jname.endswith(".json"):
                continue
            try:
                with open(os.path.join(JSON_DIR, jname), encoding="utf-8") as f:
                    data = json.load(f)
            except Exception:
                continue
            for u in (data.get("includes", {}) or {}).get("users", []) or []:
                url = u.get("profile_image_url") or ""
                pid = extract_profile_image_id(url)
                if not pid or pid not in idx.avatar_by_pid:
                    continue
                name = (u.get("name") or "").strip()
                username = (u.get("username") or "").strip()
                if name and name not in idx.avatar_by_name:
                    idx.avatar_by_name[name] = pid
                    name_link += 1
                if username and username not in idx.avatar_by_username:
                    idx.avatar_by_username[username] = pid
                    user_link += 1

    if verbose:
        safe_print(f"本地媒体索引：{img_count} 张图 / {vid_count} 个视频 / {av_count} 个头像")
        if name_link or user_link:
            safe_print(f"  头像反射映射：{name_link} 个 name / {user_link} 个 username")
    return idx


# ============================================================================
# ── 完成列表 / 失败列表 ─────────────────────────────────────────────────────
# ============================================================================

def load_done_set(path: str) -> set[str]:
    """加载完成列表为 set。文件不存在返回空集合。"""
    if not os.path.exists(path):
        return set()
    out: set[str] = set()
    try:
        with open(path, encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith("#"):
                    out.add(line)
    except Exception:
        pass
    return out


def append_done(path: str, entry: str) -> None:
    """线程安全地追加一行到完成列表；立即 flush + fsync 保证其他进程立即可见。"""
    with _file_lock:
        os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
        with open(path, "a", encoding="utf-8") as f:
            f.write(entry + "\n")
            f.flush()
            try:
                os.fsync(f.fileno())
            except OSError:
                pass


def append_failed(path: str, entry: str) -> None:
    """线程安全地追加一行到失败列表；立即 flush + fsync 保证文件实时可见。
    跟 append_done 配对使用，让用户跑的过程中随时能看到累积进度（不必等到末尾）。"""
    with _file_lock:
        os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
        with open(path, "a", encoding="utf-8") as f:
            f.write(entry + "\n")
            f.flush()
            try:
                os.fsync(f.fileno())
            except OSError:
                pass


def reset_failed_list(path: str, header_comment: str = "") -> None:
    """清空失败列表（运行开始时调用，给实时 append 一个干净起点）。"""
    with _file_lock:
        if os.path.exists(path):
            try:
                os.remove(path)
            except OSError:
                pass
        if header_comment:
            os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
            with open(path, "w", encoding="utf-8") as f:
                f.write(f"# {header_comment}\n")


def write_failed_list(path: str, items: list[str], header_comment: str = "") -> None:
    """
    写入失败列表（覆盖）。空列表则删除文件。
    items：每行一个字符串（URL 或文件名）。
    """
    if not items:
        if os.path.exists(path):
            try:
                os.remove(path)
            except OSError:
                pass
        return
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        if header_comment:
            f.write(f"# {header_comment}\n")
        for it in items:
            f.write(it + "\n")


def load_failed_list(path: str) -> list[str]:
    """加载失败列表为 list（保持顺序、去注释、去空行）。"""
    if not os.path.exists(path):
        return []
    items: list[str] = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith("#"):
                items.append(line)
    return items


# ============================================================================
# ── CDX 快照加载 ────────────────────────────────────────────────────────────
# ============================================================================

def load_snapshots_from_cdx(filepath: str) -> list[tuple[str, str]]:
    """读取本地 CDX JSON 文件，返回 [(timestamp, original_url), ...]。"""
    with open(filepath, encoding="utf-8") as f:
        data = json.load(f)
    if not data or len(data) < 2:
        return []
    headers = data[0]
    ts_idx   = headers.index("timestamp")
    orig_idx = headers.index("original")
    return [(row[ts_idx], row[orig_idx]) for row in data[1:]]


def load_snapshots_from_retry_file(filepath: str) -> list[tuple[str, str]]:
    """从失败列表里读快照。每行格式：https://web.archive.org/web/TS[im_|if_]/ORIG"""
    out: list[tuple[str, str]] = []
    for line in load_failed_list(filepath):
        parsed = parse_wayback_line(line)
        if parsed:
            out.append(parsed)
    return out


def dedupe_snapshots(snapshots: list[tuple[str, str]]) -> list[tuple[str, str]]:
    """CDX 内部去重：同一 (timestamp, original_url) 只保留一条。"""
    seen: set[tuple[str, str]] = set()
    out: list[tuple[str, str]] = []
    for row in snapshots:
        if row not in seen:
            seen.add(row)
            out.append(row)
    return out


# ============================================================================
# ── HTML：JSON 提取、清洗、Source 注释处理 ─────────────────────────────────
# ============================================================================

# 用于剥离 prettify 后 HTML 顶部所有 Source 注释行（含可能的空行）
_SOURCE_COMMENT_RE = re.compile(
    r"\A(?:\s*<!--\s*Source:[^>]*-->\s*\n?)+",
    re.IGNORECASE,
)


def strip_existing_source_comments(html_text: str) -> str:
    """剥掉 HTML 开头所有连续的 <!-- Source: ... --> 注释（防止重复累积）。"""
    return _SOURCE_COMMENT_RE.sub("", html_text)


def extract_json_from_page(html_text: str) -> dict | None:
    """从 wayback if_ 页面提取推文 JSON（来源：<div id='jsonview'><pre>）。"""
    soup = BeautifulSoup(html_text, "html.parser")
    jv = soup.find("div", id="jsonview")
    if jv:
        pre = jv.find("pre")
        if pre:
            try:
                return json.loads(pre.get_text(strip=False))
            except json.JSONDecodeError:
                return None
    return None


def _clean_script_content(src: str) -> str:
    """清掉 jsonview 相关的 JS 噪声。"""
    src = re.sub(r"[ \t]*//\s*console\.log\([^\n]*\)[\n;]?", "", src)
    src = re.sub(r"[ \t]*//\s*let\s+(True|False)\s*=[^\n]*\n?", "", src)
    src = re.sub(r"[ \t]*let\s+jsonView\s*=[^\n]*\n?", "", src)
    src = re.sub(r"[ \t]*const\s+jsonViewLink\s*=[^\n]*\n?", "", src)
    src = re.sub(r"[ \t]*const\s+jsonContent\s*=[^\n]*\n?", "", src)
    src = re.sub(r"[ \t]*const\s+nonJsonContent\s*=[^\n]*\n?", "", src)
    src = re.sub(r"[ \t]*const\s+rerenderPage\s*=.*?\};\s*\n?", "", src, flags=re.DOTALL)
    return src


def clean_html_text(html_text: str, source_url: str, media_index: MediaIndex) -> str:
    """
    清洗与改写 HTML：
      1. 剥掉已有的 Source 注释（防止累积）
      2. 清理 <script> 里的 jsonview 噪声
      3. 改写头像 src → ../avatar/avatar_{pid}.{ext}（直接由 pid 构造，不查 media_index）
      4. 改写推文图片 src → ../image/{filename}（本地有则用真实名，否则构造预期名）
      5. BS4：删 notice / jsonview / 无效图视频，替换 video src
      6. prettify + 去多余空行
      7. 顶部恰好写入 1 行 <!-- Source: ... -->
    """
    # 1. 剥旧 Source
    html_text = strip_existing_source_comments(html_text)

    # 2. script 清理
    html_text = re.sub(
        r"(<script[^>]*>)(.*?)(</script>)",
        lambda m: m.group(1) + _clean_script_content(m.group(2)) + m.group(3),
        html_text,
        flags=re.DOTALL,
    )

    # 3. 替换头像 src — 直接用 pid 构造唯一本地路径，不查 media_index
    def avatar_replacer(match: re.Match) -> str:
        tag = match.group(0)
        src_m = re.search(
            r'src="(https://web\.archive\.org/web/\d+im_/https://[^"]*profile_images/[^"]+)"',
            tag,
        )
        if not src_m:
            return tag
        src_url = src_m.group(1)
        pid = extract_profile_image_id(src_url)
        if not pid:
            return tag
        ext = ".png" if ".png" in src_url.lower() else (
              ".gif" if ".gif" in src_url.lower() else ".jpg")
        return tag.replace(src_m.group(0), f'src="../avatar/avatar_{pid}{ext}"')

    html_text = re.sub(
        r'<img\s[^>]*src="https://web\.archive\.org/web/\d+im_/https://[^"]*profile_images/[^"]+"[^>]*/?>',
        avatar_replacer,
        html_text,
    )

    # 4. 替换推文图片 src
    def image_replacer(match: re.Match) -> str:
        prefix  = match.group(1)
        src_url = match.group(2)
        suffix  = match.group(3)
        basename = extract_image_basename(src_url)
        if basename:
            fn = media_index.find_image(basename)
            if fn:
                return f'{prefix}../image/{fn}{suffix}'
        return match.group(0)

    html_text = re.sub(
        r'(<img\s[^>]*class="tweet-image[^"]*"[^>]*src=")(https://web\.archive\.org/web/\d+im_/[^"]+)(")',
        image_replacer,
        html_text,
    )
    html_text = re.sub(
        r'(<img\s[^>]*src=")(https://web\.archive\.org/web/\d+im_/[^"]+)("[^>]*class="tweet-image[^"]*")',
        image_replacer,
        html_text,
    )

    # 5. BS4：删 notice / jsonview / 无效媒体；替换 video
    soup = BeautifulSoup(html_text, "html.parser")

    for tag in soup.find_all("div", class_="notice"):
        tag.decompose()
    for tag in soup.find_all("div", id="jsonview"):
        tag.decompose()

    # 图片：fn=None 时 src 仍为 wayback 地址 → 删掉，防止破图
    for tag in soup.find_all("img", class_="tweet-image"):
        src = tag.get("src", "")
        if "web.archive.org" in src or src.startswith("http"):
            tag.decompose()

    # 头像：已始终替换为预期本地路径 ../avatar/avatar_<pid>.{ext}

    # 处理每个 <video>
    for video_tag in soup.find_all("video"):
        # 删 m3u8 source
        for src_tag in video_tag.find_all("source"):
            if ".m3u8" in src_tag.get("src", "").lower():
                src_tag.decompose()

        mp4_sources = video_tag.find_all("source")
        if not mp4_sources:
            video_tag.decompose()
            continue

        first_src = mp4_sources[0].get("src", "")
        media_key = extract_video_media_key(first_src)
        local_vname = ""
        if media_key:
            local_vname = media_index.find_video(media_key)
            if local_vname and not os.path.exists(os.path.join(VIDEO_DIR, local_vname)):
                local_vname = ""

        if local_vname:
            for src_tag in mp4_sources:
                src_tag.decompose()
            new_source = soup.new_tag("source", src=f"../video/{local_vname}", type="video/mp4")
            video_tag.append(new_source)
        # 没有本地文件：保留 video 标签（wayback URL），前端检测到 http src 直接删，不发请求

    # 6. prettify + 去多余空行
    try:
        formatted = soup.prettify(indent_chars="  ")  # bs4 >= 4.13
    except TypeError:
        raw = soup.prettify()
        lines = []
        for line in raw.splitlines():
            stripped = line.lstrip(" ")
            depth = (len(line) - len(stripped)) // 4
            lines.append("  " * depth + stripped)
        formatted = "\n".join(lines)

    result_lines = []
    prev_blank = False
    for line in formatted.splitlines():
        is_blank = not line.strip()
        if is_blank and prev_blank:
            continue
        result_lines.append(line)
        prev_blank = is_blank
    cleaned = "\n".join(result_lines)

    # 7. 顶部写入恰好 1 行 Source 注释
    return f"<!-- Source: {source_url} -->\n" + cleaned


def _replace_paths_only(html_text: str, source_url: str, media_index: MediaIndex) -> str:
    """
    已清洗过的 HTML 再次处理时，只替换媒体路径，不重跑 BS4/prettify。
    防止多次 prettify 导致 CSS 缩进累积或格式混乱。
    """
    # 剥旧 Source 注释（单行）
    html_text = strip_existing_source_comments(html_text)

    # 头像：直接构造本地路径
    def avatar_replacer(match: re.Match) -> str:
        tag = match.group(0)
        src_m = re.search(
            r'src="(https://web\.archive\.org/web/\d+im_/https://[^"]*profile_images/[^"]+)"',
            tag,
        )
        if not src_m:
            return tag
        src_url = src_m.group(1)
        pid = extract_profile_image_id(src_url)
        if not pid:
            return tag
        ext = ".png" if ".png" in src_url.lower() else (
              ".gif" if ".gif" in src_url.lower() else ".jpg")
        return tag.replace(src_m.group(0), f'src="../avatar/avatar_{pid}{ext}"')

    html_text = re.sub(
        r'<img\s[^>]*src="https://web\.archive\.org/web/\d+im_/https://[^"]*profile_images/[^"]+"[^>]*/?>',
        avatar_replacer,
        html_text,
    )

    # 图片：有 media_index 记录就替换，否则保持原样（已清洗过的 wayback URL img 已被删）
    def image_replacer(match: re.Match) -> str:
        prefix  = match.group(1)
        src_url = match.group(2)
        suffix  = match.group(3)
        basename = extract_image_basename(src_url)
        if basename:
            fn = media_index.find_image(basename)
            if fn:
                return f'{prefix}../image/{fn}{suffix}'
        return match.group(0)

    html_text = re.sub(
        r'(<img\s[^>]*class="tweet-image[^"]*"[^>]*src=")(https://web\.archive\.org/web/\d+im_/[^"]+)(")',
        image_replacer, html_text,
    )
    html_text = re.sub(
        r'(<img\s[^>]*src=")(https://web\.archive\.org/web/\d+im_/[^"]+)("[^>]*class="tweet-image[^"]*")',
        image_replacer, html_text,
    )

    # 视频：已清洗的 HTML 里 source.src 可能是 wayback URL（本地没有时保留的）
    def video_src_replacer(match: re.Match) -> str:
        src_url = match.group(1)
        media_key = extract_video_media_key(src_url)
        if media_key:
            local_vname = media_index.find_video(media_key)
            if local_vname:
                return f'src="../video/{local_vname}"'
        return match.group(0)

    html_text = re.sub(
        r'src="(https://web\.archive\.org/web/\d+[^"]*video[^"]+)"',
        video_src_replacer,
        html_text,
    )

    return f"<!-- Source: {source_url} -->\n" + html_text
# ============================================================================
# ── 子命令: fetch-html ──────────────────────────────────────────────────────
# ============================================================================
#
# 一次下载，同时完成两件事：
#   1. 把 wayback 原始 HTML 写到 html/{safe_filename}.html（未清洗，等 clean-html 处理）
#   2. 从同一份 HTML 里提取 jsonview，写到 json/{safe_filename}.json
#
# 这样替代了原本 fetch_json.py + 0037.py 的网络下载部分（原来要请求两次同一 URL）。
# ============================================================================

def _process_one_snapshot(snapshot: tuple[str, str], force: bool,
                          delay: float) -> tuple[bool, str, str]:
    """
    处理单条快照：下载 HTML + 抽取 JSON。
    返回 (success, wayback_url, error_msg)。
    """
    timestamp, original_url = snapshot
    wayback_url = f"https://web.archive.org/web/{timestamp}if_/{original_url}"
    json_path = os.path.join(JSON_DIR, safe_filename(timestamp, original_url, ".json"))
    html_path = os.path.join(HTML_DIR, safe_filename(timestamp, original_url, ".html"))

    json_exists = os.path.exists(json_path)
    html_exists = os.path.exists(html_path)
    if not force and json_exists and html_exists:
        return True, wayback_url, ""  # 都齐了，跳过

    if delay > 0:
        time.sleep(delay)

    try:
        html_text = fetch_html_text(wayback_url, log=safe_print)
    except Exception as e:
        return False, wayback_url, f"HTML 下载失败：{type(e).__name__}: {e}"

    # 写 HTML（未清洗，clean-html 阶段再处理）
    try:
        with open(html_path, "w", encoding="utf-8") as f:
            f.write(html_text)
    except Exception as e:
        return False, wayback_url, f"HTML 写入失败：{e}"

    # 抽 JSON 顺手存
    json_ok = False
    json_status = ""
    json_data = extract_json_from_page(html_text)
    if json_data is not None:
        try:
            with open(json_path, "w", encoding="utf-8") as f:
                json.dump(json_data, f, ensure_ascii=False, indent=2)
            json_ok = True
        except Exception as e:
            json_status = f"（JSON 写入失败：{e}）"
    else:
        json_status = "（页面无 jsonview）"

    if json_ok:
        return True, wayback_url, ""
    return True, wayback_url, f"HTML OK，{json_status}"


def cmd_fetch_html(args: argparse.Namespace) -> int:
    """子命令入口：下载 wayback HTML + 抽取 JSON。"""
    ensure_output_dirs()
    load_archive_index()
    install_sigint_handler()
    start_archive_index_flush_thread()

    # 1. 决定数据源
    if args.retry:
        retry_path = args.file or FAILED_HTML
        if not os.path.exists(retry_path):
            safe_print(f"[fetch-html --retry] 失败列表不存在：{retry_path}")
            stop_archive_index_flush_thread_and_save()
            return 0
        snapshots = load_snapshots_from_retry_file(retry_path)
        safe_print(f"[fetch-html] --retry 模式：从 {retry_path} 读取 {len(snapshots)} 条")
        force = True
    else:
        if not os.path.exists(CDX_LOCAL_FILE):
            safe_print(f"[fetch-html] 错误：找不到 {CDX_LOCAL_FILE}")
            safe_print("  先把 wayback CDX 数据保存为该文件（JSON 格式，首行是表头）")
            stop_archive_index_flush_thread_and_save()
            return 1
        snapshots = load_snapshots_from_cdx(CDX_LOCAL_FILE)
        snapshots = dedupe_snapshots(snapshots)
        safe_print(f"[fetch-html] 从 CDX 读取 {len(snapshots)} 条快照")
        force = bool(args.force)

    if not snapshots:
        safe_print("[fetch-html] 没有要处理的快照")
        stop_archive_index_flush_thread_and_save()
        return 0

    # 2. 过滤已完成（非重试模式）— 用 archive_index
    to_run: list[tuple[str, str]] = []
    skipped = 0
    for snap in snapshots:
        ts, url = snap
        wb_url = f"https://web.archive.org/web/{ts}if_/{url}"
        if not force:
            st = get_status(KIND_HTML, wb_url)
            if st == STATUS_DONE:
                skipped += 1
                continue
            # failed_all 默认跳过（永久失败），--force 才重试
            if st == STATUS_FAILED_ALL:
                skipped += 1
                continue
        to_run.append(snap)
    if skipped:
        safe_print(f"  跳过已完成/永久失败：{skipped} 条")
    safe_print(f"  待下载：{len(to_run)} 条")

    if not to_run:
        stop_archive_index_flush_thread_and_save()
        return 0

    # 3. 并发下载（archive_index 自动同步状态到 .txt 文件）
    workers = max(1, int(args.workers))
    delay   = max(0.0, float(args.delay))
    failed: list[str] = []
    success = 0

    with ThreadPoolExecutor(max_workers=workers) as executor:
        future_map = {
            executor.submit(_process_one_snapshot, snap, force, delay): snap
            for snap in to_run
        }
        for i, future in enumerate(as_completed(future_map), 1):
            snap = future_map[future]
            ts, url = snap
            wb_url = f"https://web.archive.org/web/{ts}if_/{url}"
            exc_obj: Exception | None = None
            try:
                ok, _, msg = future.result()
            except Exception as e:
                ok = False
                msg = f"未捕获异常：{type(e).__name__}: {e}"
                exc_obj = e
            tag = f"[{i}/{len(to_run)}]"
            if ok:
                success += 1
                set_status(KIND_HTML, wb_url, STATUS_DONE)
                tail = f"  {msg}" if msg else ""
                safe_print(f"{tag} ✓ {ts} {url}{tail}")
            else:
                failed.append(wb_url)
                # 没有异常对象时，按 msg 文本判 — SSL/4xx 算永久，其它算可救
                if exc_obj is not None:
                    fail_status = classify_failure(exc_obj)
                else:
                    msg_lower = (msg or "").lower()
                    if "sslerror" in msg_lower or " 4" in msg_lower[:20]:  # 粗略判
                        fail_status = STATUS_FAILED_ALL
                    else:
                        fail_status = STATUS_FAILED
                set_status(KIND_HTML, wb_url, fail_status, reason=msg[:200] if msg else "")
                safe_print(f"{tag} ✗ {ts} {url}  {msg}")

    # 4. 状态已实时同步到 _log/*.txt
    if failed:
        safe_print(f"[fetch-html] 失败 {len(failed)} 条已实时写入 {FAILED_HTML}")

    stop_archive_index_flush_thread_and_save()
    safe_print(f"[fetch-html] 完成：成功 {success} / 失败 {len(failed)} / 总计 {len(to_run)}")
    return 0 if not failed else 1


# ============================================================================
# ── 子命令: fetch-media ─────────────────────────────────────────────────────
# ============================================================================
#
# 读取 json/ 目录里所有推文 JSON，下载其中引用的图/视频/头像到本地。
# 自动跳过本地已有的（按 basename / media_key / pid 索引判断）。
# ============================================================================

def _iter_media_in_json(data: dict) -> tuple[list[dict], list[dict], list[dict]]:
    """
    从一份推文 JSON 里抽出 (images, videos, avatars)。
    每个元素都是字典，含足够的信息构造候选 URL。
      images:  {"url": str}
      videos:  {"url": str}
      avatars: {"url": str, "name": str, "username": str, "pid": str}
    """
    images:  list[dict] = []
    videos:  list[dict] = []
    avatars: list[dict] = []

    includes = data.get("includes", {}) or {}

    # 头像：从所有 users
    for u in includes.get("users", []) or []:
        url = u.get("profile_image_url") or ""
        if not url:
            continue
        avatars.append({
            "url": url,
            "name": (u.get("name") or "").strip(),
            "username": (u.get("username") or "").strip(),
            "pid": extract_profile_image_id(url),
        })

    # 媒体：images + videos
    for m in includes.get("media", []) or []:
        mtype = m.get("type", "")
        if mtype == "photo":
            url = m.get("url") or ""
            if url:
                images.append({"url": url})
        elif mtype in ("video", "animated_gif"):
            best = None
            best_br = -1
            for v in m.get("variants", []) or []:
                if v.get("content_type") != "video/mp4":
                    continue
                br = v.get("bit_rate", 0) or 0
                if br >= best_br:
                    best_br = br
                    best = v.get("url")
            if best:
                videos.append({"url": best})

    return images, videos, avatars


def _download_one_image(item: dict, snapshot_ts: str, media_index: MediaIndex,
                        force: bool) -> tuple[bool, str]:
    url = item["url"]
    basename = extract_image_basename(url)

    # 本地文件实际存在就跳过（force 时绕过 archive_index 状态，但不重下已有文件）
    if basename:
        existing = media_index.find_image(basename)
        if existing and os.path.exists(os.path.join(IMAGE_DIR, existing)):
            set_status(KIND_IMAGE, url, STATUS_DONE)
            return True, ""

    candidates = build_image_candidate_urls(url, snapshot_ts)
    if not candidates:
        set_status(KIND_IMAGE, url, STATUS_FAILED_ALL, reason="无候选 URL")
        return False, "无候选 URL"

    parsed = urlparse(url)
    fname_base = re.sub(r"[^\w\-_.]", "_", (parsed.netloc + parsed.path).strip("/"))[:120]
    if not fname_base.lower().endswith((".jpg", ".jpeg", ".png", ".gif", ".webp")):
        fname_base += ext_from_url(url)
    fname = f"{snapshot_ts}_{fname_base}"
    fpath = os.path.join(IMAGE_DIR, fname)

    try:
        size, _used = download_with_candidates(candidates, fpath, log=safe_print,
                                               timeout=MEDIA_TIMEOUT_IMAGE)
        media_index.register_image(basename, fname)
        set_status(KIND_IMAGE, url, STATUS_DONE)
        return True, f"{size} 字节"
    except Exception as e:
        reason = f"{type(e).__name__}: {e}"
        set_status(KIND_IMAGE, url, classify_failure(e), reason=reason)
        return False, reason


def _download_one_video(item: dict, snapshot_ts: str, media_index: MediaIndex,
                       force: bool) -> tuple[bool, str]:
    url = item["url"]
    key = extract_video_media_key(url)
    if key:
        existing = media_index.find_video(key)
        if existing and os.path.exists(os.path.join(VIDEO_DIR, existing)):
            set_status(KIND_VIDEO, url, STATUS_DONE)
            return True, ""

    candidates = build_video_candidate_urls(url, snapshot_ts)
    if not candidates:
        set_status(KIND_VIDEO, url, STATUS_FAILED_ALL, reason="无候选 URL")
        return False, "无候选 URL"

    parsed = urlparse(url)
    fname_base = re.sub(r"[^\w\-_.]", "_", (parsed.netloc + parsed.path).strip("/"))[:120]
    if not fname_base.lower().endswith(".mp4"):
        fname_base += ".mp4"
    fname = f"{snapshot_ts}_{fname_base}"
    fpath = os.path.join(VIDEO_DIR, fname)

    try:
        size, _used = download_with_candidates(candidates, fpath, log=safe_print,
                                               timeout=MEDIA_TIMEOUT_VIDEO)
        media_index.register_video(key, fname)
        set_status(KIND_VIDEO, url, STATUS_DONE)
        return True, f"{size // 1024} KB"
    except Exception as e:
        reason = f"{type(e).__name__}: {e}"
        set_status(KIND_VIDEO, url, classify_failure(e), reason=reason)
        return False, reason


def _download_one_avatar(item: dict, snapshot_ts: str, media_index: MediaIndex,
                         force: bool) -> tuple[bool, str]:
    """
    头像下载：
      1. 优先按 username → name → pid 顺序查本地，命中则直接登记不下载
      2. 否则构造候选 URL 下载
      3. 下载完成后按 (pid, name, username) 三路登记，供后续推文复用
    """
    url      = item["url"]
    name     = item.get("name", "")
    username = item.get("username", "")
    pid      = item.get("pid") or extract_profile_image_id(url)

    if not pid:
        set_status(KIND_AVATAR, url, STATUS_FAILED_ALL, reason="无法识别 profile pid")
        return False, "无法识别 profile pid"

    # 复用检查（本地有就跳过）
    existing, hit = media_index.find_avatar(pid=pid, name=name, username=username)
    if existing:
        media_index.register_avatar(pid, name, username, existing)
        set_status(KIND_AVATAR, url, STATUS_DONE)
        return True, f"复用本地（按 {hit} 命中）"

    candidates = build_avatar_candidate_urls(url, snapshot_ts)
    ext = ext_from_url(url)
    fname = f"avatar_{pid}{ext}"
    fpath = os.path.join(AVATAR_DIR, fname)

    try:
        size, _used = download_with_candidates(candidates, fpath, log=safe_print,
                                               timeout=MEDIA_TIMEOUT_IMAGE)
        media_index.register_avatar(pid, name, username, fname)
        set_status(KIND_AVATAR, url, STATUS_DONE)
        return True, f"{size // 1024} KB"
    except Exception as e:
        reason = f"{type(e).__name__}: {e}"
        set_status(KIND_AVATAR, url, classify_failure(e), reason=reason)
        return False, reason


def cmd_fetch_media(args: argparse.Namespace) -> int:
    """子命令入口：从 json/ 下载所有引用的媒体。"""
    # kinds: {'image','video','avatar'} 子集，None 表示全部（由 fetch-image/fetch-video 设置）
    kinds = getattr(args, 'kinds', None)
    ensure_output_dirs()
    load_archive_index()
    install_sigint_handler()
    start_archive_index_flush_thread()

    # 1. 决定要处理的 JSON 文件清单
    if args.retry:
        retry_path = args.file or FAILED_MEDIA
        if not os.path.exists(retry_path):
            safe_print(f"[fetch-media --retry] 失败列表不存在：{retry_path}")
            stop_archive_index_flush_thread_and_save()
            return 0
        json_files = [ln for ln in load_failed_list(retry_path) if ln.endswith(".json")]
        safe_print(f"[fetch-media] --retry 模式：从 {retry_path} 读取 {len(json_files)} 条")
        force = True
    else:
        if not os.path.isdir(JSON_DIR):
            safe_print(f"[fetch-media] JSON 目录不存在：{JSON_DIR}")
            stop_archive_index_flush_thread_and_save()
            return 1
        json_files = sorted(f for f in os.listdir(JSON_DIR) if f.endswith(".json"))
        safe_print(f"[fetch-media] 扫描到 {len(json_files)} 个 JSON 文件")
        force = bool(args.force)

    # 2. 过滤已完成 — 用 archive_index 替代旧的 done_set
    to_run: list[str] = []
    skipped = 0
    for jf in json_files:
        if not force and get_status(KIND_MEDIA, jf) == STATUS_DONE:
            skipped += 1
            continue
        to_run.append(jf)
    if skipped:
        safe_print(f"  跳过已完成：{skipped} 个")
    safe_print(f"  待处理：{len(to_run)} 个 JSON")

    if not to_run:
        stop_archive_index_flush_thread_and_save()
        return 0

    # 2.5 扫待处理 JSON 建立反向索引（URL → JSON 引用关系）
    #     这一步让 retry 时 URL 状态变化能反向更新所属 JSON 状态
    safe_print(f"  建立 archive_index 反向索引中...")
    indexed = 0
    for jf in to_run:
        path = os.path.join(JSON_DIR, jf)
        try:
            with open(path, encoding="utf-8") as f:
                data = json.load(f)
        except Exception:
            continue
        images, videos, avatars = _iter_media_in_json(data)
        for it in images:
            add_dependency(jf, KIND_IMAGE, it["url"])
        for it in videos:
            add_dependency(jf, KIND_VIDEO, it["url"])
        for it in avatars:
            add_dependency(jf, KIND_AVATAR, it["url"])
        indexed += 1
    safe_print(f"  反向索引完成（{indexed} 个 JSON）")

    # 3. 建本地媒体索引
    media_index = build_media_index(scan_json=True)

    # 4. 处理每个 JSON（archive_index 自动同步状态到 .txt 文件）
    workers = max(1, int(args.workers))
    delay   = max(0.0, float(args.delay))
    failed_jsons: list[str] = []
    success_jsons: list[str] = []
    fail_reason_counter: Counter = Counter()  # 全局失败原因聚合
    lock = threading.Lock()

    def _classify_fail_reason(msg: str) -> str:
        """把异常 msg 归类成 Top N 失败原因。"""
        if not msg:
            return "未知"
        # 优先匹配 HTTP 状态码
        m = re.search(r"\b([45]\d{2})\b", msg)
        if m:
            code = m.group(1)
            name = {"400": "Bad Request", "401": "Unauthorized",
                    "403": "Forbidden", "404": "Not Found",
                    "408": "Request Timeout", "429": "Too Many Requests",
                    "500": "Internal Server Error", "502": "Bad Gateway",
                    "503": "Service Unavailable", "504": "Gateway Timeout"}.get(code, "")
            return f"HTTP {code}" + (f" {name}" if name else "")
        if "Content-Type 异常" in msg:
            return "响应非媒体（疑似错误页）"
        if "响应过短" in msg:
            return "响应过短（疑似被截断）"
        if "ConnectTimeout" in msg or "ConnectionError" in msg or "Failed to establish" in msg:
            return "网络连接失败"
        if "ReadTimeout" in msg or "Timeout" in msg:
            return "超时"
        if "SSLError" in msg or "CertificateError" in msg:
            return "SSL 异常（wayback 未归档该资源 / 网络代理 TLS 截断）"
        if "负缓存" in msg:
            return "在负缓存里（之前 403/404）"
        if "无候选" in msg:
            return "无可用候选 URL"
        # 提取异常类型作为兜底
        m = re.match(r"^([A-Za-z][A-Za-z0-9_]*Error|Exception)", msg)
        if m:
            return m.group(1)
        return msg[:40].strip() or "未知"

    def handle_one_json(jf: str) -> tuple[str, bool, dict]:
        path = os.path.join(JSON_DIR, jf)
        try:
            with open(path, encoding="utf-8") as f:
                data = json.load(f)
        except Exception as e:
            return jf, False, {"error": f"JSON 解析失败：{e}"}

        # 从文件名推断快照 timestamp（safe_filename 格式：{ts}_...）
        snapshot_ts = extract_timestamp_from_filename(jf)

        images, videos, avatars = _iter_media_in_json(data)

        stats = {"img_ok": 0, "img_fail": 0, "vid_ok": 0, "vid_fail": 0,
                 "av_ok": 0, "av_fail": 0,
                 "fail_reasons": []}  # [(kind, reason), ...]
        any_fail = False

        for it in images:
            if kinds is not None and 'image' not in kinds:
                break
            if delay > 0:
                time.sleep(delay)
            ok, msg = _download_one_image(it, snapshot_ts, media_index, force)
            if ok:
                stats["img_ok"] += 1
            else:
                stats["img_fail"] += 1
                stats["fail_reasons"].append(("image", _classify_fail_reason(msg)))
                any_fail = True

        for it in videos:
            if kinds is not None and 'video' not in kinds:
                break
            if delay > 0:
                time.sleep(delay)
            ok, msg = _download_one_video(it, snapshot_ts, media_index, force)
            if ok:
                stats["vid_ok"] += 1
            else:
                stats["vid_fail"] += 1
                stats["fail_reasons"].append(("video", _classify_fail_reason(msg)))
                any_fail = True

        for it in avatars:
            if kinds is not None and 'avatar' not in kinds:
                break
            if delay > 0:
                time.sleep(min(delay, 0.2))
            ok, msg = _download_one_avatar(it, snapshot_ts, media_index, force)
            if ok:
                stats["av_ok"] += 1
            else:
                stats["av_fail"] += 1
                stats["fail_reasons"].append(("avatar", _classify_fail_reason(msg)))
                any_fail = True

        return jf, not any_fail, stats

    with ThreadPoolExecutor(max_workers=workers) as executor:
        future_map = {executor.submit(handle_one_json, jf): jf for jf in to_run}
        for i, future in enumerate(as_completed(future_map), 1):
            jf = future_map[future]
            try:
                _, ok, stats = future.result()
            except Exception as e:
                ok = False
                stats = {"error": f"未捕获：{type(e).__name__}: {e}"}
            tag = f"[{i}/{len(to_run)}]"
            with lock:
                if "error" in stats:
                    failed_jsons.append(jf)
                    # 没法精确分类（解析失败），算可救（用户可以再 retry）
                    set_status(KIND_MEDIA, jf, STATUS_FAILED,
                               reason=stats["error"][:200],
                               trigger_media_sync=False)
                    fail_reason_counter[stats["error"][:60]] += 1
                    safe_print(f"{tag} ✗ {jf}  {stats['error']}")
                else:
                    # 把这条 JSON 内部的失败原因合并到全局 Counter
                    for kind, reason in stats.get("fail_reasons", []):
                        fail_reason_counter[reason] += 1
                    # 统一显示 "类型 成功/总数"，零项的类型省略
                    parts = []
                    img_t = stats.get("img_ok", 0) + stats.get("img_fail", 0)
                    vid_t = stats.get("vid_ok", 0) + stats.get("vid_fail", 0)
                    av_t  = stats.get("av_ok", 0)  + stats.get("av_fail", 0)
                    if img_t > 0: parts.append(f"图 {stats['img_ok']}/{img_t}")
                    if vid_t > 0: parts.append(f"视 {stats['vid_ok']}/{vid_t}")
                    if av_t  > 0: parts.append(f"像 {stats['av_ok']}/{av_t}")
                    sm = "  ".join(parts) if parts else "（无媒体）"
                    # 根据 archive_index 算 media 状态（永久失败 + 完成都算 done）
                    media_status = evaluate_media_status(jf)
                    set_status(KIND_MEDIA, jf, media_status, trigger_media_sync=False)
                    if media_status == STATUS_DONE:
                        success_jsons.append(jf)
                        safe_print(f"{tag} ✓ {jf}  {sm}")
                    else:
                        failed_jsons.append(jf)
                        safe_print(f"{tag} ⚠ {jf}  {sm}  → 状态: {media_status}")

    # 5. 状态文件已实时同步到 _log/*.txt，不需要额外清理
    if failed_jsons:
        safe_print(f"[fetch-media] 失败 {len(failed_jsons)} 条已实时写入 {FAILED_MEDIA}")

    stop_archive_index_flush_thread_and_save()
    safe_print(f"[fetch-media] 完成：成功 {len(success_jsons)} / "
               f"失败 {len(failed_jsons)} / 总计 {len(to_run)}")

    # 6. 失败原因汇总（关键 — 让用户一眼看清是网络问题还是其它）
    if fail_reason_counter:
        total_failed_items = sum(fail_reason_counter.values())
        safe_print(f"\n══ 失败原因 TOP 10（共 {total_failed_items} 次失败下载）══")
        for reason, count in fail_reason_counter.most_common(10):
            pct = 100 * count / total_failed_items
            safe_print(f"  {count:>6}  ({pct:5.1f}%)  {reason}")
        safe_print("")
        # 给点判断提示
        top_reason, top_count = fail_reason_counter.most_common(1)[0]
        if top_count / total_failed_items > 0.6:
            if "403" in top_reason or "Forbidden" in top_reason:
                safe_print("  → 大部分失败是 403：Twitter 反爬 / 资源需登录 / IP 被限。")
                safe_print("    试试换 IP / 加 --delay 0.5 降并发 / 或确认你的网络能访问 pbs.twimg.com")
            elif "404" in top_reason or "Not Found" in top_reason:
                safe_print("  → 大部分失败是 404：资源已被原作者或平台删除，下载不到属正常。")
            elif "SSL" in top_reason:
                safe_print("  → 大部分失败是 SSL 异常。在 wayback 场景下，这通常意味着：")
                safe_print("    1. wayback 上根本没归档这张图（最常见，重试也救不回来）")
                safe_print("    2. 网络代理在 TLS 层截断（换网络/VPN 试试）")
                safe_print("    可手动测试：浏览器打开任意一条失败 URL，看是否显示")
                safe_print("    'The Wayback Machine has not archived that URL'。是 → 情况 1。")
            elif "网络" in top_reason or "超时" in top_reason or "Connection" in top_reason:
                safe_print("  → 大部分失败是网络问题：检查代理 / VPN，必要时加 --delay 减少并发。")
            elif "负缓存" in top_reason:
                safe_print("  → 大部分跳过是因为之前已记录失败。要重试加 --retry。")

    return 0 if not failed_jsons else 1


# ============================================================================
# ── 子命令: fetch-avatars ───────────────────────────────────────────────────
# ============================================================================
#
# 单独的头像修复工具：扫所有 json/ 收集出现过的用户，逐个尝试下载头像。
# 不动 image/video，专用于补头像漏下载（典型场景：fetch-media 跑得不顺利时，
# 一些早期 / 重复出现的用户头像没下载到本地）。
# ============================================================================

def _collect_all_avatars_from_json() -> list[dict]:
    """
    扫描 json/ 收集所有出现过的 (pid, name, username, snapshot_ts, url)。
    同一 pid 多次出现时合并为一条（保留最新 ts 的 url）。
    返回去重后的列表。
    """
    if not os.path.isdir(JSON_DIR):
        return []

    by_pid: dict[str, dict] = {}
    by_user_no_pid: dict[str, dict] = {}  # username 无法解析 pid 时备用

    for jname in sorted(os.listdir(JSON_DIR)):
        if not jname.endswith(".json"):
            continue
        snapshot_ts = extract_timestamp_from_filename(jname)
        try:
            with open(os.path.join(JSON_DIR, jname), encoding="utf-8") as f:
                data = json.load(f)
        except Exception:
            continue
        for u in (data.get("includes", {}) or {}).get("users", []) or []:
            url = u.get("profile_image_url") or ""
            if not url:
                continue
            pid = extract_profile_image_id(url)
            name = (u.get("name") or "").strip()
            username = (u.get("username") or "").strip()

            entry = {
                "url": url, "name": name, "username": username, "pid": pid,
                "snapshot_ts": snapshot_ts,
            }

            if pid:
                cur = by_pid.get(pid)
                if cur is None or (entry["snapshot_ts"] or "") > (cur.get("snapshot_ts") or ""):
                    by_pid[pid] = entry
            elif username:
                cur = by_user_no_pid.get(username)
                if cur is None or (entry["snapshot_ts"] or "") > (cur.get("snapshot_ts") or ""):
                    by_user_no_pid[username] = entry

    out = list(by_pid.values()) + list(by_user_no_pid.values())
    return out


def cmd_fetch_image(args: argparse.Namespace) -> int:
    """子命令入口：只下载图片（等价于 fetch-media 只处理 image 类型）。"""
    args.kinds = {'image'}
    return cmd_fetch_media(args)


def cmd_fetch_video(args: argparse.Namespace) -> int:
    """子命令入口：只下载视频（等价于 fetch-media 只处理 video 类型）。"""
    args.kinds = {'video'}
    return cmd_fetch_media(args)


def cmd_fetch_avatars(args: argparse.Namespace) -> int:
    """子命令入口：单独按 JSON 重下头像。"""
    ensure_output_dirs()
    load_archive_index()
    install_sigint_handler()
    start_archive_index_flush_thread()

    # 总是先扫所有 JSON 收集完整的 items（pid/name/username/url 全有）
    # 这样 retry 模式也能从 URL 反推出 pid/name/username
    all_items = _collect_all_avatars_from_json()

    # 1. 数据源
    if args.retry:
        retry_path = args.file or FAILED_AVATAR
        if not os.path.exists(retry_path):
            safe_print(f"[fetch-avatars --retry] 失败列表不存在：{retry_path}")
            stop_archive_index_flush_thread_and_save()
            return 0
        # avatar_failed.txt 里每行一个 URL
        failed_urls = set(load_failed_list(retry_path))
        items = [it for it in all_items if it.get("url") in failed_urls]
        safe_print(f"[fetch-avatars] --retry 模式：从 {retry_path} 读取 {len(failed_urls)} 条，"
                   f"在 JSON 里能定位 {len(items)} 条")
        force = True
    else:
        items = all_items
        # 跳过 done 和 failed_all（除非 --force）
        if not args.force:
            filtered = []
            skipped = 0
            for it in items:
                st = get_status(KIND_AVATAR, it.get("url", ""))
                if st in (STATUS_DONE, STATUS_FAILED_ALL):
                    skipped += 1
                    continue
                filtered.append(it)
            if skipped:
                safe_print(f"  跳过已完成/永久失败：{skipped} 个")
            items = filtered
        safe_print(f"[fetch-avatars] 从 json/ 收集到 {len(all_items)} 个唯一用户，"
                   f"待下载 {len(items)} 个")
        force = bool(args.force)

    if not items:
        stop_archive_index_flush_thread_and_save()
        return 0

    # 2. 本地索引
    media_index = build_media_index(scan_json=True)

    # 3. 并发下载（头像并发不宜过高，限速容易触发）
    workers = max(1, int(args.workers))
    delay_min, delay_max = DEFAULT_DELAY_AVATAR_RANGE
    failed: list[str] = []
    success = 0
    reused = 0
    lock = threading.Lock()

    def run_one(item: dict, i: int) -> None:
        nonlocal success, reused
        time.sleep(random.uniform(delay_min, delay_max))
        try:
            ok, msg = _download_one_avatar(item, item.get("snapshot_ts", ""),
                                           media_index, force)
        except Exception as e:
            ok, msg = False, f"未捕获：{type(e).__name__}: {e}"
            # 未捕获异常没经过 _download_one_avatar 内部的 set_status，这里补一下
            set_status(KIND_AVATAR, item.get("url", ""), STATUS_FAILED, reason=msg[:200])
        tag = f"[{i}/{len(items)}]"
        user_id = item.get("username") or item.get("name") or item.get("pid") or "?"
        with lock:
            if ok:
                if "复用" in msg:
                    reused += 1
                else:
                    success += 1
                safe_print(f"{tag} ✓ {user_id}  {msg}")
            else:
                failed.append(item.get("url", ""))
                safe_print(f"{tag} ✗ {user_id}  {msg}")

    with ThreadPoolExecutor(max_workers=workers) as executor:
        futures = []
        for i, it in enumerate(items, 1):
            futures.append(executor.submit(run_one, it, i))
        for fut in as_completed(futures):
            fut.result()

    # 4. 状态已实时同步到 _log/avatar_*.txt
    if failed:
        safe_print(f"[fetch-avatars] 失败 {len(failed)} 条已实时写入 {FAILED_AVATAR}")

    stop_archive_index_flush_thread_and_save()
    safe_print(f"[fetch-avatars] 完成：新下载 {success} / 复用 {reused} / 失败 {len(failed)}")
    return 0 if not failed else 1


# ============================================================================
# ── 子命令: clean-html ──────────────────────────────────────────────────────
# ============================================================================
#
# 读 html/ 里的 raw HTML，重写媒体路径为本地引用，原地覆盖。
# 通过判断顶部是否已有 <!-- Source: ... --> 注释来识别"已清洗"，
# 默认跳过已清洗文件；--force 强制重清。
# ============================================================================

def _is_html_cleaned(path: str) -> bool:
    """读前 2KB 判断是否已清洗（有 Source 注释）。"""
    try:
        with open(path, encoding="utf-8") as f:
            head = f.read(2048)
        return bool(_SOURCE_COMMENT_RE.match(head))
    except Exception:
        return False


def _extract_source_url_from_filename(fname: str) -> str:
    """
    从 html 文件名反推回 wayback 的 if_ URL，作为 Source 注释里的来源标记。
    安全 fallback：如果反推不出来就用文件名本身。
    """
    base = fname[:-5] if fname.endswith(".html") else fname
    ts = extract_timestamp_from_filename(base)
    if not ts:
        return f"local://{fname}"
    rest = base[len(ts) + 1:]
    return f"https://web.archive.org/web/{ts}if_/{rest}"


def cmd_clean_html(args: argparse.Namespace) -> int:
    """子命令入口：清洗 html/ 里的 HTML。"""
    ensure_output_dirs()

    if not os.path.isdir(HTML_DIR):
        safe_print(f"[clean-html] HTML 目录不存在：{HTML_DIR}")
        return 1

    candidates = sorted(f for f in os.listdir(HTML_DIR) if f.endswith(".html"))
    if not candidates:
        safe_print("[clean-html] 没有 HTML 文件")
        return 0

    force = bool(args.force)

    # 跳过已清洗（用 Source 注释判断）
    to_run: list[str] = []
    skipped = 0
    for fname in candidates:
        if not force and _is_html_cleaned(os.path.join(HTML_DIR, fname)):
            skipped += 1
            continue
        to_run.append(fname)
    if skipped:
        safe_print(f"  跳过已清洗：{skipped} 个")
    safe_print(f"[clean-html] 待清洗：{len(to_run)} 个")

    if not to_run:
        return 0

    # 建媒体索引（一次性，所有清洗共用）
    media_index = build_media_index(scan_json=True)

    # 顺序清洗
    failed = 0
    success = 0
    total = len(to_run)
    for i, fname in enumerate(to_run, 1):
        path = os.path.join(HTML_DIR, fname)
        try:
            with open(path, encoding="utf-8") as f:
                content = f.read()
        except Exception as e:
            safe_print(f"[{i}/{total}] ✗ {fname}  读失败：{e}")
            failed += 1
            continue

        source_url = _extract_source_url_from_filename(fname)
        already_cleaned = _is_html_cleaned(path)
        try:
            if already_cleaned:
                # 已清洗过：只替换路径，不重跑 BS4/prettify（防止多次格式化累积）
                cleaned = _replace_paths_only(content, source_url, media_index)
            else:
                cleaned = clean_html_text(content, source_url, media_index)
        except Exception as e:
            safe_print(f"[{i}/{total}] ✗ {fname}  清洗失败：{type(e).__name__}: {e}")
            failed += 1
            continue

        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write(cleaned)
        except Exception as e:
            safe_print(f"[{i}/{total}] ✗ {fname}  写回失败：{e}")
            failed += 1
            continue

        success += 1
        safe_print(f"[{i}/{total}] ✓ {fname}")

    safe_print(f"[clean-html] 完成：成功 {success} / 失败 {failed}")
    return 0 if not failed else 1
# ============================================================================
# ── 子命令: build-index（与 GitHub IncandescenceReader/build_index.py 一致）─
# ============================================================================
#
# 这一节的逻辑严格对齐 GitHub 上的原版 build_index.py：
#   - 主数据源：清洗后的 HTML（提取作者、正文、images）
#   - 元数据源：JSON（提取 tweet_id/conversation_id/媒体归属/祖先链）
#   - JSON 缺失时降级用 extract_from_html_fallback
#   - 输出格式：紧凑 JSON 数组，每条含 wanted_*/embedded_*/is_virtual 等字段
# ============================================================================


def _bi_build_image_index() -> dict:
    """basename → "../image/完整文件名"，优先索引新命名（_pbs_twimg_com_）。"""
    if not os.path.isdir(IMAGE_DIR):
        return {}
    index: dict[str, str] = {}
    fnames = sorted(
        os.listdir(IMAGE_DIR),
        key=lambda f: (0 if "_pbs_twimg_com_" in f else 1, f),
    )
    for fname in fnames:
        m = re.search(
            r"_media_(.+?)_(?:jpg|png|gif|webp|jpeg)\.(?:jpg|png|gif|webp|jpeg)$",
            fname, re.IGNORECASE,
        )
        if not m:
            m = re.search(
                r"_media_(.+?)\.(?:jpg|png|gif|webp|jpeg)$", fname, re.IGNORECASE,
            )
        if m:
            basename = m.group(1)
            if basename not in index:
                index[basename] = f"../image/{fname}"
    return index


def _bi_build_video_index() -> dict:
    """media_key(数字) → "../video/完整文件名"。"""
    if not os.path.isdir(VIDEO_DIR):
        return {}
    index: dict[str, str] = {}
    fnames = sorted(
        os.listdir(VIDEO_DIR),
        key=lambda f: (0 if "_video_twimg_com_" in f else 1, f),
    )
    for fname in fnames:
        m = re.search(r"(?:amplify_video|ext_tw_video|tweet_video)[/_](\d+)", fname)
        if m:
            key = m.group(1)
            if key not in index:
                index[key] = f"../video/{fname}"
    return index


def _bi_build_avatar_index() -> dict:
    """pid → "../avatar/完整文件名"（含正确 ext）。"""
    if not os.path.isdir(AVATAR_DIR):
        return {}
    index: dict[str, str] = {}
    for fname in sorted(os.listdir(AVATAR_DIR)):
        pid = extract_avatar_pid_from_filename(fname)
        if pid and pid not in index:
            index[pid] = f"../avatar/{fname}"
    return index


def _bi_resolve_avatar(src: str, avatar_index: dict) -> str:
    """把 wayback/pbs 头像 URL 转成本地路径；找不到返回原 src。"""
    if not src:
        return src
    if src.startswith("../avatar/"):
        return src  # 已经是本地路径（clean-html 跑过的场景，兼容）
    pid = extract_profile_image_id(src)
    if pid and pid in avatar_index:
        return avatar_index[pid]
    return src


def _bi_extract_date(html_text: str) -> str:
    """从 HTML 的 #parentdate 关联 script 提取 dateString。"""
    script_blocks = re.findall(
        r"<script[^>]*>(.*?)</script>", html_text, re.DOTALL | re.IGNORECASE,
    )
    for block in script_blocks:
        if "#parentdate" in block or '"#parentdate"' in block or "'#parentdate'" in block:
            m = re.search(r'var\s+dateString\s*=\s*"([^"]+)"', block)
            if m:
                return m.group(1)
    all_dates = re.findall(r'var\s+dateString\s*=\s*"([^"]+)"', html_text)
    if all_dates:
        return all_dates[-1]
    return ""


def _bi_extract_render_data(html_text: str) -> dict:
    """从 html 提取作者/正文/图片/embedded（详见 GitHub 原版 docstring）。"""
    result = {
        "author_name":     "",
        "author_username": "",
        "author_avatar":   "",
        "body_text":       "",
        "images":          [],
        "embedded":        None,
    }
    soup = BeautifulSoup(html_text, "html.parser")
    nonjson = soup.find(id="nonjsonview")
    if not nonjson:
        return result

    first_author = nonjson.find("div", class_="tweet-author")
    if first_author:
        name_el   = first_author.find(class_="tweet-author-name")
        uname_el  = first_author.find(class_="tweet-author-username")
        avatar_el = first_author.find("img")
        if name_el:
            result["author_name"] = name_el.get_text(strip=True)
        if uname_el:
            result["author_username"] = uname_el.get_text(strip=True)
        if avatar_el and avatar_el.get("src"):
            result["author_avatar"] = avatar_el["src"]

    content = nonjson.find("div", class_="tweet-content")
    if not content:
        return result

    embedded = content.find("div", class_="embedded-tweet-container")

    if embedded:
        emb_data = {
            "author_name":     "",
            "author_username": "",
            "author_avatar":   "",
            "body_text":       "",
            "tweet_id":        "",
            "timestamp":       "",
        }
        emb_author = embedded.find("div", class_="tweet-author")
        if emb_author:
            nm = emb_author.find(class_="tweet-author-name")
            un = emb_author.find(class_="tweet-author-username")
            av = emb_author.find("img")
            if nm: emb_data["author_name"]     = nm.get_text(strip=True)
            if un: emb_data["author_username"] = un.get_text(strip=True)
            if av and av.get("src"):
                emb_data["author_avatar"] = av["src"]

        emb_content = embedded.find("div", class_="tweet-content")
        if emb_content:
            ec_clone = BeautifulSoup(str(emb_content), "html.parser").find("div", class_="tweet-content")
            for tag in ec_clone.find_all(["script", "img"]):
                tag.decompose()
            for p_tag in ec_clone.find_all("p", class_="date"):
                p_tag.decompose()
            for br in ec_clone.find_all("br"):
                br.replace_with("\n")
            et = ec_clone.get_text(separator="", strip=False)
            lines = [l.strip() for l in et.splitlines()]
            clean: list[str] = []
            prev_empty = False
            for l in lines:
                if l == "":
                    if not prev_empty:
                        clean.append(l)
                    prev_empty = True
                else:
                    clean.append(l)
                    prev_empty = False
            emb_data["body_text"] = "\n".join(clean).strip()[:TEXT_MAX]

        for a in embedded.find_all("a"):
            href = a.get("href", "")
            m = re.search(r"/status/(\d+)", href)
            if m:
                emb_data["tweet_id"] = m.group(1)
                break

        for s in embedded.find_all("script"):
            mt = re.search(r'var\s+dateString\s*=\s*"([^"]+)"', s.string or "")
            if mt:
                emb_data["timestamp"] = mt.group(1)
                break

        result["embedded"] = emb_data

    # 图片：不在 embedded 内部的 tweet-image
    for img in content.find_all("img", class_="tweet-image"):
        in_embedded = False
        if embedded:
            p = img.parent
            while p:
                if p == embedded:
                    in_embedded = True
                    break
                p = p.parent
        if not in_embedded:
            src = img.get("src", "")
            if src:
                result["images"].append(src)

    # 纯文字（移除 embedded 和所有 img）
    content_clone = BeautifulSoup(str(content), "html.parser").find("div", class_="tweet-content")
    emb_clone = content_clone.find("div", class_="embedded-tweet-container")
    if emb_clone:
        emb_clone.decompose()
    for img in content_clone.find_all("img"):
        img.decompose()
    for script in content_clone.find_all("script"):
        script.decompose()
    for p_tag in content_clone.find_all("p", class_="date"):
        p_tag.decompose()
    for br in content_clone.find_all("br"):
        br.replace_with("\n")

    body = content_clone.get_text(separator="", strip=False)
    lines = [l.strip() for l in body.splitlines()]
    clean_lines: list[str] = []
    prev_empty = False
    for l in lines:
        if l == "":
            if not prev_empty:
                clean_lines.append(l)
            prev_empty = True
        else:
            clean_lines.append(l)
            prev_empty = False
    body = "\n".join(clean_lines).strip()
    result["body_text"] = body[:TEXT_MAX]
    return result


def _bi_extract_text(html_text: str) -> str:
    """搜索用纯文本。"""
    soup = BeautifulSoup(html_text, "html.parser")
    main_wrap = soup.find(id="nonjsonview") or soup.find("div", class_="tweet-container")
    container = None
    if main_wrap:
        for embedded in main_wrap.find_all("div", class_="embedded-tweet-container"):
            embedded.decompose()
        container = main_wrap.find("div", class_="tweet-content")
    if not container:
        container = soup.find("div", class_="tweet-content")
    if container:
        for img in container.find_all("img"):
            img.decompose()
        text = container.get_text(separator=" ", strip=True)
    else:
        text = soup.get_text(separator=" ", strip=True)
    text = re.sub(r"\s+", " ", text).strip()
    return text[:TEXT_MAX]


def _bi_extract_tweet_id_from_filename(fname: str) -> str:
    m = re.search(r"status_(\d+)", fname)
    return m.group(1) if m else ""


def _bi_fname_to_iso(fname: str) -> str:
    m = re.match(r"(\d{4})(\d{2})(\d{2})(\d{2})(\d{2})(\d{2})_", fname)
    if m:
        Y, M, D, h, mi, s = m.groups()
        return f"{Y}-{M}-{D}T{h}:{mi}:{s}.000Z"
    return "1970-01-01T00:00:00.000Z"


def _bi_build_tweet_id_index() -> dict:
    """tweet_id (来自 data.id) → json 文件路径，用于祖先链追溯。"""
    if not os.path.isdir(JSON_DIR):
        return {}
    index: dict[str, str] = {}
    for fname in os.listdir(JSON_DIR):
        if not fname.endswith(".json"):
            continue
        fpath = os.path.join(JSON_DIR, fname)
        try:
            with open(fpath, encoding="utf-8") as f:
                data = json.load(f)
            tid = str(data.get("data", {}).get("id", ""))
            if tid and tid not in index:
                index[tid] = fpath
        except Exception:
            continue
    return index


def _bi_media_lookup_for_json(json_data: dict):
    """从一份 json 提取 media_key → image_basename / video_key 映射。"""
    mk_to_image_basename: dict[str, str] = {}
    mk_to_video_key:      dict[str, str] = {}
    includes = json_data.get("includes", {}) or {}
    for media in includes.get("media", []) or []:
        mkey  = media.get("media_key", "")
        mtype = media.get("type", "")
        if mtype == "photo":
            url = media.get("url", "") or media.get("preview_image_url", "")
            if url:
                m = re.search(
                    r"/media/([^/?#]+?)\.(?:jpg|png|gif|webp|jpeg)(?:[?#]|$)",
                    url, re.IGNORECASE,
                )
                if m:
                    mk_to_image_basename[mkey] = m.group(1)
        elif mtype in ("video", "animated_gif"):
            key = None
            for v in media.get("variants", []) or []:
                if v.get("content_type") == "video/mp4":
                    url = v.get("url", "")
                    m = re.search(
                        r"(?:amplify_video|ext_tw_video|tweet_video)[/_](\d+)", url,
                    )
                    if m:
                        key = m.group(1)
                        break
            if not key:
                m = re.search(r"(\d+)$", mkey)
                if m:
                    key = m.group(1)
            if key:
                mk_to_video_key[mkey] = key
    return mk_to_image_basename, mk_to_video_key


def _bi_collect_ancestor_media(start_tweet_id: str,
                               tweet_id_index: dict,
                               max_depth: int = 50) -> tuple:
    """沿 referenced_tweets 链向上追溯，收集所有祖先推文的图/视频。"""
    image_basenames: list[str] = []
    video_keys:      list[str] = []
    visited: set[str] = set()
    current_id = start_tweet_id
    depth = 0
    while current_id and current_id not in visited and depth < max_depth:
        visited.add(current_id)
        depth += 1
        json_path = tweet_id_index.get(current_id)
        if not json_path:
            break
        try:
            with open(json_path, encoding="utf-8") as f:
                ancestor_data = json.load(f)
        except Exception:
            break

        mk_img, mk_vid = _bi_media_lookup_for_json(ancestor_data)
        anc_main = ancestor_data.get("data", {}) or {}
        anc_mk = (anc_main.get("attachments", {}) or {}).get("media_keys", []) or []
        for k in anc_mk:
            if k in mk_img:
                image_basenames.append(mk_img[k])
            if k in mk_vid:
                video_keys.append(mk_vid[k])

        next_id = None
        for ref in (anc_main.get("referenced_tweets") or []):
            if ref.get("type") in ("replied_to", "quoted"):
                next_id = str(ref.get("id", ""))
                break
        current_id = next_id
    return image_basenames, video_keys


def _bi_extract_from_json(json_data: dict, tweet_id_index: dict | None = None) -> dict:
    """从 json 提取 tweet_id/关系/媒体归属/冗余短链。"""
    result = {
        "tweet_id":                "",
        "conversation_id":         "",
        "is_reply":                False,
        "reply_to_id":             "",
        "reply_type":              "",
        "has_quoted":              False,
        "quoted_id":               "",
        "has_media":               False,
        "media_keys":              [],
        "wanted_basenames":        [],
        "embedded_basenames":      [],
        "wanted_video_keys":       [],
        "embedded_video_keys":     [],
        "remove_urls":             [],
        "embedded_remove_urls":    [],
    }
    data     = json_data.get("data", {})
    includes = json_data.get("includes", {})
    result["tweet_id"]        = str(data.get("id", ""))
    result["conversation_id"] = str(data.get("conversation_id", ""))
    for ref in data.get("referenced_tweets", []):
        rtype, rid = ref.get("type", ""), str(ref.get("id", ""))
        if rtype == "replied_to":
            result["is_reply"]    = True
            result["reply_to_id"] = rid
            result["reply_type"]  = "replied_to"
        elif rtype == "quoted":
            result["has_quoted"]  = True
            result["quoted_id"]   = rid
            result["reply_type"]  = "quoted"
    att = data.get("attachments", {})
    mk  = att.get("media_keys", [])
    result["media_keys"] = mk
    result["has_media"]  = len(mk) > 0 or bool(includes.get("media"))

    mk_to_image_basename: dict[str, str] = {}
    mk_to_video_key:      dict[str, str] = {}
    for media in includes.get("media", []):
        mkey  = media.get("media_key", "")
        mtype = media.get("type", "")
        if mtype == "photo":
            url = media.get("url", "") or media.get("preview_image_url", "")
            if url:
                m = re.search(
                    r"/media/([^/?#]+?)\.(?:jpg|png|gif|webp|jpeg)(?:[?#]|$)",
                    url, re.IGNORECASE,
                )
                if m:
                    mk_to_image_basename[mkey] = m.group(1)
        elif mtype in ("video", "animated_gif"):
            key = None
            for v in media.get("variants", []) or []:
                if v.get("content_type") == "video/mp4":
                    url = v.get("url", "")
                    m = re.search(
                        r"(?:amplify_video|ext_tw_video|tweet_video)[/_](\d+)", url,
                    )
                    if m:
                        key = m.group(1)
                        break
            if not key:
                m = re.search(r"(\d+)$", mkey)
                if m:
                    key = m.group(1)
            if key:
                mk_to_video_key[mkey] = key

    result["wanted_basenames"]  = [mk_to_image_basename[k] for k in mk if k in mk_to_image_basename]
    result["wanted_video_keys"] = [mk_to_video_key[k]      for k in mk if k in mk_to_video_key]

    ref_ids = [str(r.get("id", "")) for r in data.get("referenced_tweets", [])]
    for t in includes.get("tweets", []):
        if str(t.get("id", "")) in ref_ids:
            t_mk = t.get("attachments", {}).get("media_keys", [])
            for k in t_mk:
                if k in mk_to_image_basename:
                    result["embedded_basenames"].append(mk_to_image_basename[k])
                if k in mk_to_video_key:
                    result["embedded_video_keys"].append(mk_to_video_key[k])

    # 祖先链追溯
    if tweet_id_index:
        seen_imgs = set(result["embedded_basenames"])
        seen_vids = set(result["embedded_video_keys"])
        included_by_id = {str(t.get("id", "")): t for t in includes.get("tweets", [])}
        for first_ancestor_id in ref_ids:
            grand_ids: list[str] = []
            anc_in_includes = included_by_id.get(first_ancestor_id)
            if anc_in_includes:
                for ref in (anc_in_includes.get("referenced_tweets") or []):
                    if ref.get("type") in ("replied_to", "quoted"):
                        grand_ids.append(str(ref.get("id", "")))
            else:
                anc_path = tweet_id_index.get(first_ancestor_id)
                if anc_path:
                    try:
                        with open(anc_path, encoding="utf-8") as f:
                            anc_data = json.load(f)
                        for ref in (anc_data.get("data", {}).get("referenced_tweets") or []):
                            if ref.get("type") in ("replied_to", "quoted"):
                                grand_ids.append(str(ref.get("id", "")))
                    except Exception:
                        pass
            for grand_id in grand_ids:
                a_imgs, a_vids = _bi_collect_ancestor_media(grand_id, tweet_id_index)
                for b in a_imgs:
                    if b not in seen_imgs:
                        seen_imgs.add(b)
                        result["embedded_basenames"].append(b)
                for v in a_vids:
                    if v not in seen_vids:
                        seen_vids.add(v)
                        result["embedded_video_keys"].append(v)

    # 主推文冗余短链
    seen_urls: set[str] = set()
    for u in data.get("entities", {}).get("urls", []):
        url = u.get("url", "")
        if not url or url in seen_urls:
            continue
        is_media  = bool(u.get("media_key"))
        is_status = "/status/" in u.get("expanded_url", "")
        if is_media or is_status:
            result["remove_urls"].append(url)
            seen_urls.add(url)

    # embedded 冗余短链
    seen_urls2: set[str] = set()
    for t in includes.get("tweets", []):
        if str(t.get("id", "")) not in ref_ids:
            continue
        for u in t.get("entities", {}).get("urls", []):
            url = u.get("url", "")
            if not url or url in seen_urls2:
                continue
            is_media  = bool(u.get("media_key"))
            is_status = "/status/" in u.get("expanded_url", "")
            if is_media or is_status:
                result["embedded_remove_urls"].append(url)
                seen_urls2.add(url)

    return result


def _bi_extract_from_html_fallback(html_text: str, fname: str) -> dict:
    """JSON 缺失时的降级：从 HTML 推断关系字段。"""
    result = {
        "tweet_id":                _bi_extract_tweet_id_from_filename(fname),
        "conversation_id":         "",
        "is_reply":                False,
        "reply_to_id":             "",
        "reply_type":              "",
        "has_quoted":              False,
        "quoted_id":               "",
        "has_media":               False,
        "media_keys":              [],
        "wanted_basenames":        [],
        "embedded_basenames":      [],
        "wanted_video_keys":       [],
        "embedded_video_keys":     [],
        "remove_urls":             [],
        "embedded_remove_urls":    [],
    }
    soup = BeautifulSoup(html_text, "html.parser")
    nonjson = soup.find(id="nonjsonview")
    if not nonjson:
        return result
    imgs = nonjson.find_all("img", class_="tweet-image")
    result["has_media"] = len(imgs) > 0
    embedded = nonjson.find("div", class_="embedded-tweet-container")
    if embedded:
        for a in embedded.find_all("a"):
            href = a.get("href", "")
            m = re.search(r"/status/(\d+)", href)
            if m:
                ref_id   = m.group(1)
                user_m   = re.search(r"twitter\.com/([^/]+)/status", href)
                ref_user = user_m.group(1) if user_m else ""
                own_uname = ""
                uname_div = nonjson.find(class_="tweet-author-username")
                if uname_div:
                    own_uname = uname_div.get_text(strip=True).lstrip("@")
                if ref_user.lower() == own_uname.lower():
                    result["has_quoted"]  = True
                    result["quoted_id"]   = ref_id
                    result["reply_type"]  = "quoted_self"
                else:
                    result["has_quoted"]  = True
                    result["quoted_id"]   = ref_id
                    result["reply_type"]  = "quoted"
                break
    return result


# ============================================================================
# ── 子命令: retry / rebuild-index ───────────────────────────────────────────
# ============================================================================
#
# retry  共 12 个子选项：
#   --image-failed / --image-failed-all
#   --video-failed / --video-failed-all
#   --avatar-failed / --avatar-failed-all
#   --media-failed / --media-failed-all
#   --html-failed / --html-failed-all
#   --clean-failed / --clean-failed-all
#
# rebuild-index  重建 archive_index.json（适合迁移 / 损坏修复）
# ============================================================================

# retry 子选项映射：flag_name → (is_all, kind, txt_path)
_RETRY_TARGETS: dict[str, tuple[bool, str, str]] = {
    "image_failed":      (False, KIND_IMAGE,  FAILED_IMAGE),
    "image_failed_all":  (True,  KIND_IMAGE,  FAILED_IMAGE_ALL),
    "video_failed":      (False, KIND_VIDEO,  FAILED_VIDEO),
    "video_failed_all":  (True,  KIND_VIDEO,  FAILED_VIDEO_ALL),
    "avatar_failed":     (False, KIND_AVATAR, FAILED_AVATAR),
    "avatar_failed_all": (True,  KIND_AVATAR, FAILED_AVATAR_ALL),
    "media_failed":      (False, KIND_MEDIA,  FAILED_MEDIA),
    "media_failed_all":  (True,  KIND_MEDIA,  FAILED_MEDIA_ALL),
    "html_failed":       (False, KIND_HTML,   FAILED_HTML),
    "html_failed_all":   (True,  KIND_HTML,   FAILED_HTML_ALL),
}


def _retry_url_level_media(kind: str, urls: list[str]) -> int:
    """重试 image / video URL 列表。需要扫 JSON 找到 URL 对应的 item 元数据。"""
    if not urls:
        safe_print("[retry] 没有待重试的项")
        return 0
    if not os.path.isdir(JSON_DIR):
        safe_print(f"[retry] JSON 目录不存在：{JSON_DIR}")
        return 1

    # 把每个 URL 找回到它所在的 JSON 和 item（用 referenced_by）
    url_set = set(urls)
    targets: list[tuple[dict, str]] = []  # [(item_dict, snapshot_ts), ...]
    seen_urls: set[str] = set()

    for jf in sorted(os.listdir(JSON_DIR)):
        if not jf.endswith(".json"):
            continue
        if not (url_set - seen_urls):
            break  # 全找到了
        path = os.path.join(JSON_DIR, jf)
        try:
            with open(path, encoding="utf-8") as f:
                data = json.load(f)
        except Exception:
            continue
        snapshot_ts = extract_timestamp_from_filename(jf)
        images, videos, avatars = _iter_media_in_json(data)
        if kind == KIND_IMAGE:
            for it in images:
                if it["url"] in url_set and it["url"] not in seen_urls:
                    targets.append((it, snapshot_ts))
                    seen_urls.add(it["url"])
        elif kind == KIND_VIDEO:
            for it in videos:
                if it["url"] in url_set and it["url"] not in seen_urls:
                    targets.append((it, snapshot_ts))
                    seen_urls.add(it["url"])

    not_found = url_set - seen_urls
    if not_found:
        safe_print(f"[retry] {len(not_found)} 个 URL 在 JSON 里没找到（可能 JSON 被删了），跳过")

    if not targets:
        safe_print("[retry] 无可重试的项")
        return 0

    media_index = build_media_index(scan_json=True)
    success = 0
    failed = 0
    for i, (item, snapshot_ts) in enumerate(targets, 1):
        tag = f"[{i}/{len(targets)}]"
        try:
            if kind == KIND_IMAGE:
                ok, msg = _download_one_image(item, snapshot_ts, media_index, force=True)
            else:
                ok, msg = _download_one_video(item, snapshot_ts, media_index, force=True)
        except Exception as e:
            ok, msg = False, f"未捕获：{type(e).__name__}: {e}"
        if ok:
            success += 1
            safe_print(f"{tag} ✓ {item['url'][:80]}")
        else:
            failed += 1
            safe_print(f"{tag} ✗ {item['url'][:80]}  {msg}")

    safe_print(f"[retry] {kind} 完成：成功 {success} / 失败 {failed}")
    return 0 if failed == 0 else 1


def _retry_url_level_avatar(urls: list[str]) -> int:
    """重试 avatar URL 列表。需要扫 JSON 拿 pid/name/username。"""
    if not urls:
        safe_print("[retry] 没有待重试的项")
        return 0
    url_set = set(urls)
    all_items = _collect_all_avatars_from_json()
    items = [it for it in all_items if it.get("url") in url_set]

    not_found = url_set - {it.get("url", "") for it in items}
    if not_found:
        safe_print(f"[retry] {len(not_found)} 个 URL 在 JSON 里没找到，跳过")

    if not items:
        safe_print("[retry] 无可重试的项")
        return 0

    media_index = build_media_index(scan_json=True)
    success = 0
    failed = 0
    for i, item in enumerate(items, 1):
        tag = f"[{i}/{len(items)}]"
        try:
            ok, msg = _download_one_avatar(item, item.get("snapshot_ts", ""),
                                           media_index, force=True)
        except Exception as e:
            ok, msg = False, f"未捕获：{type(e).__name__}: {e}"
        user_id = item.get("username") or item.get("name") or item.get("pid") or "?"
        if ok:
            success += 1
            safe_print(f"{tag} ✓ {user_id}  {msg}")
        else:
            failed += 1
            safe_print(f"{tag} ✗ {user_id}  {msg}")

    safe_print(f"[retry] avatar 完成：成功 {success} / 失败 {failed}")
    return 0 if failed == 0 else 1


def _retry_media_jsons(json_filenames: list[str], force: bool) -> int:
    """重试一批 JSON 的所有媒体（复用 cmd_fetch_media 的逻辑，通过 args.file）。"""
    # 用 retry 文件路径调 cmd_fetch_media
    # 但我们直接构造 args 调 cmd_fetch_media 即可
    if not json_filenames:
        safe_print("[retry] 没有待重试的 JSON")
        return 0
    safe_print(f"[retry] 将重试 {len(json_filenames)} 个 JSON 的所有媒体")

    # 临时把这些 JSON 当 to_run 走一遍 fetch-media 流程（force=True 跳过 done 检查）
    fake_args = argparse.Namespace(
        retry=False, force=force, file=None,
        workers=DEFAULT_WORKERS_MEDIA, delay=DEFAULT_DELAY_MEDIA,
    )
    # 由于 cmd_fetch_media 默认扫所有 JSON，我们需要让它只跑指定的
    # 简单办法：临时写一个文件让 cmd_fetch_media --retry --file 来读
    tmp_path = os.path.join(LOG_DIR, "_retry_tmp.txt")
    try:
        with open(tmp_path, "w", encoding="utf-8") as f:
            for jf in json_filenames:
                f.write(jf + "\n")
        fake_args.retry = True
        fake_args.file = tmp_path
        rc = cmd_fetch_media(fake_args)
    finally:
        try:
            os.remove(tmp_path)
        except OSError:
            pass
    return rc


def _retry_html_urls(urls: list[str]) -> int:
    """重试 HTML URL 列表（复用 cmd_fetch_html --retry 的逻辑）。"""
    if not urls:
        safe_print("[retry] 没有待重试的 HTML URL")
        return 0
    tmp_path = os.path.join(LOG_DIR, "_retry_tmp_html.txt")
    try:
        with open(tmp_path, "w", encoding="utf-8") as f:
            for u in urls:
                f.write(u + "\n")
        fake_args = argparse.Namespace(
            retry=True, force=False, file=tmp_path,
            workers=DEFAULT_WORKERS_HTML, delay=DEFAULT_DELAY_HTML,
        )
        rc = cmd_fetch_html(fake_args)
    finally:
        try:
            os.remove(tmp_path)
        except OSError:
            pass
    return rc


def cmd_retry(args: argparse.Namespace) -> int:
    """retry 子命令统一入口。"""
    ensure_output_dirs()
    load_archive_index()
    install_sigint_handler()
    start_archive_index_flush_thread()

    selected = [k for k in _RETRY_TARGETS if getattr(args, k, False)]
    if len(selected) == 0:
        safe_print("[retry] 必须指定一个选项，可选：")
        for k in _RETRY_TARGETS:
            safe_print(f"  --{k.replace('_', '-')}")
        stop_archive_index_flush_thread_and_save()
        return 1
    if len(selected) > 1:
        safe_print(f"[retry] 一次只能选一个，你给了：{selected}")
        stop_archive_index_flush_thread_and_save()
        return 1

    target = selected[0]
    is_all, kind, path = _RETRY_TARGETS[target]

    if not os.path.exists(path):
        safe_print(f"[retry] 文件不存在或为空：{path}")
        stop_archive_index_flush_thread_and_save()
        return 0

    items = load_failed_list(path)
    if not items:
        safe_print(f"[retry] 文件为空：{path}")
        stop_archive_index_flush_thread_and_save()
        return 0

    safe_print(f"[retry --{target.replace('_', '-')}] 从 {path} 读取 {len(items)} 条")

    try:
        if kind == KIND_IMAGE:
            rc = _retry_url_level_media(KIND_IMAGE, items)
        elif kind == KIND_VIDEO:
            rc = _retry_url_level_media(KIND_VIDEO, items)
        elif kind == KIND_AVATAR:
            rc = _retry_url_level_avatar(items)
        elif kind == KIND_MEDIA:
            json_files = [x for x in items if x.endswith(".json")]
            rc = _retry_media_jsons(json_files, force=True)
        elif kind == KIND_HTML:
            rc = _retry_html_urls(items)
        else:
            safe_print(f"[retry] 未知 kind：{kind}")
            rc = 1
    finally:
        stop_archive_index_flush_thread_and_save()

    return rc


def cmd_rebuild_index(args: argparse.Namespace) -> int:
    """
    从 .txt 文件 + 本地媒体文件 + JSON 文件重建 archive_index.json。

    用途：
      - 首次从旧版升级（手动迁移 .txt 后跑这个）
      - archive_index.json 损坏后恢复
      - convert 之后自动调用（登记本地已存在的媒体）
    """
    ensure_output_dirs()

    # 备份现有 archive_index
    if os.path.exists(ARCHIVE_INDEX_FILE):
        backup = ARCHIVE_INDEX_FILE + ".pre-rebuild." + time.strftime("%Y%m%d_%H%M%S")
        try:
            shutil.copy2(ARCHIVE_INDEX_FILE, backup)
            safe_print(f"[rebuild-index] 备份现有 archive_index → {backup}")
        except OSError:
            pass

    safe_print("[rebuild-index] 开始重建...")

    # 1. 强制空骨架
    global _archive_index_data, _archive_index_dirty
    with _archive_index_lock:
        _archive_index_data = _make_empty_archive_index()
        _archive_index_dirty = True

    # 清空 _txt_sets 缓存（让后续读到最新的 .txt）
    with _txt_sets_lock:
        _txt_sets.clear()

    # 2. 扫所有 JSON 建立 media + 反向索引
    if os.path.isdir(JSON_DIR):
        jsons = sorted(f for f in os.listdir(JSON_DIR) if f.endswith(".json"))
        safe_print(f"[rebuild-index] 扫描 {len(jsons)} 个 JSON...")
        for jf in jsons:
            try:
                with open(os.path.join(JSON_DIR, jf), encoding="utf-8") as f:
                    data = json.load(f)
            except Exception:
                continue
            images, videos, avatars = _iter_media_in_json(data)
            for it in images:
                add_dependency(jf, KIND_IMAGE, it["url"])
            for it in videos:
                add_dependency(jf, KIND_VIDEO, it["url"])
            for it in avatars:
                add_dependency(jf, KIND_AVATAR, it["url"])

    # 3. 扫本地媒体文件，把对应 URL 标 done
    media_idx = build_media_index(scan_json=False, verbose=False)

    # 对于 archive_index 里每个 URL，看看本地有没有对应文件
    idx = load_archive_index()
    with _archive_index_lock:
        for url in list(idx[KIND_IMAGE].keys()):
            basename = extract_image_basename(url)
            if basename and media_idx.find_image(basename):
                idx[KIND_IMAGE][url]["status"] = STATUS_DONE
        for url in list(idx[KIND_VIDEO].keys()):
            key = extract_video_media_key(url)
            if key and media_idx.find_video(key):
                idx[KIND_VIDEO][url]["status"] = STATUS_DONE
        for url in list(idx[KIND_AVATAR].keys()):
            pid = extract_profile_image_id(url)
            if pid and media_idx.find_avatar(pid=pid)[0]:
                idx[KIND_AVATAR][url]["status"] = STATUS_DONE

    # 4. 从 .txt 文件读现有状态（增量合并）
    # 顺序：done > failed_all > failed（done 是终态最高优先级）
    safe_print("[rebuild-index] 合并 _log/*.txt 现有状态...")

    def _merge_txt(path: str, kind: str, status: str) -> int:
        if not os.path.exists(path):
            return 0
        added = 0
        try:
            with open(path, encoding="utf-8") as f:
                for line in f:
                    item = line.strip()
                    if not item or item.startswith("#"):
                        continue
                    with _archive_index_lock:
                        coll = idx[kind]
                        if item not in coll:
                            coll[item] = {"status": status}
                            added += 1
                        else:
                            # 升级状态：done > failed_all > failed
                            cur = coll[item].get("status", "unknown")
                            order = {STATUS_DONE: 3, STATUS_FAILED_ALL: 2, STATUS_FAILED: 1}
                            if order.get(status, 0) > order.get(cur, 0):
                                coll[item]["status"] = status
        except OSError:
            pass
        return added

    # 先 done，再 failed_all，再 failed
    for path, kind in [
        (DONE_HTML,   KIND_HTML),  (FAILED_HTML_ALL,   KIND_HTML),   (FAILED_HTML,   KIND_HTML),
        (DONE_MEDIA,  KIND_MEDIA), (FAILED_MEDIA_ALL,  KIND_MEDIA),  (FAILED_MEDIA,  KIND_MEDIA),
        (DONE_IMAGE,  KIND_IMAGE), (FAILED_IMAGE_ALL,  KIND_IMAGE),  (FAILED_IMAGE,  KIND_IMAGE),
        (DONE_VIDEO,  KIND_VIDEO), (FAILED_VIDEO_ALL,  KIND_VIDEO),  (FAILED_VIDEO,  KIND_VIDEO),
        (DONE_AVATAR, KIND_AVATAR),(FAILED_AVATAR_ALL, KIND_AVATAR), (FAILED_AVATAR, KIND_AVATAR),
    ]:
        # 根据 path 的后缀决定 status
        if path.endswith("_done.txt"):
            status = STATUS_DONE
        elif path.endswith("_failed_all.txt"):
            status = STATUS_FAILED_ALL
        else:
            status = STATUS_FAILED
        _merge_txt(path, kind, status)

    # 5. 评估 media 状态
    with _archive_index_lock:
        media_keys = list(idx[KIND_MEDIA].keys())
    for jf in media_keys:
        media_status = evaluate_media_status(jf)
        if media_status not in ("unknown",):
            with _archive_index_lock:
                idx[KIND_MEDIA][jf]["status"] = media_status

    # 6. 把内存状态写回所有 .txt 文件（重新生成，保证一致）
    safe_print("[rebuild-index] 重新生成 _log/*.txt 文件...")
    # 先清空所有 .txt 文件
    for p in ALL_LOG_TXT_FILES:
        try:
            with open(p, "w", encoding="utf-8") as f:
                pass
        except OSError:
            pass
    # 清空内存 set
    with _txt_sets_lock:
        _txt_sets.clear()

    # 对每个 (kind, key)，按当前 status 写入对应 .txt
    for kind in [KIND_HTML, KIND_MEDIA, KIND_IMAGE, KIND_VIDEO, KIND_AVATAR]:
        with _archive_index_lock:
            entries = list(idx[kind].items())
        for key, rec in entries:
            status = rec.get("status", "unknown")
            if status in (STATUS_DONE, STATUS_FAILED, STATUS_FAILED_ALL):
                _sync_txt_files_for(kind, key, status)

    # 7. 落盘 archive_index.json
    save_archive_index(force=True)

    # 8. 统计
    safe_print("[rebuild-index] 完成。统计：")
    for kind in [KIND_HTML, KIND_MEDIA, KIND_IMAGE, KIND_VIDEO, KIND_AVATAR]:
        with _archive_index_lock:
            entries = idx[kind]
        if not entries:
            continue
        d = sum(1 for r in entries.values() if r.get("status") == STATUS_DONE)
        f = sum(1 for r in entries.values() if r.get("status") == STATUS_FAILED)
        fa = sum(1 for r in entries.values() if r.get("status") == STATUS_FAILED_ALL)
        safe_print(f"  {kind:<8} 共 {len(entries):>5}  done {d:>5}  failed {f:>5}  failed_all {fa:>5}")

    return 0



def cmd_build_index(args: argparse.Namespace) -> int:
    """构建 index.json（与 GitHub IncandescenceReader/build_index.py 一致的逻辑）。"""
    ensure_output_dirs()
    if not os.path.isdir(HTML_DIR):
        safe_print(f"[build-index] HTML 目录不存在：{os.path.abspath(HTML_DIR)}")
        return 1

    html_files = sorted(f for f in os.listdir(HTML_DIR) if f.endswith(".html"))
    total = len(html_files)
    safe_print(f"共检测到 {total} 个 HTML 文件")

    json_dir_exists = os.path.isdir(JSON_DIR)
    json_count = len([f for f in os.listdir(JSON_DIR) if f.endswith(".json")]) if json_dir_exists else 0
    safe_print(f"JSON 目录：{'存在' if json_dir_exists else '不存在'}，已有 {json_count} 个 JSON 文件")

    image_index = _bi_build_image_index()
    video_index = _bi_build_video_index()
    avatar_index = _bi_build_avatar_index()
    safe_print(f"本地图片索引：{len(image_index)} 张图片（按 basename 索引）")
    safe_print(f"本地视频索引：{len(video_index)} 个视频（按 media_key 索引）")
    safe_print(f"本地头像索引：{len(avatar_index)} 个头像（按 pid 索引）")
    tweet_id_index = _bi_build_tweet_id_index()
    safe_print(f"本地推文索引：{len(tweet_id_index)} 条 tweet_id（用于祖先链追溯）\n")

    index_data: list[dict] = []
    no_date: list[str] = []
    no_json: list[str] = []
    virtual_entries: dict[str, dict] = {}

    for i, fname in enumerate(html_files, 1):
        fpath = os.path.join(HTML_DIR, fname)
        with open(fpath, encoding="utf-8", errors="replace") as f:
            html_text = f.read()

        iso_date    = _bi_extract_date(html_text)
        text        = _bi_extract_text(html_text)
        render_data = _bi_extract_render_data(html_text)

        if not iso_date:
            no_date.append(fname)
            iso_date = _bi_fname_to_iso(fname)

        json_fname = os.path.splitext(fname)[0] + ".json"
        json_path  = os.path.join(JSON_DIR, json_fname)

        if os.path.exists(json_path):
            with open(json_path, encoding="utf-8") as jf:
                json_data = json.load(jf)
            meta = _bi_extract_from_json(json_data, tweet_id_index)
        else:
            no_json.append(fname)
            meta = _bi_extract_from_html_fallback(html_text, fname)

        wanted_images    = [image_index[b] for b in meta.get("wanted_basenames",    []) if b in image_index]
        embedded_images  = [image_index[b] for b in meta.get("embedded_basenames",  []) if b in image_index]
        wanted_videos    = [video_index[k] for k in meta.get("wanted_video_keys",   []) if k in video_index]
        embedded_videos  = [video_index[k] for k in meta.get("embedded_video_keys", []) if k in video_index]

        # 解析头像：把 wayback/pbs URL 转成本地路径
        render_data["author_avatar"] = _bi_resolve_avatar(
            render_data.get("author_avatar", ""), avatar_index
        )
        if render_data.get("embedded") and render_data["embedded"].get("author_avatar"):
            render_data["embedded"]["author_avatar"] = _bi_resolve_avatar(
                render_data["embedded"]["author_avatar"], avatar_index
            )

        # wanted_avatars：推文里所有用户的本地头像路径（用于前端直接引用，不依赖猜 pid）
        wanted_avatars: list[str] = []
        if json_data:
            for user in (json_data.get("includes", {}) or {}).get("users", []) or []:
                pid = extract_profile_image_id(user.get("profile_image_url", ""))
                if pid and pid in avatar_index:
                    local_av = avatar_index[pid]
                    if local_av not in wanted_avatars:
                        wanted_avatars.append(local_av)

        def clean_urls(s: str, urls: list[str]) -> str:
            if not s or not urls:
                return s
            for u in urls:
                s = s.replace(u, "")
            s = re.sub(r"[ \t]{2,}", " ", s)
            s = re.sub(r"[ \t]+\n", "\n", s)
            s = re.sub(r"\n[ \t]+", "\n", s)
            return s.strip()

        clean_body = clean_urls(render_data["body_text"], meta.get("remove_urls", []))
        clean_text = clean_urls(text,                     meta.get("remove_urls", []))

        record = {
            "file":            fname,
            "timestamp":       iso_date,
            "date":            iso_date[:10],
            "time":            iso_date[11:19],
            "text":            clean_text,
            "tweet_id":        meta["tweet_id"],
            "conversation_id": meta["conversation_id"],
            "is_reply":        meta["is_reply"],
            "reply_to_id":     meta["reply_to_id"],
            "reply_type":      meta["reply_type"],
            "has_quoted":      meta["has_quoted"],
            "quoted_id":       meta["quoted_id"],
            "has_media":       meta["has_media"],
            "media_keys":      meta["media_keys"],
            "author_name":     render_data["author_name"],
            "author_username": render_data["author_username"],
            "author_avatar":   render_data["author_avatar"],
            "body_text":       clean_body,
            "images":          render_data["images"] if meta.get("media_keys") else [],
            "wanted_images":     wanted_images,
            "embedded_images":   embedded_images,
            "wanted_videos":     wanted_videos,
            "embedded_videos":   embedded_videos,
            "wanted_avatars":    wanted_avatars,
            "remove_urls":         meta.get("remove_urls", []),
            "embedded_remove_urls":meta.get("embedded_remove_urls", []),
            "is_virtual":      False,
        }
        index_data.append(record)

        emb = render_data.get("embedded")
        if emb and emb.get("tweet_id"):
            vid = emb["tweet_id"]
            if vid not in virtual_entries:
                ts = emb.get("timestamp") or ""
                emb_body = clean_urls(emb.get("body_text", ""),
                                      meta.get("embedded_remove_urls", []))[:TEXT_MAX]
                virtual_entries[vid] = {
                    "file":            "",
                    "timestamp":       ts,
                    "date":            ts[:10],
                    "time":            ts[11:19],
                    "text":            emb_body,
                    "tweet_id":        vid,
                    "conversation_id": "",
                    "is_reply":        False,
                    "reply_to_id":     "",
                    "reply_type":      "",
                    "has_quoted":      False,
                    "quoted_id":       "",
                    "has_media":       False,
                    "media_keys":      [],
                    "author_name":     emb.get("author_name", ""),
                    "author_username": emb.get("author_username", ""),
                    "author_avatar":   emb.get("author_avatar", ""),
                    "body_text":       emb_body,
                    "images":          [],
                    "is_virtual":      True,
                }

        if i % 200 == 0 or i == total:
            safe_print(f"  进度：{i}/{total}（json覆盖：{i - len(no_json)}/{i}）")

    real_ids = {r["tweet_id"] for r in index_data if r.get("tweet_id")}
    added_virtual = 0
    for vid, vrec in virtual_entries.items():
        if vid not in real_ids:
            index_data.append(vrec)
            added_virtual += 1

    index_data.sort(key=lambda x: x["timestamp"], reverse=True)

    os.makedirs(os.path.dirname(INDEX_FILE), exist_ok=True)
    with open(INDEX_FILE, "w", encoding="utf-8") as f:
        json.dump(index_data, f, ensure_ascii=False, separators=(",", ":"))

    safe_print(f"\n完成！共 {len(index_data)} 条记录 → {os.path.abspath(INDEX_FILE)}")
    safe_print(f"  其中 {added_virtual} 条为虚拟条目（从 embedded-tweet-container 提取的外人推文，本地无独立 html 文件）")
    if no_date:
        safe_print(f"\n警告：{len(no_date)} 个文件未找到 #parentdate，已用文件名时间戳降级")
    if no_json:
        pct = len(no_json) / total * 100
        safe_print(f"\n注意：{len(no_json)} 个文件（{pct:.1f}%）无对应 JSON，使用 HTML 结构降级推断")
        safe_print("  → 跑 fetch-html 补全 JSON 数据后，重新运行本子命令可获得完整字段")
    return 0



# ============================================================================
# ── 子命令: dedup ───────────────────────────────────────────────────────────
# ============================================================================
#
# 媒体去重 + 孤儿清理。默认 dry-run；--execute 实际删除。
# 详细输出在最后会列出报告。
# ============================================================================

def _scan_dir_with_size_mtime(directory: str) -> list[tuple[str, int, str]]:
    """扫描目录返回 [(fname, size, mtime_ts)]"""
    if not os.path.isdir(directory):
        return []
    out: list[tuple[str, int, str]] = []
    for fname in os.listdir(directory):
        path = os.path.join(directory, fname)
        if not os.path.isfile(path):
            continue
        try:
            st = os.stat(path)
        except OSError:
            continue
        out.append((fname, st.st_size, str(int(st.st_mtime))))
    return out


def _group_by_basename(files: list[tuple[str, int, str]],
                       extractor) -> tuple[dict, list[str]]:
    """按 extractor 分组；返回 (groups, unparsed)。"""
    groups: dict[str, list[tuple[str, int, str]]] = defaultdict(list)
    unparsed: list[str] = []
    for entry in files:
        fname = entry[0]
        key = extractor(fname)
        if not key:
            unparsed.append(fname)
            continue
        groups[key].append(entry)
    return groups, unparsed


def _decide_keep_largest(groups: dict) -> tuple[dict, set, dict]:
    """同 basename 保留最大文件。"""
    keep_map: dict[str, str] = {}
    remove_set: set[str] = set()
    redirect_map: dict[str, str] = {}
    for key, entries in groups.items():
        if len(entries) == 1:
            keep_map[key] = entries[0][0]
            continue
        sorted_entries = sorted(entries, key=lambda x: (-x[1], x[0]))
        kept = sorted_entries[0][0]
        keep_map[key] = kept
        for e in sorted_entries[1:]:
            remove_set.add(e[0])
            redirect_map[e[0]] = kept
    return keep_map, remove_set, redirect_map


def _format_size(n: int) -> str:
    if n < 1024:
        return f"{n} B"
    if n < 1024 ** 2:
        return f"{n/1024:.1f} KB"
    if n < 1024 ** 3:
        return f"{n/1024**2:.2f} MB"
    return f"{n/1024**3:.2f} GB"


def _scan_html_refs() -> dict[str, set[str]]:
    refs: dict[str, set[str]] = {"image": set(), "video": set(), "avatar": set()}
    if not os.path.isdir(HTML_DIR):
        return refs
    pattern = re.compile(
        r'src\s*=\s*["\'](\.\./)?(image|video|avatar)/([^"\']+)["\']',
        re.IGNORECASE,
    )
    for fname in os.listdir(HTML_DIR):
        if not fname.endswith(".html"):
            continue
        try:
            with open(os.path.join(HTML_DIR, fname), encoding="utf-8", errors="replace") as f:
                content = f.read()
        except Exception:
            continue
        for m in pattern.finditer(content):
            kind = m.group(2).lower()
            ref = m.group(3)
            if kind in refs:
                refs[kind].add(ref)
    return refs


def _backup_files(files: list[str], src_dir: str, label: str) -> str | None:
    if not files:
        return None
    ts = time.strftime("%Y%m%d_%H%M%S")
    backup_dir = os.path.join(OUTPUT_DIR, f"_dedup_backup_{label}_{ts}")
    os.makedirs(backup_dir, exist_ok=True)
    for fn in files:
        src = os.path.join(src_dir, fn)
        if os.path.exists(src):
            try:
                shutil.copy2(src, os.path.join(backup_dir, fn))
            except Exception as e:
                safe_print(f"  [警告] 备份失败 {fn}: {e}")
    return backup_dir


def _update_html_redirects(redirects: list[tuple[str, str, str]], backup: bool) -> tuple[int, int]:
    """根据 [(kind, old, new)] 更新所有 html 的 src。返回 (modified_files, total_replaces)。"""
    if not redirects or not os.path.isdir(HTML_DIR):
        return 0, 0
    if backup:
        os.makedirs(BACKUP_DIR, exist_ok=True)

    # 预编译每条 redirect 的替换规则（按 kind 准确匹配）
    compiled: list[tuple[re.Pattern, str]] = []
    for kind, old, new in redirects:
        old_e = re.escape(old)
        # src="../{kind}/{old}" 或 src="{kind}/{old}"（一致替换为相对 ../{kind}/{new}）
        compiled.append((
            re.compile(rf'(src\s*=\s*["\'])((?:\.\./)?{kind}/){old_e}(["\'])'),
            rf'\1\2{new}\3',
        ))

    mod_files = 0
    total_replaces = 0
    for fname in os.listdir(HTML_DIR):
        if not fname.endswith(".html"):
            continue
        path = os.path.join(HTML_DIR, fname)
        try:
            with open(path, encoding="utf-8") as f:
                content = f.read()
        except Exception:
            continue
        orig = content
        local_replaces = 0
        for pat, rep in compiled:
            content, n = pat.subn(rep, content)
            local_replaces += n
        if local_replaces > 0:
            if backup:
                try:
                    shutil.copy2(path, os.path.join(BACKUP_DIR, fname))
                except Exception:
                    pass
            with open(path, "w", encoding="utf-8") as f:
                f.write(content)
            mod_files += 1
            total_replaces += local_replaces
    return mod_files, total_replaces


def cmd_dedup(args: argparse.Namespace) -> int:
    """媒体去重 + 孤儿清理。默认 dry-run；--execute 实际删除。"""
    ensure_output_dirs()

    image_files  = _scan_dir_with_size_mtime(IMAGE_DIR)
    video_files  = _scan_dir_with_size_mtime(VIDEO_DIR)
    avatar_files = _scan_dir_with_size_mtime(AVATAR_DIR)

    # 分组
    img_groups,  img_unparsed  = _group_by_basename(image_files,  extract_image_basename)
    vid_groups,  vid_unparsed  = _group_by_basename(video_files,  extract_video_media_key)
    av_groups,   av_unparsed   = _group_by_basename(avatar_files, extract_avatar_pid_from_filename)

    img_keep, img_remove, img_redir = _decide_keep_largest(img_groups)
    vid_keep, vid_remove, vid_redir = _decide_keep_largest(vid_groups)
    av_keep,  av_remove,  av_redir  = _decide_keep_largest(av_groups)

    # 报告
    print("\n══ 去重分析报告 ══\n")

    def report_section(title: str, files: list, groups: dict, remove_set: set,
                       unparsed: list[str]) -> None:
        size_map = {e[0]: e[1] for e in files}
        saved = sum(size_map.get(fn, 0) for fn in remove_set)
        dup_keys = [k for k, es in groups.items() if len(es) > 1]
        safe_print(f"── {title} ──")
        safe_print(f"  文件总数：             {len(files)}")
        if unparsed:
            safe_print(f"  无法识别（保留）：     {len(unparsed)}")
        safe_print(f"  唯一 basename：        {len(groups)}")
        safe_print(f"  含重复的 basename：    {len(dup_keys)}")
        safe_print(f"  将删除的重复文件：     {len(remove_set)}")
        safe_print(f"  预估节省：             {_format_size(saved)}")

    report_section("图片", image_files,  img_groups, img_remove, img_unparsed)
    report_section("视频", video_files,  vid_groups, vid_remove, vid_unparsed)
    report_section("头像", avatar_files, av_groups,  av_remove,  av_unparsed)

    # 孤儿
    html_refs = _scan_html_refs()
    safe_print(f"\n  HTML 引用：{len(html_refs['image'])} 张图 / {len(html_refs['video'])} 个视频 / {len(html_refs['avatar'])} 个头像")

    def collect_orphans(files: list, kind: str, keep_set: set, remove_set: set) -> list[tuple[str, int]]:
        out = []
        for entry in files:
            fname, size = entry[0], entry[1]
            if fname in remove_set:
                continue
            if fname in html_refs[kind]:
                continue
            out.append((fname, size))
        return out

    orphan_imgs = collect_orphans(image_files,  "image",  set(img_keep.values()), img_remove)
    orphan_vids = collect_orphans(video_files,  "video",  set(vid_keep.values()), vid_remove)
    orphan_avs  = collect_orphans(avatar_files, "avatar", set(av_keep.values()),  av_remove)

    if args.delete_orphans:
        safe_print(f"\n  孤儿（启用 --delete-orphans）：")
        safe_print(f"    图片：{len(orphan_imgs)}（{_format_size(sum(s for _,s in orphan_imgs))}）")
        safe_print(f"    视频：{len(orphan_vids)}（{_format_size(sum(s for _,s in orphan_vids))}）")
        safe_print(f"    头像：{len(orphan_avs)}（{_format_size(sum(s for _,s in orphan_avs))}）")
    else:
        safe_print(f"\n  孤儿（仅分析，未启用 --delete-orphans）：")
        safe_print(f"    图片：{len(orphan_imgs)}  视频：{len(orphan_vids)}  头像：{len(orphan_avs)}")

    if not args.execute:
        safe_print("\n  这是 dry-run 报告。要实际执行，加 --execute")
        return 0

    # 实际删除
    safe_print("\n══ 开始执行 ══")
    if args.backup:
        for label, files, src in (
            ("image",  list(img_remove), IMAGE_DIR),
            ("video",  list(vid_remove), VIDEO_DIR),
            ("avatar", list(av_remove),  AVATAR_DIR),
        ):
            d = _backup_files(files, src, label)
            if d:
                safe_print(f"  备份 {len(files)} 个 {label} → {d}")

    # 更新 HTML 引用（先重写再删）
    redirects: list[tuple[str, str, str]] = []
    for old, new in img_redir.items():
        redirects.append(("image", old, new))
    for old, new in vid_redir.items():
        redirects.append(("video", old, new))
    for old, new in av_redir.items():
        redirects.append(("avatar", old, new))
    if redirects:
        mod, total = _update_html_redirects(redirects, backup=args.backup)
        safe_print(f"  HTML 重定向：修改 {mod} 个文件，{total} 处替换")

    # 删除
    def remove_files(files: list[str], directory: str, label: str) -> int:
        removed = 0
        for fn in files:
            p = os.path.join(directory, fn)
            try:
                os.remove(p)
                removed += 1
            except OSError as e:
                safe_print(f"    [警告] 删除失败 {fn}: {e}")
        safe_print(f"  删除 {label}：{removed}/{len(files)}")
        return removed

    remove_files(list(img_remove), IMAGE_DIR,  "图片")
    remove_files(list(vid_remove), VIDEO_DIR,  "视频")
    remove_files(list(av_remove),  AVATAR_DIR, "头像")

    if args.delete_orphans:
        remove_files([fn for fn, _ in orphan_imgs], IMAGE_DIR,  "孤儿图片")
        remove_files([fn for fn, _ in orphan_vids], VIDEO_DIR,  "孤儿视频")
        remove_files([fn for fn, _ in orphan_avs],  AVATAR_DIR, "孤儿头像")

    safe_print("\n[dedup] 完成")
    return 0


# ============================================================================
# ── 子命令: gen-lists ───────────────────────────────────────────────────────
# ============================================================================
#
# 从 json/ 反推应该下载的 URL 清单。
# 主要用于：手动检查"哪些 URL 已下载好 / 还需要下载"，或喂给其它工具批量请求。
# ============================================================================

_GEN_LIST_NAME_RE = re.compile(r"^(\d{14})_twitter_com_(.+)_status_(\d+)\.json$")


def cmd_gen_lists(args: argparse.Namespace) -> int:
    """
    从 json/ 目录所有 JSON 文件名派生：
      _url_list.txt    每行一个 wayback URL（https://web.archive.org/web/{ts}/https://twitter.com/{user}/status/{tid}）
      _list_media.txt  每行一个 JSON 文件名

    跟原版 _gen_list.py 一字不差，确保产物可与 GitHub 成品 diff 一致。
    """
    ensure_output_dirs()
    if not os.path.isdir(JSON_DIR):
        safe_print(f"[gen-lists] JSON 目录不存在：{JSON_DIR}")
        return 1

    files = sorted(f for f in os.listdir(JSON_DIR) if f.endswith(".json"))
    if not files:
        safe_print(f"[gen-lists] {JSON_DIR} 下没有 JSON 文件")
        return 0

    media_lines: list[str] = []
    url_lines:   list[str] = []
    skipped:     list[str] = []

    for fname in files:
        m = _GEN_LIST_NAME_RE.match(fname)
        if not m:
            skipped.append(fname)
            continue
        timestamp, username, tid = m.group(1), m.group(2), m.group(3)
        media_lines.append(fname)
        url_lines.append(
            f"https://web.archive.org/web/{timestamp}/"
            f"https://twitter.com/{username}/status/{tid}"
        )

    with open(MEDIA_LIST_FILE, "w", encoding="utf-8") as f:
        f.write("\n".join(media_lines) + "\n")
    with open(URL_LIST_FILE, "w", encoding="utf-8") as f:
        f.write("\n".join(url_lines) + "\n")

    safe_print(f"扫描 {JSON_DIR}/")
    safe_print(f"  共 {len(files)} 个 JSON 文件")
    safe_print(f"  解析成功：{len(media_lines)}")
    if skipped:
        safe_print(f"  跳过（文件名不匹配）：{len(skipped)}")
        for s in skipped[:5]:
            safe_print(f"    - {s}")
        if len(skipped) > 5:
            safe_print(f"    ... 还有 {len(skipped) - 5} 个")
    safe_print(f"")
    safe_print(f"输出：")
    safe_print(f"  {MEDIA_LIST_FILE}  ({len(media_lines)} 行)")
    safe_print(f"  {URL_LIST_FILE}    ({len(url_lines)} 行)")
    return 0


# ============================================================================
# ── 子命令: convert ─────────────────────────────────────────────────────────
# ============================================================================
#
# 把外部 dump（download_archive.py 的输出）转换成本项目格式。
# 输入约定：dump 目录里有 snapshots.json + 一堆下载好的媒体文件。
# 输出：写到本工作目录的 json/, image/, video/, avatar/ 下。
# ============================================================================

def _safe_copy(src: str, dst: str) -> bool:
    if not os.path.exists(src):
        return False
    if os.path.exists(dst):
        return True
    try:
        shutil.copy2(src, dst)
        return True
    except Exception as e:
        safe_print(f"  [警告] 复制失败 {src} → {dst}: {e}")
        return False


def _find_dump_assets(dump_dir: str) -> tuple[str, str]:
    """
    定位 dump 目录里的 snapshots.json 和 assets 子目录。
    download_archive.py 输出的标准结构：
      <dump_dir>/
        ├── {USER}_archive.html              ← 主 HTML
        ├── ...其他排序变体.html
        └── {USER}_archive_assets/           ← 这里是 assets_dir
            ├── snapshots.json
            ├── media_index.json
            ├── json/{ts}_{tid}.json
            └── media/{hash}.{ext}
    也兼容用户自己整理过的简单格式（snapshots.json 在 dump_dir 根下）。
    返回 (snapshots.json 路径, assets_dir 路径)。
    """
    # 优先在根目录找
    cand = os.path.join(dump_dir, "snapshots.json")
    if os.path.exists(cand):
        return cand, dump_dir
    # 找 {USER}_archive_assets/ 目录
    for entry in os.listdir(dump_dir):
        sub = os.path.join(dump_dir, entry)
        if not os.path.isdir(sub):
            continue
        cand = os.path.join(sub, "snapshots.json")
        if os.path.exists(cand):
            return cand, sub
    # 兜底：递归一层
    for root, dirs, files in os.walk(dump_dir):
        if "snapshots.json" in files:
            return os.path.join(root, "snapshots.json"), root
        # 限制递归深度，不深入太多
        if root != dump_dir and os.path.dirname(root) != dump_dir:
            dirs.clear()
    return "", ""


def _classify_media_url(media_url: str) -> str:
    """
    根据原始 URL 判断类型：thumb / avatar / video / image。
    thumb 表示视频缩略图（amplify_video_thumb / ext_tw_video_thumb / tweet_video_thumb），
    用户成品里不保留这些。
    """
    if any(t in media_url for t in (
        "amplify_video_thumb", "ext_tw_video_thumb", "tweet_video_thumb",
    )):
        return "thumb"
    if "profile_images" in media_url:
        return "avatar"
    if ("video.twimg.com" in media_url or
        "ext_tw_video" in media_url or
        "amplify_video/" in media_url or
        media_url.lower().endswith(".mp4")):
        return "video"
    return "image"


def _media_safe_local_name(media_url: str, ts: str, ext: str) -> str:
    """
    给从 dump 复制过来的媒体生成本项目格式的本地文件名。
    遵循 safe_filename 规则：{ts}_{URL前缀清洗}{ext}
    """
    if not ts:
        ts = "00000000000000"
    return safe_filename(ts, media_url, ext)


def cmd_convert(args: argparse.Namespace) -> int:
    """
    从 download_archive.py 的 dump 转成本项目格式。

    把 dump 里：
      assets/json/{ts}_{tid}.json   → wayback_snapshots/json/{ts}_twitter_com_{user}_status_{tid}.json
      assets/media/{hash}.jpg       → wayback_snapshots/image|video|avatar/ （按 URL 类型分流）
                                      文件名按本项目的 safe_filename 重命名

    依赖 dump 里的 media_index.json（原 URL → hash 文件路径）做反查。
    """
    dump_dir = args.dump_dir
    if not os.path.isdir(dump_dir):
        safe_print(f"[convert] dump 目录不存在：{dump_dir}")
        return 1
    ensure_output_dirs()

    # 1. 定位 snapshots.json 和 assets 目录
    snapshots_path, assets_dir = _find_dump_assets(dump_dir)
    if not snapshots_path:
        safe_print(f"[convert] 在 {dump_dir} 里找不到 snapshots.json")
        return 1
    safe_print(f"[convert] dump_dir = {dump_dir}")
    safe_print(f"[convert] assets_dir = {assets_dir}")

    # 2. 解析 snapshots.json
    try:
        with open(snapshots_path, encoding="utf-8") as f:
            snap_data = json.load(f)
    except Exception as e:
        safe_print(f"[convert] snapshots.json 解析失败：{e}")
        return 1

    user = ""
    snapshots: list[dict] = []
    if isinstance(snap_data, dict):
        # download_archive.py 格式：{user, snapshots: [{timestamp, original_url, json_filename}]}
        user = snap_data.get("user", "")
        snapshots = snap_data.get("snapshots", []) or []
    elif isinstance(snap_data, list):
        # 简单数组格式（用户自己整理过的）
        snapshots = snap_data
    if not snapshots:
        safe_print(f"[convert] snapshots.json 里没有快照条目")
        return 1
    safe_print(f"[convert] user = @{user or '(未指定)'}")
    safe_print(f"[convert] 快照条数：{len(snapshots)}")

    # 3. 解析 media_index.json（原 URL → 本地 hash 路径）
    media_index_path = os.path.join(assets_dir, "media_index.json")
    media_url_to_path: dict[str, str] = {}
    if os.path.exists(media_index_path):
        try:
            with open(media_index_path, encoding="utf-8") as f:
                media_url_to_path = json.load(f)
            safe_print(f"[convert] media_index.json：{len(media_url_to_path)} 条映射")
        except Exception as e:
            safe_print(f"[convert] media_index.json 解析失败：{e}")
    else:
        safe_print(f"[convert] media_index.json 不存在，跳过媒体复制")

    src_json_dir = os.path.join(assets_dir, "json")

    # 4. 逐快照复制 + 重命名 JSON；同时记录每条 json 对应的 timestamp 供后续媒体命名用
    copied_json = 0
    json_url_to_ts: dict[str, str] = {}  # original_url → snapshot timestamp
    for snap in snapshots:
        ts  = str(snap.get("timestamp") or snap.get("ts") or "")
        url = (snap.get("original_url") or snap.get("original") or snap.get("url") or "")
        src_json_name = snap.get("json_filename", "")
        if not (ts and url):
            continue
        json_url_to_ts[url] = ts

        # 找源 JSON 文件
        src_json_path = ""
        if src_json_name:
            cand = os.path.join(src_json_dir, src_json_name)
            if os.path.exists(cand):
                src_json_path = cand
        if not src_json_path:
            # 兜底：尝试从 tweet_id 构造文件名
            m = re.search(r"/status/(\d+)", url)
            if m:
                cand = os.path.join(src_json_dir, f"{ts}_{m.group(1)}.json")
                if os.path.exists(cand):
                    src_json_path = cand
        if not src_json_path:
            continue

        dst_json_name = safe_filename(ts, url, ".json")
        if _safe_copy(src_json_path, os.path.join(JSON_DIR, dst_json_name)):
            copied_json += 1

    safe_print(f"[convert] 复制 JSON：{copied_json}")

    # 5. 从所有复制完的 JSON 反扫，建立 media URL → 最早 timestamp 的映射，
    #    同时建立 profile_pid → user.id 映射（私密账号场景下，avatar 用 user.id 命名）。
    safe_print(f"[convert] 扫描 JSON 建立媒体 URL → timestamp / profile_pid → user.id 映射...")
    media_url_to_ts: dict[str, str] = {}
    profile_pid_to_user_id: dict[str, str] = {}

    def _register_media_ts(url: str, ts: str) -> None:
        if not url or not ts:
            return
        old = media_url_to_ts.get(url, "")
        # 取最早的 ts（数字字符串比较）
        if not old or ts < old:
            media_url_to_ts[url] = ts

    for jname in os.listdir(JSON_DIR):
        if not jname.endswith(".json"):
            continue
        # 从文件名取 ts
        ts = extract_timestamp_from_filename(jname)
        try:
            with open(os.path.join(JSON_DIR, jname), encoding="utf-8") as f:
                data = json.load(f)
        except Exception:
            continue
        includes = data.get("includes", {}) or {}
        # 头像 URL + 建立 profile_pid → user.id 映射
        for u in includes.get("users", []) or []:
            purl = u.get("profile_image_url") or ""
            _register_media_ts(purl, ts)
            uid = str(u.get("id") or "")
            pid = extract_profile_image_id(purl)
            if uid and pid:
                # 同 pid 多次出现保留第一次（通常多个 user 不会共享同一 pid，但保险起见）
                profile_pid_to_user_id.setdefault(pid, uid)
        # 推文媒体
        for m in includes.get("media", []) or []:
            mtype = m.get("type", "")
            if mtype == "photo":
                _register_media_ts(m.get("url") or "", ts)
            elif mtype in ("video", "animated_gif"):
                for v in m.get("variants", []) or []:
                    if v.get("content_type") == "video/mp4":
                        _register_media_ts(v.get("url") or "", ts)
            if m.get("preview_image_url"):
                _register_media_ts(m["preview_image_url"], ts)

    safe_print(f"[convert] 媒体 URL → ts 映射：{len(media_url_to_ts)} 条")
    safe_print(f"[convert] profile_pid → user.id 映射：{len(profile_pid_to_user_id)} 条")

    # 6. 复制媒体并按本项目命名规则重命名
    include_unreferenced = bool(getattr(args, "include_unreferenced", False))
    copied_img = copied_vid = copied_av = 0
    skipped_thumb = skipped_unref = skipped_other = 0
    if media_url_to_path:
        for media_url, hash_path in media_url_to_path.items():
            kind = _classify_media_url(media_url)

            # 跳过视频缩略图
            if kind == "thumb":
                skipped_thumb += 1
                continue

            # 默认跳过未在 JSON 中引用的（头像总是保留）
            ts = media_url_to_ts.get(media_url, "")
            if not ts and kind != "avatar" and not include_unreferenced:
                skipped_unref += 1
                continue

            # 解析源文件位置
            src = None
            for base in (dump_dir, os.path.dirname(assets_dir), assets_dir, os.path.dirname(dump_dir)):
                if not base:
                    continue
                cand = os.path.join(base, hash_path)
                if os.path.exists(cand):
                    src = cand
                    break
            if not src:
                cand = os.path.join(assets_dir, "media", os.path.basename(hash_path))
                if os.path.exists(cand):
                    src = cand
            if not src:
                skipped_other += 1
                continue

            ext_in_hash = os.path.splitext(hash_path)[1].lower()
            ext = ext_in_hash if ext_in_hash else ext_from_url(media_url)

            if kind == "avatar":
                # 用 user.id（而不是 profile_pid）命名，跟原版 render_html_json.py 的约定一致
                # 这样 render-html 生成的 src 跟本地实际文件名能对上
                profile_pid = extract_profile_image_id(media_url)
                user_id = profile_pid_to_user_id.get(profile_pid, "")
                if not user_id:
                    # 反查不到 user.id 时，fallback 用 profile_pid（罕见情况）
                    user_id = profile_pid
                if not user_id:
                    skipped_other += 1
                    continue
                dst_name = f"avatar_{user_id}{ext}"
                dst = os.path.join(AVATAR_DIR, dst_name)
                if _safe_copy(src, dst):
                    copied_av += 1
            elif kind == "video":
                if not ts:
                    ts = "00000000000000"
                dst_name = _media_safe_local_name(media_url, ts, ".mp4" if not ext or ext == ".jpg" else ext)
                dst = os.path.join(VIDEO_DIR, dst_name)
                if _safe_copy(src, dst):
                    copied_vid += 1
            else:  # image
                if not ts:
                    ts = "00000000000000"
                dst_name = _media_safe_local_name(media_url, ts, ext if ext else ".jpg")
                dst = os.path.join(IMAGE_DIR, dst_name)
                if _safe_copy(src, dst):
                    copied_img += 1

    safe_print(f"[convert] 完成：")
    safe_print(f"  json:   {copied_json}")
    safe_print(f"  image:  {copied_img}")
    safe_print(f"  video:  {copied_vid}")
    safe_print(f"  avatar: {copied_av}")
    if skipped_thumb:
        safe_print(f"  跳过视频缩略图：{skipped_thumb}")
    if skipped_unref:
        safe_print(f"  跳过未引用的图/视频：{skipped_unref}  (加 --include-unreferenced 保留)")
    if skipped_other:
        safe_print(f"  跳过其它：{skipped_other}")

    # 自动建立 archive_index（把本地已存在的媒体登记为 done）
    safe_print(f"\n[convert] 自动建立 archive_index.json...")
    cmd_rebuild_index(argparse.Namespace())

    safe_print(f"\n后续：")
    safe_print(f"  python {os.path.relpath(sys.argv[0])} render-html")
    safe_print(f"  python {os.path.relpath(sys.argv[0])} fetch-media   # 补缺头像/图等")
    safe_print(f"  python {os.path.relpath(sys.argv[0])} build-index")
    return 0


# ============================================================================
# ── 子命令: fetch-cdx ───────────────────────────────────────────────────────
# ============================================================================
#
# 调用 Wayback CDX API 抓取某账号所有归档快照，写入 ./cdx_data.json。
# 用法（在一个干净账号目录里）：
#   mkdir accounts/<username> && cd accounts/<username>
#   python ../../archive.py fetch-cdx <username>
#   python ../../archive.py all
#
# CDX API：
#   http://web.archive.org/cdx/search/cdx?
#       url=twitter.com/<username>/status/&matchType=prefix&output=json&...
# 参数说明：
#   matchType=prefix     用前缀匹配（而非 URL 通配符 '*'）
#   filter=mimetype:application/json  只要 JSON 推文（不要图片/CSS 等）
# ============================================================================

CDX_BASE_URL = "https://web.archive.org/cdx/search/cdx"


def cmd_fetch_cdx(args: argparse.Namespace) -> int:
    """抓取某账号的 CDX 数据，写到 ./cdx_data.json。"""
    user = (args.username or "").strip().lstrip("@")
    if not user:
        safe_print("[fetch-cdx] 必须指定用户名")
        return 1

    params = {
        "url":        f"twitter.com/{user}/status/",
        "matchType":  "prefix",
        "output":     "json",
        "filter":     "mimetype:application/json",
    }
    if args.collapse_digest:
        params["collapse"] = "digest"
    if args.from_ts:
        params["from"] = args.from_ts
    if args.to_ts:
        params["to"] = args.to_ts

    safe_print(f"[fetch-cdx] 查询 CDX API: user=@{user}")
    safe_print(f"  url={CDX_BASE_URL}")
    safe_print(f"  params={params}")

    try:
        resp = get_session().get(CDX_BASE_URL, params=params, timeout=60)
        resp.raise_for_status()
    except Exception as e:
        safe_print(f"[fetch-cdx] 请求失败：{type(e).__name__}: {e}")
        if "hostname_blocked" in str(e) or "403" in str(e):
            safe_print(
                "  注意：你的网络可能屏蔽了 web.archive.org。\n"
                "  解决：换代理 / VPN / 直连环境后重试。"
            )
        return 1

    try:
        rows = resp.json()
    except json.JSONDecodeError as e:
        safe_print(f"[fetch-cdx] CDX 返回不是 JSON：{e}")
        safe_print(f"  前 500 字节：{resp.text[:500]}")
        return 1

    if not isinstance(rows, list) or len(rows) < 1:
        safe_print(f"[fetch-cdx] CDX 返回为空（账号可能没有归档）")
        return 1

    # 备份已有的 cdx_data.json
    if os.path.exists(CDX_LOCAL_FILE) and not args.force:
        backup = CDX_LOCAL_FILE + ".bak"
        try:
            shutil.copy2(CDX_LOCAL_FILE, backup)
            safe_print(f"  备份现有 cdx_data.json → {backup}")
        except Exception:
            pass

    with open(CDX_LOCAL_FILE, "w", encoding="utf-8") as f:
        json.dump(rows, f, ensure_ascii=False, indent=None, separators=(",", ":"))

    # 统计
    snapshots = len(rows) - 1
    timestamps = [r[rows[0].index("timestamp")] for r in rows[1:]] if snapshots else []
    first_ts = min(timestamps) if timestamps else "—"
    last_ts  = max(timestamps) if timestamps else "—"

    safe_print(f"\n[fetch-cdx] 写入 {CDX_LOCAL_FILE}")
    safe_print(f"  快照总数：{snapshots}")
    if timestamps:
        safe_print(f"  时间范围：{first_ts} ~ {last_ts}")
    safe_print(f"\n下一步：python {os.path.relpath(sys.argv[0])} all")
    return 0



# ============================================================================
#
# 从 json/ 生成"伪 wayback 风格"的 HTML，专用于私密账号（没有真 wayback 快照）。
# 渲染出来的 HTML 直接引用本地 image/ video/ avatar/ 资源。
# ============================================================================
# ── 子命令: render-html ─────────────────────────────────────────────────────
# ============================================================================
#
# 把 json/ 渲染成 wayback 风格的 HTML，写入 html/。专用于私密账号场景
# （没有真 wayback 快照，但通过 convert 拿到 dump JSON 后需要"伪造"HTML）。
#
# 关键：输出的 HTML 结构必须跟"真 wayback HTML + clean-html 清洗后"的产物
# 严格一致，因为下游 build-index / Reader.html 用同一套 BeautifulSoup 选择器
# 解析（#nonjsonview / .tweet-author / .tweet-content / .embedded-tweet-container
# / .tweet-image / .tweet-video）。
#
# CSS 直接照搬 GitHub TauCeti_10700 成品（同 md5 一致）。
# ============================================================================

# 完整 wayback HTML head（含 CSS），直接照搬成品（md5 = fbe44bdc4011642641e41526b761adbb）
_WAYBACK_HEAD = """<!DOCTYPE html>
<html>
<head>
<meta charset=\"utf-8\"/>
<meta content=\"text/html; charset=utf-8\" http-equiv=\"content-type\"/>
<title>
Wayback Machine
</title>
<style type=\"text/css\">
body {
\t\t\t\tmargin:0;
\t\t\t\tpadding: 20px;
\t\t\t\tbackground-color: #000;
\t\t\t\tmin-height: 100vh;
\t\t\t\tbox-sizing: border-box;
\t\t\t}

.tweet-container {
  font-family: Helvetica, Arial, sans-serif;
  padding: 12px 16px;
  border: 1px solid #cfd9de;
  border-radius: 12px;
  margin-top: 20px;
\t\t\t\tmargin-left: auto;
\t\t\t\tmargin-right: auto;
\t\t\t\tbackground-color: white;
  max-width: 100%;
  display: flex;
  flex-direction: column;
  justify-content: center;
  align-items: center;
  max-width: max-content;
}

.tweet-container > #nonjsonview {
  max-width: 600px;
  margin-left: auto;
  margin-right: auto;

}

.tweet-author {
  display: flex;
  flex-direction: row;
  align-items: center;
  padding-bottom: 0.75rem;
}

.tweet-author-profile-image img {
  width: 48px;
  max-width: 48px;
  height: 48px;
  max-height: 48px;
  overflow: hidden;
  border-radius: 50%;
  margin-right: 5px;
}

.tweet-author-info {
  display: flex;
  flex-direction: column;
}

.tweet-author-name {
  font-weight: bold;
}

.tweet-content {
  font-size: 1.25rem;
}

\t\t\t.tweet-image {
\t\t\t\twidth: 100%;
\t\t\t\theight: auto;
\t\t\t\tmargin-top: 12px;
\t\t\t\tborder-radius: 12px;
\t\t\t}

\t\t\t.embedded-tweet-container {
\t\t\t\tbox-sizing: border-box;
\t\t\t\tmargin-top: 12px;
\t\t\t\tpadding: 12px;
\t\t\t\tborder: 1px solid #cfd9de;
  border-radius: 12px;
\t\t\t\tbackground-color: white;
\t\t\t\tmax-width: 100%;
\t\t\t}
\t\t\t.date {
\t\t\t\tfont-size: 0.75rem;
\t\t\t\tcolor: #657786;
\t\t\t\tmargin-top: 12px;
\t\t\t}
\t\t\t.date a {
\t\t\t\tcolor: #657786;
\t\t\t\ttext-decoration: none;
\t\t\t}
\t\t\t.date a:hover {
\t\t\t\ttext-decoration: underline;
\t\t\t}
  .on {
    display: block;
  }
  .off {
    display: none;
  }
.tweet-video {
  width: 100%;
  height: auto;
  margin-top: 12px;
  border-radius: 12px;
}
</style>
</head>
"""


# ── 本地媒体查找 ──────────────────────────────────────────────

_AVATAR_FNAME_PID_RE = re.compile(r"^avatar_(\d+)\.(?:jpg|jpeg|png|gif|webp)$", re.IGNORECASE)

# render-html 阶段共享的"username/name → 本地 avatar 文件"反射缓存
# 由 cmd_render_html 在开始时扫一遍 JSON 建立，避免每条推文都重扫
_RENDER_AVATAR_BY_USERNAME: dict[str, str] = {}
_RENDER_AVATAR_BY_NAME: dict[str, str] = {}
_RENDER_AVATAR_BY_PID: dict[str, str] = {}


def _build_render_avatar_indexes() -> None:
    """
    在 render-html 开始时一次性扫 avatar/ + json/ 建立三路反射索引：
      pid → 本地文件名（直接来自 avatar/ 目录）
      name → 本地文件名（通过 JSON.includes.users 反扫）
      username → 本地文件名（同上）

    跟 fetch-media 的 MediaIndex 头像三路反射逻辑一致，保证 render-html 在
    "同用户换过头像、本地保留旧头像"的场景下也能正确选用现有本地文件。
    """
    _RENDER_AVATAR_BY_PID.clear()
    _RENDER_AVATAR_BY_NAME.clear()
    _RENDER_AVATAR_BY_USERNAME.clear()
    if not os.path.isdir(AVATAR_DIR):
        return

    # 1. 扫 avatar 目录建 pid → fname
    for fname in os.listdir(AVATAR_DIR):
        m = _AVATAR_FNAME_PID_RE.match(fname)
        if m:
            _RENDER_AVATAR_BY_PID.setdefault(m.group(1), fname)

    # 2. 扫所有 JSON 的 includes.users。对每个 user，同时尝试 user.id 和 profile_pid 作为
    #    avatar 文件命名约定（兼容两套体系）。任一在本地命中就建立 username/name 反射。
    if not os.path.isdir(JSON_DIR):
        return
    for jname in os.listdir(JSON_DIR):
        if not jname.endswith(".json"):
            continue
        try:
            with open(os.path.join(JSON_DIR, jname), encoding="utf-8") as f:
                data = json.load(f)
        except Exception:
            continue
        for u in (data.get("includes", {}) or {}).get("users", []) or []:
            url = u.get("profile_image_url") or ""
            uid = str(u.get("id") or "")
            profile_pid = extract_profile_image_id(url)
            # 候选：user.id（TauCeti 模式）+ profile_pid（AnIncandescence 模式）
            fname = None
            for candidate in (uid, profile_pid):
                if candidate and candidate in _RENDER_AVATAR_BY_PID:
                    fname = _RENDER_AVATAR_BY_PID[candidate]
                    break
            if not fname:
                continue
            name = (u.get("name") or "").strip()
            username = (u.get("username") or "").strip().lstrip("@")
            if name:
                _RENDER_AVATAR_BY_NAME.setdefault(name, fname)
            if username:
                _RENDER_AVATAR_BY_USERNAME.setdefault(username, fname)


def _find_local_avatar_path(try_ids: list[str], name: str = "", username: str = "") -> str:
    """
    在 avatar/ 目录按一组候选 ID + 反射查找头像。
    try_ids: 候选 ID 列表（如 [user.id, profile_pid]），按顺序尝试。
    顺序很重要：传 user.id 在前则优先 TauCeti 模式（render_html_json.py 约定）；
    传 profile_pid 在前则优先 AnIncandescence 模式（fetch-media 约定）。
    """
    # 1. 按每个候选 ID 直接查
    for tid in try_ids:
        if tid and tid in _RENDER_AVATAR_BY_PID:
            return f"../avatar/{_RENDER_AVATAR_BY_PID[tid]}"
    # 2. username 反射
    if username:
        un = username.strip().lstrip("@")
        if un in _RENDER_AVATAR_BY_USERNAME:
            return f"../avatar/{_RENDER_AVATAR_BY_USERNAME[un]}"
    # 3. name 反射
    if name:
        nm = name.strip()
        if nm in _RENDER_AVATAR_BY_NAME:
            return f"../avatar/{_RENDER_AVATAR_BY_NAME[nm]}"
    # 4. 索引未建时的兜底（被直接调用而非通过 cmd_render_html）
    if not _RENDER_AVATAR_BY_PID and os.path.isdir(AVATAR_DIR):
        for fname in os.listdir(AVATAR_DIR):
            m = _AVATAR_FNAME_PID_RE.match(fname)
            if m and m.group(1) in try_ids:
                return f"../avatar/{fname}"
    return ""


def _find_local_image_for_url(url: str) -> str:
    """按 basename 在本地 image/ 找文件，返回 ../image/{filename}（找不到返回空）。"""
    if not url or not os.path.isdir(IMAGE_DIR):
        return ""
    basename = extract_image_basename(url)
    if not basename:
        return ""
    fnames = sorted(
        os.listdir(IMAGE_DIR),
        key=lambda f: (0 if "_pbs_twimg_com_" in f else 1, f),
    )
    for fname in fnames:
        if extract_image_basename(fname) == basename:
            return f"../image/{fname}"
    return ""


def _find_local_video_for_url(url: str) -> str:
    """按 media_key 在本地 video/ 找文件，返回 ../video/{filename}（找不到返回空）。"""
    if not url or not os.path.isdir(VIDEO_DIR):
        return ""
    key = extract_video_media_key(url)
    if not key:
        return ""
    fnames = sorted(
        os.listdir(VIDEO_DIR),
        key=lambda f: (0 if "_video_twimg_com_" in f else 1, f),
    )
    for fname in fnames:
        if extract_video_media_key(fname) == key:
            return f"../video/{fname}"
    return ""


def _select_video_url_from_media(m: dict) -> str:
    """从一个 video / animated_gif media 选最高码率 mp4 URL。"""
    best_url = ""
    best_br = -1
    for v in m.get("variants", []) or []:
        if v.get("content_type") != "video/mp4":
            continue
        br = v.get("bit_rate", 0) or 0
        if br >= best_br:
            best_br = br
            best_url = v.get("url", "")
    return best_url


# ── HTML 片段渲染 ─────────────────────────────────────────────

def _render_author_block(user: dict) -> str:
    """
    渲染 tweet-author 块。
    src 选择策略（按 TauCeti 成品 / 原版 render_html_json.py 约定）：
      1. 先按 user.id 在本地找头像（TauCeti 模式：avatar_{user_id}.{ext}）
      2. 再按 profile_pid 找（AnIncandescence 模式：avatar_{profile_pid}.{ext}）
      3. 再按 username / name 反射
      4. 都找不到时：用 user.id 写预期路径 ../avatar/avatar_{uid}.{ext}（**不留空**，
         这样 build-index 提取的 author_avatar 始终非空，本地补全后 Reader 自动可见）
    """
    name = html_module.escape((user.get("name") or "").strip())
    username = (user.get("username") or "").strip().lstrip("@")
    uid = str(user.get("id") or "")
    purl = user.get("profile_image_url") or ""
    profile_pid = extract_profile_image_id(purl)

    avatar_src = _find_local_avatar_path(
        try_ids=[uid, profile_pid],
        name=(user.get("name") or "").strip(),
        username=username,
    )
    if not avatar_src and uid:
        # 本地暂未下载 — 用 user.id 写预期路径
        ext = ext_from_url(purl) if purl else ".jpg"
        avatar_src = f"../avatar/avatar_{uid}{ext}"
    if not avatar_src:
        avatar_src = html_module.escape(purl)

    return (
        '  <div class="tweet-author">\n'
        '  <div class="tweet-author-profile-image">\n'
        f'  <img alt="{name}" src="{avatar_src}"/>\n'
        '  </div>\n'
        '  <div class="tweet-author-info">\n'
        '  <div class="tweet-author-name">\n'
        f'  {name}\n'
        '  </div>\n'
        '  <div class="tweet-author-username">\n'
        f'  @{html_module.escape(username)}\n'
        '  </div>\n'
        '  </div>\n'
        '  </div>'
    )


def _render_media_html(media_keys: list, media_by_key: dict) -> str:
    """根据 media_keys 渲染 <img class="tweet-image"> / <video class="tweet-video">。"""
    parts: list[str] = []
    for k in media_keys or []:
        m = media_by_key.get(k)
        if not m:
            continue
        mtype = m.get("type", "")
        if mtype == "photo":
            url = m.get("url") or m.get("preview_image_url") or ""
            local = _find_local_image_for_url(url)
            src = local if local else html_module.escape(url)
            if src:
                parts.append(f'  <img class="tweet-image" src="{src}"/>')
        elif mtype in ("video", "animated_gif"):
            best = _select_video_url_from_media(m)
            local = _find_local_video_for_url(best)
            src = local if local else html_module.escape(best)
            if src:
                # 跟成品格式一致：<video class="tweet-video" controls="" src="..."></video>
                parts.append(f'  <video class="tweet-video" controls="" src="{src}">\n  </video>')
    return "\n".join(parts)


def _render_embedded_block(ref_tweet: dict, users_by_id: dict,
                           media_by_key: dict, own_username: str) -> str:
    """
    渲染 embedded-tweet-container（嵌套被引用推文）。
    own_username：本推文作者的 @username（用于在 href 里区分 self quote）。
    被引用推文的作者信息从 users_by_id 查；找不到则降级为 ref_tweet 内嵌的字段。
    """
    author_id = str(ref_tweet.get("author_id") or "")
    author = users_by_id.get(author_id, {}) or {
        "name": "",
        "username": ref_tweet.get("author_username") or "",
        "profile_image_url": "",
    }
    ref_text = (ref_tweet.get("text") or "").strip()
    ref_text_html = html_module.escape(ref_text)
    ref_tid = str(ref_tweet.get("id") or "")
    ref_username = (author.get("username") or "").lstrip("@")
    ref_created = ref_tweet.get("created_at") or ""

    # embedded 内部 media（如果本 ref_tweet 自带 attachments.media_keys）
    ref_mk = (ref_tweet.get("attachments") or {}).get("media_keys") or []
    media_html = _render_media_html(ref_mk, media_by_key)

    # date 块：成品里链接到原推文页（哪怕本地访问不到，结构必须保留）
    href = f"https://twitter.com/{ref_username}/status/{ref_tid}" if ref_tid and ref_username else "/"
    date_block = (
        '  <p class="date">\n'
        f'  <a href="{html_module.escape(href)}" id="qt{ref_tid}">\n'
        '  </a>\n'
        '  </p>'
    )

    # embedded 内部 script（设这个 qt{tid} 的时间）
    script_block = ""
    if ref_created and ref_tid:
        script_block = (
            '  <script>\n'
            f'  var dateString = "{ref_created}";\n'
            '\t\t\t\tvar date = new Date(dateString);\n'
            f'\t\t\t\tdocument.getElementById("qt{ref_tid}").innerText = date;\n'
            '  </script>'
        )

    # 拼装：author + content (text + 可选media) + date + 可选script
    inner_pieces = [
        '  <div class="embedded-tweet-container">',
        _render_author_block(author),
        '  <div class="tweet-content">',
        f'  {ref_text_html}',
    ]
    if media_html:
        inner_pieces.append(media_html)
    inner_pieces.append(date_block)
    if script_block:
        inner_pieces.append(script_block)
    inner_pieces.append('  </div>')   # 闭 tweet-content
    inner_pieces.append('  </div>')   # 闭 embedded-tweet-container
    return "\n".join(inner_pieces)


def _render_one_html(td: dict, includes: dict, own_username_hint: str = "") -> str:
    """
    渲染一条推文的完整 HTML。td = data 节点；includes 含 users/tweets/media。
    """
    users_by_id = {str(u.get("id") or ""): u for u in includes.get("users", []) or []}
    media_by_key = {m.get("media_key", ""): m for m in includes.get("media", []) or []}
    extra_tweets = {str(t.get("id") or ""): t for t in includes.get("tweets", []) or []}

    author_id = str(td.get("author_id") or "")
    author = users_by_id.get(author_id, {})
    own_username = (author.get("username") or own_username_hint).lstrip("@")

    # 主推文正文
    text = (td.get("text") or "").strip()
    text_html = html_module.escape(text)

    # 主推文媒体（仅本推文的 media_keys）
    own_mk = (td.get("attachments") or {}).get("media_keys") or []
    main_media_html = _render_media_html(own_mk, media_by_key)

    # 嵌入的被引用 / 被回复推文（从 includes.tweets 找）
    ref_blocks: list[str] = []
    for ref in td.get("referenced_tweets", []) or []:
        rid = str(ref.get("id") or "")
        rtype = ref.get("type") or ""
        if not rid:
            continue
        rt = extra_tweets.get(rid)
        if rt:
            ref_blocks.append(_render_embedded_block(rt, users_by_id, media_by_key, own_username))

    # 拼装 tweet-content 区域
    pieces = [f"  {text_html}", "  <!-- If there's a quoted tweet, embed it here!-->"]
    if ref_blocks:
        pieces.append("\n".join(ref_blocks))
    if main_media_html:
        pieces.append(main_media_html)
    pieces.append('  <p class="date">\n  <a href="/" id="parentdate">\n  </a>\n  </p>')

    content_block = (
        '  <div class="tweet-content">\n'
        + "\n".join(pieces) + "\n"
        + "  </div>"
    )

    # 主推文末尾 script（设 #parentdate 时间 + currentURL）
    created = td.get("created_at") or ""
    main_script = (
        '<script>\n'
        f'var dateString = "{created}";\n'
        'var date = new Date(dateString);\n'
        'var currentURL = window.location.href;\n'
        'document.querySelector("#parentdate").innerText = date;\n'
        'document.querySelector("#parentdate").href = currentURL;\n'
        '</script>'
    )

    # Source 注释（render-html 用 x_api:// 协议，明示这是从 API JSON 渲染的，不是 wayback）
    tid = str(td.get("id") or "")
    source_comment = f"<!-- Source: x_api://{own_username}/status/{tid} -->\n" if tid else ""

    return (
        source_comment
        + _WAYBACK_HEAD
        + '<body>\n'
        + '<div class="tweet-container on">\n'
        + '<div id="nonjsonview">\n'
        + _render_author_block(author) + "\n"
        + content_block + "\n"
        + '</div>\n'
        + '</div>\n'
        + main_script + "\n"
        + '</body>\n'
        + '</html>\n'
    )


def cmd_render_html(args: argparse.Namespace) -> int:
    """从 json/ 渲染 wayback 风格的 HTML（私密账号场景）。"""
    ensure_output_dirs()
    if not os.path.isdir(JSON_DIR):
        safe_print(f"[render-html] JSON 目录不存在：{JSON_DIR}")
        return 1

    # 建立 username/name → 本地头像 反射索引（一次性，所有 HTML 渲染共用）
    _build_render_avatar_indexes()
    safe_print(
        f"[render-html] 头像反射索引："
        f"{len(_RENDER_AVATAR_BY_PID)} 个 pid / "
        f"{len(_RENDER_AVATAR_BY_USERNAME)} 个 username / "
        f"{len(_RENDER_AVATAR_BY_NAME)} 个 name"
    )

    force = bool(args.force)
    json_files = sorted(f for f in os.listdir(JSON_DIR) if f.endswith(".json"))
    safe_print(f"[render-html] 扫到 {len(json_files)} 个 JSON")

    rendered = 0
    skipped = 0
    failed = 0

    for jname in json_files:
        html_name = jname[:-5] + ".html"
        html_path = os.path.join(HTML_DIR, html_name)
        if os.path.exists(html_path) and not force:
            skipped += 1
            continue
        try:
            with open(os.path.join(JSON_DIR, jname), encoding="utf-8") as f:
                data = json.load(f)
        except Exception as e:
            safe_print(f"  ✗ {jname}  JSON 解析失败：{e}")
            failed += 1
            continue

        td = data.get("data") or {}
        includes = data.get("includes") or {}

        # 从文件名兜底获取用户名（safe_filename 化的 URL 里能解出来）
        un_hint = ""
        mm = re.match(r"^\d{14}_twitter_com_(.+)_status_\d+\.json$", jname)
        if mm:
            un_hint = mm.group(1)

        try:
            content = _render_one_html(td, includes, un_hint)
        except Exception as e:
            safe_print(f"  ✗ {jname}  渲染失败：{type(e).__name__}: {e}")
            failed += 1
            continue

        try:
            with open(html_path, "w", encoding="utf-8") as f:
                f.write(content)
            rendered += 1
        except Exception as e:
            safe_print(f"  ✗ {jname}  HTML 写入失败：{e}")
            failed += 1

    safe_print(f"[render-html] 完成：渲染 {rendered} / 跳过 {skipped} / 失败 {failed}")
    return 0 if not failed else 1


# ============================================================================
# ── 子命令: all ─────────────────────────────────────────────────────────────
# ============================================================================
#
# 按顺序跑 fetch-html → fetch-media → clean-html → build-index。
# 任何一步失败都继续往下走（保留失败列表供 --retry 用），但最终返回非零退出码。
# ============================================================================

def cmd_all(args: argparse.Namespace) -> int:
    overall = 0

    safe_print("\n╔══════════════════════════════════════════════════════════╗")
    safe_print("║  Phase 1/4: fetch-html                                   ║")
    safe_print("╚══════════════════════════════════════════════════════════╝")
    a1 = argparse.Namespace(
        retry=False, force=False, file=None,
        workers=DEFAULT_WORKERS_HTML, delay=DEFAULT_DELAY_HTML,
    )
    overall |= cmd_fetch_html(a1)

    safe_print("\n╔══════════════════════════════════════════════════════════╗")
    safe_print("║  Phase 2/4: fetch-media                                  ║")
    safe_print("╚══════════════════════════════════════════════════════════╝")
    a2 = argparse.Namespace(
        retry=False, force=False, file=None,
        workers=DEFAULT_WORKERS_MEDIA, delay=DEFAULT_DELAY_MEDIA,
    )
    overall |= cmd_fetch_media(a2)

    safe_print("\n╔══════════════════════════════════════════════════════════╗")
    safe_print("║  Phase 3/4: clean-html                                   ║")
    safe_print("╚══════════════════════════════════════════════════════════╝")
    a3 = argparse.Namespace(force=False)
    overall |= cmd_clean_html(a3)

    safe_print("\n╔══════════════════════════════════════════════════════════╗")
    safe_print("║  Phase 4/4: build-index                                  ║")
    safe_print("╚══════════════════════════════════════════════════════════╝")
    a4 = argparse.Namespace()
    overall |= cmd_build_index(a4)

    safe_print("\n[all] 全部阶段完成")
    return overall


# ============================================================================
# ── argparse 入口 ───────────────────────────────────────────────────────────
# ============================================================================

def _add_retry_args(p: argparse.ArgumentParser, default_failed_file: str) -> None:
    p.add_argument("--retry", action="store_true",
                   help=f"只跑失败清单里的（默认读 {default_failed_file}）")
    p.add_argument("--file", default=None, metavar="PATH",
                   help="自定义失败清单路径（与 --retry 搭配）")
    p.add_argument("--force", action="store_true",
                   help="忽略 _done_list 与本地已存在文件，全部重做")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="archive.py",
        description="IncandescenceReader 一体化存档工具",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
命令分组：

公开账号工作流（从 Wayback 抓数据）：
  fetch-cdx <user>        拉取 CDX 数据
  fetch-html              下载 wayback HTML
  fetch-media             下载图片/视频/头像
  fetch-avatars           补缺头像
  clean-html              清洗 HTML 重写媒体路径
  build-index             生成 Reader 用的 index.json
  all                     fetch-html → fetch-media → clean-html → build-index

私密账号工作流（从外部 dump 转换）：
  convert <dump_dir>      把外部 dump 转成本项目格式（自动建立 archive_index）
  render-html             从 JSON 渲染 wayback 风格 HTML

重试失败项（10 个子选项）：
  retry --image-failed [/--image-failed-all]      单图重试
  retry --video-failed [/--video-failed-all]      单视频重试
  retry --avatar-failed [/--avatar-failed-all]    单头像重试
  retry --media-failed [/--media-failed-all]      整条 JSON 媒体重试
  retry --html-failed [/--html-failed-all]        HTML 重试

维护工具：
  dedup                   去重重复媒体 + 更新 HTML 引用
  gen-lists               生成 _url_list.txt / _list_media.txt
  rebuild-index           重建 _log/archive_index.json（从 .txt 文件 + 本地媒体）

状态文件统一存放在 wayback_snapshots/_log/ 目录下。
""",
    )
    sub = parser.add_subparsers(dest="command", required=True, metavar="<command>")

    # fetch-html
    p = sub.add_parser("fetch-html", help="下载 wayback HTML + 抽取 JSON")
    _add_retry_args(p, FAILED_HTML)
    p.add_argument("--workers", type=int, default=DEFAULT_WORKERS_HTML)
    p.add_argument("--delay",   type=float, default=DEFAULT_DELAY_HTML)
    p.set_defaults(func=cmd_fetch_html)

    # fetch-media
    p = sub.add_parser("fetch-media", help="下载所有 JSON 里引用的媒体")
    _add_retry_args(p, FAILED_MEDIA)
    p.add_argument("--workers", type=int, default=DEFAULT_WORKERS_MEDIA)
    p.add_argument("--delay",   type=float, default=DEFAULT_DELAY_MEDIA)
    p.set_defaults(func=cmd_fetch_media)

    # fetch-image
    p = sub.add_parser("fetch-image", help="只下载图片")
    p.add_argument("--workers", type=int, default=DEFAULT_WORKERS_MEDIA)
    p.add_argument("--delay",   type=float, default=DEFAULT_DELAY_MEDIA)
    p.add_argument("--force",   action="store_true")
    p.set_defaults(func=cmd_fetch_image, retry=False, file=None)

    # fetch-video
    p = sub.add_parser("fetch-video", help="只下载视频")
    p.add_argument("--workers", type=int, default=DEFAULT_WORKERS_MEDIA)
    p.add_argument("--delay",   type=float, default=DEFAULT_DELAY_MEDIA)
    p.add_argument("--force",   action="store_true")
    p.set_defaults(func=cmd_fetch_video, retry=False, file=None)

    # fetch-avatars
    p = sub.add_parser("fetch-avatars", help="单独重下头像（修复用）")
    _add_retry_args(p, FAILED_AVATAR)
    p.add_argument("--workers", type=int, default=DEFAULT_WORKERS_AVATAR)
    p.set_defaults(func=cmd_fetch_avatars)

    # clean-html
    p = sub.add_parser("clean-html", help="清洗 HTML，重写媒体路径为本地引用")
    p.add_argument("--force", action="store_true", help="忽略已清洗标记，全部重新清洗")
    p.set_defaults(func=cmd_clean_html)

    # build-index
    p = sub.add_parser("build-index", help="生成 index.json（profile.json 由用户手动维护）")
    p.set_defaults(func=cmd_build_index)

    # dedup
    p = sub.add_parser("dedup", help="媒体去重 + 孤儿清理（默认 dry-run）")
    p.add_argument("--execute", action="store_true",
                   help="实际执行删除（默认只分析报告）")
    p.add_argument("--backup",  action="store_true",
                   help="删除前备份到 _dedup_backup_*/")
    p.add_argument("--delete-orphans", action="store_true",
                   help="同时删除没被 HTML 引用的孤儿文件")
    p.set_defaults(func=cmd_dedup)

    # gen-lists
    p = sub.add_parser("gen-lists", help="生成 _url_list.txt / _list_media.txt")
    p.set_defaults(func=cmd_gen_lists)

    # fetch-cdx
    p = sub.add_parser("fetch-cdx", help="调用 Wayback CDX API 抓取账号的快照清单 → cdx_data.json")
    p.add_argument("username", help="Twitter 用户名（不带 @）")
    p.add_argument("--from", dest="from_ts", default="",
                   help="起始时间戳 YYYYMMDDhhmmss（可选）")
    p.add_argument("--to", dest="to_ts", default="",
                   help="结束时间戳 YYYYMMDDhhmmss（可选）")
    p.add_argument("--collapse-digest", action="store_true",
                   help="按 digest 去重（同内容多版本只保留一条，更精简）")
    p.add_argument("--force", action="store_true",
                   help="覆盖现有 cdx_data.json 时不备份")
    p.set_defaults(func=cmd_fetch_cdx)

    # convert
    p = sub.add_parser("convert", help="把外部 dump 转换为本项目格式（私密账号）")
    p.add_argument("dump_dir", help="dump 根目录（含 snapshots.json 或子目录里有）")
    p.add_argument("--include-unreferenced", action="store_true",
                   help="同时复制未在任何 JSON 里引用的孤立媒体（默认跳过，行为更贴合成品）")
    p.set_defaults(func=cmd_convert)

    # render-html
    p = sub.add_parser("render-html", help="从 JSON 渲染伪 wayback HTML（私密账号）")
    p.add_argument("--force", action="store_true", help="覆盖已存在的 html")
    p.set_defaults(func=cmd_render_html)

    # all
    p = sub.add_parser("all", help="一把梭：fetch-html → fetch-media → clean-html → build-index")
    p.set_defaults(func=cmd_all)

    # retry  ★ 新子命令：12 个子选项
    p = sub.add_parser("retry", help="重试失败项（共 12 个子选项 --xxx-failed[-all]）")
    g = p.add_argument_group("重试目标（互斥，只能选一个）")
    g.add_argument("--image-failed",      action="store_true", dest="image_failed",
                   help="重试 _log/image_failed.txt 里的图片 URL（可救失败）")
    g.add_argument("--image-failed-all",  action="store_true", dest="image_failed_all",
                   help="重试 _log/image_failed_all.txt 里的图片 URL（含永久失败）")
    g.add_argument("--video-failed",      action="store_true", dest="video_failed",
                   help="重试 _log/video_failed.txt")
    g.add_argument("--video-failed-all",  action="store_true", dest="video_failed_all",
                   help="重试 _log/video_failed_all.txt")
    g.add_argument("--avatar-failed",     action="store_true", dest="avatar_failed",
                   help="重试 _log/avatar_failed.txt")
    g.add_argument("--avatar-failed-all", action="store_true", dest="avatar_failed_all",
                   help="重试 _log/avatar_failed_all.txt")
    g.add_argument("--media-failed",      action="store_true", dest="media_failed",
                   help="重试 _log/media_failed.txt（整条 JSON）")
    g.add_argument("--media-failed-all",  action="store_true", dest="media_failed_all",
                   help="重试 _log/media_failed_all.txt（整条 JSON，含永久失败）")
    g.add_argument("--html-failed",       action="store_true", dest="html_failed",
                   help="重试 _log/html_failed.txt")
    g.add_argument("--html-failed-all",   action="store_true", dest="html_failed_all",
                   help="重试 _log/html_failed_all.txt")
    p.set_defaults(func=cmd_retry)

    # rebuild-index  ★ 新子命令：从 .txt 文件 + 本地媒体重建 archive_index.json
    p = sub.add_parser("rebuild-index",
                       help="重建 _log/archive_index.json（迁移 / 损坏修复用）")
    p.set_defaults(func=cmd_rebuild_index)

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        return args.func(args)
    except KeyboardInterrupt:
        safe_print("\n[中断] 用户取消")
        return 130


if __name__ == "__main__":
    sys.exit(main())
