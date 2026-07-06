#!/usr/bin/env python3
"""Prefetch upstream source files for ``source_context=full`` evaluation.

For each benchmark, download ONLY the file(s) named in ``manifest.source.path``
at the pinned ``manifest.source.commit_hash``, from the manifest's
``repo_url`` — via ``raw.githubusercontent.com`` (no clone; just the relevant
files). Write them under ``benchmarks/<repo>/upstream_source/`` (gitignored, so
upstream source is NEVER committed into our benchmark) preserving the upstream
relative path, plus a ``PROVENANCE.txt`` recording url@sha + paths.

Run ONCE before a full-context eval so evals read from disk — no network on the
eval critical path. Idempotent: re-running refreshes the cache.

Usage:
    python scripts/prefetch_upstream.py                 # all repos
    python scripts/prefetch_upstream.py pyradix rsa     # specific repos
    python scripts/prefetch_upstream.py --check         # report only, no fetch
"""

from __future__ import annotations

import json
import sys
import urllib.error
import urllib.request
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
BENCH = REPO_ROOT / "benchmarks"
ALL_REPOS = sorted(p.name for p in BENCH.iterdir() if (p / "manifest.json").is_file())


def _raw_url(repo_url: str, sha: str, path: str) -> str:
    # repo_url like https://github.com/<owner>/<repo>
    owner_repo = repo_url.rstrip("/").removeprefix("https://github.com/")
    return f"https://raw.githubusercontent.com/{owner_repo}/{sha}/{path.lstrip('/')}"


def _paths(src: dict) -> list[str]:
    p = src.get("path")
    if p is None:
        return []
    return p if isinstance(p, list) else [p]


def _fetch(url: str, timeout: int = 60) -> bytes:
    req = urllib.request.Request(url, headers={"User-Agent": "vero-prefetch"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


def prefetch_repo(repo: str, *, check_only: bool = False) -> dict:
    mpath = BENCH / repo / "manifest.json"
    src = json.loads(mpath.read_text()).get("source", {})
    repo_url, sha, paths = src.get("repo_url"), src.get("commit_hash"), _paths(src)
    result = {
        "repo": repo,
        "url": repo_url,
        "sha": sha,
        "paths": paths,
        "fetched": [],
        "errors": [],
    }
    if not (repo_url and sha):
        result["errors"].append("missing repo_url or commit_hash")
        return result
    if not paths:
        result["errors"].append("no source.path set (backfill needed)")
        return result

    dst_root = BENCH / repo / "upstream_source"
    if check_only:
        for p in paths:
            url = _raw_url(repo_url, sha, p)
            try:
                _fetch(url, timeout=30)
                result["fetched"].append(p)
            except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError) as e:
                result["errors"].append(f"{p}: {e}")
        return result

    dst_root.mkdir(parents=True, exist_ok=True)
    prov = [
        f"# upstream source for {repo} (source_context=full) — DO NOT COMMIT",
        f"repo_url: {repo_url}",
        f"commit_hash: {sha}",
        "files:",
    ]
    for p in paths:
        url = _raw_url(repo_url, sha, p)
        try:
            data = _fetch(url)
        except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError) as e:
            result["errors"].append(f"{p}: {e}")
            continue
        if not data.strip():
            result["errors"].append(f"{p}: empty")
            continue
        out = dst_root / p
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_bytes(data)
        result["fetched"].append(p)
        prov.append(f"  {p}  ({len(data)} bytes)  {url}")
    (dst_root / "PROVENANCE.txt").write_text("\n".join(prov) + "\n", encoding="utf-8")
    return result


def main(argv: list[str]) -> int:
    check_only = "--check" in argv
    repos = [a for a in argv if not a.startswith("--")] or ALL_REPOS
    ok = 0
    fail = []
    for repo in repos:
        r = prefetch_repo(repo, check_only=check_only)
        status = (
            "OK"
            if (r["fetched"] and not r["errors"])
            else ("PARTIAL" if r["fetched"] else "FAIL")
        )
        if status == "OK":
            ok += 1
        else:
            fail.append(repo)
        print(f"  {repo:20} {status:8} fetched={r['fetched']} errors={r['errors']}")
    print(f"\n{ok}/{len(repos)} OK" + (f" — needs attention: {fail}" if fail else ""))
    return 0 if not fail else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
