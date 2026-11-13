#!/usr/bin/env python3
"""Fail when a public page uses a status phrase with no evidence behind it."""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DENY = [
    ("hundred-z3", re.compile(r"100%\s*z3", re.I)),
    ("hundred-verified", re.compile(r"100%\s*verified", re.I)),
    ("governance-solved", re.compile(r"governance solved", re.I)),
    ("zero-divergence", re.compile(r"zero divergence", re.I)),
    ("six-x", re.compile(r"6x harder|harder to capture", re.I)),
    ("nearly-two-years", re.compile(r"nearly two years", re.I)),
]
EXTS = {".md", ".html", ".txt", ".svg", ".js", ".yml", ".json"}
SKIP_DIRS = {".git", "node_modules", "target", "_site", "_next", "out", "modules"}
SKIP_FILES = {"scripts/check-public-claims.py", "CLAIMS.md"}

hits = []
for dirpath, dirnames, filenames in os.walk(ROOT):
    dirnames[:] = [name for name in dirnames if name not in SKIP_DIRS]
    for name in filenames:
        if os.path.splitext(name)[1] not in EXTS:
            continue
        path = os.path.join(dirpath, name)
        rel = os.path.relpath(path, ROOT)
        if rel in SKIP_FILES:
            continue
        try:
            lines = open(path, encoding="utf-8", errors="replace").read().splitlines()
        except OSError:
            continue
        for number, line in enumerate(lines, 1):
            for phrase_id, pattern in DENY:
                if pattern.search(line):
                    hits.append(f"{rel}:{number} {phrase_id}")
if hits:
    print("public claims: denied phrase", file=sys.stderr)
    print("\n".join(hits), file=sys.stderr)
    sys.exit(1)
print("check-public-claims: ok")
