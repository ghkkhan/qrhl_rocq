#!/usr/bin/env python3
"""Strip Rocq (* ... *) comments (nesting-aware), preserving line numbers.

Used by the audit so that hygiene checks apply to declarations rather than to
prose: a comment may legitimately *explain* the qRHL context of a substrate
file, but no declaration in it may depend on qRHL notions.
"""
import sys

def strip(src: str) -> str:
    out, depth, i, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("(*", i):
            depth += 1; i += 2; continue
        if src.startswith("*)", i) and depth:
            depth -= 1; i += 2; continue
        ch = src[i]
        out.append(ch if (depth == 0 or ch == "\n") else " ")
        i += 1
    return "".join(out)

for path in sys.argv[1:]:
    with open(path, encoding="utf-8") as fh:
        for num, line in enumerate(strip(fh.read()).splitlines(), 1):
            if line.strip():
                print(f"{path}:{num}:{line}")
