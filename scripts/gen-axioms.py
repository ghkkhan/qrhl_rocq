#!/usr/bin/env python3
"""Regenerate the inventory section of AXIOMS.md from Interface.v.

The trusted surface must be reviewable, and a hand-maintained list would drift
from the signature within a week. So the prose part of AXIOMS.md is written by
hand and the inventory is generated from the source by this script.
"""
import re, sys, pathlib

SRC = pathlib.Path("theories/Substrate/Interface.v")
OUT = pathlib.Path("AXIOMS.md")
MARK = "<!-- BEGIN GENERATED INVENTORY -->"
ENDM = "<!-- END GENERATED INVENTORY -->"

text = SRC.read_text(encoding="utf-8")

# Section headers written as (** ** Title *) inside the Module Type.
# Declarations are Parameter/Axiom at two-space indentation.
lines = text.splitlines()
section = "(ungrouped)"
groups: dict[str, list[tuple[str, str]]] = {}
i = 0
while i < len(lines):
    line = lines[i]
    m = re.match(r"\s*\(\*\* \*\* (.+?)\s*\*?\)?\s*$", line)
    if m:
        section = m.group(1).strip().rstrip("*").strip()
        groups.setdefault(section, [])
        i += 1
        continue
    m = re.match(r"^  (Parameter|Axiom)\s+([A-Za-z_][A-Za-z0-9_']*)\s*:", line)
    if m:
        kind, name = m.group(1), m.group(2)
        body = [line.split(":", 1)[1].strip()]
        while not body[-1].rstrip().endswith("."):
            i += 1
            if i >= len(lines):
                break
            body.append(lines[i].strip())
        stmt = " ".join(x for x in body if x).rstrip(".")
        stmt = re.sub(r"\s+", " ", stmt)
        groups.setdefault(section, []).append((kind, name, stmt))
    i += 1

rows = [MARK, ""]
n_par = n_ax = 0
for sec, decls in groups.items():
    if not decls:
        continue
    rows.append(f"### {sec}")
    rows.append("")
    rows.append("| kind | name | statement |")
    rows.append("|---|---|---|")
    for kind, name, stmt in decls:
        if kind == "Parameter":
            n_par += 1
        else:
            n_ax += 1
        esc = stmt.replace("|", r"\|")
        rows.append(f"| {kind} | `{name}` | `{esc}` |")
    rows.append("")
rows.append(f"**Totals: {n_par} parameters, {n_ax} axioms.**")
rows.append("")
rows.append(ENDM)
inventory = "\n".join(rows)

if OUT.exists():
    doc = OUT.read_text(encoding="utf-8")
    if MARK in doc and ENDM in doc:
        head = doc.split(MARK)[0]
        tail = doc.split(ENDM)[1]
        OUT.write_text(head + inventory + tail, encoding="utf-8")
    else:
        OUT.write_text(doc.rstrip() + "\n\n" + inventory + "\n", encoding="utf-8")
else:
    OUT.write_text(inventory + "\n", encoding="utf-8")
print(f"AXIOMS.md: {n_par} parameters, {n_ax} axioms across {len(groups)} sections")
