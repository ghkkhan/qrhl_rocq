#!/usr/bin/env bash
# Audit the development's trusted surface. Three invariants:
#
#   1. Nothing is admitted, anywhere.
#   2. No free-standing Axiom / Conjecture / Hypothesis outside the substrate
#      signature. Assumptions belong in Module Type HILBERT_SUBSTRATE, where
#      they are structurally visible in the functor signature rather than
#      being global axioms.
#      Note: a `Hypothesis` inside a Section is discharged and so is harmless,
#      but telling that from a `Hypothesis` at top level (which Rocq treats as
#      an axiom) is not reliable textually. Sections should use `Context`,
#      which is the same thing and keeps this check strict.
#   3. Substrate hygiene: no *declaration* under theories/Substrate/ may
#      mention qRHL vocabulary. This is the architectural bet of the project --
#      the substrate assumes textbook functional analysis and nothing about
#      qRHL -- and it is the one thing worth checking mechanically.
#
# Checks run against comment-stripped .v sources, so prose is free to explain
# itself. Exit non-zero on any violation.

set -uo pipefail
cd "$(dirname "$0")/.."
fail=0
note() { printf '%s\n' "$*" | sed 's/^/    /'; }

VFILES=$(find theories models -name '*.v' 2>/dev/null | sort)
if [ -z "$VFILES" ]; then echo "no .v files found"; exit 0; fi

# shellcheck disable=SC2086
STRIPPED=$(python3 scripts/strip_comments.py $VFILES)

echo "== audit 1/3: no admitted proofs =="
hits=$(printf '%s\n' "$STRIPPED" | grep -E ':[0-9]+:.*(\bAdmitted\b|\badmit\b|\bgive_up\b)')
if [ -n "$hits" ]; then echo "FAIL"; note "$hits"; fail=1; else echo "ok"; fi

echo "== audit 2/3: no axioms outside the substrate signature =="
hits=$(printf '%s\n' "$STRIPPED" \
        | grep -E ':[0-9]+:\s*(Axiom|Conjecture|Hypothesis)\b' \
        | grep -vE '^theories/Substrate/(Interface|Registers)\.v:')
if [ -n "$hits" ]; then echo "FAIL"; note "$hits"; fail=1; else echo "ok"; fi

echo "== audit 3/3: substrate hygiene =="
# qRHL-specific vocabulary. Deliberately narrow: these are names that could
# only appear in a substrate file if the abstraction had leaked.
banned='\bqrhl|\bCla\b|equant|\bqeq\b|\bidx1\b|\bidx2\b|\bprecond|\bpostcond|\bdenote\b|\bjudgment\b'
hits=$(printf '%s\n' "$STRIPPED" | grep -E "^theories/Substrate/" | grep -E "$banned")
if [ -n "$hits" ]; then echo "FAIL"; note "$hits"; fail=1; else echo "ok"; fi

echo
if [ "$fail" -eq 0 ]; then echo "AUDIT PASSED"; else echo "AUDIT FAILED"; fi
exit $fail
