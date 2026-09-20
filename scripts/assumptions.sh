#!/usr/bin/env bash
# Report the logical assumptions the concrete layer rests on.
#
# The substrate is a Module Type and everything above it is a functor, so those
# files declare no axioms and `Print Assumptions` cannot be run on them without
# an instance. What *can* be audited is the concrete layer -- Ambient, Cnum and
# Sums -- which is ordinary mathematics and must rest on nothing beyond the
# ambient logic that AXIOMS.md declares: classical higher-order logic with
# choice and extensionality, plus the reals.
#
# Any drift from scripts/assumptions.expected is a failure: it means a new
# assumption crept into the part of the development that is supposed to have
# none of its own.
set -uo pipefail
cd "$(dirname "$0")/.."

# Rocq derives a module name from the file name, so it must be a valid
# identifier: no dashes, hence no mktemp template.
PROBEDIR=$(mktemp -d)
PROBE="$PROBEDIR/qrhl_assumption_probe.v"
trap 'rm -rf "$PROBEDIR"' EXIT

cat > "$PROBE" <<'EOF'
From QRHL.Substrate Require Import Ambient Cnum Sums.
Print Assumptions tsum_tonelli.
Print Assumptions tsum_partition_le.
Print Assumptions tsum_add.
Print Assumptions tsum_scale.
Print Assumptions C_field_theory.
EOF

OUT=$(rocq compile -R theories QRHL "$PROBE" 2>&1 \
       | grep -oE '^[A-Za-z_][A-Za-z0-9_.]* :' | sed 's/ :$//' | sort -u)

if [ ! -f scripts/assumptions.expected ]; then
  printf '%s\n' "$OUT" > scripts/assumptions.expected
  echo "recorded scripts/assumptions.expected:"; printf '%s\n' "$OUT"
  exit 0
fi

if diff -u scripts/assumptions.expected <(printf '%s\n' "$OUT"); then
  echo "assumptions unchanged:"; printf '%s\n' "$OUT" | sed 's/^/  /'
else
  echo "FAIL: the concrete layer's assumptions drifted from the expected set."
  exit 1
fi
