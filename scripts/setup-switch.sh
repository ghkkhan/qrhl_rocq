#!/usr/bin/env bash
# Create a dedicated opam switch for this project.
#
# Phases 0-3 need only rocq-prover + rocq-stdlib. Phase 4 (models/FinDim.v)
# additionally needs mathcomp; pass --with-mathcomp for that.
set -euo pipefail

SWITCH=qrhl
WITH_MATHCOMP=0
[ "${1:-}" = "--with-mathcomp" ] && WITH_MATHCOMP=1

opam switch create "$SWITCH" ocaml-base-compiler.5.1.1 || true
eval "$(opam env --switch=$SWITCH)"
opam repo add rocq-released https://rocq-prover.org/opam/released || true
opam install -y rocq-prover.9.1.0 rocq-stdlib vsrocq-language-server

if [ "$WITH_MATHCOMP" = 1 ]; then
  opam install -y rocq-mathcomp-algebra.2.6.0 rocq-mathcomp-analysis.1.18.0
fi

echo
echo "Done. Activate with:  eval \$(opam env --switch=$SWITCH)"
