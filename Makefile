# qRHL in Rocq -- top-level Makefile.
#
# Requires `rocq` (>= 9.1) on PATH and nothing else: the development depends on
# the Rocq standard library only. See scripts/setup-switch.sh for a dedicated
# opam switch; Phase 4 (models/) additionally needs mathcomp.

COQMAKEFILE := Makefile.coq

.PHONY: all build audit examples clean distclean assumptions axioms

all: build

$(COQMAKEFILE): _CoqProject
	rocq makefile -f _CoqProject -o $(COQMAKEFILE)

build: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)

# Trusted-surface audit: no admits, no stray axioms, substrate hygiene.
audit:
	@scripts/audit.sh

# Regenerate the trusted-surface inventory in AXIOMS.md from Interface.v.
axioms:
	@python3 scripts/gen-axioms.py

# Print Assumptions on every soundness theorem; the expected output is checked
# in at scripts/assumptions.expected and any drift is a failure.
assumptions: build
	@scripts/assumptions.sh

examples: build
	@echo "examples are part of the build; see theories/Examples/"

clean:
	@if [ -f $(COQMAKEFILE) ]; then $(MAKE) -f $(COQMAKEFILE) clean; fi

distclean: clean
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf
