# Handoff notes

Working notes for picking this project back up. `README.md` says what the
project *is*; this file says what has been decided, what has been learned, and
what to do next. Read this first, then `AXIOMS.md`, then
`theories/Substrate/Interface.v`.

Last updated at commit `c588539`.

---

## 1. Orientation in one minute

A Rocq formalization of Unruh, *Quantum Relational Hoare Logic* (POPL 2019,
`qRHL.pdf` in this directory, arXiv:1802.03188v2).

The whole project turns on one line:

> **The substrate may assume textbook functional analysis.
> It may not assume anything about qRHL.**

`theories/Substrate/Interface.v` is a `Module Type HILBERT_SUBSTRATE`.
Everything else is a functor over it. Consequently the development declares
**no axioms of its own**, and the claim it supports is precise: *if the
substrate has a model, every rule proved here is sound.* The original
`qrhl-tool` axiomatizes its **tactics and simplification rules** instead
(paper §1.3) — that gap is the contribution, so do not erode it.

Three gates enforce this, all wired into `make`:

```sh
make              # build (rocq >= 9.1, stdlib only, no external libraries)
make audit        # no admits; no axioms outside the signature; no qRHL
                  # vocabulary inside theories/Substrate/
make assumptions  # Print Assumptions on the concrete layer, diffed against
                  # scripts/assumptions.expected
make axioms       # regenerate AXIOMS.md's inventory from Interface.v
```

`make audit` has already caught two real mistakes (an `Admitted` written while
sketching, and section `Hypothesis` declarations). Trust it; don't work around
it. If a section needs hypotheses, use `Context`, not `Hypothesis` — a section
`Hypothesis` is discharged and harmless, but that is not reliably detectable
from text, so the audit bans the keyword.

Build environment: `rocq` 9.1.0 from the existing `squirrel` opam switch. The
development needs **only the Rocq standard library**. `scripts/setup-switch.sh`
creates a dedicated switch; `--with-mathcomp` adds the Phase 4 dependencies.

---

## 2. Architecture

```
Substrate/Ambient.v     classical HOL (the logic the paper's proofs live in)
Substrate/Cnum.v        C := R * R  (Rocq's stdlib has no complex numbers)
Substrate/Sums.v        unordered sums: rearrangement, Tonelli, additivity
Substrate/Interface.v   Module Type HILBERT_SUBSTRATE   <-- trusted surface
Substrate/Theory.v      derived: lattice, operators, tensor, division, kernels
Substrate/Sanity.v      degeneracy canaries for the signature
Core/Vars.v             cvar/qvar, cmem/qmem, side, rcmem/rqmem, updates
Core/Expr.v             generic expression record; expr and rexpr instances
Core/Registers.v        the memory split, U_vars, A»Q, one-sided lifts
Core/Syntax.v           prog inductive, wt, fv, loopfree
Core/Semantics.v        [[c]], Pr, denote_wf_trace, denote_add
Core/Predicate.v        Def 13/14/16/18/20/23, Lem 15/17/24/25
Core/QEq.v              Def 27 quantum equality, Lem 31
Core/Judgment.v         Definition 35, Lemma 36 forward
Rules/General.v         Skip, Conseq, Seq
Rules/Classical.v       Assign1
Rules/Quantum.v         QApply1
```

Functor chain (each layer `Include`s the previous one's application):

```
HTheory S ──┐
            ├─> RegTheory S V ─> SyntaxTheory ─> SemTheory ─> PredTheory
ExprTheory V┘                                                      │
                                                                   v
                       Rules/{General,Classical,Quantum}  <─ JudgmentTheory <─ QEqTheory
```

Adding a file means: `Include <previous layer> S V.` at the top, and a line in
`_CoqProject` **in dependency order** (the build does not sort for you).

---

## 3. Design decisions — do not relitigate these

Each of these was chosen deliberately and has paid off. Reversing one is a
large refactor.

**Tagging is a product, not a renaming.** The paper builds `V1`, `V2` as fresh
copies of `V` related by `idx_1`, `idx_2`, and warns the reader (§2) to "assume
that they are the identity". Here relational memory is indexed by
`side * var`, so `idx_i` is a projection and rule `Sym`'s `U_rename,σ` is an
involution on `side`. **`idx` does not appear in Definition 35 at all.** This
removes a large fraction of Appendix A's notational overhead.

**One reindexing combinator.** Associativity and commutativity of `⊗`,
`U_vars,Q` and `U_rename,σ` are all `Ubij`, which turns a bijection of index
types into a unitary.

**Registers are predicates, and generic in the variable type.** `wsub P :=
forall w, if P w then wty w else unit` makes `wsub P × wsub ¬P ≅ wmem` a
*pointwise* case split under `funext` — no recursion, no tensor
reassociation. The padding with `unit` is what keeps it a plain function type.
The construction is generic over `(W, wty)` and instantiated twice, at `qvar`
and at `side * qvar`, via `Notation` (so every generic lemma applies
unchanged).

**Quantum statements are indexed by variable *sets*, not ordered lists.** The
paper types the operator in `apply e to Q` on `Type^list_Q` and then inserts
`U_vars,Q` to move it onto the set-indexed space; indexing by a `qset` makes
that conjugation the identity. Side benefit: `Type^list_Q` is what forced
"lists of *distinct* variables" as a side condition on every quantum statement
and rule — with sets it disappears.

**Only the positive cone `T⁺(X)` is axiomatized, not all of `T(X)`.** The
paper's appeal to "any operator can be written as a combination of four
positive ones" exists only to license extending a superoperator from cq basis
elements; here cq-states *are* families (`cmem -> tcp qmem`), so the semantics
is defined directly and that step never arises.

**One-sided lifts are defined through the side split.** `roliftL P A :=
Urqpair† ∘ (olift P A ⊗ id) ∘ Urqpair`, *not* `rolift (qidx SL P)`. The two
agree, but proving that is register associativity, which the signature cannot
express (see §5). Defining it this way costs nothing — "on side *i*" is exactly
what the paper's `idx_i` means — and it makes the projection laws follow from
generic partial-trace axioms. The two notions must be reconciled only for
Lemma 32.

**`sem_assign` carries its guard as an `if`, not a subset type.** So the index
is uniformly `ctype x`, the same as sampling and measurement. All three clauses
now follow one pattern, and the projections are provable without
dependent-pair equality.

---

## 4. Rocq-specific gotchas, learned the hard way

These cost real time. They will recur.

- **Higher-order unification.** `apply summable_inj`, `apply
  tcp_sum_singleton`, `apply tsum_partition_le` will fail with "cannot unify
  `?F j` with …". Always supply the family explicitly:
  `apply (summable_inj h (fun m => tcp_trace (r m)))`.
- **`rewrite` needs a syntactic match.** `rewrite (tcp_trace_sum …)` fails if
  the `tcp_sum` is hidden behind a definition — `unfold sem_sample` first.
  When the orientation is awkward, use `transitivity` rather than fighting it.
- **`replace … with … by tac; tac2` parses as `by (tac; tac2)`.** This silently
  runs your closing tactic on the *side* goal. Put them on separate lines.
- **Dependent matches on booleans.** To case-split on `P w` when values are
  indexed by it, the match must abstract over *all* the relevant booleans at
  once and take the values as arguments — see `bmerge`/`bpickl`/`bpickr` in
  `Registers.v`. And `cbv [wneg wsub] in *` must unfold the index *in the
  hypotheses' types* first, or abstraction leaves `wneg P w` behind and the
  match stops typechecking.
- **`C_scope` hijacks `*` and `+`.** Annotate real-number goals with `%R`.
  `ring` sometimes picks the wrong ring; `lra` or an explicit `Rmult_1_l` is
  more reliable.
- **`*)` inside a comment.** Writing `A^*)` closes the comment early. Use
  `A^adj` in prose.
- **Shell escaping when writing proofs via Python heredocs.** A lone `\` before
  a newline gets eaten as a line continuation, silently turning `/\` into `/`.
  Build the string with `chr(92)` or check with `grep -n '/ \{2,\}'` afterwards.
- **Rocq derives a module name from the filename**, so temp files must be valid
  identifiers: no dashes. `mktemp` templates with `-` break `rocq compile`.
- **Editing by text splicing is dangerous.** Two index-based splices corrupted
  `Registers.v` badly enough that rewriting the file was faster than repairing
  it. Prefer whole-file writes for anything structural; commit first.

---

## 5. What is proved

All of the below is kernel-checked with **no admits anywhere**.

**Substrate/Sums.v** — unordered sums over arbitrary index types:
`tsum_approx` (approximation from below), `tsum_partition_le` (the ε-split
partition bound), `tsum_pairs_le_iter` / `tsum_iter_le_pairs` /
**`tsum_tonelli`** (both directions), `tsum_add`, `tsum_scale`,
`summable_inj`/`tsum_inj_le`, `tsum_single_val`, plus subdistributions.

**Substrate/Theory.v** — the complete-lattice structure on subspaces (meets,
joins, span, orthocomplement, De Morgan); operator algebra including
**`oadj_invol`, `oadj_ocomp`, `oadj_oid` derived, not assumed**, from
`inner_oadj` plus nondegeneracy; kernels and fixed subspaces as *preimages*
(so `hfix` needs no new axiom); images with the preimage adjunction;
`himg_isometry_meet_oim`, which is what makes `QApply1`'s precondition work;
`tcp_sum_pair`, `tcp_sum_swap`.

**Core** — variables and memories; the generic expression record; the register
split with `Wsplit`, `Wsplit2` (disjoint union, needed for the three-way split
of Definition 27), `wolift` as a unital `*`-homomorphism, one-sided lifts and
their projection laws; the program syntax; the denotational semantics with

- **`denote_wf_trace`** — `⟦c⟧` really is a cq-superoperator on `T⁺_cq[V]`
  (preserves summability, does not increase the trace), for loop-free programs;
- **`denote_add`** — `⟦c⟧` is additive on the positive cone, loop-free;

predicates (Defs 13/14/16/18/20/23, Lemmas 15/17/24/25); quantum equality
(Def 27, Lemma 31 — whose proof needs *no* hypothesis, because the adjoint laws
are derived); **Definition 35** with separability as a definition rather than
an assumption, and Lemma 36 forward (`qrhl_to_pure`).

**Rules** — `Skip` (Lem 54), `Conseq` (Lem 46), `Seq` (Lem 47), `QApply1`
(Lem 65), `Assign1` (Lem 55).

---

## 6. The trusted surface

44 parameters, 117 axioms, grouped in `Interface.v`:

| group | params | axioms |
|---|---|---|
| Vectors (`l2 X`) | 7 | 15 |
| Subspaces | 8 | 15 |
| Bounded operators | 9 | 10 |
| Preimages | 1 | 1 |
| Tensor product | 4 | 13 |
| Reindexing (`Ubij`) | 1 | 3 |
| Positive trace-class | 14 | 60 |

Discipline when adding one: it must be a statement you could cite a textbook
for; it must be *used* by a proof you are writing now (never speculatively);
and it must not mention qRHL vocabulary. `make axioms` regenerates the
inventory; `AXIOMS.md` names, for every *absent* axiom, the first proof that
will need it.

`Sanity.v` derives four concrete *inequalities* from the signature (the lattice
has ≥2 elements, distinct kets span distinct lines, `⊥` is not the identity,
the tensor does not collapse). This catches a degenerate or contradictory
signature cheaply. It is **not** a consistency proof — only Phase 4's model
discharges that risk.

---

## 7. What to do next, in order

### 7a. `If1` / `JointIf` — cheapest, do this first

Needs only the binary `denote_add` (have it) plus **separability closed under
binary sums**. That in turn needs `tcp_sum` over `bool` to be binary addition:

```coq
Lemma tcp_sum_bool {X} (G : bool -> tcp X) : tcp_sum G = tcp_add (G true) (G false).
```

Provable from `tcp_sum_ub` / `tcp_sum_least` / `tcp_ext` by enumerating the
duplicate-free lists of booleans (nil, `[true]`, `[false]`, and the two
two-element ones). Then `tcp_sep` is closed under `tcp_add` via
`tcp_sum_sigma` at `K := bool`.

The rest of `If1` is straightforward: split `r` by `ev (idx SL e) rm`, note the
guard is independent of the other side's memory (so it commutes with the
projection), and recombine. `rcqs_projR` is additive via `rtcpR_add` +
`tcp_sum_add`.

### 7b. `Sample1`

Follows `Assign1` exactly, with subdistribution weights. Additionally needs

```coq
Axiom tcp_sum_scale_const : forall X J (c : J -> R) (r : tcp X),
  (forall j, 0 <= c j)%R -> summable c ->
  tcp_sum (fun j => tcp_scale (c j) r) = tcp_scale (tsum c) r.
```

and the `Cla[e is total]` bookkeeping (the precondition only constrains
memories whose block is nonzero — see `psat_Cla`).

### 7c. `Case`, and Lemma 36's converse

**`Case` needs `denote` *normality*, not additivity** — this was the main
surprise of the last session. The case split is over an arbitrary result type,
not two branches, so binary additivity does not suffice:

```coq
Theorem denote_sum : ... -> denote c (cqs_sum F) = cqs_sum (fun j => denote c (F j)).
```

Another induction over the syntax, in the shape of `denote_add`, needing sum
exchange in the `Assign`/`Sample`/`Measure` clauses. Once it exists, Lemma 36's
converse (`qrhl_pure -> qrhl`) becomes reachable: decompose via
`tcp_decompose`, apply the hypothesis per pure component, and reassemble. The
paper's equations (11)–(14) are exactly that bookkeeping.

### 7d. `QInit1`

Needs **abstract superoperators** in the signature, with `E ⊗ id`.
Initialization discards a register and prepares a fresh state, which is a
channel, not a conjugation, so none of the existing `tcp_conj` machinery
applies. Definition 10's locality — and hence rules `Frame` and `Equal` — needs
the same thing, so do it once and properly.

### 7e. `Measure1`, `JointMeasureSimple`

Per-outcome witnesses reassembled; same machinery as 7c.

### 7f. §4.4's two remaining lemmas

- **Lemma 29 / Corollary 30** needs the Schmidt decomposition (paper Lemma 7)
  as a new axiom. The *converse* direction — the one the examples use, to
  *establish* a quantum equality — is six lines and needs only that `U₁`, `U₂`
  are isometries. Do that first.
- **Lemma 32** needs register associativity: that `rolift (qidx SL P)` agrees
  with `roliftL P`. Not provable from the current signature — `Wsplit` is built
  from `Ubij` and so has laws only on basis vectors, while the identity has a
  general vector in the middle. Options: an `op_ext_ket`-style
  determination axiom plus a long derivation, or an abstract register primitive
  (Unruh's *Registers*, CoqQ's `qreg`). **This moves the hygiene line, so raise
  it rather than deciding alone.**

### 7g. Then Phase 1e onward

Ltac2 tactics and the EPR examples (Phase 1's exit criterion), Phase 2's
structural rules and loops (`while` also unblocks extending `denote_wf_trace`
and `denote_add` past `loopfree`), Phase 3's `Trans`/`Adversary`/ROR-OT-CPA, and
Phase 4's finite-dimensional model — which is the only thing that turns
"sound relative to a signature" into "sound".

---

## 8. Things that turned out to be false or surprising

Recorded so they are not re-derived.

- **`Assign1`'s guard is not satisfied at a single old value.** If `e` is
  constant it holds for *every* one. What is true is that (target, old value)
  is in bijection with (source, the target's old `x`), and *under that
  bijection* the guard becomes "this is what `e` says of the source", which is
  unique. The sum collapses **after** reindexing, not before — and that is
  exactly why the right-hand projection comes back unchanged. An earlier
  attempt assumed the wrong thing here and had to be thrown away.
- **`Case` needs normality, not additivity** (see 7c).
- **The other partial trace is not derivable from a tensor swap.** Going
  `tcp_ptrace ∘ tcp_conj Uswap` would need the swap's action on a general,
  non-product, non-pure operator, which the signature cannot compute. Hence
  `tcp_ptrace2` is a primitive.
- **Register associativity looked like a fork requiring a redesign; it was
  not.** Defining one-sided lifts through the side split sidesteps it entirely
  for the rules. It is still needed for Lemma 32 alone.
- **Fubini for unordered nonnegative sums is no longer a substrate concern** —
  it is proved in `Sums.v` (`tsum_tonelli`, `tsum_partition_le`). Earlier notes
  listing it as a needed axiom are obsolete.

---

## 9. Working practices

- Commit messages: explain *why*, name the paper lemma numbers, record
  surprises. End with the `Co-Authored-By` line the session's attribution
  reminder specifies.
- Run `make audit` before every commit; `make assumptions` when the concrete
  layer changes; `make axioms` when `Interface.v` changes.
- Keep `README.md`'s status table and `AXIOMS.md`'s "not yet in the signature"
  list honest — they are the fastest way back into the project.
- The scratch paper text is recoverable with
  `pdftotext -layout qRHL.pdf -` when a lemma statement needs checking.
