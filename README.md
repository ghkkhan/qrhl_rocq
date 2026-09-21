# qRHL in Rocq

A Rocq formalization of **quantum relational Hoare logic**, following
Dominique Unruh, *Quantum Relational Hoare Logic* (POPL 2019;
[arXiv:1802.03188v2](https://arxiv.org/abs/1802.03188), the 89-page version in
`qRHL.pdf`).

## Why

The reference implementation, `qrhl-tool` (Scala + Isabelle/HOL), is not
foundational. From §1.3 of the paper:

> All tactics in the tool, and many of the simplification rules in Isabelle are
> axiomatized (and backed by the proofs in this paper).

The 32 pages of soundness proofs in Appendix A are pen-and-paper. The goal here
is a development in which **Definition 35 is a definition, and every rule in
Figures 1–3 is a kernel-checked theorem** — with the standard Hilbert space
facts the proofs rest on isolated in a single auditable interface.

There is, as far as we can tell, no other qRHL formalization in Coq/Rocq.

## The shape of the thing

```
theories/Substrate/   the trusted surface, and derived theory
  Ambient.v           classical HOL: the logic the paper's proofs live in
  Cnum.v              C over stdlib R (Rocq's stdlib has no complex numbers)
  Sums.v              unordered sums of nonneg reals; subdistributions
  Interface.v         Module Type HILBERT_SUBSTRATE  <-- everything assumed
  Theory.v            derived: subspace lattice, operators, tensor, division
  Sanity.v            degeneracy canaries for the signature
theories/Core/        variables, expressions, syntax, registers, semantics,
                      predicates, quantum equality, the qRHL judgment
theories/Rules/       the rules of Figures 1-3, with soundness proofs
theories/Tactics/     Ltac2 tactics mirroring qrhl-tool's
theories/Examples/    the paper's §6 examples
models/               Phase 4: instantiations of HILBERT_SUBSTRATE
```

`HILBERT_SUBSTRATE` is a `Module Type`; every other file is a functor over it.
So the development declares **no axioms of its own**, and the claim it supports
is precise: *if the substrate has a model, every rule proved here is sound.*
See [AXIOMS.md](AXIOMS.md).

Two simplifications over the paper's presentation are worth knowing about,
because they remove a large fraction of Appendix A's notational overhead:

- **Tagging is a product, not a renaming.** Instead of building `V1`, `V2` as
  fresh variable sets related to `V` by bijections `idx_i`, the relational
  memory is indexed by `side * var`. `idx1`/`idx2` collapse to projection and
  `U_rename,σ` for rule `Sym` collapses to an involution on `side`. The paper
  itself advises the reader to "assume that they are the identity" (§2); here
  that is literally true.
- **Quantum statements are indexed by variable *sets*.** The paper types the
  operator in `apply e to Q` on the ordered `Type^list_Q` and then inserts
  `U_vars,Q` into the semantics to move it onto the set-indexed space. Indexing
  by a `qset` makes that conjugation the identity, deletes the
  distinct-variables side condition from every quantum statement and rule, and
  leaves `U_vars,Q` as a convenience layer for writing concrete gates. The
  paper treats these conversions as noise: "we will ignore them in our
  informal discussions" (§5.1).
- **One reindexing combinator.** Associativity and commutativity of `⊗`, the
  variable isomorphisms `U_vars,Q` (Def. 19) and the renamings `U_rename,σ` are
  all instances of `Ubij`, which turns a bijection of index types into a
  unitary.

## Status

| phase | content | state |
|---|---|---|
| 0 | build, ambient logic, `C`, unordered sums | **done** |
| 1a | substrate signature, derived theory, canaries | **done** |
| 1b | variables, expressions, syntax | **done** |
| 1b | registers: memory split, `U_vars`, `A»Q`, `S»Q` | **done** (set-indexed; ordered `Type^list_Q` bridge pending) |
| 1b | semantics `⟦c⟧`, `Pr[e : c(ρ)]`, point-mass laws | **done** |
| 1b | `denote_wf_trace`: `⟦c⟧` is a cq-superoperator | **done** for loop-free programs |
| 1b | `denote_add`: `⟦c⟧` is additive | **done** for loop-free programs |
| 1b | `denote_sum`: `⟦c⟧` is normal (`⟦c⟧(∑ⱼρⱼ) = ∑ⱼ⟦c⟧ρⱼ`) | **done** for loop-free programs |
| 1c | predicates (Def 13/14/16/18/20/23, Lem 15/17/24/25) | **done** |
| 1c | quantum equality (Def 27, Lem 31); `Y₁ ≡quant Y₂` | **done**; Lem 29/32 deferred (see below) |
| 1c | Definition 35 (the judgment), Lemma 36 → | **done**; Lemma 36 ← deferred |
| 1d | `Skip` `Conseq` `Seq` `Case` `QApply1` `Assign1` `If1` `JointIf` `Sample1` `Measure1` | **done** |
| 2 | `QrhlElim` (Lemma 50) and its equality form | **done** (ahead of its phase) |
| 1d | the other 3 vertical-slice rules | in progress, see below |
| 1e | Ltac2 tactics, EPR + EPR-measure examples | not started |
| 2 | `Sym` `Frame` `Equal` `QrhlElim(Eq)`, loops | not started |
| 3 | `Trans` `JointMeasure` `Adversary`, ROR-OT-CPA | not started |
| 4 | finite-dimensional model | not started |

Phase 1's exit criterion is that `theories/Examples/EPR.v` and
`EPRMeasure.v` close, stating the paper's (20) and (21) verbatim.

### What is done, and what remains

The analysis that three obligations were waiting on is **finished**.
`Substrate/Sums.v` now has unordered sums with approximation from below, the
partition bound, both directions of Tonelli over a product, additivity,
scaling, and reindexing along injections. On top of it, `denote_wf_trace`
proves that `⟦c⟧` really is a cq-superoperator on `T⁺_cq[V]` — it preserves
summability and does not increase the total trace — for loop-free programs.
Assignment reindexes along an injection (its side condition pins the target
memory down); sampling and measurement do not, so they go through the bijection
`(m′,a) ↦ (m′(x:=a), m′ x)` and then Tonelli.

`QApply1` is proved, which means the witness-construction machinery works end
to end: `Registers.v` now has one-sided lifts `roliftL`/`roliftR` with the two
facts every one-sided rule needs — the left projection sees the action, the
right one does not — and `Rules/Quantum.v` factors the shared
well-formedness/separability/projection reasoning into a `OneSided` section
that `QInit1` reuses.

One design decision is worth knowing. A one-sided lift is **defined** by
conjugating through `Urqpair` and acting on a tensor factor, rather than as
`rolift (qidx SL P)`, the relational register carrying the same variables. The
two agree, but proving that means relating two different decompositions of the
same memory — register associativity — which the current signature cannot
express: `Wsplit` is built from `Ubij` and so has laws only on basis vectors,
while the identity in question has a general vector in the middle. Defining it
this way costs nothing for the rules, since "on side *i*" is exactly what the
paper's `idx_i` means. The two notions have to be reconciled only for Lemma 32.

`Assign1` is also proved, which exercised the other half of the machinery: the
witness is a pushforward, so its two projections need sums to be pushed through
partial traces and reassociated. That needed normality of `tcp_sum` and
operator-level Tonelli in the signature, and it drove one change to the
semantics — `sem_assign` now carries its guard as an `if` rather than as a
subset type, so that the index is uniformly `ctype x`, the same as for sampling
and measurement. That uniformity is what makes the projections provable without
dependent-pair equality, and it makes all three clauses follow one pattern.

Worth recording about `Assign1`: the guard is *not* satisfied at a single old
value — if `e` is constant it holds for every one. What is true is that
(target, old value) is in bijection with (source, the target's old `x`), and
under that bijection the guard becomes "this is what `e` says of the source",
which *is* unique. So the sum collapses after reindexing, not before, and that
is exactly why the right-hand projection comes back unchanged.

`denote_add` — that `⟦c⟧` is additive on the positive cone — is also proved for
loop-free programs, which is what lets a state be split and the pieces
recombined.

`denote_sum` — normality of `⟦c⟧`, i.e. `⟦c⟧(∑ⱼ ρⱼ) = ∑ⱼ ⟦c⟧ρⱼ` for an
arbitrary index type — is proved for loop-free programs. The three clauses
with a sum of their own (assignment, sampling, measurement) are where the work
is: there the statement's sum and the family's sum have to be exchanged, which
is `tcp_sum_swap` and so needs all four of its summability side conditions. It
took one new axiom, normality of the tensor in the factor that varies, for the
`Q ←q e` clause.

On top of it, `Case` is proved. The state is cut into the pieces on which the
expression takes each value; at a given memory exactly one piece survives, so
the pieces sum back to the original. `Core/Judgment.v` now has the general
machinery for summed families of relational states (`rcqs_fam`, `rcqs_sum`,
well-formedness, separability, satisfaction, and normality of both
projections), which is also precisely what the converse of Lemma 36 was
waiting on. Note that `Case` carries `wt`/`loopfree` side conditions the
paper's rule does not: they come from `denote_sum`, and go away once the
`while` clause is added to that induction.

`QrhlElim` (Lemma 50) is proved, out of phase order, because it is what makes
the logic usable: it is how a judgment turns into a statement about
probabilities, and so it is the last step of any game-based proof. The paper's
two side conditions — that `ρ₁` and `ρ₂` are the marginals of `ρ` up to the
renaming that puts a single-sided state on side *i* — are not hypotheses here:
Definition 35's projections already land in `cqs` on the nose, so `ρ₁` *is*
`rcqs_projL ρ`. The argument is then short: write both probabilities as sums
of the witness's trace over pairs of memories, keeping on the left those pairs
whose `m₁` satisfies `e` and on the right those whose `m₂` satisfies `f`; the
postcondition says the first set of pairs is inside the second wherever the
witness is nonzero, so the comparison is pointwise. The equality form
(`QrhlElimEq`'s core, with `Cla[idx₁ e ⟺ idx₂ f]`) follows from the two
inequalities. `QrhlElimEq` proper additionally needs locality, so it is still
outstanding.

`Measure1` completes the family of one-sided rules. Its shape is `Sample1`'s
with a conjugation by the outcome's projector where the subdistribution's
weight was, so it reuses `rbeta` verbatim; what is new is the two ends. On the
postcondition side, the paper's `(B{z/x₁} ∩ im e′_z) + (im e′_z)^⊥` works
because a projector is the identity on its image and kills the
orthocomplement, so its image of that join lands in `B` — proved as
`himg_proj_meet_oim`, with only "a projector fixes its image" assumed. On the
right-hand projection, totality of the measurement is exactly what is needed
and exactly what the paper's `Cla[idx₁ e is a total measurement]` supplies: a
total measurement is trace-preserving, so the other side's reduced state does
not move. Both the bound and its equality case have to be carried from the
register to the whole memory first (`olift_meas`, `olift_meas_total`), which
is where `meas_bound_tensor` and `meas_total_tensor` are used.

Still to do in Phase 1d, with what each actually needs (established, not
guessed):

| rule | what it needs |
|---|---|
| ~~`If1`, `JointIf`~~ | **done** — needed no new axioms |
| ~~`Sample1`~~ | **done** |
| ~~`Measure1`~~ | **done** — four textbook axioms: a projector fixes its image, `Meas(D,X)⊗id ⊆ Meas(D,X⊗Y)` (bounded and total forms), and that a total measurement on one factor leaves the other factor's reduced state alone |
| ~~`Case`~~ | **done** — needed `denote_sum`; carries `wt`/`loopfree` side conditions until the loop clause is added |
| `QInit1` | abstract superoperators — initialization discards a register and prepares a fresh state, which is a channel, not a conjugation |
| `JointSample` | a two-sided reindexing: the witness updates `x₁` and `y₂` together along a coupling, so `rbeta` has to be replaced by its joint analogue |
| `JointMeasureSimple` | the same, plus the quantum equality `Q′₁ ≡quant Q′₂` in the precondition |

The converse of Lemma 36 is the natural next one: `denote_sum` and the
`rcqs_fam` machinery `Case` needed are exactly what it was waiting on.

### Two smaller gaps in §4.4

**Lemma 29 / Corollary 30** — the characterization of quantum equality on
separable states. Needs the Schmidt decomposition (the paper's Lemma 7). The
converse direction, which is what the examples use, is six lines and only needs
`U₁`, `U₂` isometric.

**Lemma 32** — used twice in the EPR derivation to simplify `QApply1`'s
preconditions. Needs coherence between a lift over one register and a lift over
a larger one containing it — i.e. item (3) above.

## Building

Needs `rocq` >= 9.1 on `PATH` and nothing else — the Rocq standard library is
the only dependency. (Phase 4 additionally needs mathcomp.)

```sh
make              # build
make audit        # trusted surface: no admits, no stray axioms, hygiene
make assumptions  # Print Assumptions on the concrete layer, diffed against
                  # scripts/assumptions.expected
make axioms       # regenerate the AXIOMS.md inventory from Interface.v
```

`scripts/setup-switch.sh` creates a dedicated opam switch if you want one;
`--with-mathcomp` adds the Phase 4 dependencies.

## Reading order

`HANDOFF.md` if you are picking the project up: it holds the design decisions,
the Rocq gotchas that cost time, and the ordered list of what to do next.

Otherwise `AXIOMS.md` first, then `theories/Substrate/Interface.v` — between
them they fix everything the rest of the development is allowed to assume.
