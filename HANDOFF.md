# Handoff notes

Working notes for picking this project back up. `README.md` says what the
project *is*; this file says what has been decided, what has been learned, and
what to do next. Read this first, then `AXIOMS.md`, then
`theories/Substrate/Interface.v`.

Last updated at commit `16cdd44`. Seventeen of the paper's rules are proved,
Lemma 36 is proved in both directions, and there are no admits and no axioms
outside the substrate signature.

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
Substrate/Theory.v      derived: lattice, operators, tensor, division, kernels,
                        Ubij_oid / Ubij_ocomp / Uswap_Uswap / tcp_conj_Uswap
Substrate/Sanity.v      degeneracy canaries for the signature
Core/Vars.v             cvar/qvar, cmem/qmem, side, rcmem/rqmem, updates,
                        the right-sided/cross-side rcupd mirrors
Core/Expr.v             generic expression record; expr and rexpr instances;
                        rswap (the classical half of a predicate swap)
Core/Registers.v        the memory split, U_vars, A»Q, one-sided lifts,
                        Urqswap and the coherence/shrink lemmas for it
Core/Syntax.v           prog inductive, wt, fv, loopfree (now unused)
Core/Semantics.v        [[c]], Pr, the While section (telescoping bound),
                        denote_wf_trace / denote_add / denote_sum, cqs_fam
Core/Predicate.v        Def 13/14/16/18/20/23, Lem 15/17/24/25, predswap
Core/QEq.v              Def 27 quantum equality, Lem 31
Core/Judgment.v         Definition 35, Lemma 36 forward, rbeta / rbeta2,
                        rcqs_sum / rcqs_fam and the projection normality laws,
                        rcqs_swap and its psat/projection laws
Rules/General.v         Skip, Conseq, Seq, Case, QrhlElim (+ equality form),
                        Sym
Rules/Classical.v       Assign1, Sample1, If1, JointIf, JointWhile, JointSample
Rules/Quantum.v         QApply1, Measure1
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
`inner_oadj` plus nondegeneracy; **`op_ext` is now also derived**, as a
one-line corollary of `op_ext_ket` (see §6); kernels and fixed subspaces as
*preimages* (so `hfix` needs no new axiom); images with the preimage
adjunction; `himg_isometry_meet_oim`, which is what makes `QApply1`'s
precondition work, and `himg_oid`; `tcp_sum_pair`, `tcp_sum_swap`; `Ubij_oid`
and `Ubij_ocomp`, the two lemmas that make every syntactic identity between
the development's reindexing unitaries an index-level computation; `Uswap`'s
own `Uswap_Uswap` (self-inverse) and `tcp_conj_Uswap` (conjugating a tensor
product by the factor swap exchanges the factors).

**Core** — variables and memories; the generic expression record; the register
split with `Wsplit`, `Wsplit2` (disjoint union, needed for the three-way split
of Definition 27), `wolift` as a unital `*`-homomorphism, one-sided lifts and
their projection laws; the program syntax; the denotational semantics with

- **`denote_wf_trace`** — `⟦c⟧` really is a cq-superoperator on `T⁺_cq[V]`
  (preserves summability, does not increase the trace);
- **`denote_add`** — `⟦c⟧` is additive on the positive cone;
- **`denote_sum`** — `⟦c⟧` is *normal*: `⟦c⟧(∑ⱼρⱼ) = ∑ⱼ⟦c⟧ρⱼ` for an
  arbitrary index type. Packaged with `cqs_fam`, whose single condition is
  joint summability of the traces over (index, memory);
- **`denote_scale`** — `⟦c⟧(a·ρ) = a·⟦c⟧ρ` for `a ≥ 0`;

All three now hold for **every** well-typed program, loops included; the loop
clause is the telescoping estimate in `Semantics.v`'s `While` section.
`loopfree` is no longer used anywhere.

predicates (Defs 13/14/16/18/20/23, Lemmas 15/17/24/25); quantum equality
(Def 27, Lemma 31 — whose proof needs *no* hypothesis, because the adjoint laws
are derived); **Definition 35** with separability as a definition rather than
an assumption, and **Lemma 36 in both directions** (`qrhl_to_pure` and
`qrhl_pure_to_qrhl` — the latter needs `wt c`/`wt d`; see §7a).

Judgment.v additionally has the relational counterpart — `rcqs_sum` /
`rcqs_fam` with well-formedness, separability, satisfaction, the identity
`cqs_trace ∘ rcqs_projL = rcqs_trace`, and normality of both projections —
plus `tcp_sep_sum`, the one-sided reindexing `rbeta`, `rsep_pure_decompose`
(the spectral theorem pushed through separability), and `rcqs_scale` with its
own well-formedness/separability/satisfaction lemmas.

**Rules** — seventeen of the paper's, with the lemma number each is proved
from:

| rule | lemma | notes |
|---|---|---|
| `Skip` | 54 | |
| `Conseq` | 46 | = `qrhl_mono` |
| `Seq` | 47 | plus the two skip corollaries |
| `Case` | 48 | needs only well-typedness |
| `QrhlElim` | 50 | plus the equality form; ahead of its phase |
| `Assign1` | 55 | |
| `Sample1` | 56 | |
| `If1` | 58 | |
| `JointIf` | 59 | |
| `JointWhile` | 61 | ahead of its phase; no termination condition needed |
| `Measure1` | 62 | |
| `JointSample` | 57 | both projections need a marginal collapse, not just one -- see §7b |
| `Sym` | 44 | ahead of its phase; needed `op_ext_ket` -- see §7c |
| `QApply1` | 65 | |

`grep -rhoE "Theorem rule_[A-Za-z_0-9]+" theories/Rules/ | sort -u` is the
authoritative list.

---

## 6. The trusted surface

Grouped as `Interface.v` groups them; `make axioms` regenerates the full
inventory in `AXIOMS.md`, which is where the statements live.

| group | params | axioms |
|---|---|---|
| Vectors: the space l2(X) | 7 | 15 |
| Subspaces | 8 | 15 |
| Bounded operators | 9 | 10 |
| Preimages of subspaces | 1 | 1 |
| Tensor product | 4 | 13 |
| Reindexing | 1 | 3 |
| Positive trace-class operators | 14 | 71 |
| **total** | **44** | **128** |

Additions since Lemma 36's converse was proved (this count; `make axioms`
regenerates `AXIOMS.md`, which is authoritative): **`op_ext_ket`** (replacing
`op_ext`, net zero axioms -- see §7c), at +2, **`tcp_ptrace_pswap`** /
**`tcp_conj_pswap`** (the factor-swap versions of the existing
partial-trace/tensor laws -- textbook, but not derivable from `op_ext_ket`
alone, since the swap's action on a general non-ket vector is exactly the
continuity gap the signature declines to expose), and at +1, **`tcp_proj_vscale`**
(rescaling a vector rescales its projection by the modulus squared -- needed
to normalize the unnormalized vectors `tcp_decompose` hands back; see §7a).
Everything landed for Lemma 36's converse itself (steps 1-4 of the old §7a
plan, and the theorem's own assembly) added **zero** further axioms --
`make assumptions` is unchanged from before that work.

Discipline when adding one: it must be a statement you could cite a textbook
for; it must be *used* by a proof you are writing now (never speculatively);
and it must not mention qRHL vocabulary. `make axioms` regenerates the
inventory; `AXIOMS.md` names, for every *absent* axiom, the first proof that
will need it.

`Sanity.v` derives five concrete *inequalities* from the signature (the lattice
has ≥2 elements, distinct kets span distinct lines, `⊥` is not the identity,
the tensor does not collapse, and `op_ext_ket` does not collapse operators
that act differently on kets). This catches a degenerate or contradictory
signature cheaply. It is **not** a consistency proof — only Phase 4's model
discharges that risk.

---

## 7. What to do next, in order

Everything in Phase 1d is done except `QInit1` and `JointMeasureSimple`. The
ordering below reflects what is actually blocked by what, not the phase
numbering.

### 7a. Lemma 36's converse — DONE

`qrhl_pure_to_qrhl : wt c -> wt d -> qrhl_pure A c d B -> qrhl A c d B`
(`Judgment.v`), the direction one uses to *establish* a judgment. Together
with the forward direction (`qrhl_to_pure`, proved earlier), Lemma 36 is now
proved both ways — but **not as a clean iff**: the converse needs `wt c` and
`wt d` (well-typedness), which the forward direction and the paper's
statement do not. This is unavoidable, not a choice — `denote_scale`,
`denote_sum`, and `denote_trace_le` (the facts the assembly leans on) all
carry a `wt` hypothesis, because `⟦·⟧` is defined for every syntactic
program but is only *shown* additive/normal/trace-non-increasing under
well-typedness. Every rule proof that invokes this direction already
threads `wt c`/`wt d` through (rule `Case` does the same), so this costs
nothing downstream; it is just a fact worth having said explicitly rather
than leaving the docstring's "both directions" claim to imply an iff.

The four steps the previous version of this section planned all landed
essentially as predicted:

1. `rsep_pure_decompose`: `rsep (r rm)` plus `tcp_decompose` on each tensor
   factor writes `r rm = ∑ tcp_proj (rprod φ ψ)`, via `tcp_tensor_proj`,
   `tcp_conj_proj`, and the new `tcp_tensor_sum_sum` (the general two-sums-
   tensor-into-one-sigma-sum fact, of which `tcp_tensor_sum_l`/
   `tcp_tensor_sum_r` are the one-sided cases).
2. `tcp_proj_normalize` (one new axiom, `tcp_proj_vscale`-derived) normalizes
   the unnormalized vectors `tcp_decompose` hands back; made total by
   `tcp_proj_decompose_unit` (handling the zero-vector case with a default
   unit ket, scaled by 0) so callers never case-split on it.
3. `denote_scale` — proved exactly as planned, a `denote_add`-shaped
   induction.
4. The sigma-index bookkeeping (`rsep_pure_decompose`'s witness type,
   `pure_scaled_witness`'s per-component application of `qrhl_pure`, and the
   main theorem's assembly via `rcqs_sum`/`rcqs_fam`) was the real work, and
   turned out to need **one more piece than budgeted**: closing the two
   projection equations (`rcqs_projL (rcqs_sum r') = denote c (rcqs_projL r)`
   and its mirror) cannot be done directly from the per-component witnesses'
   own projection facts (`HL`/`HR` in the proof) — `denote_sum` needs to know
   the *input* family (the scaled point masses fed to `qrhl_pure`) is jointly
   summable, and that fact isn't otherwise available. The fix was an
   auxiliary "input" point-mass family `R0` (one `rdirac` per
   (memory, decomposition-component) pair) that exists purely so the proof
   can invoke `rcqs_projL_sum`/`rcqs_fam_projL` on it — its own summability
   comes for free from the same `lamf` bound the witnesses' summability
   needs, and it sums back to `r` itself (`Hcollapse`, proved via
   `tcp_sum_sigma` read right-to-left plus `tcp_sum_singleton`). This
   "construct an rcqs whose only job is to be summed" pattern is worth
   knowing if a similar closure gap shows up again.

Budget honestly, in retrospect: right order of magnitude, wrong shape —
the four steps landed as one-line summaries each said they would, but step 4
alone needed `tcp_sum_sigma` three separate times (the decomposition's own
flatten, the collapse, and the scalar-summability transfer via
`tcp_summable_trace`), not once.

### 7b. `JointSample` (Lem 57) — DONE

Proved. No new axioms. It is *not* "about the size of `Sample1`" — an earlier
note here said that, and it was too optimistic. The witness is `Sample1`'s
pattern with a two-sided reindexing `rbeta2` (Judgment.v) in place of `rbeta`,
and `Substrate/Sums.v` gained the marginals (`marginal1`/`marginal2`,
`dmarginal1`/`dmarginal2`) via `tsum_iter_le_pairs`/`tsum_tonelli`, exactly as
expected. What made it larger: unlike `Sample1` (where only the *unsampled*
side's projection needs a probability identity, and the *other* projection is
free combinatorics), here **both** sides are sampled, so **both** projections
need a marginal-collapse argument, not just one. Each projection is therefore
a *two-layer* proof: an inner layer collapses the other variable and the other
side's classical memory together via `sbeta` and the marginal identity
(`Sample1_projR`'s totality-collapse pattern, with a marginal value playing
the role totality played), and an outer layer brings the kept variable to the
front via a `cmem * (X * Y) ≅ Y * (cmem * X)`-style Fubini regrouping
(`Sample1_projL`'s pattern, one level up, needing three separate
`tcp_sum_pair`/`tcp_sum_bij` calls chained together rather than one
`tcp_sum_swap`). See `Rules/Classical.v`'s `sampleLR_projL_inner` /
`sampleLR_projR_inner` for the inner layer and `sampleLR_projL` /
`sampleLR_projR` for the outer one — the second is a near-exact mirror of the
first (swap `SL↔SR`, `x↔y`, `e1↔e2`, `rtcpL↔rtcpR`, `marginal1↔marginal2`) and
compiled on the first try once the first one worked, which is worth knowing if
this pattern recurs (it will, for `JointMeasureSimple`).

### 7c. `op_ext_ket` and `Sym` — DONE

Added `op_ext_ket`:

```coq
Axiom op_ext_ket : forall X Y (A B : op X Y),
    (forall x : X, oapp A (ket x) = oapp B (ket x)) -> A = B.
```

The user asked me to consult a stronger model on this decision, having no
view themselves on substrate design. That consultation's recommendation,
followed here: add it, because the signature already contains `Ubij_unitary`
— the *same* assumption family (determination of a bounded operator by its
action on the computational basis) — with a comment explaining it is assumed
rather than derived because deriving it needs continuity the signature won't
expose. `op_ext_ket` makes that same commitment explicit rather than opening
a new category of assumption.

It turned out to let the signature's old `op_ext` (extensionality over *all*
vectors) become a one-line corollary: `op_ext_ket`'s hypothesis (agreement on
kets) is strictly weaker than `op_ext`'s (agreement everywhere), so anything
satisfying the latter satisfies the former. Net change to the trusted
surface from that swap alone: **zero axioms**. Added a `Sanity.v` canary
(`canary_op_ext_ket_nondegenerate`) since it's the first axiom quantifying
over *all* operators.

Then proved, using it: `Ubij_oid` (the identity reindexing is `oid`) and
`Ubij_ocomp` (composing two `Ubij`s along composable maps is the `Ubij` of the
composite) in `Theory.v` — every syntactic identity between the development's
reindexing unitaries reduces to this pattern — and rule **`Sym`** (Lem 44).
`{A} c ~ d {B}` gives `{predswap A} d ~ c {predswap B}`, where:

- **`predswap`** (`Predicate.v`) is `gmap (himg Urqswap) (rswap A)` — `rswap`
  (already in `Expr.v`, from before this stretch of work) swaps the classical
  memory and already discharges the `ev_local` obligation for the swapped
  free-variable set; `gmap (himg Urqswap)` then applies the quantum side swap
  pointwise. **This answers the open question** the previous version of this
  section flagged ("how to swap a predicate") — it was already half-answered
  by `rswap`, which nobody had connected to `pred` yet.
- **`Urqswap`** (`Registers.v`) is `Ubij rqmem_swap rqmem_swap ...`. The key
  identity `ocomp Urqpair Urqswap = ocomp Uswap Urqpair` is an `op_ext_ket`
  computation (`rq_pair (rqmem_swap m) = pswap (rq_pair m)`, pure `qsel`
  algebra). From it: `rtcpL (tcp_conj Urqswap r) = rtcpR r` and its mirror
  (`rtcpL_Urqswap`, `rtcpR_Urqswap`), and (composed with `Urqpair_Urqswap`
  again) that conjugating by `Urqswap` preserves separability
  (`rsep_Urqswap`) — **using one new axiom**, `tcp_conj_pswap`: conjugating a
  *product* by the factor swap exchanges the factors
  (`tcp_conj Uswap (tcp_tensor r s) = tcp_tensor s r`). This is **not**
  derivable from `op_ext_ket` alone — same reason `tcp_ptrace_pswap` (added
  for the `rtcpL`/`rtcpR` exchange, also new) wasn't: both need the swap's
  action on a *general* tensor vector, not just a ket, which the signature's
  continuity gap puts out of reach. Textbook nonetheless.
- **`rcqs_swap r := fun rm => tcp_conj Urqswap (r (rcmem_swap rm))`**
  (`Judgment.v`) is the witness-level swap. Its `psat` law needed only *one*
  direction of "swapping twice is the identity" —
  `himg_Urqswap_shrink : himg Urqswap (himg Urqswap S) ≤h S` — proved via the
  existing `himg_isometry_meet_oim` plus `oim Urqswap = htop` (`Urqswap` is
  onto: every ket is `oapp Urqswap` of the ket at the swapped memory) plus
  self-adjointness. The *equality* `himg U (himg U S) = S` for a unitary `U`
  is **not** derived (the reverse inequality direction of
  `himg_isometry_meet_oim`-style reasoning isn't available), and turned out
  not to be needed: `psat`'s obligation is an inequality, in both directions
  the proof uses.

`rule_Sym` itself: given `r` satisfying `predswap A`, `rcqs_swap r` satisfies
`A` (`rcqs_swap_psat_from_predswap`, using the shrink lemma), so the
hypothesis applies to it; its witness `s` satisfies `B`, so `rcqs_swap s`
satisfies `predswap B` (`rcqs_swap_psat_to_predswap`, no shrink needed — just
monotonicity) and is returned as the witness. The two projections exchange
along with the two programs (`rcqs_projL_swap`, `rcqs_projR_swap`), which is
what lines the swapped witness up with `d` on the left and `c` on the right.

No admits, no axioms beyond the two named above (net +2: `tcp_ptrace_pswap`,
`tcp_conj_pswap`; `op_ext_ket` replacing `op_ext` is net 0). 44 parameters,
127 axioms.

### 7d. `QInit1`, and register coherence — the reassociation is DONE; the rule is not

**Update: the assessment below (register coherence needs one monolithic
dependent `Ubij`, "likely the most painful Rocq in the development") was
wrong, on both difficulty and shape.** It took three small, independent
`Registers.v` lemmas, none of them the feared `bmerge`/`bpickl`/`bpickr`
construction, and the whole thing (including both round-trip proofs and the
final `op_ext_ket` lift) is under 100 lines:

- **`rqneg_qidx`**: `rqneg (qidx SL Q) = wunion (qidx SL (qneg Q)) (qidx SR
  (fun _ => true))`, a `wset` equality over `rqvar`, proved by `funext` +
  `destruct` + `destruct (Q q)`. Used only as a fact about *plain functions*
  inside the next lemma's proof — never as a type-level transport.
- **`Urelab s Q : op (rqsub (qidx s Q)) (qsub Q)`**: one side's copy of a
  register is just that register, relabeled. The trick that makes this
  cheap: *destruct `s` at the top of the definition*, not inside the round
  trip proofs. Once `s` is a concrete constructor, `qidx s Q` reduces to `Q`
  (or to the constant `false`) *by computation alone* (`side_eqb SL SL`
  reduces to `true` by iota, no `qidx_same`-style transport needed), so both
  round trips close by `destruct + reflexivity`. The version that tried to
  stay generic in `s` and transport along `qidx_same` produced a stuck
  `eq_rect` immediately (an opaque `Qed` proof used as a computational
  transport) — that's the one dead end worth remembering.
- **`Uassoc Q`**, the actual reassociation, between `rqsub (qidx SL Q) *
  rqsub (rqneg (qidx SL Q))` and `(qsub Q * qsub (qneg Q)) * qmem`: built the
  *same* way as `Urelab` — both directions are plain functions that type
  themselves correctly by computation once the side tag is concrete, so no
  `Wsplit2` (disjoint-union combinator) and no transport of `rqneg_qidx`
  along the operator's domain type were needed, even though that was the
  obvious way to try to assemble it from existing pieces. `rqneg_qidx` is
  used only inside `wjoin_qidx_SL`, again purely as a fact about how a
  *memory function* (not a register type) decomposes.
- **`rUsplit_qidx_SL`**: `rUsplit (qidx SL Q) = ocomp (oadj Urqpair) (ocomp
  (tensoro (Usplit Q) oid) (Uassoc Q))`, the full operator identity, proved
  first on kets (`rUsplit_qidx_SL_ket`, pure index algebra in the
  `rq_pair_swap`/`Urqpair_Urqswap` pattern) and then lifted by `op_ext_ket`.

So `op_ext_ket` *did* make this cheap, once the reassociation was built the
right way; the earlier note's pessimism came from assuming the reassociation
had to be built as one dependent `Ubij` with the padding threaded through
by hand, when in fact each piece independently reduces to a concrete side
before any dependent matching is needed.

**What is still open**: `rule_QInit1` itself. The witness — discard `Q`,
tensor in the fresh state, via `Urqpair` + `Usplit Q`, exactly `sem_qinit`
lifted to act on one factor of `qmem * qmem` — never needs the
reassociation at all (it stays entirely in the `Urqpair` picture, like every
other one-sided rule). The reassociation is needed only to connect
`hdivReg`/`pdiv`'s precondition (stated through `rUsplit (qidx SL Q)`,
because that is the paper's surface form) back to that picture when
extracting what `psat r (pdiv ...)` gives about `r`'s decomposition. That
connection, the witness's projections and separability, and the rule proof
itself are not attempted yet.

### 7e. `JointMeasureSimple` (Lem 64)

`Measure1`'s pattern applied on both sides at once, plus the quantum equality
`Q′₁ ≡quant Q′₂` in the precondition. Notably it does *not* require the
measurements to be total (the paper says so explicitly, p. 32), so
`tcp_ptrace2_meas_tensor` is not what makes its projections work — the two
sides' measurements cancel against each other through the quantum equality
instead. Expect the same two-layer projection structure `JointSample` needed
(§7b): both projections need a collapse argument here too, since both sides
measure. `rbeta2` should not be reusable as-is (the summed index is now a
*measurement outcome* shared by both sides via the quantum equality, not a
pair of independently-updated classical variables), but the Fubini-regrouping
technique (`sig1`/`sig2` bijections between `cmem * (X * Y)` and
`Y * (cmem * X)`) should port directly.

### 7f. §4.4's two remaining lemmas

- **Lemma 29 / Corollary 30** needs the Schmidt decomposition (paper Lemma 7)
  as a new axiom. The *converse* direction — the one the examples use, to
  *establish* a quantum equality — is six lines and needs only that `U₁`, `U₂`
  are isometries. Do that first.
- **Lemma 32** is the register-coherence statement of §7d; it falls out of the
  same work.

### 7g. Then Phase 1e onward

Ltac2 tactics and the EPR examples (Phase 1's exit criterion, gated on §7d),
Phase 2's remaining structural rules (`Frame`, `Equal`, `QrhlElimEq`) and
`While1` (`JointWhile` and `Sym` are done; `While1` needs Definition 22's
totality and a locality condition), Phase 3's `Trans`/`Adversary`/ROR-OT-CPA,
and Phase 4's finite-dimensional model — which is the only thing that turns
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
- **`Case` needs normality, not additivity.** Now proved (`denote_sum`). The
  case split is over an arbitrary result type, not two branches, so binary
  additivity does not suffice.
- **`Measure1`'s right projection is exactly where totality is used.** The
  right program is `skip`, so the right marginal has to come back unchanged,
  and only a *trace-preserving* operation on the left does that. This is what
  `Cla[idx₁ e is a total measurement]` is doing in the precondition, and it is
  why `JointMeasureSimple` — which the paper says needs no totality — must
  work differently.
- **`QrhlElim` needs no register machinery.** The paper states it with a
  renaming superoperator `E_{rename,idxᵢ}` relating `ρᵢ` to a marginal of `ρ`.
  Here Definition 35's projections already land in `cqs`, so `ρ₁` *is*
  `rcqs_projL ρ` and the side conditions vanish. It was proved far ahead of
  its phase because of that.
- **`rewrite` fails surprisingly often on terms that print identically.** Three
  times now (`tcp_trace_conj_isometry in Hb`, `olift_meas_total`'s `Heq`,
  `tcp_ptraceL_sum` in the `QInit` clause of `denote_sum`) a `rewrite` was
  rejected with "found no subterm matching" against a term visibly present in
  the goal — implicit type arguments elaborated differently (`qmem` versus
  `wmem qvar qtype`). The fix is always the same: replace the `rewrite` with an
  explicit `transitivity` to the intended term and close it with `apply`,
  which unifies up to conversion. Reach for that immediately rather than
  fighting the `rewrite`.
- **`JointSample` was not "about the size of `Sample1`"** — an earlier note
  in this file said that, extrapolating from the "no architectural obstacle,
  just a two-sided reindexing" observation. That part was right, but it missed
  that *both* projections would need a probability-collapse argument (`Sample1`
  only needed one, on the un-sampled side), doubling the projection proofs and
  adding an extra Fubini-regrouping layer neither of `Sample1`'s two
  projections needed on its own. Lesson: "no architectural obstacle" is not
  the same estimate as "same size" — count how many projections need a
  collapse, not just whether one does.
- **The other partial trace is not derivable from a tensor swap.** Going
  `tcp_ptrace ∘ tcp_conj Uswap` would need the swap's action on a general,
  non-product, non-pure operator, which the signature cannot compute. Hence
  `tcp_ptrace2` is a primitive, *and* (as of `Sym`) the swap-exchange fact
  needed one new axiom, `tcp_ptrace_pswap`, rather than being derivable.
- **Register associativity looked like a fork requiring a redesign; it was
  not.** Defining one-sided lifts through the side split sidesteps it entirely
  for the rules. It is still needed for `QInit1` and Lemma 32 — and, unlike
  `Sym`'s coherence problem, `op_ext_ket` only makes that one *possible*, not
  cheap; see §7d.
- **Fubini for unordered nonnegative sums is no longer a substrate concern** —
  it is proved in `Sums.v` (`tsum_tonelli`, `tsum_partition_le`). Earlier notes
  listing it as a needed axiom are obsolete.
- **`himg U (himg U S) = S` for a unitary `U` is not derivable, only one
  inequality direction is** (`himg_isometry_meet_oim` plus `oim U = htop` plus
  self-adjointness, giving `himg U (himg U S) ≤h S`). This did not block
  `Sym`, because `psat`'s obligation is an inequality in the first place — but
  it means "swapping a predicate twice gives back the original predicate" is
  *not* a lemma in this development, only "twice-swapped state satisfies the
  once-swapped predicate" is (in both directions, which is all `Sym` needs).
  If a later proof genuinely needs the equality, it will need a new axiom for
  it (the reverse `himg` inclusion for a unitary is exactly the kind of fact
  the `himg_ocomp` gap in `Theory.v` also lacks — `himg_ocomp_le` is one
  direction only).
- **`Judgment.v` is now large enough that silent name collisions are a real
  cost.** While building Lemma 36's converse a new `tcp_sep_scale` was
  written from scratch (with a `(0 <= a)%R` hypothesis) before noticing an
  *unconditional* `tcp_sep_scale` already existed, from earlier `roliftL`
  work, a few hundred lines further down the same file (bounding the
  summable-family trace via `Rabs a` instead of assuming nonnegativity).
  Rocq caught the duplicate name at compile time, not the redundant work —
  grep for a lemma's likely name before writing it, especially for anything
  shaped like "X is preserved by scaling/tensoring/conjugating".
- **The `R0`-detour pattern** (§7a): when an assembled sum's projection can't
  be related back to the original state directly from the per-component
  witnesses' own projection facts, because `denote_sum` needs the *input*
  family's joint summability and that isn't otherwise in hand, build a
  throwaway `rcqs` (here, one `rdirac` per component) whose only purpose is
  to have `rcqs_projL_sum`/`rcqs_fam_projL` invoked on it. Worth reaching for
  again rather than trying to force the closure through the witnesses alone.

---

## 9. Commit log, most recent first

Each commit message explains *why*; this is just the map.

| commit | what |
|---|---|
| `16cdd44` | `qrhl_pure_to_qrhl` — Lemma 36's converse, the main theorem |
| `11a08bc` | trace/summability helpers (`inner_rprod`, `rdirac_trace`/`cqdirac_trace`, `cqs_scale_wf`/`cqs_trace_scale`, `tcp_summable_zero`) the converse's assembly needs |
| `1c7ccae` | `pure_scaled_witness` — the converse's per-component step |
| `7dac726` | scaling preserves `rcqs_wf`/`rcqs_sep`/`psat` |
| `a7c8892` | `rsep_pure_decompose` — the spectral theorem pushed through separability |
| `76a25a3` | `rcqs_scale`, `tcp_proj_vzero`/`tcp_proj_decompose_unit`, `tcp_tensor_sum_sum`, `rprod_proj`/`rprod_normalize_total`, `cqdirac_scale` — the converse's normalization/sum-flattening building blocks |
| `8587d1e` | `denote_scale`; `tcp_scale_tensor_r` |
| `34e32a7` | `tcp_tensor_sum_l`, `tcp_proj_normalize` (steps 1-2 of the converse's plan) |
| `7f69f69` | `op_ext_ket` (replacing `op_ext`); `Sym` (Lem 44); `Urqswap`, `predswap`, `rcqs_swap`; two new axioms (`tcp_ptrace_pswap`, `tcp_conj_pswap`) |
| `3a869ab` | `JointSample` (Lem 57); `Core/Vars.v` right/cross-side `rcupd` mirrors; `Core/Judgment.v` `rbeta2`; `Substrate/Sums.v` marginals |
| `8563c58` | `JointWhile` (Lem 61) |
| `f343d18` | the three `denote` inductions now cover loops; `loopfree` retired |
| `3c22b94` | docs refresh; the register-coherence write-up |
| `98bc31f` | `QrhlElim` and its equality form (Lem 50) |
| `1287c9a` | `denote_sum` (normality) and `Case` (Lem 48) |
| `edfb058` | `Measure1` (Lem 62) |
| `6734743` | `Sample1` (Lem 56) |
| `530a960` | `If1` and `JointIf`, with no new axioms |
| `eca6235` | this file, first version |
| `c588539` | README: what each remaining Phase 1d rule needs |
| `506d4d3` | `[[c]]` is additive on the positive cone |

---

## 10. Working practices

- Commit messages: explain *why*, name the paper lemma numbers, record
  surprises. End with the `Co-Authored-By` line the session's attribution
  reminder specifies.
- Run `make audit` before every commit; `make assumptions` when the concrete
  layer changes; `make axioms` when `Interface.v` changes.
- Keep `README.md`'s status table and `AXIOMS.md`'s "not yet in the signature"
  list honest — they are the fastest way back into the project.
- The scratch paper text is recoverable with
  `pdftotext -layout qRHL.pdf -` when a lemma statement needs checking.
