# The trusted surface

Everything in this development is proved except the contents of
`theories/Substrate/Interface.v`, which is a `Module Type` declaring standard
Hilbert space theory. This file records what is assumed and why each assumption
is legitimate.

## What "trusted" means here

`HILBERT_SUBSTRATE` is a module *signature*, not a list of global axioms. Every
other file is a functor over it. Consequences:

- the development declares **no axioms of its own** — `scripts/audit.sh`
  enforces this, and `Print Assumptions` on a soundness theorem comes back
  clean;
- the dependency is structural and visible in every functor's signature;
- the claim the development supports is exactly: **if `HILBERT_SUBSTRATE` has a
  model, every qRHL rule proved here is sound.**

Phase 4 is about building a model (finite-dimensional, via mathcomp), which
turns that conditional into an unconditional statement for the
finite-dimensional fragment — which covers every example in the paper.

## The hygiene rule

> The substrate may assume textbook functional analysis.
> It may not assume anything about qRHL.

`scripts/audit.sh` checks the second half mechanically: no declaration under
`theories/Substrate/` may mention qRHL vocabulary. The first half is a human
review obligation, and the table below is what there is to review.

This is the one property that distinguishes this development from the original
`qrhl-tool`, which (§1.3 of the paper) axiomatizes *its tactics and
simplification rules* — that is, the qRHL content itself.

## Ambient logic

Separately from the substrate, the development works in classical higher-order
logic: `theories/Substrate/Ambient.v` re-exports the Rocq standard library's
axioms for the reals (`completeness`), functional and propositional
extensionality, excluded middle and Hilbert choice.

This is deliberate. Unruh's proofs, and `qrhl-tool` itself, live in
Isabelle/HOL — classical HOL with choice and extensionality. §2 of the paper is
classical throughout: arbitrary decompositions of positive operators into
rank-one projections, suprema of uncountable families, the non-separable
Schmidt decomposition, and the definition of `supp` as a least projector all
presuppose it. A constructive rendering would be a different theorem, not a
more faithful one.

## Justification by group

| group | what it assumes | standard reference |
|---|---|---|
| Vectors | `l2 X` is a complex inner-product space with the computational basis orthonormal | any functional analysis text; paper §2 |
| Subspaces | the closed subspaces form a complete lattice; membership plus extensionality | Birkhoff–von Neumann; paper §4.2 |
| `hocompl_hspan` | `(span M)^⊥ = M^⊥` | standard |
| `hocompl_invol` | `S^⊥⊥ = S` — the projection theorem | standard; the only place closedness is essentially used |
| Operators | `op X Y` is a `*`-algebra acting on `l2`, determined by its action | standard |
| `hpreim` | the preimage of a closed subspace under a bounded operator is closed | standard; makes Def. 20's `÷` definable |
| Tensor | `l2 (X * Y)` is the tensor product, with product vectors total | the paper *defines* `l2[V1] ⊗ l2[V2] := l2[V1 V2]` (§2) |
| `Ubij` | a bijection of index types induces a unitary permuting the basis | standard; subsumes `U_vars,Q` and `U_rename,σ` |
| Positive trace-class | `T⁺(X)` is an ordered cone with trace, conjugation, partial trace, arbitrary sums, and support | paper §2 |
| `tcp_decompose` | every positive trace-class operator is a sum of rank-one projections | spectral theorem; paper §2 states it |

### A scoping note on `tcp`

The paper works with all of `T(X)`; we axiomatize only the positive cone
`T⁺(X)`. Nothing in qRHL needs more — Definition 35 quantifies over `T⁺_cq`,
every statement's denotation preserves positivity, and `Pr[e : c(ρ)]` is a sum
of traces. The paper's appeal to "any operator in `T[V^qu]` can be written as a
linear combination of four `ρ_a ∈ T⁺`" (§3.4) exists only to show that fixing a
superoperator on cq basis elements fixes it everywhere; here the semantics is
defined directly on families, so that step does not arise.

## Not yet in the signature

Deliberately absent, to be added *on demand*. Each entry names the first proof
that will need it, so the cost of the next step is legible:

- **normality of `tcp_sum` for the partial traces** —
  `tcp_ptrace (tcp_sum F) = tcp_sum (tcp_ptrace ∘ F)` and its mirror. Wanted
  first by rule `Assign1`, whose witness is a sum over the preimage of a memory
  update on one side. (Normality for `tcp_conj` is already in, since
  `QApply1` needed it.)
- **Tonelli for `tcp_sum`** — that a sum over pairs may be reassociated. Same
  proof, and also the converse of Lemma 36.
- **abstract superoperators and `E ⊗ id`** — needed to apply a *channel*
  (rather than a conjugation) to one tensor factor. Rule `QInit1` needs this:
  initialization discards a register and prepares a fresh state, which is not
  a conjugation. Definition 10's locality, and hence rules `Frame` and `Equal`,
  need the same thing.
- **Schmidt decomposition** (paper Lemma 7) — Lemma 29, hence `≡quant`.
- **register associativity** — that `rolift (qidx SL P)` agrees with the
  one-sided lift `roliftL P`. Needed *only* by Lemma 32, which relates a
  one-sided lift to a quantum equality spanning both sides. The rules avoid it
  because `roliftL` is defined through the side split directly.
- **suprema of increasing bounded families** — the `while` denotation, and
  hence extending `denote_wf_trace` past loop-free programs.

Note that *Fubini for unordered nonnegative sums*, listed here previously, is
no longer needed from the signature: it is proved in
`theories/Substrate/Sums.v` (`tsum_tonelli`, `tsum_partition_le`).

## Inventory

Generated from `theories/Substrate/Interface.v` by `scripts/gen-axioms.py`
(`make axioms`). Do not edit by hand.

<!-- BEGIN GENERATED INVENTORY -->

### Vectors: the space l2(X)

| kind | name | statement |
|---|---|---|
| Parameter | `l2` | `Type -> Type` |
| Parameter | `vzero` | `forall {X}, l2 X` |
| Parameter | `vadd` | `forall {X}, l2 X -> l2 X -> l2 X` |
| Parameter | `vopp` | `forall {X}, l2 X -> l2 X` |
| Parameter | `vscale` | `forall {X}, C -> l2 X -> l2 X` |
| Parameter | `inner` | `forall {X}, l2 X -> l2 X -> C` |
| Parameter | `ket` | `forall {X}, X -> l2 X` |
| Axiom | `vadd_comm` | `forall X (u v : l2 X), vadd u v = vadd v u` |
| Axiom | `vadd_assoc` | `forall X (u v w : l2 X), vadd u (vadd v w) = vadd (vadd u v) w` |
| Axiom | `vadd_zero` | `forall X (v : l2 X), vadd v vzero = v` |
| Axiom | `vadd_opp` | `forall X (v : l2 X), vadd v (vopp v) = vzero` |
| Axiom | `vscale_1` | `forall X (v : l2 X), vscale C1 v = v` |
| Axiom | `vscale_assoc` | `forall X (a b : C) (v : l2 X), vscale a (vscale b v) = vscale (Cmult a b) v` |
| Axiom | `vscale_addv` | `forall X (a : C) (u v : l2 X), vscale a (vadd u v) = vadd (vscale a u) (vscale a v)` |
| Axiom | `vscale_adda` | `forall X (a b : C) (v : l2 X), vscale (Cplus a b) v = vadd (vscale a v) (vscale b v)` |
| Axiom | `vscale_0` | `forall X (v : l2 X), vscale C0 v = vzero` |
| Axiom | `inner_conj` | `forall X (u v : l2 X), inner u v = Cconj (inner v u)` |
| Axiom | `inner_addr` | `forall X (u v w : l2 X), inner u (vadd v w) = Cplus (inner u v) (inner u w)` |
| Axiom | `inner_scaler` | `forall X (a : C) (u v : l2 X), inner u (vscale a v) = Cmult a (inner u v)` |
| Axiom | `inner_ge0` | `forall X (v : l2 X), Cge0 (inner v v)` |
| Axiom | `inner_definite` | `forall X (v : l2 X), inner v v = C0 -> v = vzero` |
| Axiom | `inner_ket` | `forall X (x y : X), inner (ket x) (ket y) = if excluded_middle_informative (x = y) then C1 else C0` |

### Subspaces

| kind | name | statement |
|---|---|---|
| Parameter | `hspace` | `Type -> Type` |
| Parameter | `hmem` | `forall {X}, l2 X -> hspace X -> Prop` |
| Axiom | `hspace_ext` | `forall X (S T : hspace X), (forall v, hmem v S <-> hmem v T) -> S = T` |
| Axiom | `hmem_vzero` | `forall X (S : hspace X), hmem vzero S` |
| Axiom | `hmem_vadd` | `forall X (S : hspace X) (u v : l2 X), hmem u S -> hmem v S -> hmem (vadd u v) S` |
| Axiom | `hmem_vscale` | `forall X (S : hspace X) (a : C) (v : l2 X), hmem v S -> hmem (vscale a v) S` |
| Parameter | `hbot` | `forall {X}, hspace X` |
| Parameter | `htop` | `forall {X}, hspace X` |
| Parameter | `hInf` | `forall {X} {J : Type}, (J -> hspace X) -> hspace X` |
| Parameter | `hSup` | `forall {X} {J : Type}, (J -> hspace X) -> hspace X` |
| Axiom | `hmem_hbot` | `forall X (v : l2 X), hmem v hbot <-> v = vzero` |
| Axiom | `hmem_htop` | `forall X (v : l2 X), hmem v (@htop X)` |
| Axiom | `hmem_hInf` | `forall X J (F : J -> hspace X) (v : l2 X), hmem v (hInf F) <-> (forall j, hmem v (F j))` |
| Axiom | `hSup_ub` | `forall X J (F : J -> hspace X) (j : J) (v : l2 X), hmem v (F j) -> hmem v (hSup F)` |
| Axiom | `hSup_least` | `forall X J (F : J -> hspace X) (T : hspace X), (forall j v, hmem v (F j) -> hmem v T) -> (forall v, hmem v (hSup F) -> hmem v T)` |
| Parameter | `hspan` | `forall {X}, (l2 X -> Prop) -> hspace X` |
| Axiom | `hspan_ub` | `forall X (M : l2 X -> Prop) (v : l2 X), M v -> hmem v (hspan M)` |
| Axiom | `hspan_least` | `forall X (M : l2 X -> Prop) (T : hspace X), (forall v, M v -> hmem v T) -> (forall v, hmem v (hspan M) -> hmem v T)` |
| Axiom | `hspan_ket` | `forall X, hspan (fun v => exists x : X, v = ket x) = htop` |
| Parameter | `hocompl` | `forall {X}, hspace X -> hspace X` |
| Axiom | `hmem_hocompl` | `forall X (S : hspace X) (v : l2 X), hmem v (hocompl S) <-> (forall w, hmem w S -> inner w v = C0)` |
| Axiom | `hocompl_hspan` | `forall X (M : l2 X -> Prop) (v : l2 X), hmem v (hocompl (hspan M)) <-> (forall w, M w -> inner w v = C0)` |
| Axiom | `hocompl_invol` | `forall X (S : hspace X), hocompl (hocompl S) = S` |

### Bounded operators

| kind | name | statement |
|---|---|---|
| Parameter | `op` | `Type -> Type -> Type` |
| Parameter | `oapp` | `forall {X Y}, op X Y -> l2 X -> l2 Y` |
| Parameter | `oid` | `forall {X}, op X X` |
| Parameter | `ocomp` | `forall {X Y Z}, op Y Z -> op X Y -> op X Z` |
| Parameter | `oadj` | `forall {X Y}, op X Y -> op Y X` |
| Parameter | `ozero` | `forall {X Y}, op X Y` |
| Parameter | `oadd` | `forall {X Y}, op X Y -> op X Y -> op X Y` |
| Parameter | `oopp` | `forall {X Y}, op X Y -> op X Y` |
| Parameter | `oscale` | `forall {X Y}, C -> op X Y -> op X Y` |
| Axiom | `op_ext` | `forall X Y (A B : op X Y), (forall v, oapp A v = oapp B v) -> A = B` |
| Axiom | `oapp_vadd` | `forall X Y (A : op X Y) (u v : l2 X), oapp A (vadd u v) = vadd (oapp A u) (oapp A v)` |
| Axiom | `oapp_vscale` | `forall X Y (A : op X Y) (a : C) (v : l2 X), oapp A (vscale a v) = vscale a (oapp A v)` |
| Axiom | `oapp_oid` | `forall X (v : l2 X), oapp oid v = v` |
| Axiom | `oapp_ocomp` | `forall X Y Z (A : op Y Z) (B : op X Y) (v : l2 X), oapp (ocomp A B) v = oapp A (oapp B v)` |
| Axiom | `oapp_ozero` | `forall X Y (v : l2 X), oapp (@ozero X Y) v = vzero` |
| Axiom | `oapp_oadd` | `forall X Y (A B : op X Y) (v : l2 X), oapp (oadd A B) v = vadd (oapp A v) (oapp B v)` |
| Axiom | `oapp_oopp` | `forall X Y (A : op X Y) (v : l2 X), oapp (oopp A) v = vopp (oapp A v)` |
| Axiom | `oapp_oscale` | `forall X Y (a : C) (A : op X Y) (v : l2 X), oapp (oscale a A) v = vscale a (oapp A v)` |
| Axiom | `inner_oadj` | `forall X Y (A : op X Y) (v : l2 Y) (w : l2 X), inner (oapp (oadj A) v) w = inner v (oapp A w)` |

### Preimages of subspaces

| kind | name | statement |
|---|---|---|
| Parameter | `hpreim` | `forall {X Y}, op X Y -> hspace Y -> hspace X` |
| Axiom | `hmem_hpreim` | `forall X Y (A : op X Y) (S : hspace Y) (v : l2 X), hmem v (hpreim A S) <-> hmem (oapp A v) S` |

### Tensor product

| kind | name | statement |
|---|---|---|
| Parameter | `tensorv` | `forall {X Y}, l2 X -> l2 Y -> l2 (X * Y)` |
| Parameter | `tensoro` | `forall {X1 Y1 X2 Y2}, op X1 Y1 -> op X2 Y2 -> op (X1 * X2) (Y1 * Y2)` |
| Axiom | `tensorv_ket` | `forall X Y (x : X) (y : Y), tensorv (ket x) (ket y) = ket (x, y)` |
| Axiom | `tensorv_addl` | `forall X Y (u v : l2 X) (w : l2 Y), tensorv (vadd u v) w = vadd (tensorv u w) (tensorv v w)` |
| Axiom | `tensorv_addr` | `forall X Y (u : l2 X) (v w : l2 Y), tensorv u (vadd v w) = vadd (tensorv u v) (tensorv u w)` |
| Axiom | `tensorv_scalel` | `forall X Y (a : C) (u : l2 X) (w : l2 Y), tensorv (vscale a u) w = vscale a (tensorv u w)` |
| Axiom | `tensorv_scaler` | `forall X Y (a : C) (u : l2 X) (w : l2 Y), tensorv u (vscale a w) = vscale a (tensorv u w)` |
| Axiom | `inner_tensorv` | `forall X Y (u1 u2 : l2 X) (v1 v2 : l2 Y), inner (tensorv u1 v1) (tensorv u2 v2) = Cmult (inner u1 u2) (inner v1 v2)` |
| Axiom | `hspan_tensorv` | `forall X Y, hspan (fun u : l2 (X * Y) => exists v w, u = tensorv v w) = htop` |
| Axiom | `tensoro_app` | `forall X1 Y1 X2 Y2 (A : op X1 Y1) (B : op X2 Y2) v w, oapp (tensoro A B) (tensorv v w) = tensorv (oapp A v) (oapp B w)` |
| Axiom | `tensoro_oid` | `forall X Y, tensoro (@oid X) (@oid Y) = oid` |
| Axiom | `tensoro_ocomp` | `forall X1 Y1 Z1 X2 Y2 Z2 (A : op Y1 Z1) (B : op X1 Y1) (A' : op Y2 Z2) (B' : op X2 Y2), tensoro (ocomp A B) (ocomp A' B') = ocomp (tensoro A A') (tensoro B B')` |
| Axiom | `tensoro_oadj` | `forall X1 Y1 X2 Y2 (A : op X1 Y1) (B : op X2 Y2), oadj (tensoro A B) = tensoro (oadj A) (oadj B)` |
| Parameter | `otensorR` | `forall {X Y}, l2 Y -> op X (X * Y)` |
| Axiom | `otensorR_app` | `forall X Y (w : l2 Y) (v : l2 X), oapp (@otensorR X Y w) v = tensorv v w` |
| Parameter | `otensorL` | `forall {X Y}, l2 X -> op Y (X * Y)` |
| Axiom | `otensorL_app` | `forall X Y (v : l2 X) (w : l2 Y), oapp (@otensorL X Y v) w = tensorv v w` |

### Reindexing

| kind | name | statement |
|---|---|---|
| Parameter | `Ubij` | `forall {X Y} (f : X -> Y) (g : Y -> X), (forall x, g (f x) = x) -> (forall y, f (g y) = y) -> op X Y` |
| Axiom | `Ubij_ket` | `forall X Y f g H1 H2 (x : X), oapp (@Ubij X Y f g H1 H2) (ket x) = ket (f x)` |
| Axiom | `Ubij_adj` | `forall X Y f g H1 H2, oadj (@Ubij X Y f g H1 H2) = Ubij g f H2 H1` |
| Axiom | `Ubij_unitary` | `forall X Y f g H1 H2, ocomp (oadj (@Ubij X Y f g H1 H2)) (Ubij f g H1 H2) = oid /\ ocomp (Ubij f g H1 H2) (oadj (Ubij f g H1 H2)) = oid` |

### Positive trace-class operators

| kind | name | statement |
|---|---|---|
| Parameter | `tcp` | `Type -> Type` |
| Parameter | `tcp_zero` | `forall {X}, tcp X` |
| Parameter | `tcp_add` | `forall {X}, tcp X -> tcp X -> tcp X` |
| Parameter | `tcp_scale` | `forall {X}, R -> tcp X -> tcp X` |
| Parameter | `tcp_trace` | `forall {X}, tcp X -> R` |
| Parameter | `tcp_le` | `forall {X}, tcp X -> tcp X -> Prop` |
| Parameter | `tcp_proj` | `forall {X}, l2 X -> tcp X` |
| Parameter | `tcp_conj` | `forall {X Y}, op X Y -> tcp X -> tcp Y` |
| Parameter | `tcp_ptrace` | `forall {X Y}, tcp (X * Y) -> tcp X` |
| Parameter | `tcp_ptrace2` | `forall {X Y}, tcp (X * Y) -> tcp Y` |
| Parameter | `tcp_tensor` | `forall {X Y}, tcp X -> tcp Y -> tcp (X * Y)` |
| Parameter | `tcp_supp` | `forall {X}, tcp X -> hspace X` |
| Parameter | `tcp_summable` | `forall {X} {J : Type}, (J -> tcp X) -> Prop` |
| Parameter | `tcp_sum` | `forall {X} {J : Type}, (J -> tcp X) -> tcp X` |
| Axiom | `tcp_ext` | `forall X (r s : tcp X), tcp_le r s -> tcp_le s r -> r = s` |
| Axiom | `tcp_add_comm` | `forall X (r s : tcp X), tcp_add r s = tcp_add s r` |
| Axiom | `tcp_add_assoc` | `forall X (r s t : tcp X), tcp_add r (tcp_add s t) = tcp_add (tcp_add r s) t` |
| Axiom | `tcp_add_zero` | `forall X (r : tcp X), tcp_add r tcp_zero = r` |
| Axiom | `tcp_le_refl` | `forall X (r : tcp X), tcp_le r r` |
| Axiom | `tcp_le_trans` | `forall X (r s t : tcp X), tcp_le r s -> tcp_le s t -> tcp_le r t` |
| Axiom | `tcp_le_add` | `forall X (r s : tcp X), tcp_le r s <-> exists t, s = tcp_add r t` |
| Axiom | `tcp_scale_1` | `forall X (r : tcp X), tcp_scale 1 r = r` |
| Axiom | `tcp_scale_0` | `forall X (r : tcp X), tcp_scale 0 r = tcp_zero` |
| Axiom | `tcp_scale_add` | `forall X (a : R) (r s : tcp X), tcp_scale a (tcp_add r s) = tcp_add (tcp_scale a r) (tcp_scale a s)` |
| Axiom | `tcp_scale_assoc` | `forall X (a b : R) (r : tcp X), tcp_scale a (tcp_scale b r) = tcp_scale (a * b)%R r` |
| Axiom | `tcp_trace_nonneg` | `forall X (r : tcp X), (0 <= tcp_trace r)%R` |
| Axiom | `tcp_trace_zero` | `forall X, tcp_trace (@tcp_zero X) = 0%R` |
| Axiom | `tcp_trace_add` | `forall X (r s : tcp X), tcp_trace (tcp_add r s) = (tcp_trace r + tcp_trace s)%R` |
| Axiom | `tcp_trace_scale` | `forall X (a : R) (r : tcp X), tcp_trace (tcp_scale a r) = (a * tcp_trace r)%R` |
| Axiom | `tcp_trace_faithful` | `forall X (r : tcp X), tcp_trace r = 0%R -> r = tcp_zero` |
| Axiom | `tcp_trace_proj` | `forall X (v : l2 X), tcp_trace (tcp_proj v) = Cre (inner v v)` |
| Axiom | `tcp_conj_proj` | `forall X Y (A : op X Y) (v : l2 X), tcp_conj A (tcp_proj v) = tcp_proj (oapp A v)` |
| Axiom | `tcp_conj_add` | `forall X Y (A : op X Y) (r s : tcp X), tcp_conj A (tcp_add r s) = tcp_add (tcp_conj A r) (tcp_conj A s)` |
| Axiom | `tcp_conj_scale` | `forall X Y (A : op X Y) (a : R) (r : tcp X), tcp_conj A (tcp_scale a r) = tcp_scale a (tcp_conj A r)` |
| Axiom | `tcp_conj_zero` | `forall X Y (A : op X Y), tcp_conj A (@tcp_zero X) = tcp_zero` |
| Axiom | `tcp_conj_oid` | `forall X (r : tcp X), tcp_conj oid r = r` |
| Axiom | `tcp_conj_ocomp` | `forall X Y Z (A : op Y Z) (B : op X Y) (r : tcp X), tcp_conj (ocomp A B) r = tcp_conj A (tcp_conj B r)` |
| Axiom | `tcp_conj_tensor` | `forall X X' Y Y' (A : op X X') (B : op Y Y') (r : tcp X) (s : tcp Y), tcp_conj (tensoro A B) (tcp_tensor r s) = tcp_tensor (tcp_conj A r) (tcp_conj B s)` |
| Axiom | `tcp_conj_sum` | `forall X Y J (A : op X Y) (F : J -> tcp X), tcp_summable F -> tcp_conj A (tcp_sum F) = tcp_sum (fun j => tcp_conj A (F j))` |
| Axiom | `tcp_supp_conj` | `forall X Y (A : op X Y) (r : tcp X), tcp_supp (tcp_conj A r) = hspan (fun w => exists v, hmem v (tcp_supp r) /\ w = oapp A v)` |
| Axiom | `oim_isometry_fix` | `forall X Y (A : op X Y) (v : l2 Y), ocomp (oadj A) A = oid -> hmem v (hspan (fun w => exists u, w = oapp A u)) -> oapp A (oapp (oadj A) v) = v` |
| Axiom | `tcp_trace_conj_proj_le` | `forall X (A : op X X) (r : tcp X), ocomp A A = A -> oadj A = A -> (tcp_trace (tcp_conj A r) <= tcp_trace r)%R` |
| Axiom | `tcp_trace_meas_tensor` | `forall X Y (D : Type) (M : D -> op X X) (r : tcp (X * Y)), (forall z, ocomp (M z) (M z) = M z) -> (forall z, oadj (M z) = M z) -> (forall v : l2 X, summable (fun z => Cre (inner v (oapp (M z) v)))) -> (forall v : l2 X, (tsum (fun z => Cre (inner v (oapp (M z) v))) <= Cre (inner v v))%R) -> summable (fun z => tcp_trace (tcp_conj (tensoro (M z) oid) r)) /\ (tsum (fun z => tcp_trace (tcp_conj (tensoro (M z) oid) r)) <= tcp_trace r)%R` |
| Axiom | `tcp_trace_conj_isometry` | `forall X Y (A : op X Y) (r : tcp X), ocomp (oadj A) A = oid -> tcp_trace (tcp_conj A r) = tcp_trace r` |
| Axiom | `tcp_ptrace_add` | `forall X Y (r s : tcp (X * Y)), tcp_ptrace (tcp_add r s) = tcp_add (tcp_ptrace r) (tcp_ptrace s)` |
| Axiom | `tcp_ptrace_scale` | `forall X Y (a : R) (r : tcp (X * Y)), tcp_ptrace (tcp_scale a r) = tcp_scale a (tcp_ptrace r)` |
| Axiom | `tcp_ptrace_trace` | `forall X Y (r : tcp (X * Y)), tcp_trace (tcp_ptrace r) = tcp_trace r` |
| Axiom | `tcp_ptrace_tensor` | `forall X Y (r : tcp X) (s : tcp Y), tcp_ptrace (tcp_tensor r s) = tcp_scale (tcp_trace s) r` |
| Axiom | `tcp_ptrace2_add` | `forall X Y (r s : tcp (X * Y)), tcp_ptrace2 (tcp_add r s) = tcp_add (tcp_ptrace2 r) (tcp_ptrace2 s)` |
| Axiom | `tcp_ptrace2_scale` | `forall X Y (a : R) (r : tcp (X * Y)), tcp_ptrace2 (tcp_scale a r) = tcp_scale a (tcp_ptrace2 r)` |
| Axiom | `tcp_ptrace2_trace` | `forall X Y (r : tcp (X * Y)), tcp_trace (tcp_ptrace2 r) = tcp_trace r` |
| Axiom | `tcp_ptrace2_tensor` | `forall X Y (r : tcp X) (s : tcp Y), tcp_ptrace2 (tcp_tensor r s) = tcp_scale (tcp_trace r) s` |
| Axiom | `tcp_ptrace_sum` | `forall X Y J (F : J -> tcp (X * Y)), tcp_summable F -> tcp_ptrace (tcp_sum F) = tcp_sum (fun j => tcp_ptrace (F j))` |
| Axiom | `tcp_ptrace2_sum` | `forall X Y J (F : J -> tcp (X * Y)), tcp_summable F -> tcp_ptrace2 (tcp_sum F) = tcp_sum (fun j => tcp_ptrace2 (F j))` |
| Axiom | `tcp_ptrace_conj_tensorL` | `forall X X' Y (A : op X X') (r : tcp (X * Y)), tcp_ptrace (tcp_conj (tensoro A oid) r) = tcp_conj A (tcp_ptrace r)` |
| Axiom | `tcp_ptrace2_conj_tensorL` | `forall X X' Y (A : op X X') (r : tcp (X * Y)), ocomp (oadj A) A = oid -> tcp_ptrace2 (tcp_conj (tensoro A oid) r) = tcp_ptrace2 r` |
| Axiom | `tcp_ptrace2_conj_tensorR` | `forall X Y Y' (B : op Y Y') (r : tcp (X * Y)), tcp_ptrace2 (tcp_conj (tensoro oid B) r) = tcp_conj B (tcp_ptrace2 r)` |
| Axiom | `tcp_ptrace_conj_tensorR` | `forall X Y Y' (B : op Y Y') (r : tcp (X * Y)), ocomp (oadj B) B = oid -> tcp_ptrace (tcp_conj (tensoro oid B) r) = tcp_ptrace r` |
| Axiom | `tcp_tensor_proj` | `forall X Y (v : l2 X) (w : l2 Y), tcp_tensor (tcp_proj v) (tcp_proj w) = tcp_proj (tensorv v w)` |
| Axiom | `tcp_summable_trace` | `forall X J (F : J -> tcp X), tcp_summable F <-> summable (fun j => tcp_trace (F j))` |
| Axiom | `tcp_trace_sum` | `forall X J (F : J -> tcp X), tcp_summable F -> tcp_trace (tcp_sum F) = tsum (fun j => tcp_trace (F j))` |
| Axiom | `tcp_sum_ub` | `forall X J (F : J -> tcp X) (l : list J), tcp_summable F -> NoDup l -> tcp_le (tcp_lsum F l) (tcp_sum F)` |
| Axiom | `tcp_sum_least` | `forall X J (F : J -> tcp X) (s : tcp X), tcp_summable F -> (forall l, NoDup l -> tcp_le (tcp_lsum F l) s) -> tcp_le (tcp_sum F) s` |
| Axiom | `tcp_sum_not_summable` | `forall X J (F : J -> tcp X), ~ tcp_summable F -> tcp_sum F = tcp_zero` |
| Axiom | `tcp_sum_bij` | `forall X (I J : Type) (h : J -> I) (g : I -> J) (F : I -> tcp X), (forall j, g (h j) = j) -> (forall i, h (g i) = i) -> tcp_summable F -> tcp_summable (fun j => F (h j)) /\ tcp_sum (fun j => F (h j)) = tcp_sum F` |
| Axiom | `tcp_sum_sigma` | `forall X (K : Type) (Pk : K -> Type) (F : forall k, Pk k -> tcp X), (forall k, tcp_summable (F k)) -> tcp_summable (fun k => tcp_sum (F k)) -> tcp_summable (fun p : sigT Pk => F (projT1 p) (projT2 p)) /\ tcp_sum (fun k => tcp_sum (F k)) = tcp_sum (fun p : sigT Pk => F (projT1 p) (projT2 p))` |
| Axiom | `tcp_supp_eq0` | `forall X (r : tcp X), tcp_supp r = hbot <-> r = tcp_zero` |
| Axiom | `tcp_supp_proj` | `forall X (v : l2 X), tcp_supp (tcp_proj v) = hspan (fun u => u = v)` |
| Axiom | `tcp_supp_add` | `forall X (r s : tcp X), tcp_supp (tcp_add r s) = hSup (fun b : bool => if b then tcp_supp r else tcp_supp s)` |
| Axiom | `tcp_supp_scale` | `forall X (a : R) (r : tcp X), (0 < a)%R -> tcp_supp (tcp_scale a r) = tcp_supp r` |
| Axiom | `tcp_supp_sum` | `forall X J (F : J -> tcp X), tcp_summable F -> tcp_supp (tcp_sum F) = hSup (fun j => tcp_supp (F j))` |
| Axiom | `tcp_decompose` | `forall X (r : tcp X), exists (J : Type) (psi : J -> l2 X), tcp_summable (fun j => tcp_proj (psi j)) /\ r = tcp_sum (fun j => tcp_proj (psi j))` |

**Totals: 44 parameters, 115 axioms.**

<!-- END GENERATED INVENTORY -->
