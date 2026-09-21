(** * The substrate signature: standard Hilbert space theory, assumed.

    ================================================================
    THIS FILE IS THE ENTIRE TRUSTED SURFACE OF THE DEVELOPMENT.
    ================================================================

    Everything else is proved. The architectural bet of the project is the line
    drawn here:

      the substrate may assume textbook functional analysis;
      it may not assume anything about qRHL.

    [scripts/audit.sh] enforces the second half mechanically. The first half is
    a review obligation: every axiom below should be a statement you could cite
    a functional analysis textbook for, and [AXIOMS.md] records the citation.

    Because this is a [Module Type] rather than a list of [Axiom]s, the
    development contains *no axioms*: the dependency is structural, visible in
    the signature of every functor, and [Print Assumptions] on a rule's
    soundness proof comes back clean. The claim the development supports is
    therefore precise -- *if the substrate has a model, every rule is sound* --
    and Phase 4 is about building one.

    Design notes, in order of how much work they save:

    - We axiomatize [l2 X] for an arbitrary index type [X] directly, rather
      than an abstract category of Hilbert spaces. This follows the paper
      (section 2) and makes the tensor product concrete: the paper *defines*
      [l2[V1] (x) l2[V2] := l2[V1 V2]], so here [l2 (X * Y)] plays the role of
      [l2 X (x) l2 Y] and the tensor product is automatically commutative and
      associative up to reindexing.

    - All reindexing -- associativity and commutativity of the tensor, the
      variable isomorphisms [U_vars,Q], and the renamings [U_rename,sigma] --
      is handled by the single combinator [Ubij], which turns a bijection of
      index types into a unitary. The paper spends considerable notational
      effort on these (section 2, "A note on notation"); here they are one
      mechanism with one set of laws.

    - Subspaces are given by a membership predicate plus extensionality, not by
      a list of lattice laws. Almost every lattice fact is then a theorem
      rather than an axiom, which both shrinks the trusted surface and reduces
      the chance of an inconsistent signature.

    Naming: [v] for vectors, [A] [B] for operators, [S] [T] for subspaces,
    [X] [Y] [Z] for index types. *)

From Stdlib Require Import List.
From QRHL.Substrate Require Import Ambient Cnum Sums.

Module Type HILBERT_SUBSTRATE.

  (* ================================================================= *)
  (** ** Vectors: the space l2(X) *)

  (** [l2 X] is the Hilbert space of square-summable functions [X -> C]; the
      paper's [l2(X)], and for [X = Type^set_V], the paper's [l2[V]]. *)
  Parameter l2 : Type -> Type.

  Parameter vzero  : forall {X}, l2 X.
  Parameter vadd   : forall {X}, l2 X -> l2 X -> l2 X.
  Parameter vopp   : forall {X}, l2 X -> l2 X.
  Parameter vscale : forall {X}, C -> l2 X -> l2 X.

  (** The inner product, conjugate-linear in its *first* argument (the physics
      convention, matching the paper's use of [psi psi^*]). *)
  Parameter inner : forall {X}, l2 X -> l2 X -> C.

  (** The computational basis: the paper's [|x>]. *)
  Parameter ket : forall {X}, X -> l2 X.

  (** *** Vector space laws *)

  Axiom vadd_comm  : forall X (u v : l2 X), vadd u v = vadd v u.
  Axiom vadd_assoc : forall X (u v w : l2 X), vadd u (vadd v w) = vadd (vadd u v) w.
  Axiom vadd_zero  : forall X (v : l2 X), vadd v vzero = v.
  Axiom vadd_opp   : forall X (v : l2 X), vadd v (vopp v) = vzero.

  Axiom vscale_1     : forall X (v : l2 X), vscale C1 v = v.
  Axiom vscale_assoc : forall X (a b : C) (v : l2 X),
      vscale a (vscale b v) = vscale (Cmult a b) v.
  Axiom vscale_addv  : forall X (a : C) (u v : l2 X),
      vscale a (vadd u v) = vadd (vscale a u) (vscale a v).
  Axiom vscale_adda  : forall X (a b : C) (v : l2 X),
      vscale (Cplus a b) v = vadd (vscale a v) (vscale b v).
  Axiom vscale_0     : forall X (v : l2 X), vscale C0 v = vzero.

  (** *** Inner product laws *)

  Axiom inner_conj : forall X (u v : l2 X), inner u v = Cconj (inner v u).
  Axiom inner_addr : forall X (u v w : l2 X),
      inner u (vadd v w) = Cplus (inner u v) (inner u w).
  Axiom inner_scaler : forall X (a : C) (u v : l2 X),
      inner u (vscale a v) = Cmult a (inner u v).

  (** Positive definiteness. [Cge0] is from [Cnum]: real and nonnegative. *)
  Axiom inner_ge0 : forall X (v : l2 X), Cge0 (inner v v).
  Axiom inner_definite : forall X (v : l2 X), inner v v = C0 -> v = vzero.

  (** The computational basis is orthonormal (section 2: "The vectors [|x>]
      with [x in X] form a basis of [l2(X)], the computational basis"). *)
  Axiom inner_ket : forall X (x y : X),
      inner (ket x) (ket y) = if excluded_middle_informative (x = y) then C1 else C0.

  (* ================================================================= *)
  (** ** Subspaces

      "The word subspace always refers to a topologically closed subspace"
      (section 2). Predicates in the sense of Definition 13 are valued in
      [hspace]. *)

  Parameter hspace : Type -> Type.
  Parameter hmem   : forall {X}, l2 X -> hspace X -> Prop.

  (** Extensionality. With this, subspace equality is membership equivalence
      and the lattice laws below become provable rather than assumed. *)
  Axiom hspace_ext : forall X (S T : hspace X),
      (forall v, hmem v S <-> hmem v T) -> S = T.

  (** Subspaces are linear subspaces. (Closedness is not expressible as a
      membership law; it enters through [hocompl_invol] below, which is
      equivalent to the projection theorem.) *)
  Axiom hmem_vzero  : forall X (S : hspace X), hmem vzero S.
  Axiom hmem_vadd   : forall X (S : hspace X) (u v : l2 X),
      hmem u S -> hmem v S -> hmem (vadd u v) S.
  Axiom hmem_vscale : forall X (S : hspace X) (a : C) (v : l2 X),
      hmem v S -> hmem (vscale a v) S.

  (** *** The complete lattice

      The rules need *arbitrary* meets and joins, not just binary ones: rule
      Measure1 intersects over [z in Type_x], rule Sample1 over [z in supp e],
      and rule JointMeasure over a relation [f]. So the lattice is complete,
      with [J] an arbitrary index type. *)

  Parameter hbot : forall {X}, hspace X.
  Parameter htop : forall {X}, hspace X.
  Parameter hInf : forall {X} {J : Type}, (J -> hspace X) -> hspace X.
  Parameter hSup : forall {X} {J : Type}, (J -> hspace X) -> hspace X.

  Axiom hmem_hbot : forall X (v : l2 X), hmem v hbot <-> v = vzero.
  Axiom hmem_htop : forall X (v : l2 X), hmem v (@htop X).

  (** Meets are pointwise: an intersection of closed subspaces is closed. *)
  Axiom hmem_hInf : forall X J (F : J -> hspace X) (v : l2 X),
      hmem v (hInf F) <-> (forall j, hmem v (F j)).

  (** Joins are *not* pointwise -- the paper's [sum_i M_i := span (union_i M_i)]
      -- so they are characterized as least upper bounds instead. *)
  Axiom hSup_ub : forall X J (F : J -> hspace X) (j : J) (v : l2 X),
      hmem v (F j) -> hmem v (hSup F).
  Axiom hSup_least : forall X J (F : J -> hspace X) (T : hspace X),
      (forall j v, hmem v (F j) -> hmem v T) ->
      (forall v, hmem v (hSup F) -> hmem v T).

  (** *** Span

      The least closed subspace containing a set of vectors (section 2:
      "For [M subset l2(X)], [span M] denotes the smallest subspace of [l2(X)]
      containing [M]"). *)

  Parameter hspan : forall {X}, (l2 X -> Prop) -> hspace X.

  Axiom hspan_ub : forall X (M : l2 X -> Prop) (v : l2 X),
      M v -> hmem v (hspan M).
  Axiom hspan_least : forall X (M : l2 X -> Prop) (T : hspace X),
      (forall v, M v -> hmem v T) -> (forall v, hmem v (hspan M) -> hmem v T).

  (** The computational basis is total: its span is everything. *)
  Axiom hspan_ket : forall X,
      hspan (fun v => exists x : X, v = ket x) = htop.

  (** *** Orthogonal complement

      Membership is definitional; the content is [hocompl_invol], which is the
      projection theorem and the only place closedness is really used. *)

  Parameter hocompl : forall {X}, hspace X -> hspace X.

  Axiom hmem_hocompl : forall X (S : hspace X) (v : l2 X),
      hmem v (hocompl S) <-> (forall w, hmem w S -> inner w v = C0).

  (** [(span M)^perp = M^perp]: a vector orthogonal to a set is orthogonal to
      its closed span. Needed because [hocompl] is the only way to *produce* a
      subspace from an orthogonality condition, and several derived facts
      (De Morgan, in particular) need the subspace [{w : <w,v> = 0}]. *)
  Axiom hocompl_hspan : forall X (M : l2 X -> Prop) (v : l2 X),
      hmem v (hocompl (hspan M)) <-> (forall w, M w -> inner w v = C0).

  (** Projection theorem. Equivalent to: every closed subspace of a Hilbert
      space is the range of an orthogonal projection. *)
  Axiom hocompl_invol : forall X (S : hspace X), hocompl (hocompl S) = S.

  (* ================================================================= *)
  (** ** Bounded operators

      [op X Y] is the paper's [B(X,Y)]: bounded linear operators
      [l2 X -> l2 Y]. We never need to *define* an operator by a formula --
      operators either come from the substrate's combinators or are supplied by
      the program being verified -- so boundedness never has to be checked. *)

  Parameter op : Type -> Type -> Type.

  Parameter oapp   : forall {X Y}, op X Y -> l2 X -> l2 Y.
  Parameter oid    : forall {X}, op X X.
  Parameter ocomp  : forall {X Y Z}, op Y Z -> op X Y -> op X Z.
  Parameter oadj   : forall {X Y}, op X Y -> op Y X.
  Parameter ozero  : forall {X Y}, op X Y.
  Parameter oadd   : forall {X Y}, op X Y -> op X Y -> op X Y.
  Parameter oopp   : forall {X Y}, op X Y -> op X Y.
  Parameter oscale : forall {X Y}, C -> op X Y -> op X Y.

  (** Operators are determined by their action on the computational basis --
      the totality of an orthonormal basis. This is strictly stronger than
      extensionality over *all* vectors (which it implies, by specializing to
      [v := ket x]): agreeing on a spanning set forces agreement everywhere,
      including on vectors -- infinite sums of kets -- that are not
      themselves finite combinations of basis vectors. That gap is exactly
      the continuity [Ubij_unitary]'s comment declines to expose, so unlike
      that axiom this one cannot be derived and has to be assumed directly.

      What it buys: every unitary in the development ([Wsplit], [Urqpair],
      the register reassociations, the side swap) is a [Ubij] or a [tensoro]
      of [Ubij]s, and those send kets to kets (see [Ubij_ket] below and
      [tensoro_app] combined with [tensorv_ket]), so any identity between
      *composites* of them becomes an index-level computation instead of an
      analytic one. *)
  Axiom op_ext_ket : forall X Y (A B : op X Y),
      (forall x : X, oapp A (ket x) = oapp B (ket x)) -> A = B.

  Axiom oapp_vadd : forall X Y (A : op X Y) (u v : l2 X),
      oapp A (vadd u v) = vadd (oapp A u) (oapp A v).
  Axiom oapp_vscale : forall X Y (A : op X Y) (a : C) (v : l2 X),
      oapp A (vscale a v) = vscale a (oapp A v).

  Axiom oapp_oid   : forall X (v : l2 X), oapp oid v = v.
  Axiom oapp_ocomp : forall X Y Z (A : op Y Z) (B : op X Y) (v : l2 X),
      oapp (ocomp A B) v = oapp A (oapp B v).
  Axiom oapp_ozero : forall X Y (v : l2 X), oapp (@ozero X Y) v = vzero.
  Axiom oapp_oadd  : forall X Y (A B : op X Y) (v : l2 X),
      oapp (oadd A B) v = vadd (oapp A v) (oapp B v).
  Axiom oapp_oopp  : forall X Y (A : op X Y) (v : l2 X),
      oapp (oopp A) v = vopp (oapp A v).
  Axiom oapp_oscale : forall X Y (a : C) (A : op X Y) (v : l2 X),
      oapp (oscale a A) v = vscale a (oapp A v).

  (** The defining property of the adjoint. *)
  Axiom inner_oadj : forall X Y (A : op X Y) (v : l2 Y) (w : l2 X),
      inner (oapp (oadj A) v) w = inner v (oapp A w).

  (* ================================================================= *)
  (** ** Preimages of subspaces

      The preimage of a closed subspace under a bounded operator is a closed
      subspace. This is what makes the paper's "division" [A / psi]
      (Definition 20) definable: see [Substrate/Theory.v]. Stated generically
      here, as substrate hygiene requires. *)

  Parameter hpreim : forall {X Y}, op X Y -> hspace Y -> hspace X.

  Axiom hmem_hpreim : forall X Y (A : op X Y) (S : hspace Y) (v : l2 X),
      hmem v (hpreim A S) <-> hmem (oapp A v) S.

  (* ================================================================= *)
  (** ** Tensor product

      Following the paper's definition [l2[V1] (x) l2[V2] := l2[V1 V2]], the
      tensor of [l2 X] and [l2 Y] *is* [l2 (X * Y)]. *)

  Parameter tensorv : forall {X Y}, l2 X -> l2 Y -> l2 (X * Y).
  Parameter tensoro : forall {X1 Y1 X2 Y2},
      op X1 Y1 -> op X2 Y2 -> op (X1 * X2) (Y1 * Y2).

  (** [(psi (x) phi)(m1 m2) := psi(m1) phi(m2)], read off on the basis. *)
  Axiom tensorv_ket : forall X Y (x : X) (y : Y),
      tensorv (ket x) (ket y) = ket (x, y).

  Axiom tensorv_addl : forall X Y (u v : l2 X) (w : l2 Y),
      tensorv (vadd u v) w = vadd (tensorv u w) (tensorv v w).
  Axiom tensorv_addr : forall X Y (u : l2 X) (v w : l2 Y),
      tensorv u (vadd v w) = vadd (tensorv u v) (tensorv u w).
  Axiom tensorv_scalel : forall X Y (a : C) (u : l2 X) (w : l2 Y),
      tensorv (vscale a u) w = vscale a (tensorv u w).
  Axiom tensorv_scaler : forall X Y (a : C) (u : l2 X) (w : l2 Y),
      tensorv u (vscale a w) = vscale a (tensorv u w).

  Axiom inner_tensorv : forall X Y (u1 u2 : l2 X) (v1 v2 : l2 Y),
      inner (tensorv u1 v1) (tensorv u2 v2) = Cmult (inner u1 u2) (inner v1 v2).

  (** Product vectors are total in the tensor product. *)
  Axiom hspan_tensorv : forall X Y,
      hspan (fun u : l2 (X * Y) => exists v w, u = tensorv v w) = htop.

  (** [(A (x) B)(psi (x) phi) := A psi (x) B phi] (section 2). *)
  Axiom tensoro_app : forall X1 Y1 X2 Y2 (A : op X1 Y1) (B : op X2 Y2) v w,
      oapp (tensoro A B) (tensorv v w) = tensorv (oapp A v) (oapp B w).

  Axiom tensoro_oid : forall X Y, tensoro (@oid X) (@oid Y) = oid.
  Axiom tensoro_ocomp : forall X1 Y1 Z1 X2 Y2 Z2
      (A : op Y1 Z1) (B : op X1 Y1) (A' : op Y2 Z2) (B' : op X2 Y2),
      tensoro (ocomp A B) (ocomp A' B') = ocomp (tensoro A A') (tensoro B B').
  Axiom tensoro_oadj : forall X1 Y1 X2 Y2 (A : op X1 Y1) (B : op X2 Y2),
      oadj (tensoro A B) = tensoro (oadj A) (oadj B).

  (** Tensoring on the right with a fixed vector is a bounded operator; this is
      the map whose preimage gives the paper's [A / psi]. *)
  Parameter otensorR : forall {X Y}, l2 Y -> op X (X * Y).
  Axiom otensorR_app : forall X Y (w : l2 Y) (v : l2 X),
      oapp (@otensorR X Y w) v = tensorv v w.

  (** ... and on the left. Definition 20 divides by a state on the register,
      which sits in the *first* factor. *)
  Parameter otensorL : forall {X Y}, l2 X -> op Y (X * Y).
  Axiom otensorL_app : forall X Y (v : l2 X) (w : l2 Y),
      oapp (@otensorL X Y v) w = tensorv v w.

  (* ================================================================= *)
  (** ** Reindexing

      One combinator for every isomorphism in the paper: the associativity and
      commutativity of [(x)], the variable isomorphisms [U_vars,Q]
      (Definition 19), and the renamings [U_rename,sigma] (section 2). A
      bijection of index types induces a unitary, acting by permuting the
      computational basis.

      Inverses are given explicitly rather than through [bijective] plus
      choice, so that the induced unitary is a function of the data. *)

  Parameter Ubij : forall {X Y} (f : X -> Y) (g : Y -> X),
      (forall x, g (f x) = x) -> (forall y, f (g y) = y) -> op X Y.

  Axiom Ubij_ket : forall X Y f g H1 H2 (x : X),
      oapp (@Ubij X Y f g H1 H2) (ket x) = ket (f x).

  Axiom Ubij_adj : forall X Y f g H1 H2,
      oadj (@Ubij X Y f g H1 H2) = Ubij g f H2 H1.

  (** A permutation of an orthonormal basis extends to a unitary. Stated rather
      than derived: deriving it from [Ubij_ket] needs the continuity of the
      inner product, which the signature deliberately does not expose. *)
  Axiom Ubij_unitary : forall X Y f g H1 H2,
      ocomp (oadj (@Ubij X Y f g H1 H2)) (Ubij f g H1 H2) = oid /\
      ocomp (Ubij f g H1 H2) (oadj (Ubij f g H1 H2)) = oid.

  (* ================================================================= *)
  (** ** Positive trace-class operators

      The paper's [T^+(X)]: "the set of all mixed quantum states that a memory
      with variables V can be in" (section 2).

      DESIGN NOTE. The paper works with all of [T(X)] and takes superoperators
      to be linear maps on it. We axiomatize only the *positive cone*
      [T^+(X)]. Nothing in qRHL needs more: Definition 35 quantifies over
      [T^+_cq], the denotations of all eight statements map positive operators
      to positive operators (conjugation, partial trace, restriction and convex
      combination all preserve positivity), and [Pr[e : c(rho)]] is a sum of
      traces. The paper's appeal to "any operator in [T[V^qu]] can be written as
      a linear combination of four [rho_a in T^+]" (section 3.4) exists only to
      show that fixing a superoperator on cq basis elements fixes it
      everywhere; in our representation the semantics is defined directly on
      families, so that step is not needed.

      The saving is real: no signed or complex operator order, no Jordan
      decomposition, and positivity is a property of the type rather than a
      side condition on every lemma. *)

  Parameter tcp : Type -> Type.

  Parameter tcp_zero  : forall {X}, tcp X.
  Parameter tcp_add   : forall {X}, tcp X -> tcp X -> tcp X.
  (** Scaling by a *nonnegative* real; the only scalars qRHL ever applies to
      states are probabilities. *)
  Parameter tcp_scale : forall {X}, R -> tcp X -> tcp X.
  Parameter tcp_trace : forall {X}, tcp X -> R.
  Parameter tcp_le    : forall {X}, tcp X -> tcp X -> Prop.

  (** [proj(psi) := psi psi^*] (section 2). *)
  Parameter tcp_proj : forall {X}, l2 X -> tcp X.

  (** [rho |-> A rho A^*]: the action of quantum application and of the
      projectors in a measurement. *)
  Parameter tcp_conj : forall {X Y}, op X Y -> tcp X -> tcp Y.

  (** The paper's [tr^[X]_Y : T[X Y] -> T[X]] (section 2), discarding the
      second factor ... *)
  Parameter tcp_ptrace : forall {X Y}, tcp (X * Y) -> tcp X.

  (** ... and the same discarding the first. Both orientations are needed --
      Definition 35 takes [tr^[V1]_V2] and [tr^[V2]_V1] of the same state --
      and the second is not derivable from the first plus a tensor swap: that
      route would need the swap's action on a general (non-product, non-pure)
      operator, which the signature has no way to compute. Axiomatizing the
      partial trace over either factor is equally textbook. *)
  Parameter tcp_ptrace2 : forall {X Y}, tcp (X * Y) -> tcp Y.

  Parameter tcp_tensor : forall {X Y}, tcp X -> tcp Y -> tcp (X * Y).

  (** [supp rho], the image of the least projector [P] with [P rho P = rho]
      (section 2). This is what Definition 14 uses to say a state satisfies a
      predicate. *)
  Parameter tcp_supp : forall {X}, tcp X -> hspace X.

  (** *** Sums over arbitrary index sets

      "When we write [sum_{i in I} rho_i] we do not assume a finite or countable
      set [I]. [sum_i rho_i] is defined as the least upper bound of
      [sum_{i in J} rho_i] where [J] ranges over all finite subsets of [I].
      [sum_i rho_i in T^+(X)] exists iff [sum_i tr rho_i] exists" (section 2).

      Total by fiat, junk [tcp_zero] when not summable, exactly as [tsum]. *)

  Parameter tcp_summable : forall {X} {J : Type}, (J -> tcp X) -> Prop.
  Parameter tcp_sum : forall {X} {J : Type}, (J -> tcp X) -> tcp X.

  (** Finite partial sums, over a duplicate-free list of indices. A plain
      definition, not an assumption -- it is here rather than in [Theory.v]
      only so that the axioms below can mention it. *)
  Definition tcp_lsum {X J} (F : J -> tcp X) (l : list J) : tcp X :=
    fold_right (fun j acc => tcp_add (F j) acc) tcp_zero l.

  (** *** Laws *)

  Axiom tcp_ext : forall X (r s : tcp X),
      tcp_le r s -> tcp_le s r -> r = s.

  Axiom tcp_add_comm  : forall X (r s : tcp X), tcp_add r s = tcp_add s r.
  Axiom tcp_add_assoc : forall X (r s t : tcp X),
      tcp_add r (tcp_add s t) = tcp_add (tcp_add r s) t.
  Axiom tcp_add_zero  : forall X (r : tcp X), tcp_add r tcp_zero = r.

  Axiom tcp_le_refl  : forall X (r : tcp X), tcp_le r r.
  Axiom tcp_le_trans : forall X (r s t : tcp X),
      tcp_le r s -> tcp_le s t -> tcp_le r t.
  (** The order is the one generated by addition: [r <= s] iff [s] is [r] plus
      something positive. *)
  Axiom tcp_le_add : forall X (r s : tcp X),
      tcp_le r s <-> exists t, s = tcp_add r t.

  Axiom tcp_scale_1    : forall X (r : tcp X), tcp_scale 1 r = r.
  Axiom tcp_scale_0    : forall X (r : tcp X), tcp_scale 0 r = tcp_zero.
  Axiom tcp_scale_add  : forall X (a : R) (r s : tcp X),
      tcp_scale a (tcp_add r s) = tcp_add (tcp_scale a r) (tcp_scale a s).
  Axiom tcp_scale_assoc : forall X (a b : R) (r : tcp X),
      tcp_scale a (tcp_scale b r) = tcp_scale (a * b)%R r.

  (** *** Trace *)

  Axiom tcp_trace_nonneg : forall X (r : tcp X), (0 <= tcp_trace r)%R.
  Axiom tcp_trace_zero   : forall X, tcp_trace (@tcp_zero X) = 0%R.
  Axiom tcp_trace_add    : forall X (r s : tcp X),
      tcp_trace (tcp_add r s) = (tcp_trace r + tcp_trace s)%R.
  Axiom tcp_trace_scale  : forall X (a : R) (r : tcp X),
      tcp_trace (tcp_scale a r) = (a * tcp_trace r)%R.
  (** Faithfulness: a positive operator of trace zero is zero. *)
  Axiom tcp_trace_faithful : forall X (r : tcp X),
      tcp_trace r = 0%R -> r = tcp_zero.
  Axiom tcp_trace_proj : forall X (v : l2 X),
      tcp_trace (tcp_proj v) = Cre (inner v v).

  (** Scaling a vector rescales its rank-one projection by the squared
      modulus: [proj(a.v) = |a|^2 . proj(v)] (textbook -- this is literally
      what [tcp_proj v := |v><v|] means). It is what lets [Lemma 36]'s
      converse normalize the (generally unnormalized) vectors [tcp_decompose]
      hands back. *)
  Axiom tcp_proj_vscale : forall X (a : C) (v : l2 X),
      tcp_proj (vscale a v) = tcp_scale (Csqmod a) (tcp_proj v).

  (** *** Conjugation *)

  Axiom tcp_conj_proj : forall X Y (A : op X Y) (v : l2 X),
      tcp_conj A (tcp_proj v) = tcp_proj (oapp A v).
  Axiom tcp_conj_add : forall X Y (A : op X Y) (r s : tcp X),
      tcp_conj A (tcp_add r s) = tcp_add (tcp_conj A r) (tcp_conj A s).
  Axiom tcp_conj_scale : forall X Y (A : op X Y) (a : R) (r : tcp X),
      tcp_conj A (tcp_scale a r) = tcp_scale a (tcp_conj A r).
  Axiom tcp_conj_zero : forall X Y (A : op X Y),
      tcp_conj A (@tcp_zero X) = tcp_zero.
  Axiom tcp_conj_oid : forall X (r : tcp X), tcp_conj oid r = r.
  Axiom tcp_conj_ocomp : forall X Y Z (A : op Y Z) (B : op X Y) (r : tcp X),
      tcp_conj (ocomp A B) r = tcp_conj A (tcp_conj B r).

  (** Conjugation respects the tensor. *)
  Axiom tcp_conj_tensor : forall X X' Y Y' (A : op X X') (B : op Y Y')
                                 (r : tcp X) (s : tcp Y),
      tcp_conj (tensoro A B) (tcp_tensor r s)
      = tcp_tensor (tcp_conj A r) (tcp_conj B s).

  (** Normality: conjugation commutes with the suprema that define infinite
      sums. This is what lets a state written as a sum be pushed through an
      operation, and it is needed by every rule that builds a witness. *)
  Axiom tcp_conj_sum : forall X Y J (A : op X Y) (F : J -> tcp X),
      tcp_summable F ->
      tcp_conj A (tcp_sum F) = tcp_sum (fun j => tcp_conj A (F j)).

  (** The support of a conjugate is the image of the support. *)
  Axiom tcp_supp_conj : forall X Y (A : op X Y) (r : tcp X),
      tcp_supp (tcp_conj A r)
      = hspan (fun w => exists v, hmem v (tcp_supp r) /\ w = oapp A v).
  (** The range of an isometry is closed, so [A A^*] acts as the identity on
      it. (The image is written out as the span of the range, which is how
      [im A] is defined downstream.) *)
  Axiom oim_isometry_fix : forall X Y (A : op X Y) (v : l2 Y),
      ocomp (oadj A) A = oid ->
      hmem v (hspan (fun w => exists u, w = oapp A u)) ->
      oapp A (oapp (oadj A) v) = v.

  (** A projector is the identity on its image (whose closedness is the
      content). The companion of [oim_isometry_fix]. *)
  Axiom oim_proj_fix : forall X (P : op X X) (v : l2 X),
      ocomp P P = P -> oadj P = P ->
      hmem v (hspan (fun w => exists u, w = oapp P u)) -> oapp P v = v.

  (** [Meas(D, X) (x) id ⊆ Meas(D, X (x) Y)]: the measurement bound survives
      tensoring with the identity. This is the inner-product companion of
      [tcp_trace_meas_tensor] below; it is what lets a measurement on a
      register be read as a measurement on the whole memory. *)
  Axiom meas_bound_tensor :
    forall X Y (D : Type) (M : D -> op X X),
      (forall v : l2 X, summable (fun z => Cre (inner v (oapp (M z) v)))) ->
      (forall v : l2 X,
          (tsum (fun z => Cre (inner v (oapp (M z) v))) <= Cre (inner v v))%R) ->
      (forall w : l2 (X * Y),
          summable (fun z => Cre (inner w (oapp (tensoro (M z) oid) w)))) /\
      (forall w : l2 (X * Y),
          (tsum (fun z => Cre (inner w (oapp (tensoro (M z) oid) w)))
           <= Cre (inner w w))%R).

  (** Totality of a projective measurement likewise survives tensoring with the
      identity. *)
  Axiom meas_total_tensor :
    forall X Y (D : Type) (M : D -> op X X),
      (forall v : l2 X, summable (fun z => Cre (inner v (oapp (M z) v)))) ->
      (forall v : l2 X,
          tsum (fun z => Cre (inner v (oapp (M z) v))) = Cre (inner v v)) ->
      (forall w : l2 (X * Y),
          summable (fun z => Cre (inner w (oapp (tensoro (M z) oid) w)))) /\
      (forall w : l2 (X * Y),
          tsum (fun z => Cre (inner w (oapp (tensoro (M z) oid) w)))
          = Cre (inner w w)).

  (** A *total* projective measurement on the first factor is trace-preserving
      there, so it leaves the second factor's reduced state unchanged. This is
      what makes the right-hand projection of rule Measure1 come back
      unchanged, and it is why the rule requires the measurement to be
      total. *)
  Axiom tcp_ptrace2_meas_tensor :
    forall X Y (D : Type) (M : D -> op X X) (r : tcp (X * Y)),
      (forall z, ocomp (M z) (M z) = M z) ->
      (forall z, oadj (M z) = M z) ->
      (forall v : l2 X, summable (fun z => Cre (inner v (oapp (M z) v)))) ->
      (forall v : l2 X,
          tsum (fun z => Cre (inner v (oapp (M z) v))) = Cre (inner v v)) ->
      tcp_ptrace2 (tcp_sum (fun z => tcp_conj (tensoro (M z) oid) r))
      = tcp_ptrace2 r.

  (** Conjugation by a projector does not increase the trace. *)
  Axiom tcp_trace_conj_proj_le : forall X (A : op X X) (r : tcp X),
      ocomp A A = A -> oadj A = A ->
      (tcp_trace (tcp_conj A r) <= tcp_trace r)%R.

  (** A projective measurement, extended by the identity on the rest of the
      system, does not increase the trace:
      [sum_z tr((M_z (x) id) rho (M_z (x) id)) <= tr rho].

      The hypotheses are the definition of [Meas(D, X)] from section 2, with the
      bound [sum_z M_z <= id] stated through inner products so that no sum of
      operators is needed. Stated with the [(x) id] already in place because
      that is how measurements act: on one register of a larger memory, and the
      bound does not survive being read off the register alone. *)
  Axiom tcp_trace_meas_tensor :
    forall X Y (D : Type) (M : D -> op X X) (r : tcp (X * Y)),
      (forall z, ocomp (M z) (M z) = M z) ->
      (forall z, oadj (M z) = M z) ->
      (forall v : l2 X, summable (fun z => Cre (inner v (oapp (M z) v)))) ->
      (forall v : l2 X,
          (tsum (fun z => Cre (inner v (oapp (M z) v))) <= Cre (inner v v))%R) ->
      summable (fun z => tcp_trace (tcp_conj (tensoro (M z) oid) r)) /\
      (tsum (fun z => tcp_trace (tcp_conj (tensoro (M z) oid) r))
       <= tcp_trace r)%R.

  (** Isometries preserve the trace; this is why [apply] and [Q <-q e] are
      trace-preserving and measurements are trace-decreasing. *)
  Axiom tcp_trace_conj_isometry : forall X Y (A : op X Y) (r : tcp X),
      ocomp (oadj A) A = oid -> tcp_trace (tcp_conj A r) = tcp_trace r.

  (** *** Partial trace and tensor *)

  Axiom tcp_ptrace_add : forall X Y (r s : tcp (X * Y)),
      tcp_ptrace (tcp_add r s) = tcp_add (tcp_ptrace r) (tcp_ptrace s).
  Axiom tcp_ptrace_scale : forall X Y (a : R) (r : tcp (X * Y)),
      tcp_ptrace (tcp_scale a r) = tcp_scale a (tcp_ptrace r).
  Axiom tcp_ptrace_trace : forall X Y (r : tcp (X * Y)),
      tcp_trace (tcp_ptrace r) = tcp_trace r.
  Axiom tcp_ptrace_tensor : forall X Y (r : tcp X) (s : tcp Y),
      tcp_ptrace (tcp_tensor r s) = tcp_scale (tcp_trace s) r.

  Axiom tcp_ptrace2_add : forall X Y (r s : tcp (X * Y)),
      tcp_ptrace2 (tcp_add r s) = tcp_add (tcp_ptrace2 r) (tcp_ptrace2 s).
  Axiom tcp_ptrace2_scale : forall X Y (a : R) (r : tcp (X * Y)),
      tcp_ptrace2 (tcp_scale a r) = tcp_scale a (tcp_ptrace2 r).
  Axiom tcp_ptrace2_trace : forall X Y (r : tcp (X * Y)),
      tcp_trace (tcp_ptrace2 r) = tcp_trace r.
  Axiom tcp_ptrace2_tensor : forall X Y (r : tcp X) (s : tcp Y),
      tcp_ptrace2 (tcp_tensor r s) = tcp_scale (tcp_trace r) s.

  (** Normality of the partial traces: they commute with infinite sums. *)
  Axiom tcp_ptrace_sum : forall X Y J (F : J -> tcp (X * Y)),
      tcp_summable F ->
      tcp_ptrace (tcp_sum F) = tcp_sum (fun j => tcp_ptrace (F j)).
  Axiom tcp_ptrace2_sum : forall X Y J (F : J -> tcp (X * Y)),
      tcp_summable F ->
      tcp_ptrace2 (tcp_sum F) = tcp_sum (fun j => tcp_ptrace2 (F j)).

  (** *** Partial trace versus an operation on one factor

      Acting on a factor that is *kept* commutes with the partial trace; acting
      on a factor that is *discarded* leaves it unchanged, provided the action
      is trace-preserving there. These four are the standard partial-trace
      laws, and they are what lets a program acting on one side of a relational
      state be pushed through the projections of Definition 35. *)

  Axiom tcp_ptrace_conj_tensorL : forall X X' Y (A : op X X') (r : tcp (X * Y)),
      tcp_ptrace (tcp_conj (tensoro A oid) r) = tcp_conj A (tcp_ptrace r).

  Axiom tcp_ptrace2_conj_tensorL : forall X X' Y (A : op X X') (r : tcp (X * Y)),
      ocomp (oadj A) A = oid ->
      tcp_ptrace2 (tcp_conj (tensoro A oid) r) = tcp_ptrace2 r.

  Axiom tcp_ptrace2_conj_tensorR : forall X Y Y' (B : op Y Y') (r : tcp (X * Y)),
      tcp_ptrace2 (tcp_conj (tensoro oid B) r) = tcp_conj B (tcp_ptrace2 r).

  Axiom tcp_ptrace_conj_tensorR : forall X Y Y' (B : op Y Y') (r : tcp (X * Y)),
      ocomp (oadj B) B = oid ->
      tcp_ptrace (tcp_conj (tensoro oid B) r) = tcp_ptrace r.

  (** Swapping the two factors turns one partial trace into the other. Not
      derivable from the four laws above: those relate a partial trace to
      *the same* partial trace of an action on one factor, whereas this
      exchanges *which* factor is traced out, which needs the reindexing
      unitary's action on a general (non-product, non-pure) operator -- exactly
      what the signature declines to expose beyond kets ([Ubij_ket]). Stated
      with the swap given explicitly via [Ubij] rather than through a named
      [Uswap] combinator, since [Uswap] is derived, not part of the
      signature. *)
  Axiom tcp_ptrace_pswap : forall X Y H1 H2 (r : tcp (X * Y)),
      tcp_ptrace
        (tcp_conj (@Ubij (X * Y) (Y * X)
                     (fun p => (snd p, fst p)) (fun q => (snd q, fst q)) H1 H2)
                  r)
      = tcp_ptrace2 r.

  (** Conjugating a *product* by the factor swap exchanges the factors. Not
      derivable from [tcp_ptrace_pswap] (a partial trace forgets too much to
      pin down the whole state) or from [tcp_conj_proj] plus [tcp_decompose]
      (that route needs the swap's action on a general, non-ket, tensor
      vector -- [tensorv v w] for non-basis [v], [w] -- which is exactly the
      continuity the signature does not expose). Textbook nonetheless: this
      is literally what "the factor swap" means. *)
  Axiom tcp_conj_pswap : forall X Y H1 H2 (r : tcp X) (s : tcp Y),
      tcp_conj (@Ubij (X * Y) (Y * X)
                  (fun p => (snd p, fst p)) (fun q => (snd q, fst q)) H1 H2)
               (tcp_tensor r s)
      = tcp_tensor s r.

  Axiom tcp_tensor_proj : forall X Y (v : l2 X) (w : l2 Y),
      tcp_tensor (tcp_proj v) (tcp_proj w) = tcp_proj (tensorv v w).
  Axiom tcp_scale_tensor_l : forall X Y (a : R) (r : tcp X) (s : tcp Y),
      tcp_scale a (tcp_tensor r s) = tcp_tensor (tcp_scale a r) s.
  Axiom tcp_tensor_add_r : forall X Y (r : tcp X) (s t : tcp Y),
      tcp_tensor r (tcp_add s t)
      = tcp_add (tcp_tensor r s) (tcp_tensor r t).

  (** Normality of the tensor in the factor that varies. Needed for the
      [Q <-q e] clause of [denote_sum], where a fresh state is tensored onto a
      sum of reduced states. *)
  Axiom tcp_tensor_sum_r : forall X Y J (r : tcp X) (F : J -> tcp Y),
      tcp_summable F ->
      tcp_tensor r (tcp_sum F) = tcp_sum (fun j => tcp_tensor r (F j)).

  (** *** Sums *)

  Axiom tcp_summable_trace : forall X J (F : J -> tcp X),
      tcp_summable F <-> summable (fun j => tcp_trace (F j)).
  Axiom tcp_trace_sum : forall X J (F : J -> tcp X),
      tcp_summable F -> tcp_trace (tcp_sum F) = tsum (fun j => tcp_trace (F j)).
  (** [sum_i rho_i] "is defined as the least upper bound of [sum_{i in J} rho_i]
      where [J] ranges over all finite subsets of [I]" (section 2) -- stated as
      exactly that: an upper bound, and the least one. *)
  Axiom tcp_sum_ub : forall X J (F : J -> tcp X) (l : list J),
      tcp_summable F -> NoDup l -> tcp_le (tcp_lsum F l) (tcp_sum F).
  Axiom tcp_sum_least : forall X J (F : J -> tcp X) (s : tcp X),
      tcp_summable F ->
      (forall l, NoDup l -> tcp_le (tcp_lsum F l) s) -> tcp_le (tcp_sum F) s.
  Axiom tcp_sum_not_summable : forall X J (F : J -> tcp X),
      ~ tcp_summable F -> tcp_sum F = tcp_zero.

  (** Scaling commutes with sums, and a sum of rescalings of one operator is
      that operator rescaled by the total. The second is what makes sampling
      trace-preserving when the distribution is total. *)
  Axiom tcp_scale_sum : forall X J (a : R) (F : J -> tcp X),
      tcp_summable F ->
      tcp_scale a (tcp_sum F) = tcp_sum (fun j => tcp_scale a (F j)).

  Axiom tcp_sum_scale_const : forall X J (c : J -> R) (r : tcp X),
      (forall j, (0 <= c j)%R) -> summable c ->
      tcp_sum (fun j => tcp_scale (c j) r) = tcp_scale (tsum c) r.

  (** Sums are additive. *)
  Axiom tcp_sum_add : forall X J (F G : J -> tcp X),
      tcp_summable F -> tcp_summable G ->
      tcp_sum (fun j => tcp_add (F j) (G j))
      = tcp_add (tcp_sum F) (tcp_sum G).

  (** Reindexing along a bijection. *)
  Axiom tcp_sum_bij : forall X (I J : Type) (h : J -> I) (g : I -> J)
                             (F : I -> tcp X),
      (forall j, g (h j) = j) -> (forall i, h (g i) = i) ->
      tcp_summable F ->
      tcp_summable (fun j => F (h j)) /\
      tcp_sum (fun j => F (h j)) = tcp_sum F.

  (** Tonelli: an iterated sum of positive operators may be flattened into a
      single sum over the dependent pairs. Textbook (monotone convergence),
      and the operator counterpart of [tsum_tonelli] in [Sums.v]. *)
  Axiom tcp_sum_sigma : forall X (K : Type) (Pk : K -> Type)
                               (F : forall k, Pk k -> tcp X),
      (forall k, tcp_summable (F k)) ->
      tcp_summable (fun k => tcp_sum (F k)) ->
      tcp_summable (fun p : sigT Pk => F (projT1 p) (projT2 p)) /\
      tcp_sum (fun k => tcp_sum (F k))
      = tcp_sum (fun p : sigT Pk => F (projT1 p) (projT2 p)).

  (** *** Support

      The properties of [supp] that Definition 14 and the rule proofs use. *)

  (** Faithfulness of the support: only the zero operator has zero support.
      This is what makes Lemma 24 work -- [Cla[e]] constrains exactly those
      memories whose block is nonzero. *)
  Axiom tcp_supp_eq0 : forall X (r : tcp X), tcp_supp r = hbot <-> r = tcp_zero.
  Axiom tcp_supp_proj : forall X (v : l2 X),
      tcp_supp (tcp_proj v) = hspan (fun u => u = v).
  Axiom tcp_supp_add : forall X (r s : tcp X),
      tcp_supp (tcp_add r s) = hSup (fun b : bool => if b then tcp_supp r else tcp_supp s).
  Axiom tcp_supp_scale : forall X (a : R) (r : tcp X),
      (0 < a)%R -> tcp_supp (tcp_scale a r) = tcp_supp r.
  Axiom tcp_supp_sum : forall X J (F : J -> tcp X),
      tcp_summable F -> tcp_supp (tcp_sum F) = hSup (fun j => tcp_supp (F j)).

  (** Every positive trace-class operator is a sum of rank-one projections
      (section 2: "any [rho in T^+(X)] can be decomposed in this way"). This is
      the spectral theorem for positive trace-class operators, and it is what
      lets Lemma 36 reduce qRHL to pure initial states. *)
  Axiom tcp_decompose : forall X (r : tcp X),
      exists (J : Type) (psi : J -> l2 X),
        tcp_summable (fun j => tcp_proj (psi j))
        /\ r = tcp_sum (fun j => tcp_proj (psi j)).

End HILBERT_SUBSTRATE.
