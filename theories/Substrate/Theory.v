(** * Derived Hilbert space theory.

    The first functor layer over [HILBERT_SUBSTRATE]. Everything here is
    *proved* from the signature: the complete-lattice structure on subspaces,
    the orthocomplement laws, the standard operator predicates, images, tensor
    products of subspaces, and the "division" operation.

    This file is where the signature gets its first real workout. If a lemma
    here needs an axiom that is not in [Interface.v], that is the signal to add
    it there -- deliberately, with a citation -- rather than to work around it. *)

From Stdlib Require Import List Lra.
From QRHL.Substrate Require Import Ambient Cnum Sums Interface.

Module HTheory (S : HILBERT_SUBSTRATE).
  Include S.

  (* ================================================================= *)
  (** ** Notation *)

  Declare Scope hs_scope.
  Delimit Scope hs_scope with hs.
  Open Scope hs_scope.

  Notation "u '+v' v" := (vadd u v) (at level 50, left associativity) : hs_scope.
  Notation "a '*v' v" := (vscale a v) (at level 40, left associativity) : hs_scope.
  Notation "'<[' u ',' v ']>'" := (inner u v) : hs_scope.
  Notation "A '^A'" := (oadj A) (at level 20) : hs_scope.
  Notation "A 'o' B" := (ocomp A B) (at level 40, left associativity) : hs_scope.
  Notation "A '@v' v" := (oapp A v) (at level 40, left associativity) : hs_scope.
  Notation "v '\in' S" := (hmem v S) (at level 70) : hs_scope.

  (* ================================================================= *)
  (** ** Basic vector facts *)

  Lemma vadd_zero_l {X} (v : l2 X) : vadd vzero v = v.
  Proof. rewrite vadd_comm; apply vadd_zero. Qed.

  Lemma vadd_opp_l {X} (v : l2 X) : vadd (vopp v) v = vzero.
  Proof. rewrite vadd_comm; apply vadd_opp. Qed.

  Lemma inner_vzero_r {X} (u : l2 X) : inner u vzero = C0.
  Proof. rewrite <- (vscale_0 X u), inner_scaler; ring. Qed.

  Lemma inner_vzero_l {X} (u : l2 X) : inner vzero u = C0.
  Proof. rewrite inner_conj, inner_vzero_r; apply Cconj_C0. Qed.

  (** Conjugate-linearity in the first argument, derived from linearity in the
      second plus conjugate symmetry. *)
  Lemma inner_scalel {X} (a : C) (u v : l2 X) :
    inner (vscale a u) v = Cmult (Cconj a) (inner u v).
  Proof.
    rewrite inner_conj, inner_scaler, Cconj_mult, <- inner_conj; reflexivity.
  Qed.

  Lemma vadd_cancel_l {X} (a b c : l2 X) : vadd a b = vadd a c -> b = c.
  Proof.
    intros H.
    transitivity (vadd (vopp a) (vadd a b)).
    - rewrite vadd_assoc, vadd_opp_l, vadd_zero_l; reflexivity.
    - rewrite H, vadd_assoc, vadd_opp_l, vadd_zero_l; reflexivity.
  Qed.

  Lemma vsub_zero {X} (u v : l2 X) : vadd u (vopp v) = vzero -> u = v.
  Proof.
    intros H.
    transitivity (vadd (vadd u (vopp v)) v).
    - rewrite <- vadd_assoc, vadd_opp_l, vadd_zero; reflexivity.
    - rewrite H, vadd_zero_l; reflexivity.
  Qed.

  (** Negation is scaling by [-1]; this is what lets the inner-product laws be
      stated only for [vadd] and [vscale] in the signature. *)
  Lemma vopp_scale {X} (v : l2 X) : vopp v = vscale (Copp C1) v.
  Proof.
    apply (vadd_cancel_l v).
    rewrite vadd_opp, <- (vscale_1 X v) at 1.
    rewrite <- vscale_adda.
    replace (Cplus C1 (Copp C1)) with C0 by ring.
    symmetry; apply vscale_0.
  Qed.

  Lemma inner_oppr {X} (u v : l2 X) : inner u (vopp v) = Copp (inner u v).
  Proof. rewrite vopp_scale, inner_scaler; ring. Qed.

  Lemma inner_addl {X} (u v w : l2 X) :
    inner (vadd u v) w = Cplus (inner u w) (inner v w).
  Proof.
    rewrite inner_conj, inner_addr, Cconj_plus, <- !inner_conj; reflexivity.
  Qed.

  Lemma inner_oppl {X} (u v : l2 X) : inner (vopp u) v = Copp (inner u v).
  Proof.
    rewrite inner_conj, inner_oppr, Cconj_opp, <- inner_conj; reflexivity.
  Qed.

  (** Nondegeneracy: a vector is determined by its inner products. *)
  Lemma inner_nondeg {X} (u v : l2 X) :
    (forall w, inner w u = inner w v) -> u = v.
  Proof.
    intros H; apply vsub_zero, inner_definite.
    rewrite inner_addr, inner_oppr, (H (vadd u (vopp v))); ring.
  Qed.

  Lemma inner_nondeg_l {X} (u v : l2 X) :
    (forall w, inner u w = inner v w) -> u = v.
  Proof.
    intros H; apply inner_nondeg; intros w.
    rewrite inner_conj, (H w), <- inner_conj; reflexivity.
  Qed.

  (** Extensionality over *all* vectors, weakened from [op_ext_ket]'s
      extensionality over just the computational basis: agreeing everywhere
      certainly agrees on kets. Kept under the name the rest of the
      development already uses. *)
  Lemma op_ext {X Y} (A B : op X Y) :
    (forall v, oapp A v = oapp B v) -> A = B.
  Proof. intros H; apply op_ext_ket; intros x; apply H. Qed.

  Lemma op_ext_inner {X Y} (A B : op X Y) :
    (forall v w, inner w (oapp A v) = inner w (oapp B v)) -> A = B.
  Proof.
    intros H; apply op_ext; intros v; apply inner_nondeg; intros w; apply H.
  Qed.

  (** *** Adjoint laws

      All derived from [inner_oadj] plus nondegeneracy -- none assumed. *)

  Lemma oadj_invol {X Y} (A : op X Y) : oadj (oadj A) = A.
  Proof.
    apply op_ext_inner; intros v w.
    rewrite inner_conj, inner_oadj, inner_conj, inner_oadj.
    rewrite Cconj_involutive; reflexivity.
  Qed.

  Lemma oadj_ocomp {X Y Z} (A : op Y Z) (B : op X Y) :
    oadj (ocomp A B) = ocomp (oadj B) (oadj A).
  Proof.
    apply op_ext; intros v; apply inner_nondeg_l; intros w.
    rewrite inner_oadj, !oapp_ocomp, inner_oadj, inner_oadj; reflexivity.
  Qed.

  Lemma oadj_oid {X} : oadj (@oid X) = oid.
  Proof.
    apply op_ext; intros v; apply inner_nondeg_l; intros w.
    rewrite inner_oadj, !oapp_oid; reflexivity.
  Qed.

  (** Basis vectors are nonzero: the first thing that would fail if the
      signature had collapsed. *)
  Lemma ket_neq_vzero {X} (x : X) : ket x <> vzero.
  Proof.
    intros H.
    assert (Hc : inner (ket x) (ket x) = C0)
      by (rewrite H at 2; apply inner_vzero_r).
    rewrite inner_ket in Hc.
    destruct (excluded_middle_informative (x = x)) as [_ | Hn]; [| tauto ].
    exact (C1_neq_C0 Hc).
  Qed.

  (* ================================================================= *)
  (** ** The subspace lattice *)

  Definition hle {X} (S T : hspace X) : Prop := forall v, hmem v S -> hmem v T.

  Notation "S '<=h' T" := (hle S T) (at level 70) : hs_scope.

  Lemma hle_refl {X} (S : hspace X) : S <=h S.
  Proof. intros v H; exact H. Qed.

  Lemma hle_trans {X} (S T U : hspace X) : S <=h T -> T <=h U -> S <=h U.
  Proof. intros H1 H2 v Hv; apply H2, H1, Hv. Qed.

  (** Antisymmetry is extensionality: this is why the signature gives
      [hspace_ext] instead of a list of lattice laws. *)
  Lemma hle_antisym {X} (S T : hspace X) : S <=h T -> T <=h S -> S = T.
  Proof.
    intros H1 H2; apply hspace_ext; intros v; split; [ apply H1 | apply H2 ].
  Qed.

  Lemma hbot_le {X} (S : hspace X) : hbot <=h S.
  Proof.
    intros v Hv; apply hmem_hbot in Hv; subst v; apply hmem_vzero.
  Qed.

  Lemma hle_htop {X} (S : hspace X) : S <=h htop.
  Proof. intros v _; apply hmem_htop. Qed.

  (** *** Arbitrary meets and joins *)

  Lemma hInf_lb {X J} (F : J -> hspace X) (j : J) : hInf F <=h F j.
  Proof. intros v Hv; apply (proj1 (hmem_hInf _ _ F v) Hv). Qed.

  Lemma hInf_glb {X J} (F : J -> hspace X) (T : hspace X) :
    (forall j, T <=h F j) -> T <=h hInf F.
  Proof.
    intros H v Hv; apply (proj2 (hmem_hInf _ _ F v)); intros j; apply H, Hv.
  Qed.

  Lemma hSup_lb {X J} (F : J -> hspace X) (j : J) : F j <=h hSup F.
  Proof. intros v Hv; eapply hSup_ub; exact Hv. Qed.

  Lemma hSup_lub {X J} (F : J -> hspace X) (T : hspace X) :
    (forall j, F j <=h T) -> hSup F <=h T.
  Proof.
    intros H v Hv; eapply hSup_least; [| exact Hv ].
    intros j w Hw; apply H with (j := j); exact Hw.
  Qed.

  (** *** Binary meet and join

      The paper writes [cap] for conjunction and [+] for disjunction of
      predicates (Birkhoff-von Neumann quantum logic, section 4.2). *)

  Definition hmeet {X} (S T : hspace X) : hspace X :=
    hInf (fun b : bool => if b then S else T).
  Definition hjoin {X} (S T : hspace X) : hspace X :=
    hSup (fun b : bool => if b then S else T).

  Notation "S '/\h' T" := (hmeet S T) (at level 45, right associativity) : hs_scope.
  Notation "S '\/h' T" := (hjoin S T) (at level 52, right associativity) : hs_scope.

  Lemma hmem_hmeet {X} (S T : hspace X) v :
    hmem v (S /\h T) <-> hmem v S /\ hmem v T.
  Proof.
    unfold hmeet; rewrite hmem_hInf; split.
    - intros H; split; [ apply (H true) | apply (H false) ].
    - intros [H1 H2] [|]; assumption.
  Qed.

  Lemma hmeet_lel {X} (S T : hspace X) : S /\h T <=h S.
  Proof. intros v Hv; apply hmem_hmeet in Hv; tauto. Qed.

  Lemma hmeet_ler {X} (S T : hspace X) : S /\h T <=h T.
  Proof. intros v Hv; apply hmem_hmeet in Hv; tauto. Qed.

  Lemma hmeet_glb {X} (S T U : hspace X) : U <=h S -> U <=h T -> U <=h S /\h T.
  Proof.
    intros H1 H2 v Hv; apply hmem_hmeet; split; [ apply H1 | apply H2 ]; exact Hv.
  Qed.

  Lemma hjoin_lel {X} (S T : hspace X) : S <=h S \/h T.
  Proof. apply (hSup_lb (fun b : bool => if b then S else T) true). Qed.

  Lemma hjoin_ler {X} (S T : hspace X) : T <=h S \/h T.
  Proof. apply (hSup_lb (fun b : bool => if b then S else T) false). Qed.

  Lemma hjoin_lub {X} (S T U : hspace X) : S <=h U -> T <=h U -> S \/h T <=h U.
  Proof. intros H1 H2; apply hSup_lub; intros [|]; assumption. Qed.

  Lemma hmeet_comm {X} (S T : hspace X) : S /\h T = T /\h S.
  Proof.
    apply hle_antisym; apply hmeet_glb;
      solve [ apply hmeet_lel | apply hmeet_ler ].
  Qed.

  Lemma hjoin_comm {X} (S T : hspace X) : S \/h T = T \/h S.
  Proof.
    apply hle_antisym; apply hjoin_lub;
      solve [ apply hjoin_lel | apply hjoin_ler ].
  Qed.

  Lemma hmeet_idem {X} (S : hspace X) : S /\h S = S.
  Proof.
    apply hle_antisym; [ apply hmeet_lel | apply hmeet_glb; apply hle_refl ].
  Qed.

  Lemma hmeet_htop {X} (S : hspace X) : S /\h htop = S.
  Proof.
    apply hle_antisym; [ apply hmeet_lel |].
    apply hmeet_glb; [ apply hle_refl | apply hle_htop ].
  Qed.

  Lemma hmeet_hbot {X} (S : hspace X) : S /\h hbot = hbot.
  Proof.
    apply hle_antisym; [ apply hmeet_ler |].
    apply hmeet_glb; [ apply hbot_le | apply hle_refl ].
  Qed.

  Lemma hjoin_htop {X} (S : hspace X) : S \/h htop = htop.
  Proof.
    apply hle_antisym; [ apply hjoin_lub; [ apply hle_htop | apply hle_refl ]
                       | apply hjoin_ler ].
  Qed.

  Lemma hjoin_hbot {X} (S : hspace X) : S \/h hbot = S.
  Proof.
    apply hle_antisym; [ apply hjoin_lub; [ apply hle_refl | apply hbot_le ]
                       | apply hjoin_lel ].
  Qed.

  (** Monotonicity, used constantly by rule Conseq. *)
  Lemma hmeet_mono {X} (S S' T T' : hspace X) :
    S <=h S' -> T <=h T' -> S /\h T <=h S' /\h T'.
  Proof.
    intros H1 H2; apply hmeet_glb.
    - eapply hle_trans; [ apply hmeet_lel | exact H1 ].
    - eapply hle_trans; [ apply hmeet_ler | exact H2 ].
  Qed.

  Lemma hjoin_mono {X} (S S' T T' : hspace X) :
    S <=h S' -> T <=h T' -> S \/h T <=h S' \/h T'.
  Proof.
    intros H1 H2; apply hjoin_lub.
    - eapply hle_trans; [ exact H1 | apply hjoin_lel ].
    - eapply hle_trans; [ exact H2 | apply hjoin_ler ].
  Qed.

  Lemma hInf_mono {X J} (F G : J -> hspace X) :
    (forall j, F j <=h G j) -> hInf F <=h hInf G.
  Proof.
    intros H; apply hInf_glb; intros j.
    eapply hle_trans; [ apply (hInf_lb F j) | apply H ].
  Qed.

  (* ================================================================= *)
  (** ** Span *)

  Lemma hspan_mono {X} (M N : l2 X -> Prop) :
    (forall v, M v -> N v) -> hspan M <=h hspan N.
  Proof.
    intros H v Hv; eapply hspan_least; [| exact Hv ].
    intros w Hw; apply hspan_ub, H, Hw.
  Qed.

  Lemma hspan_le {X} (M : l2 X -> Prop) (T : hspace X) :
    (forall v, M v -> hmem v T) -> hspan M <=h T.
  Proof. intros H v Hv; eapply hspan_least; [ exact H | exact Hv ]. Qed.

  (** The span of a single vector: the paper's [span{psi}]. *)
  Definition hspan1 {X} (v : l2 X) : hspace X := hspan (fun u => u = v).

  Lemma hmem_hspan1 {X} (v : l2 X) : hmem v (hspan1 v).
  Proof. apply hspan_ub; reflexivity. Qed.

  Lemma hspan1_le {X} (v : l2 X) (T : hspace X) : hmem v T -> hspan1 v <=h T.
  Proof. intros H; apply hspan_le; intros u ->; exact H. Qed.

  (* ================================================================= *)
  (** ** Orthocomplement *)

  (** The subspace of vectors orthogonal to a single given vector. Derived via
      [hocompl_hspan]; it is what makes De Morgan provable. *)
  Lemma hmem_hocompl_hspan1 {X} (v w : l2 X) :
    hmem w (hocompl (hspan1 v)) <-> inner v w = C0.
  Proof.
    unfold hspan1; rewrite hocompl_hspan; split.
    - intros H; apply H; reflexivity.
    - intros H u ->; exact H.
  Qed.

  (** Orthogonality is symmetric, in the form we keep needing. *)
  Lemma inner_eq0_sym {X} (v w : l2 X) : inner v w = C0 -> inner w v = C0.
  Proof.
    intros H; rewrite inner_conj, H; apply Cconj_C0.
  Qed.

  Lemma hocompl_antitone {X} (S T : hspace X) :
    S <=h T -> hocompl T <=h hocompl S.
  Proof.
    intros H v Hv; apply hmem_hocompl; intros w Hw.
    apply (proj1 (hmem_hocompl _ _ _) Hv), H, Hw.
  Qed.

  Lemma hle_hocompl_hocompl {X} (S : hspace X) : S <=h hocompl (hocompl S).
  Proof. rewrite hocompl_invol; apply hle_refl. Qed.

  (** De Morgan. The join direction is the one that needs [hocompl_hspan]. *)
  Lemma hocompl_hSup {X J} (F : J -> hspace X) :
    hocompl (hSup F) = hInf (fun j => hocompl (F j)).
  Proof.
    apply hle_antisym.
    - apply hInf_glb; intros j; apply hocompl_antitone, hSup_lb.
    - intros v Hv; apply hmem_hocompl.
      (* Everything in [hSup F] is orthogonal to [v], because [hocompl (hspan1 v)]
         is a subspace containing every [F j] -- this is the step that needs
         [hocompl_hspan], since orthogonality to [v] has to *be* a subspace. *)
      assert (H : forall w, hmem w (hSup F) -> hmem w (hocompl (hspan1 v))).
      { apply (hSup_least X J F (hocompl (hspan1 v))).
        intros j w Hw.
        apply hmem_hocompl_hspan1, inner_eq0_sym.
        apply (proj1 (hmem_hocompl _ _ _)
                     (proj1 (hmem_hInf _ _ _ v) Hv j)), Hw. }
      intros w Hw.
      apply inner_eq0_sym, hmem_hocompl_hspan1, H, Hw.
  Qed.

  Lemma hocompl_htop {X} : hocompl (@htop X) = hbot.
  Proof.
    apply hle_antisym.
    - intros v Hv; apply hmem_hbot.
      apply inner_definite.
      apply (proj1 (hmem_hocompl _ _ _) Hv), hmem_htop.
    - apply hbot_le.
  Qed.

  Lemma hocompl_hbot {X} : hocompl (@hbot X) = htop.
  Proof.
    rewrite <- hocompl_htop, hocompl_invol; reflexivity.
  Qed.

  (** [S cap S^perp = 0], the quantum analogue of non-contradiction. *)
  Lemma hmeet_hocompl {X} (S : hspace X) : S /\h hocompl S = hbot.
  Proof.
    apply hle_antisym; [| apply hbot_le ].
    intros v Hv; apply hmem_hmeet in Hv; destruct Hv as [H1 H2].
    apply hmem_hbot, inner_definite.
    apply (proj1 (hmem_hocompl _ _ _) H2), H1.
  Qed.

  (* ================================================================= *)
  (** ** Operator algebra

      Consequences of [op_ext] plus the application laws. None of this is
      assumed. *)

  Lemma ocomp_assoc {X Y Z W} (A : op Z W) (B : op Y Z) (C : op X Y) :
    ocomp A (ocomp B C) = ocomp (ocomp A B) C.
  Proof. apply op_ext; intros v; rewrite !oapp_ocomp; reflexivity. Qed.

  Lemma ocomp_oid_l {X Y} (A : op X Y) : ocomp oid A = A.
  Proof. apply op_ext; intros v; rewrite oapp_ocomp, oapp_oid; reflexivity. Qed.

  Lemma ocomp_oid_r {X Y} (A : op X Y) : ocomp A oid = A.
  Proof. apply op_ext; intros v; rewrite oapp_ocomp, oapp_oid; reflexivity. Qed.

  Lemma oapp_vzero {X Y} (A : op X Y) : oapp A vzero = vzero.
  Proof.
    rewrite <- (vscale_0 X vzero), oapp_vscale, vscale_0; reflexivity.
  Qed.

  Lemma tensorv_vzero_l {X Y} (w : l2 Y) : tensorv (@vzero X) w = vzero.
  Proof.
    rewrite <- (vscale_0 X vzero), tensorv_scalel, vscale_0; reflexivity.
  Qed.

  Lemma tensorv_vzero_r {X Y} (v : l2 X) : tensorv v (@vzero Y) = vzero.
  Proof.
    rewrite <- (vscale_0 Y vzero), tensorv_scaler, vscale_0; reflexivity.
  Qed.

  (* ================================================================= *)
  (** ** Operator predicates *)

  Definition opositive {X} (A : op X X) : Prop :=
    forall v, Cge0 (inner v (oapp A v)).

  Definition ole {X} (A B : op X X) : Prop :=
    opositive (oadd B (oopp A)).

  Definition oisometry {X Y} (A : op X Y) : Prop := ocomp (oadj A) A = oid.

  Definition ounitary {X Y} (A : op X Y) : Prop :=
    ocomp (oadj A) A = oid /\ ocomp A (oadj A) = oid.

  (** "A projector is an operator [P] with [P^2 = P = P^*]" (section 2). *)
  Definition oprojector {X} (P : op X X) : Prop :=
    ocomp P P = P /\ oadj P = P.

  Lemma ounitary_isometry {X Y} (A : op X Y) : ounitary A -> oisometry A.
  Proof. intros [H _]; exact H. Qed.

  Lemma oisometry_tensoro_l {X X' Y} (A : op X X') :
    oisometry A -> oisometry (@tensoro X X' Y Y A oid).
  Proof.
    intros HA; unfold oisometry.
    rewrite tensoro_oadj, oadj_oid, <- tensoro_ocomp, HA, ocomp_oid_l,
            tensoro_oid; reflexivity.
  Qed.

  Lemma oisometry_tensoro_r {X Y Y'} (B : op Y Y') :
    oisometry B -> oisometry (@tensoro X X Y Y' oid B).
  Proof.
    intros HB; unfold oisometry.
    rewrite tensoro_oadj, oadj_oid, <- tensoro_ocomp, HB, ocomp_oid_l,
            tensoro_oid; reflexivity.
  Qed.

  (** Conjugating an isometry by a unitary gives an isometry. *)
  Lemma oisometry_conj {X Y} (W : op X Y) (A : op Y Y) :
    ounitary W -> oisometry A -> oisometry (ocomp (oadj W) (ocomp A W)).
  Proof.
    intros [H1 H2] HA; unfold oisometry in *.
    apply op_ext; intros v.
    rewrite oapp_ocomp, oapp_oid.
    rewrite !oadj_ocomp, oadj_invol, !oapp_ocomp.
    rewrite <- (oapp_ocomp _ _ _ W (oadj W)), H2, oapp_oid.
    rewrite <- (oapp_ocomp _ _ _ (oadj A) A), HA, oapp_oid.
    rewrite <- oapp_ocomp, H1, oapp_oid; reflexivity.
  Qed.

  Lemma oprojector_tensoro_l {X Y} (A : op X X) :
    oprojector A -> oprojector (@tensoro X X Y Y A oid).
  Proof.
    intros [H1 H2]; split.
    - rewrite <- tensoro_ocomp, H1, ocomp_oid_l; reflexivity.
    - rewrite tensoro_oadj, oadj_oid, H2; reflexivity.
  Qed.

  (** Conjugating a projector by a unitary gives a projector. *)
  Lemma oprojector_conj {X Y} (W : op X Y) (A : op Y Y) :
    ounitary W -> oprojector A -> oprojector (ocomp (oadj W) (ocomp A W)).
  Proof.
    intros [H1 H2] [HA1 HA2]; split.
    - apply op_ext; intros v.
      rewrite !oapp_ocomp.
      rewrite <- (oapp_ocomp _ _ _ W (oadj W)), H2, oapp_oid.
      rewrite <- (oapp_ocomp _ _ _ A A), HA1; reflexivity.
    - rewrite !oadj_ocomp, oadj_invol, HA2, ocomp_assoc; reflexivity.
  Qed.

  Lemma oisometry_oadj {X Y} (W : op X Y) : ounitary W -> oisometry (oadj W).
  Proof. intros [H1 H2]; unfold oisometry; rewrite oadj_invol; exact H2. Qed.

  Lemma oisometry_inner {X Y} (A : op X Y) (v w : l2 X) :
    oisometry A -> inner (oapp A v) (oapp A w) = inner v w.
  Proof.
    intros H.
    rewrite <- inner_oadj, <- oapp_ocomp, H, oapp_oid; reflexivity.
  Qed.

  (** Reindexing unitaries really are unitary, repackaged into the predicate. *)
  Lemma Ubij_ounitary {X Y} f g H1 H2 : ounitary (@Ubij X Y f g H1 H2).
  Proof. apply Ubij_unitary. Qed.

  (** The identity reindexing is [oid], and composing two [Ubij]s along
      composable index maps is the [Ubij] of the composite -- both index-level
      computations once [op_ext_ket] is in hand. Every syntactic identity
      between the reindexing unitaries used throughout the development
      ([Wsplit], [Urqpair], the register reassociations, the side swap)
      reduces to this pattern: unfold both sides via [Ubij_ket], and what
      remains is an equation between the index maps. *)
  Lemma Ubij_oid {X} (f : X -> X) (Hf : forall x, f (f x) = x) :
    (forall x, f x = x) -> Ubij f f Hf Hf = oid.
  Proof.
    intros Hid; apply op_ext_ket; intros x.
    rewrite Ubij_ket, oapp_oid, Hid; reflexivity.
  Qed.

  Lemma Ubij_ocomp {X Y Z} (f1 : X -> Y) (g1 : Y -> X) (H1 : forall x, g1 (f1 x) = x)
        (H1' : forall y, f1 (g1 y) = y)
        (f2 : Y -> Z) (g2 : Z -> Y) (H2 : forall y, g2 (f2 y) = y)
        (H2' : forall z, f2 (g2 z) = z)
        (H3 : forall x, g1 (g2 (f2 (f1 x))) = x)
        (H3' : forall z, f2 (f1 (g1 (g2 z))) = z) :
    ocomp (Ubij f2 g2 H2 H2') (Ubij f1 g1 H1 H1')
    = Ubij (fun x => f2 (f1 x)) (fun z => g1 (g2 z)) H3 H3'.
  Proof.
    apply op_ext_ket; intros x.
    rewrite oapp_ocomp, !Ubij_ket; reflexivity.
  Qed.

  (* ================================================================= *)
  (** ** Images *)

  (** The paper's [im A]. Defined as the closed span of the range, which
      agrees with the range itself exactly when the range is closed -- the case
      for the projectors and isometries the rules actually apply it to. *)
  Definition oim {X Y} (A : op X Y) : hspace Y :=
    hspan (fun w => exists v, w = oapp A v).

  Lemma hmem_oim {X Y} (A : op X Y) (v : l2 X) : hmem (oapp A v) (oim A).
  Proof. apply hspan_ub; exists v; reflexivity. Qed.

  (** The image of a subspace. Used for the paper's [e' . B] in rule
      QApply1 and for the lifting [S >> Q] of Definition 19. *)
  Definition himg {X Y} (A : op X Y) (S : hspace X) : hspace Y :=
    hspan (fun w => exists v, hmem v S /\ w = oapp A v).

  Lemma hmem_himg {X Y} (A : op X Y) (S : hspace X) (v : l2 X) :
    hmem v S -> hmem (oapp A v) (himg A S).
  Proof. intros H; apply hspan_ub; exists v; split; [ exact H | reflexivity ]. Qed.

  Lemma himg_le {X Y} (A : op X Y) (S : hspace X) (T : hspace Y) :
    (forall v, hmem v S -> hmem (oapp A v) T) -> himg A S <=h T.
  Proof. intros H; apply hspan_le; intros w [v [Hv ->]]; apply H, Hv. Qed.

  Lemma himg_mono {X Y} (A : op X Y) (S T : hspace X) :
    S <=h T -> himg A S <=h himg A T.
  Proof.
    intros H; apply himg_le; intros v Hv; apply hmem_himg, H, Hv.
  Qed.

  (** An image is below a subspace exactly when the source is below the
      preimage. This is the adjunction that makes image reasoning tractable
      without ever needing to name an element of the image. *)
  Lemma himg_le_via_preim {X Y} (A : op X Y) (S : hspace X) (U : hspace Y) :
    S <=h hpreim A U -> himg A S <=h U.
  Proof.
    intros H v Hv.
    eapply hspan_least; [| exact Hv ].
    intros w [u [Hu ->]].
    apply (proj1 (hmem_hpreim _ _ A U u)), H, Hu.
  Qed.

  Lemma himg_ocomp_le {X Y Z} (A : op Y Z) (B : op X Y) (S : hspace X) :
    himg A (himg B S) <=h himg (ocomp A B) S.
  Proof.
    apply himg_le_via_preim, himg_le; intros u Hu.
    apply hmem_hpreim; rewrite <- oapp_ocomp; apply hmem_himg; exact Hu.
  Qed.

  (** [A A^*] is the identity on the range of an isometry, so applying [A^*]
      and then [A] to something already in [im A] gets it back. This is the
      step that makes rule QApply1's precondition work. *)
  Lemma himg_isometry_meet_oim {X Y} (A : op X Y) (S : hspace Y) :
    oisometry A -> himg A (himg (oadj A) (hmeet S (oim A))) <=h S.
  Proof.
    intros HA.
    eapply hle_trans; [ apply himg_ocomp_le |].
    apply himg_le; intros v Hv.
    apply hmem_hmeet in Hv; destruct Hv as [HvS HvIm].
    rewrite oapp_ocomp, (oim_isometry_fix _ _ A v HA HvIm); exact HvS.
  Qed.

  Lemma himg_hjoin_le {X Y} (A : op X Y) (S T : hspace X) :
    himg A (hjoin S T) <=h hjoin (himg A S) (himg A T).
  Proof.
    apply himg_le_via_preim, hjoin_lub; intros v Hv; apply hmem_hpreim.
    - apply hjoin_lel, hmem_himg, Hv.
    - apply hjoin_ler, hmem_himg, Hv.
  Qed.

  (** A projector annihilates the orthocomplement of its image. *)
  Lemma oproj_kills_ocompl {X} (P : op X X) (v : l2 X) :
    oprojector P -> hmem v (hocompl (oim P)) -> oapp P v = vzero.
  Proof.
    intros [H1 H2] Hv; apply inner_definite.
    (* <Pv, Pv> = <v, P P v> = <v, P v> = 0, the last because v _|_ im P *)
    transitivity (inner v (oapp P v)).
    - rewrite <- H2 at 1.
      rewrite inner_oadj, <- oapp_ocomp, H1; reflexivity.
    - apply inner_eq0_sym.
      apply (proj1 (hmem_hocompl _ _ _) Hv), hmem_oim.
  Qed.

  (** The step that makes rule Measure1's precondition work: applying a
      projector to [(S cap im P) + (im P)^perp] lands inside [S]. *)
  Lemma himg_proj_meet_oim {X} (P : op X X) (S : hspace X) :
    oprojector P -> himg P (hjoin (hmeet S (oim P)) (hocompl (oim P))) <=h S.
  Proof.
    intros HP.
    eapply hle_trans; [ apply himg_hjoin_le |].
    apply hjoin_lub.
    - apply himg_le; intros v Hv.
      apply hmem_hmeet in Hv; destruct Hv as [HvS HvIm].
      rewrite (oim_proj_fix _ P v (proj1 HP) (proj2 HP) HvIm); exact HvS.
    - apply himg_le; intros v Hv.
      rewrite (oproj_kills_ocompl P v HP Hv); apply hmem_vzero.
  Qed.

  Lemma himg_hbot {X Y} (A : op X Y) : himg A hbot = hbot.
  Proof.
    apply hle_antisym; [| apply hbot_le ].
    apply himg_le; intros v Hv; apply hmem_hbot in Hv; subst v.
    apply hmem_hbot, oapp_vzero.
  Qed.

  Lemma himg_oid {X} (S : hspace X) : himg oid S = S.
  Proof.
    apply hle_antisym.
    - apply himg_le; intros v Hv; rewrite oapp_oid; exact Hv.
    - intros v Hv; rewrite <- (oapp_oid _ v) at 1; apply hmem_himg, Hv.
  Qed.

  (* ================================================================= *)
  (** ** Kernels and fixed subspaces

      Both are preimages, so the substrate's [hpreim] already provides them --
      no new assumption. [hfix] is what Definition 27 needs: quantum equality
      is "the subspace fixed by" a particular operator. *)

  Definition oker {X Y} (A : op X Y) : hspace X := hpreim A hbot.

  Lemma hmem_oker {X Y} (A : op X Y) (v : l2 X) :
    hmem v (oker A) <-> oapp A v = vzero.
  Proof. unfold oker; rewrite hmem_hpreim, hmem_hbot; reflexivity. Qed.

  Definition hfix {X} (A : op X X) : hspace X := oker (oadd A (oopp oid)).

  Lemma hmem_hfix {X} (A : op X X) (v : l2 X) :
    hmem v (hfix A) <-> oapp A v = v.
  Proof.
    unfold hfix; rewrite hmem_oker, oapp_oadd, oapp_oopp, oapp_oid.
    split.
    - intros H.
      (* [A v + (-v) = 0], so adding [v] on the right gives [A v = v] *)
      assert (Hv : vadd (vadd (oapp A v) (vopp v)) v = vadd vzero v)
        by (rewrite H; reflexivity).
      rewrite <- vadd_assoc, vadd_opp_l, vadd_zero, vadd_zero_l in Hv.
      exact Hv.
    - intros ->; apply vadd_opp.
  Qed.

  Lemma hfix_oid {X} : hfix (@oid X) = htop.
  Proof.
    apply hle_antisym; [ apply hle_htop |].
    intros v _; apply hmem_hfix, oapp_oid.
  Qed.

  (* ================================================================= *)
  (** ** Tensor products of subspaces *)

  Definition htensor {X Y} (S : hspace X) (T : hspace Y) : hspace (X * Y) :=
    hspan (fun u => exists v w, hmem v S /\ hmem w T /\ u = tensorv v w).

  Lemma hmem_htensor {X Y} (S : hspace X) (T : hspace Y) v w :
    hmem v S -> hmem w T -> hmem (tensorv v w) (htensor S T).
  Proof.
    intros Hv Hw; apply hspan_ub; exists v, w; repeat split; assumption.
  Qed.

  Lemma htensor_le {X Y} (S : hspace X) (T : hspace Y) (U : hspace (X * Y)) :
    (forall v w, hmem v S -> hmem w T -> hmem (tensorv v w) U) ->
    htensor S T <=h U.
  Proof.
    intros H; apply hspan_le; intros u [v [w [Hv [Hw ->]]]]; apply H; assumption.
  Qed.

  Lemma htensor_mono {X Y} (S S' : hspace X) (T T' : hspace Y) :
    S <=h S' -> T <=h T' -> htensor S T <=h htensor S' T'.
  Proof.
    intros H1 H2; apply htensor_le; intros v w Hv Hw.
    apply hmem_htensor; [ apply H1 | apply H2 ]; assumption.
  Qed.

  Lemma htensor_hbot_l {X Y} (T : hspace Y) : htensor (@hbot X) T = hbot.
  Proof.
    apply hle_antisym; [| apply hbot_le ].
    apply htensor_le; intros a b Ha Hb.
    apply hmem_hbot in Ha; subst a.
    apply hmem_hbot, tensorv_vzero_l.
  Qed.

  Lemma htensor_top {X Y} : htensor (@htop X) (@htop Y) = htop.
  Proof.
    apply hle_antisym; [ apply hle_htop |].
    rewrite <- (hspan_tensorv X Y).
    apply hspan_le; intros u [v [w ->]].
    apply hmem_htensor; apply hmem_htop.
  Qed.

  (* ================================================================= *)
  (** ** Swapping tensor factors

      [tcp_ptrace] discards the *second* factor; the semantics of quantum
      initialization needs to discard the first. One reindexing unitary covers
      it, as usual. *)

  Definition pswap {A B : Type} (ab : A * B) : B * A := (snd ab, fst ab).

  Lemma pswap_invol {A B : Type} (ab : A * B) : pswap (pswap ab) = ab.
  Proof. destruct ab; reflexivity. Qed.

  Definition Uswap {A B : Type} : op (A * B) (B * A) :=
    Ubij (@pswap A B) (@pswap B A) (@pswap_invol A B) (@pswap_invol B A).

  Lemma Uswap_ket {A B : Type} (ab : A * B) :
    oapp Uswap (ket ab) = ket (pswap ab).
  Proof. apply Ubij_ket. Qed.

  Lemma Uswap_unitary {A B : Type} : ounitary (@Uswap A B).
  Proof. apply Ubij_ounitary. Qed.

  (** Swapping twice is the identity -- an index computation via [Ubij_ocomp]
      and [Ubij_oid], [pswap]'s own involution supplying the two hypotheses
      each needs. *)
  Lemma Uswap_Uswap {A B : Type} : ocomp (@Uswap B A) (@Uswap A B) = oid.
  Proof.
    apply op_ext_ket; intros [a b].
    rewrite oapp_ocomp, !Uswap_ket, oapp_oid; reflexivity.
  Qed.

  (** Swapping the two factors turns each partial trace into the other -- the
      named-[Uswap] form of the signature's [tcp_ptrace_pswap]. The second
      direction is not a second axiom: it follows from the first applied at
      the swapped type, plus [Uswap_Uswap]. *)
  Lemma tcp_ptrace_Uswap {X Y} (r : tcp (X * Y)) :
    tcp_ptrace (tcp_conj Uswap r) = tcp_ptrace2 r.
  Proof. unfold Uswap; apply tcp_ptrace_pswap. Qed.

  Lemma tcp_ptrace2_Uswap {X Y} (r : tcp (X * Y)) :
    tcp_ptrace2 (tcp_conj Uswap r) = tcp_ptrace r.
  Proof.
    rewrite <- (tcp_ptrace_Uswap (tcp_conj Uswap r)).
    rewrite <- tcp_conj_ocomp, Uswap_Uswap, tcp_conj_oid.
    reflexivity.
  Qed.

  (** The named-[Uswap] form of [tcp_conj_pswap]: conjugating a product by
      the factor swap exchanges the factors. *)
  Lemma tcp_conj_Uswap {X Y} (r : tcp X) (s : tcp Y) :
    tcp_conj Uswap (tcp_tensor r s) = tcp_tensor s r.
  Proof. unfold Uswap; apply tcp_conj_pswap. Qed.

  (** Trace out the *first* factor, keeping the second: the signature's
      [tcp_ptrace2], under the name the rest of the development uses. *)
  Definition tcp_ptraceL {X Y} (r : tcp (X * Y)) : tcp Y := tcp_ptrace2 r.

  Lemma tcp_ptraceL_add {X Y} (r s : tcp (X * Y)) :
    tcp_ptraceL (tcp_add r s) = tcp_add (tcp_ptraceL r) (tcp_ptraceL s).
  Proof. apply tcp_ptrace2_add. Qed.

  Lemma tcp_ptraceL_trace {X Y} (r : tcp (X * Y)) :
    tcp_trace (tcp_ptraceL r) = tcp_trace r.
  Proof. apply tcp_ptrace2_trace. Qed.

  Lemma tcp_ptraceL_scale {X Y} (a : R) (r : tcp (X * Y)) :
    tcp_ptraceL (tcp_scale a r) = tcp_scale a (tcp_ptraceL r).
  Proof. apply tcp_ptrace2_scale. Qed.

  Lemma tcp_ptraceL_tensor {X Y} (r : tcp X) (s : tcp Y) :
    tcp_ptraceL (tcp_tensor r s) = tcp_scale (tcp_trace r) s.
  Proof. apply tcp_ptrace2_tensor. Qed.

  Lemma tcp_scale_zero {X} (a : R) : tcp_scale a (@tcp_zero X) = tcp_zero.
  Proof.
    apply tcp_trace_faithful; rewrite tcp_trace_scale, tcp_trace_zero; ring.
  Qed.

  Lemma tcp_ptrace_zero {X Y} : tcp_ptrace (@tcp_zero (X * Y)) = tcp_zero.
  Proof.
    apply tcp_trace_faithful; rewrite tcp_ptrace_trace; apply tcp_trace_zero.
  Qed.

  Lemma tcp_ptraceL_zero {X Y} : tcp_ptraceL (@tcp_zero (X * Y)) = tcp_zero.
  Proof.
    apply tcp_trace_faithful; rewrite tcp_ptraceL_trace; apply tcp_trace_zero.
  Qed.

  (** The trace is multiplicative on tensors -- read off from [tcp_ptrace_tensor]
      and the trace-preservation of the partial trace. *)
  Lemma tcp_trace_tensor {X Y} (r : tcp X) (s : tcp Y) :
    tcp_trace (tcp_tensor r s) = (tcp_trace r * tcp_trace s)%R.
  Proof.
    rewrite <- (tcp_ptrace_trace X Y (tcp_tensor r s)).
    rewrite tcp_ptrace_tensor, tcp_trace_scale; ring.
  Qed.

  Lemma tcp_ptraceL_sum {X Y J} (F : J -> tcp (X * Y)) :
    tcp_summable F ->
    tcp_ptraceL (tcp_sum F) = tcp_sum (fun j => tcp_ptraceL (F j)).
  Proof. apply tcp_ptrace2_sum. Qed.

  Lemma tcp_summable_ptraceL {X Y J} (F : J -> tcp (X * Y)) :
    tcp_summable F -> tcp_summable (fun j => tcp_ptraceL (F j)).
  Proof.
    intros H; apply tcp_summable_trace.
    apply (summable_mono _ (fun j => tcp_trace (F j)));
      [ apply tcp_summable_trace; exact H
      | intros j; rewrite tcp_ptraceL_trace; apply Rle_refl ].
  Qed.

  Lemma tcp_summable_tensor_r {X Y J} (r : tcp X) (F : J -> tcp Y) :
    tcp_summable F -> tcp_summable (fun j => tcp_tensor r (F j)).
  Proof.
    intros H; apply tcp_summable_trace.
    apply (summable_mono _ (fun j => (tcp_trace r * tcp_trace (F j))%R)).
    - apply summable_scale;
        [ apply tcp_trace_nonneg
        | intros j; apply tcp_trace_nonneg
        | apply tcp_summable_trace; exact H ].
    - intros j; rewrite tcp_trace_tensor; apply Rle_refl.
  Qed.

  Lemma tcp_tensor_zero_r {X Y} (r : tcp X) :
    tcp_tensor r (@tcp_zero Y) = tcp_zero.
  Proof.
    apply tcp_trace_faithful; rewrite tcp_trace_tensor, tcp_trace_zero; ring.
  Qed.

  (* ================================================================= *)
  (** ** The order and finite sums on positive trace-class operators *)

  Lemma tcp_add_zero_l {X} (r : tcp X) : tcp_add tcp_zero r = r.
  Proof. rewrite tcp_add_comm; apply tcp_add_zero. Qed.

  Lemma tcp_zero_le {X} (r : tcp X) : tcp_le tcp_zero r.
  Proof.
    apply tcp_le_add; exists r; rewrite tcp_add_zero_l; reflexivity.
  Qed.

  Lemma tcp_lsum_nil {X J} (F : J -> tcp X) : tcp_lsum F nil = tcp_zero.
  Proof. reflexivity. Qed.

  Lemma tcp_lsum_cons {X J} (F : J -> tcp X) (j : J) (l : list J) :
    tcp_lsum F (j :: l) = tcp_add (F j) (tcp_lsum F l).
  Proof. reflexivity. Qed.

  Lemma tcp_trace_lsum {X J} (F : J -> tcp X) (l : list J) :
    tcp_trace (tcp_lsum F l) = lsum (fun j => tcp_trace (F j)) l.
  Proof.
    induction l as [| j t IH].
    - rewrite tcp_lsum_nil, tcp_trace_zero; reflexivity.
    - rewrite tcp_lsum_cons, tcp_trace_add, IH; reflexivity.
  Qed.

  (** A family supported at one index: its finite partial sums are either zero
      or that one term. *)
  Lemma tcp_lsum_supported {X J} (F : J -> tcp X) (j0 : J) (l : list J) :
    NoDup l -> (forall j, j <> j0 -> F j = tcp_zero) ->
    tcp_lsum F l =
      (if excluded_middle_informative (In j0 l) then F j0 else tcp_zero).
  Proof.
    intros Hnd H; induction l as [| j t IH].
    - destruct (excluded_middle_informative (In j0 nil)) as [Hin | _];
        [ destruct Hin | reflexivity ].
    - inversion Hnd as [| ? ? Hnj Hndt]; subst.
      rewrite tcp_lsum_cons, (IH Hndt).
      destruct (excluded_middle_informative (j = j0)) as [-> | Hne].
      + destruct (excluded_middle_informative (In j0 t)) as [Hin | _];
          [ contradiction |].
        destruct (excluded_middle_informative (In j0 (j0 :: t))) as [_ | Hno];
          [ apply tcp_add_zero | exfalso; apply Hno; left; reflexivity ].
      + rewrite (H j Hne), tcp_add_zero_l.
        destruct (excluded_middle_informative (In j0 t)) as [Hin | Hnin];
          destruct (excluded_middle_informative (In j0 (j :: t))) as [Hin' | Hno];
          try reflexivity.
        * exfalso; apply Hno; right; exact Hin.
        * destruct Hin' as [Heq | Hin']; [ congruence | contradiction ].
  Qed.

  Lemma tcp_summable_conj {X Y J} (A : op X Y) (F : J -> tcp X) :
    ocomp (oadj A) A = oid -> tcp_summable F ->
    tcp_summable (fun j => tcp_conj A (F j)).
  Proof.
    intros HA Hs; apply tcp_summable_trace.
    apply (summable_mono _ (fun j => tcp_trace (F j))).
    - apply tcp_summable_trace; exact Hs.
    - intros j; rewrite (tcp_trace_conj_isometry _ _ _ _ HA); apply Rle_refl.
  Qed.

  Lemma tcp_summable_singleton {X J} (F : J -> tcp X) (j0 : J) :
    (forall j, j <> j0 -> F j = tcp_zero) -> tcp_summable F.
  Proof.
    intros H; apply tcp_summable_trace.
    apply summable_bounded with (M := tcp_trace (F j0)).
    intros l Hnd.
    rewrite <- tcp_trace_lsum, (tcp_lsum_supported F j0 l Hnd H).
    destruct (excluded_middle_informative (In j0 l)).
    - apply Rle_refl.
    - rewrite tcp_trace_zero; apply tcp_trace_nonneg.
  Qed.

  (** ... and so the infinite sum collapses to that term. This is what makes
      the semantics of assignment and measurement computable on point masses. *)
  Lemma tcp_sum_singleton {X J} (F : J -> tcp X) (j0 : J) :
    (forall j, j <> j0 -> F j = tcp_zero) -> tcp_sum F = F j0.
  Proof.
    intros H.
    assert (Hs : tcp_summable F) by (apply (tcp_summable_singleton F j0); exact H).
    apply tcp_ext.
    - apply tcp_sum_least; [ exact Hs |].
      intros l Hnd; rewrite (tcp_lsum_supported F j0 l Hnd H).
      destruct (excluded_middle_informative (In j0 l));
        [ apply tcp_le_refl | apply tcp_zero_le ].
    - replace (F j0) with (tcp_lsum F (j0 :: nil))
        by (rewrite tcp_lsum_cons, tcp_lsum_nil; apply tcp_add_zero).
      apply tcp_sum_ub; [ exact Hs |].
      constructor; [ intros HH; inversion HH | constructor ].
  Qed.

  (** *** Tonelli, specialized to a product index

      The dependent-sum form of [tcp_sum_sigma] reindexed along
      [sigT (fun _ => A) ~= K * A]. *)

  Lemma tcp_sum_pair {X} {K A : Type} (F : K -> A -> tcp X) :
    (forall k, tcp_summable (F k)) ->
    tcp_summable (fun k => tcp_sum (F k)) ->
    tcp_summable (fun p : K * A => F (fst p) (snd p)) /\
    tcp_sum (fun k => tcp_sum (F k))
    = tcp_sum (fun p : K * A => F (fst p) (snd p)).
  Proof.
    intros Hk Hit.
    destruct (tcp_sum_sigma X K (fun _ : K => A) F Hk Hit) as [Hs Heq].
    (* [sigT (fun _ => A)] and [K * A] are in bijection *)
    destruct (tcp_sum_bij X (sigT (fun _ : K => A)) (K * A)
                (fun p : K * A => existT (fun _ : K => A) (fst p) (snd p))
                (fun q : sigT (fun _ : K => A) => (projT1 q, projT2 q))
                (fun q => F (projT1 q) (projT2 q))
                (fun p => match p with (k, a) => eq_refl end)
                (fun q => match q with existT _ k a => eq_refl end)
                Hs) as [Hs2 Heq2].
    split; [ exact Hs2 | rewrite Heq, <- Heq2; reflexivity ].
  Qed.

  (** Exchanging the two indices of a double sum. *)
  Lemma tcp_sum_swap {X} {K A : Type} (F : K -> A -> tcp X) :
    (forall k, tcp_summable (F k)) ->
    tcp_summable (fun k => tcp_sum (F k)) ->
    (forall a, tcp_summable (fun k => F k a)) ->
    tcp_summable (fun a => tcp_sum (fun k => F k a)) ->
    tcp_sum (fun k => tcp_sum (F k))
    = tcp_sum (fun a => tcp_sum (fun k => F k a)).
  Proof.
    intros H1 H2 H3 H4.
    destruct (tcp_sum_pair F H1 H2) as [_ Heq1].
    destruct (tcp_sum_pair (fun a k => F k a) H3 H4) as [Hs2 Heq2].
    rewrite Heq1, Heq2.
    (* the two product indexings differ by the swap *)
    destruct (tcp_sum_bij X (A * K) (K * A)
                (fun p : K * A => (snd p, fst p))
                (fun q : A * K => (snd q, fst q))
                (fun q : A * K => F (snd q) (fst q))
                (fun p => match p with (k, a) => eq_refl end)
                (fun q => match q with (a, k) => eq_refl end)
                Hs2) as [_ Heq3].
    rewrite <- Heq3; reflexivity.
  Qed.

  (** *** A sum over [bool] is a binary addition

      Needed because separability has to be closed under binary sums (rule
      If1), and the only way to combine two decompositions is to index them
      jointly. *)

  Lemma tcp_le_add_l {X} (r s : tcp X) : tcp_le r (tcp_add r s).
  Proof. apply tcp_le_add; exists s; reflexivity. Qed.

  Lemma tcp_le_add_r {X} (r s : tcp X) : tcp_le s (tcp_add r s).
  Proof. rewrite tcp_add_comm; apply tcp_le_add_l. Qed.

  Lemma tcp_lsum_bool_le {X} (G : bool -> tcp X) (l : list bool) :
    NoDup l -> tcp_le (tcp_lsum G l) (tcp_add (G true) (G false)).
  Proof.
    intros Hnd; destruct l as [| b t].
    - rewrite tcp_lsum_nil; apply tcp_zero_le.
    - destruct (nodup_bool_tail b t Hnd) as [-> | ->].
      + rewrite tcp_lsum_cons, tcp_lsum_nil, tcp_add_zero.
        destruct b; [ apply tcp_le_add_l | apply tcp_le_add_r ].
      + rewrite !tcp_lsum_cons, tcp_lsum_nil, tcp_add_zero.
        destruct b; simpl; [ apply tcp_le_refl |].
        rewrite tcp_add_comm; apply tcp_le_refl.
  Qed.

  Lemma tcp_summable_bool {X} (G : bool -> tcp X) : tcp_summable G.
  Proof.
    apply tcp_summable_trace, summable_bounded
      with (M := (tcp_trace (G true) + tcp_trace (G false))%R).
    intros l Hnd; apply lsum_bool_le;
      [ intros b; apply tcp_trace_nonneg | exact Hnd ].
  Qed.

  Lemma tcp_sum_bool {X} (G : bool -> tcp X) :
    tcp_sum G = tcp_add (G true) (G false).
  Proof.
    apply tcp_ext.
    - apply tcp_sum_least; [ apply tcp_summable_bool |].
      intros l Hnd; apply tcp_lsum_bool_le; exact Hnd.
    - replace (tcp_add (G true) (G false))
         with (tcp_lsum G (true :: false :: nil))
         by (unfold tcp_lsum; simpl; rewrite tcp_add_zero; reflexivity).
      apply tcp_sum_ub; [ apply tcp_summable_bool |].
      constructor; [ intros H; destruct H as [H | H]; [ discriminate | destruct H ]
                   | constructor; [ intros H; destruct H | constructor ] ].
  Qed.

  (** The everywhere-zero family sums to zero. *)
  Lemma tcp_sum_zero {X J} (F : J -> tcp X) :
    (forall j, F j = tcp_zero) -> tcp_sum F = tcp_zero.
  Proof.
    intros H.
    destruct (classic (inhabited J)) as [[j0] | Hno].
    - rewrite (tcp_sum_singleton F j0); [ apply H | intros j _; apply H ].
    - apply tcp_ext; [| apply tcp_zero_le ].
      apply tcp_sum_least.
      + apply tcp_summable_trace, summable_bounded with (M := 0%R).
        intros l Hnd; rewrite <- tcp_trace_lsum.
        destruct l as [| j t]; [ rewrite tcp_lsum_nil, tcp_trace_zero; apply Rle_refl |].
        exfalso; apply Hno; exact (inhabits j).
      + intros l Hnd; destruct l as [| j t].
        * rewrite tcp_lsum_nil; apply tcp_le_refl.
        * exfalso; apply Hno; exact (inhabits j).
  Qed.

  (* ================================================================= *)
  (** ** Division

      Definition 20: [phi in A / psi  iff  phi (x) psi in A]. Immediate from
      the substrate's [hpreim] and [otensorR]; the paper's remark that
      [(B (x) span{psi}) / psi = B] is the reason for the notation. *)

  Definition hdiv {X Y} (A : hspace (X * Y)) (w : l2 Y) : hspace X :=
    hpreim (otensorR w) A.

  Lemma hmem_hdiv {X Y} (A : hspace (X * Y)) (w : l2 Y) (v : l2 X) :
    hmem v (hdiv A w) <-> hmem (tensorv v w) A.
  Proof.
    unfold hdiv; rewrite hmem_hpreim, otensorR_app; reflexivity.
  Qed.

  Lemma hdiv_mono {X Y} (A B : hspace (X * Y)) (w : l2 Y) :
    A <=h B -> hdiv A w <=h hdiv B w.
  Proof.
    intros H v Hv; apply hmem_hdiv; apply H; apply hmem_hdiv; exact Hv.
  Qed.

  (** Division by a state on the *first* factor -- the orientation
      Definition 20 uses, since the register being initialized is the first
      factor of the register split. *)
  Definition hdivL {X Y} (A : hspace (X * Y)) (v : l2 X) : hspace Y :=
    hpreim (otensorL v) A.

  Lemma hmem_hdivL {X Y} (A : hspace (X * Y)) (v : l2 X) (w : l2 Y) :
    hmem w (hdivL A v) <-> hmem (tensorv v w) A.
  Proof.
    unfold hdivL; rewrite hmem_hpreim, otensorL_app; reflexivity.
  Qed.

  Lemma hdivL_mono {X Y} (A B : hspace (X * Y)) (v : l2 X) :
    A <=h B -> hdivL A v <=h hdivL B v.
  Proof.
    intros H w Hw; apply hmem_hdivL; apply H; apply hmem_hdivL; exact Hw.
  Qed.

End HTheory.
