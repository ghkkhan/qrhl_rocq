(** * The qRHL judgment.

    Section 5: Definition 35 and Lemma 36.

    Definition 35: "Let [c1], [c2] be programs with [fv(c1), fv(c2) subseteq V].
    Let [A], [B] be predicates over [V1 V2]. Then [{A} c1 ~ c2 {B}] holds iff
    for all [(V1,V2)]-separable [rho in T^+_cq[V1 V2]] that satisfy [A], we have
    that there exists a [(V1,V2)]-separable [rho' in T^+_cq[V1 V2]] that
    satisfies [B] such that

        tr^[V1]_V2 rho'  =  [idx_1 c1] (tr^[V1]_V2 rho)
        tr^[V2]_V1 rho'  =  [idx_2 c2] (tr^[V2]_V1 rho)."

    Two things are worth noticing about how this comes out here.

    First, [idx_1] and [idx_2] have vanished from the statement. The paper needs
    them because [V1] and [V2] are fresh copies of [V], so a program over [V]
    has to be renamed before it can act on them. Here the relational memory is
    indexed by [side * var], so [tr^[V1]_V2 rho] is already a cq-state over the
    untagged [V] and [denote c1] applies to it directly. This is the same
    simplification as everywhere else in the development, and it is at its most
    visible in the central definition.

    Second, separability is a *definition*, not an assumption: section 2 says an
    operator is [(V1,V2)]-separable iff "it can be written as [sum_i rho_i (x)
    rho'_i]", and the substrate already has arbitrary sums and tensors of
    positive trace-class operators, so that transcribes directly.

    Definition 35 is the whole point of the development: everything in
    [Rules/] is a theorem *about this definition*. *)

From Stdlib Require Import List Lra.
From QRHL.Substrate Require Import Ambient Cnum Sums Interface Theory.
From QRHL.Core Require Import Vars Expr Registers Syntax Semantics Predicate QEq.

Module JudgmentTheory (S : HILBERT_SUBSTRATE) (V : PROGRAM_VARS).
  Include QEqTheory S V.

  (* ================================================================= *)
  (** ** Separability

      Section 2: "We call an operator [rho in T^+[V1 V2]] [(V1,V2)]-separable
      iff it can be written as [sum_i rho_i (x) rho'_i] for some
      [rho_i in T^+[V1]] and [rho'_i in T^+[V2]]." *)

  Definition tcp_sep {X Y : Type} (r : tcp (X * Y)) : Prop :=
    exists (J : Type) (f : J -> tcp X) (g : J -> tcp Y),
      tcp_summable (fun j => tcp_tensor (f j) (g j)) /\
      r = tcp_sum (fun j => tcp_tensor (f j) (g j)).

  Lemma tcp_sep_tensor {X Y} (a : tcp X) (b : tcp Y) :
    tcp_sep (tcp_tensor a b).
  Proof.
    exists unit, (fun _ => a), (fun _ => b); split.
    - apply (tcp_summable_singleton _ tt); intros [] H; congruence.
    - symmetry.
      apply (tcp_sum_singleton (fun _ : unit => tcp_tensor a b) tt).
      intros [] H; congruence.
  Qed.

  Lemma tcp_sep_zero {X Y} : tcp_sep (@tcp_zero (X * Y)).
  Proof.
    exists unit, (fun _ => tcp_zero), (fun _ => tcp_zero); split.
    - apply (tcp_summable_singleton _ tt); intros [] H; congruence.
    - rewrite (tcp_sum_singleton _ tt) by (intros [] H; congruence).
      symmetry; apply tcp_trace_faithful.
      rewrite tcp_trace_tensor, tcp_trace_zero; ring.
  Qed.

  (** Separability of a relational quantum state, i.e. across the two sides.
      [Urqpair] is the isomorphism [l2[V1^qu V2^qu] ~= l2[V1^qu] (x) l2[V2^qu]]
      from [Registers.v]. *)
  Definition rsep (r : tcp rqmem) : Prop := tcp_sep (tcp_conj Urqpair r).

  Lemma rsep_zero : rsep tcp_zero.
  Proof. unfold rsep; rewrite tcp_conj_zero; apply tcp_sep_zero. Qed.

  (** Conjugating by the factor swap preserves separability: it just
      exchanges the two families witnessing it. Needed by rule Sym, whose
      witness conjugates by [Urqswap]. *)
  Lemma tcp_sep_Uswap {X Y} (r : tcp (X * Y)) :
    tcp_sep r -> tcp_sep (tcp_conj Uswap r).
  Proof.
    intros [J [f [g [Hs Heq]]]].
    exists J, g, f; split.
    - assert (Heq2 : (fun j => tcp_tensor (g j) (f j))
                      = (fun j => tcp_conj Uswap (tcp_tensor (f j) (g j))))
        by (apply funext; intros j; symmetry; apply tcp_conj_Uswap).
      rewrite Heq2.
      apply (tcp_summable_conj Uswap _ (proj1 Uswap_unitary) Hs).
    - rewrite Heq, (tcp_conj_sum _ _ _ _ _ Hs).
      f_equal; apply funext; intros j; apply tcp_conj_Uswap.
  Qed.

  (** [rsep]'s own form: swapping the two sides preserves separability. *)
  Lemma rsep_Urqswap (r : tcp rqmem) : rsep r -> rsep (tcp_conj Urqswap r).
  Proof.
    intros Hr; unfold rsep.
    rewrite <- tcp_conj_ocomp, Urqpair_Urqswap, tcp_conj_ocomp.
    apply tcp_sep_Uswap, Hr.
  Qed.


  (** A cq-state is separable when each of its blocks is. The classical part of
      a cq-operator is already block-diagonal across the two sides, so nothing
      more is needed. *)
  Definition rcqs_sep (r : rcqs) : Prop := forall rm, rsep (r rm).


  (* ================================================================= *)
  (** ** Swapping a relational state

      Rule Sym's witness: read the given state at the memory with its
      classical halves exchanged, then apply the quantum side swap. This is
      the state-level counterpart of [predswap] in [Predicate.v], and
      [rcqs_swap_wf] / [rcqs_swap_sep] / [rcqs_swap_psat] below are exactly
      what makes [predswap]'s choices line up with it. *)

  Definition rcqs_swap (r : rcqs) : rcqs :=
    fun rm => tcp_conj Urqswap (r (rcmem_swap rm)).

  Lemma rcqs_swap_wf (r : rcqs) : rcqs_wf r -> rcqs_wf (rcqs_swap r).
  Proof.
    intros Hr; unfold rcqs_wf, rcqs_swap.
    apply (tcp_summable_conj Urqswap _ (proj1 Urqswap_unitary)).
    apply (proj1 (tcp_sum_bij rqmem rcmem rcmem rcmem_swap rcmem_swap r
                    rcmem_swap_invol rcmem_swap_invol Hr)).
  Qed.

  Lemma rcqs_swap_sep (r : rcqs) : rcqs_sep r -> rcqs_sep (rcqs_swap r).
  Proof. intros Hr rm; unfold rcqs_swap; apply rsep_Urqswap, Hr. Qed.

  (** The [psat] step in both directions rule Sym needs: reading the state
      swap's support needs only [himg]'s monotonicity, in the direction that
      matches the hypothesis, and [himg_Urqswap_shrink] in the other. *)

  Lemma rcqs_swap_psat_from_predswap (r : rcqs) (A : pred) :
    psat r (predswap A) -> psat (rcqs_swap r) A.
  Proof.
    intros Hsat rm; unfold rcqs_swap.
    rewrite tcp_supp_conj.
    change (hspan (fun w => exists v, hmem v (tcp_supp (r (rcmem_swap rm)))
                                      /\ w = oapp Urqswap v))
      with (himg Urqswap (tcp_supp (r (rcmem_swap rm)))).
    eapply hle_trans; [ apply himg_mono, (Hsat (rcmem_swap rm)) |].
    rewrite ev_predswap, rcmem_swap_invol; apply himg_Urqswap_shrink.
  Qed.

  Lemma rcqs_swap_psat_to_predswap (r : rcqs) (A : pred) :
    psat r A -> psat (rcqs_swap r) (predswap A).
  Proof.
    intros Hsat rm; unfold rcqs_swap.
    rewrite tcp_supp_conj.
    change (hspan (fun w => exists v, hmem v (tcp_supp (r (rcmem_swap rm)))
                                      /\ w = oapp Urqswap v))
      with (himg Urqswap (tcp_supp (r (rcmem_swap rm)))).
    rewrite ev_predswap.
    apply himg_mono, (Hsat (rcmem_swap rm)).
  Qed.

  (** Swapping the state exchanges the two projections. *)

  Lemma rcqs_projL_swap (r : rcqs) : rcqs_projL (rcqs_swap r) = rcqs_projR r.
  Proof.
    apply funext; intros m1; unfold rcqs_projL, rcqs_projR, rcqs_swap.
    f_equal; apply funext; intros m2.
    change (rcmem_swap (m1, m2)) with (m2, m1).
    apply rtcpL_Urqswap.
  Qed.

  Lemma rcqs_projR_swap (r : rcqs) : rcqs_projR (rcqs_swap r) = rcqs_projL r.
  Proof.
    apply funext; intros m2; unfold rcqs_projL, rcqs_projR, rcqs_swap.
    f_equal; apply funext; intros m1.
    change (rcmem_swap (m1, m2)) with (m2, m1).
    apply rtcpR_Urqswap.
  Qed.
  (** Separability is closed under binary sums: index the two decompositions
      jointly over [bool], flatten with [tcp_sum_sigma], and use that a sum
      over [bool] is a binary addition. *)
  Lemma tcp_sep_add {X Y} (r s : tcp (X * Y)) :
    tcp_sep r -> tcp_sep s -> tcp_sep (tcp_add r s).
  Proof.
    intros [J1 [f1 [g1 [Hs1 Hr]]]] [J2 [f2 [g2 [Hs2 Hss]]]].
    pose (Pk := fun b : bool => if b then J1 else J2).
    pose (ff := fun p : sigT Pk =>
                  match p with
                  | existT _ true j  => f1 j
                  | existT _ false j => f2 j
                  end).
    pose (gg := fun p : sigT Pk =>
                  match p with
                  | existT _ true j  => g1 j
                  | existT _ false j => g2 j
                  end).
    pose (F := fun (b : bool) (j : Pk b) =>
                 tcp_tensor (ff (existT Pk b j)) (gg (existT Pk b j))).
    assert (Hfun : (fun p : sigT Pk => F (projT1 p) (projT2 p))
                   = (fun p : sigT Pk => tcp_tensor (ff p) (gg p)))
      by (apply funext; intros [[|] j]; reflexivity).
    assert (HFa : forall b, tcp_summable (F b)) by (intros [|]; assumption).
    assert (HFit : tcp_summable (fun b => tcp_sum (F b)))
      by apply tcp_summable_bool.
    destruct (tcp_sum_sigma _ _ Pk F HFa HFit) as [Hsig Heqsig].
    exists (sigT Pk), ff, gg; split.
    - rewrite <- Hfun; exact Hsig.
    - rewrite <- Hfun, <- Heqsig, tcp_sum_bool.
      assert (HFt : tcp_sum (F true) = r)
        by (rewrite Hr; f_equal; apply funext; intros j; reflexivity).
      assert (HFf : tcp_sum (F false) = s)
        by (rewrite Hss; f_equal; apply funext; intros j; reflexivity).
      rewrite HFt, HFf; reflexivity.
  Qed.

  (** Acting on one tensor factor sends a sum of products to a sum of
      products. The hypothesis is only needed to keep the family summable, so
      it is stated as the trace bound rather than as isometry or projectivity;
      both of the rules that use this supply it. *)
  Lemma tcp_sep_conj_tensorL {X Y} (A : op X X) (r : tcp (X * Y)) :
    (forall s : tcp X, (tcp_trace (tcp_conj A s) <= tcp_trace s)%R) ->
    tcp_sep r -> tcp_sep (tcp_conj (tensoro A oid) r).
  Proof.
    intros Hbd [J [f [g [Hs Heq]]]].
    exists J, (fun j => tcp_conj A (f j)), g; split.
    - apply tcp_summable_trace.
      apply (summable_mono _ (fun j => tcp_trace (tcp_tensor (f j) (g j)))).
      + apply tcp_summable_trace; exact Hs.
      + intros j; rewrite !tcp_trace_tensor.
        apply Rmult_le_compat_r; [ apply tcp_trace_nonneg | apply Hbd ].
    - rewrite Heq, (tcp_conj_sum _ _ _ _ _ Hs).
      f_equal; apply funext; intros j.
      rewrite tcp_conj_tensor, tcp_conj_oid; reflexivity.
  Qed.

  Lemma rsep_roliftL (P : qset) (A : op (qsub P) (qsub P)) (r : tcp rqmem) :
    (forall s : tcp qmem,
        (tcp_trace (tcp_conj (olift P A) s) <= tcp_trace s)%R) ->
    rsep r -> rsep (tcp_conj (roliftL P A) r).
  Proof.
    intros Hbd Hr; unfold rsep; rewrite conj_roliftL.
    apply tcp_sep_conj_tensorL; assumption.
  Qed.

  Lemma tcp_sep_scale {X Y} (a : R) (r : tcp (X * Y)) :
    tcp_sep r -> tcp_sep (tcp_scale a r).
  Proof.
    intros [J [f [g [Hs Hr]]]].
    exists J, (fun j => tcp_scale a (f j)), g; split.
    - apply tcp_summable_trace.
      apply (summable_mono _ (fun j => (Rabs a * tcp_trace (tcp_tensor (f j) (g j)))%R)).
      + apply summable_scale;
          [ apply Rabs_pos
          | intros j; apply tcp_trace_nonneg
          | apply tcp_summable_trace; exact Hs ].
      + intros j; rewrite !tcp_trace_tensor, tcp_trace_scale.
        rewrite <- Rmult_assoc.
        apply Rmult_le_compat_r; [ apply tcp_trace_nonneg |].
        apply Rmult_le_compat_r; [ apply tcp_trace_nonneg | apply Rle_abs ].
    - rewrite Hr, (tcp_scale_sum _ _ _ _ Hs).
      f_equal; apply funext; intros j; apply tcp_scale_tensor_l.
  Qed.

  (* ================================================================= *)
  (* ================================================================= *)
  (** ** The one-sided reindexing

      [(rm, a) |-> (rm with x_1 := a, the old x_1)], the relational
      counterpart of [sbeta] in [Semantics.v], and an involution for the same
      reason. Every rule whose statement updates a classical variable on one
      side -- Assign1, Sample1, Measure1 -- reindexes its double sum with it:
      the pair (target memory, summation index) is in bijection with (source
      memory, the target's old value of [x]), and it is only after that
      reindexing that the sum collapses. *)

  Definition rbeta (x : cvar) (p : rcmem * ctype x) : rcmem * ctype x :=
    (rcupd (fst p) (SL, x) (snd p), csel SL (fst p) x).

  Lemma rbeta_invol (x : cvar) (p : rcmem * ctype x) :
    rbeta x (rbeta x p) = p.
  Proof.
    destruct p as [rm a]; unfold rbeta; cbn [fst snd].
    rewrite rcupd_rcupd_L, rcupd_id_L, csel_rcupd_L, cupd_same; reflexivity.
  Qed.

  Lemma rbeta_inj (x : cvar) (p q : rcmem * ctype x) :
    rbeta x p = rbeta x q -> p = q.
  Proof.
    intros H; rewrite <- (rbeta_invol x p), <- (rbeta_invol x q), H;
      reflexivity.
  Qed.

  Lemma rcupd_inj (x : cvar) (rm : rcmem) (a b : ctype x) :
    rcupd rm (SL, x) a = rcupd rm (SL, x) b -> a = b.
  Proof.
    intros Hab.
    assert (H : csel SL (rcupd rm (SL, x) a) x
                = csel SL (rcupd rm (SL, x) b) x)
      by (rewrite Hab; reflexivity).
    rewrite !csel_rcupd_L, !cupd_same in H; exact H.
  Qed.

  (* ================================================================= *)
  (** ** The two-sided reindexing

      The relational counterpart of [rbeta], for rules that update a variable
      on *each* side at once -- JointSample, JointMeasureSimple. [(SL, x)] and
      [(SR, y)] are always distinct relational variables (different sides), so
      unlike the paper's statement this needs no side condition relating [x]
      and [y]; the two updates simply commute ([rcupd_comm_LR]). *)

  Definition rbeta2 (x y : cvar) (p : rcmem * (ctype x * ctype y))
    : rcmem * (ctype x * ctype y) :=
    (rcupd (rcupd (fst p) (SL, x) (fst (snd p))) (SR, y) (snd (snd p)),
     (csel SL (fst p) x, csel SR (fst p) y)).

  Lemma rbeta2_invol (x y : cvar) (p : rcmem * (ctype x * ctype y)) :
    rbeta2 x y (rbeta2 x y p) = p.
  Proof.
    destruct p as [rm [a b]]; unfold rbeta2; cbn [fst snd].
    rewrite csel_rcupd_R_other, csel_rcupd_L, cupd_same,
            csel_rcupd_R, cupd_same.
    rewrite (rcupd_comm_LR rm x a y b), rcupd_rcupd_L.
    rewrite <- (csel_rcupd_R_other rm y b).
    rewrite rcupd_id_L, rcupd_rcupd_R, rcupd_id_R.
    reflexivity.
  Qed.

  Lemma rbeta2_inj (x y : cvar) (p q : rcmem * (ctype x * ctype y)) :
    rbeta2 x y p = rbeta2 x y q -> p = q.
  Proof.
    intros H; rewrite <- (rbeta2_invol x y p), <- (rbeta2_invol x y q), H;
      reflexivity.
  Qed.

  Lemma rcupd2_inj (x y : cvar) (rm : rcmem) (p q : ctype x * ctype y) :
    rcupd (rcupd rm (SL, x) (fst p)) (SR, y) (snd p)
    = rcupd (rcupd rm (SL, x) (fst q)) (SR, y) (snd q) -> p = q.
  Proof.
    intros H.
    assert (Ha : fst p = fst q).
    { assert (Hc : csel SL (rcupd (rcupd rm (SL, x) (fst p)) (SR, y) (snd p)) x
                   = csel SL (rcupd (rcupd rm (SL, x) (fst q)) (SR, y) (snd q)) x)
        by (rewrite H; reflexivity).
      rewrite !csel_rcupd_R_other, !csel_rcupd_L, !cupd_same in Hc; exact Hc. }
    assert (Hb : snd p = snd q).
    { assert (Hc : csel SR (rcupd (rcupd rm (SL, x) (fst p)) (SR, y) (snd p)) y
                   = csel SR (rcupd (rcupd rm (SL, x) (fst q)) (SR, y) (snd q)) y)
        by (rewrite H; reflexivity).
      rewrite !csel_rcupd_R, !cupd_same in Hc; exact Hc. }
    destruct p, q; cbn in Ha, Hb; subst; reflexivity.
  Qed.

  (** The two "undo one step" corollaries of [rbeta2_invol] that
      [JointSample] needs directly: the first component recovers [rm] no
      matter which order the two updates are applied in (they commute), and
      the second component recovers the pair. *)
  Lemma rcupd2_id (x y : cvar) (rm : rcmem) (p : ctype x * ctype y) :
    rcupd (rcupd (rcupd (rcupd rm (SL, x) (fst p)) (SR, y) (snd p))
                  (SR, y) (csel SR rm y)) (SL, x) (csel SL rm x)
    = rm.
  Proof.
    rewrite <- (rcupd_comm_LR (rcupd (rcupd rm (SL, x) (fst p)) (SR, y) (snd p))
                  x (csel SL rm x) y (csel SR rm y)).
    exact (f_equal fst (rbeta2_invol x y (rm, p))).
  Qed.

  Lemma csel2_id (x y : cvar) (rm : rcmem) (p : ctype x * ctype y) :
    (csel SL (rcupd (rcupd rm (SL, x) (fst p)) (SR, y) (snd p)) x,
     csel SR (rcupd (rcupd rm (SL, x) (fst p)) (SR, y) (snd p)) y) = p.
  Proof.
    exact (f_equal snd (rbeta2_invol x y (rm, p))).
  Qed.

  (* ================================================================= *)
  (** ** Adding and restricting relational states

      The operations a rule needs when it splits its input by a classical
      condition and recombines the two witnesses: rules If1 and JointIf. *)

  Definition rcqs_add (r s : rcqs) : rcqs := fun rm => tcp_add (r rm) (s rm).

  Definition rrestr (e : rexpr bool) (r : rcqs) : rcqs :=
    fun rm => if ev e rm then r rm else tcp_zero.

  Definition rrestrn (e : rexpr bool) (r : rcqs) : rcqs :=
    fun rm => if ev e rm then tcp_zero else r rm.

  Lemma rrestr_split (e : rexpr bool) (r : rcqs) :
    rcqs_add (rrestr e r) (rrestrn e r) = r.
  Proof.
    apply funext; intros rm; unfold rcqs_add, rrestr, rrestrn.
    destruct (ev e rm); [ apply tcp_add_zero | apply tcp_add_zero_l ].
  Qed.

  Lemma rcqs_add_wf (r s : rcqs) :
    rcqs_wf r -> rcqs_wf s -> rcqs_wf (rcqs_add r s).
  Proof.
    intros Hr Hs; apply tcp_summable_trace.
    apply (summable_mono _ (fun rm => (tcp_trace (r rm) + tcp_trace (s rm))%R)).
    - apply summable_add; apply tcp_summable_trace; assumption.
    - intros rm; unfold rcqs_add; rewrite tcp_trace_add; apply Rle_refl.
  Qed.

  Lemma rcqs_add_sep (r s : rcqs) :
    rcqs_sep r -> rcqs_sep s -> rcqs_sep (rcqs_add r s).
  Proof.
    intros Hr Hs rm; unfold rsep, rcqs_add.
    rewrite tcp_conj_add; apply tcp_sep_add; [ apply Hr | apply Hs ].
  Qed.

  Lemma rrestr_wf (e : rexpr bool) (r : rcqs) :
    rcqs_wf r -> rcqs_wf (rrestr e r).
  Proof.
    intros Hr; apply tcp_summable_trace.
    apply (summable_mono _ (fun rm => tcp_trace (r rm))).
    - apply tcp_summable_trace; exact Hr.
    - intros rm; unfold rrestr; destruct (ev e rm);
        [ apply Rle_refl | rewrite tcp_trace_zero; apply tcp_trace_nonneg ].
  Qed.

  Lemma rrestrn_wf (e : rexpr bool) (r : rcqs) :
    rcqs_wf r -> rcqs_wf (rrestrn e r).
  Proof.
    intros Hr; apply tcp_summable_trace.
    apply (summable_mono _ (fun rm => tcp_trace (r rm))).
    - apply tcp_summable_trace; exact Hr.
    - intros rm; unfold rrestrn; destruct (ev e rm);
        [ rewrite tcp_trace_zero; apply tcp_trace_nonneg | apply Rle_refl ].
  Qed.

  Lemma rrestr_sep (e : rexpr bool) (r : rcqs) :
    rcqs_sep r -> rcqs_sep (rrestr e r).
  Proof.
    intros Hr rm; unfold rrestr; destruct (ev e rm);
      [ apply Hr | apply rsep_zero ].
  Qed.

  Lemma rrestrn_sep (e : rexpr bool) (r : rcqs) :
    rcqs_sep r -> rcqs_sep (rrestrn e r).
  Proof.
    intros Hr rm; unfold rrestrn; destruct (ev e rm);
      [ apply rsep_zero | apply Hr ].
  Qed.

  (** Restricting only shrinks supports, so any predicate survives. *)
  Lemma rrestr_psat (e : rexpr bool) (r : rcqs) (A : pred) :
    psat r A -> psat (rrestr e r) A.
  Proof.
    intros Hsat rm; unfold rrestr; destruct (ev e rm); [ apply Hsat |].
    rewrite (proj2 (tcp_supp_eq0 _ _) eq_refl); apply hbot_le.
  Qed.

  Lemma rrestrn_psat (e : rexpr bool) (r : rcqs) (A : pred) :
    psat r A -> psat (rrestrn e r) A.
  Proof.
    intros Hsat rm; unfold rrestrn; destruct (ev e rm); [| apply Hsat ].
    rewrite (proj2 (tcp_supp_eq0 _ _) eq_refl); apply hbot_le.
  Qed.

  (** ... and the restriction records the value of the condition. *)
  Lemma rrestr_psat_Cla (e : rexpr bool) (r : rcqs) :
    psat (rrestr e r) (Cla e).
  Proof.
    apply psat_Cla; intros rm Hnz; unfold rrestr in Hnz.
    destruct (ev e rm); [ reflexivity | congruence ].
  Qed.

  Lemma rrestrn_psat_Cla (e : rexpr bool) (r : rcqs) :
    psat (rrestrn e r) (Cla (gmap negb e)).
  Proof.
    apply psat_Cla; intros rm Hnz; unfold rrestrn in Hnz; cbn [ev gmap].
    destruct (ev e rm); [ congruence | reflexivity ].
  Qed.

  (** The projections are additive. *)
  Lemma rcqs_projL_add (a b : rcqs) :
    rcqs_wf a -> rcqs_wf b ->
    rcqs_projL (rcqs_add a b) = cqs_add (rcqs_projL a) (rcqs_projL b).
  Proof.
    intros Ha Hb; apply funext; intros m1.
    unfold rcqs_projL, rcqs_add, cqs_add.
    transitivity (tcp_sum (fun m2 : cmem =>
                    tcp_add (rtcpL (a (m1, m2))) (rtcpL (b (m1, m2))))).
    { f_equal; apply funext; intros m2; apply rtcpL_add. }
    apply (tcp_sum_add _ _ _ _ (rcqs_slice_wf a m1 Ha) (rcqs_slice_wf b m1 Hb)).
  Qed.

  Lemma rcqs_projR_add (a b : rcqs) :
    rcqs_wf a -> rcqs_wf b ->
    rcqs_projR (rcqs_add a b) = cqs_add (rcqs_projR a) (rcqs_projR b).
  Proof.
    intros Ha Hb; apply funext; intros m2.
    unfold rcqs_projR, rcqs_add, cqs_add.
    transitivity (tcp_sum (fun m1 : cmem =>
                    tcp_add (rtcpR (a (m1, m2))) (rtcpR (b (m1, m2))))).
    { f_equal; apply funext; intros m1; apply rtcpR_add. }
    apply (tcp_sum_add _ _ _ _ (rcqs_slice_wf_R a m2 Ha)
                               (rcqs_slice_wf_R b m2 Hb)).
  Qed.

  (** A left-hand condition does not depend on the right-hand memory, so it
      passes straight through the left projection. *)
  Lemma rcqs_projL_rrestr (e : expr bool) (r : rcqs) :
    rcqs_projL (rrestr (idx SL e) r) = restr e (rcqs_projL r).
  Proof.
    apply funext; intros m1; unfold rcqs_projL, rrestr, restr.
    destruct (ev e m1) eqn:He.
    - f_equal; apply funext; intros m2; cbn [ev]; unfold idx; cbn [ev csel fst snd].
      rewrite He; reflexivity.
    - transitivity (tcp_sum (fun _ : cmem => @tcp_zero qmem)).
      + f_equal; apply funext; intros m2; cbn [ev]; unfold idx;
          cbn [ev csel fst snd].
        rewrite He; apply rtcpL_zero.
      + apply tcp_sum_zero; intros _; reflexivity.
  Qed.

  Lemma rcqs_projL_rrestrn (e : expr bool) (r : rcqs) :
    rcqs_projL (rrestrn (idx SL e) r) = restrn e (rcqs_projL r).
  Proof.
    apply funext; intros m1; unfold rcqs_projL, rrestrn, restrn.
    destruct (ev e m1) eqn:He.
    - transitivity (tcp_sum (fun _ : cmem => @tcp_zero qmem)).
      + f_equal; apply funext; intros m2; cbn [ev]; unfold idx;
          cbn [ev csel fst snd].
        rewrite He; apply rtcpL_zero.
      + apply tcp_sum_zero; intros _; reflexivity.
    - f_equal; apply funext; intros m2; cbn [ev]; unfold idx; cbn [ev csel fst snd].
      rewrite He; reflexivity.
  Qed.

  Lemma rrestr_nz (e : rexpr bool) (r : rcqs) (rm : rcmem) :
    rrestr e r rm <> tcp_zero -> ev e rm = true /\ r rm <> tcp_zero.
  Proof.
    unfold rrestr; destruct (ev e rm); intros H;
      [ split; [ reflexivity | exact H ] | congruence ].
  Qed.

  Lemma rcqs_trace_rrestr_split (e : rexpr bool) (s : rcqs) :
    rcqs_wf s ->
    (rcqs_trace (rrestr e s) + rcqs_trace (rrestrn e s))%R = rcqs_trace s.
  Proof.
    intros Hs; unfold rcqs_trace.
    rewrite <- (tsum_add (fun rm => tcp_trace (rrestr e s rm))
                         (fun rm => tcp_trace (rrestrn e s rm))
                         (fun rm => tcp_trace_nonneg _ _)
                         (fun rm => tcp_trace_nonneg _ _)
                         (proj1 (tcp_summable_trace _ _ _) (rrestr_wf e s Hs))
                         (proj1 (tcp_summable_trace _ _ _) (rrestrn_wf e s Hs))).
    f_equal; apply funext; intros rm; unfold rrestr, rrestrn.
    destruct (ev e rm); rewrite tcp_trace_zero; lra.
  Qed.

  Lemma rrestrn_nz (e : rexpr bool) (r : rcqs) (rm : rcmem) :
    rrestrn e r rm <> tcp_zero -> ev e rm = false /\ r rm <> tcp_zero.
  Proof.
    unfold rrestrn; destruct (ev e rm); intros H;
      [ congruence | split; [ reflexivity | exact H ] ].
  Qed.

  (** When two conditions -- one on each side -- agree wherever the state is
      nonzero, restricting by the left one and projecting to the right is the
      same as projecting and then restricting by the right one. This is what
      rule JointIf's hypothesis [A subseteq Cla[idx_1 e_1 = idx_2 e_2]] buys. *)

  Lemma rcqs_projR_rrestr_swap (e1 e2 : expr bool) (r : rcqs) :
    (forall rm, r rm <> tcp_zero ->
                ev e1 (csel SL rm) = ev e2 (csel SR rm)) ->
    rcqs_projR (rrestr (idx SL e1) r) = restr e2 (rcqs_projR r).
  Proof.
    intros Heq; apply funext; intros m2.
    unfold rcqs_projR, rrestr, restr.
    destruct (ev e2 m2) eqn:He2.
    - f_equal; apply funext; intros m1.
      unfold idx; cbn [ev csel fst snd].
      destruct (ev e1 m1) eqn:He1; [ reflexivity |].
      destruct (classic (r (m1, m2) = tcp_zero)) as [Hz | Hz].
      + rewrite Hz; reflexivity.
      + exfalso; specialize (Heq (m1, m2) Hz); cbn [csel fst snd] in Heq;
          rewrite He1, He2 in Heq; discriminate.
    - transitivity (tcp_sum (fun _ : cmem => @tcp_zero qmem)).
      + f_equal; apply funext; intros m1.
        unfold idx; cbn [ev csel fst snd].
        destruct (ev e1 m1) eqn:He1; [| apply rtcpR_zero ].
        destruct (classic (r (m1, m2) = tcp_zero)) as [Hz | Hz].
        * rewrite Hz; apply rtcpR_zero.
        * exfalso; specialize (Heq (m1, m2) Hz); cbn [csel fst snd] in Heq;
            rewrite He1, He2 in Heq; discriminate.
      + apply tcp_sum_zero; intros _; reflexivity.
  Qed.

  Lemma rcqs_projR_rrestrn_swap (e1 e2 : expr bool) (r : rcqs) :
    (forall rm, r rm <> tcp_zero ->
                ev e1 (csel SL rm) = ev e2 (csel SR rm)) ->
    rcqs_projR (rrestrn (idx SL e1) r) = restrn e2 (rcqs_projR r).
  Proof.
    intros Heq; apply funext; intros m2.
    unfold rcqs_projR, rrestrn, restrn.
    destruct (ev e2 m2) eqn:He2.
    - transitivity (tcp_sum (fun _ : cmem => @tcp_zero qmem)).
      + f_equal; apply funext; intros m1.
        unfold idx; cbn [ev csel fst snd].
        destruct (ev e1 m1) eqn:He1; [ apply rtcpR_zero |].
        destruct (classic (r (m1, m2) = tcp_zero)) as [Hz | Hz].
        * rewrite Hz; apply rtcpR_zero.
        * exfalso; specialize (Heq (m1, m2) Hz); cbn [csel fst snd] in Heq;
            rewrite He1, He2 in Heq; discriminate.
      + apply tcp_sum_zero; intros _; reflexivity.
    - f_equal; apply funext; intros m1.
      unfold idx; cbn [ev csel fst snd].
      destruct (ev e1 m1) eqn:He1; [| reflexivity ].
      destruct (classic (r (m1, m2) = tcp_zero)) as [Hz | Hz].
      + rewrite Hz; reflexivity.
      + exfalso; specialize (Heq (m1, m2) Hz); cbn [csel fst snd] in Heq;
          rewrite He1, He2 in Heq; discriminate.
  Qed.

  (* ================================================================= *)
  (* ================================================================= *)
  (** ** Families of relational states

      Rule Case splits a state by the value of a classical expression and
      reassembles the witnesses it gets back; the converse of Lemma 36 does
      the same with the components of a spectral decomposition. Both need the
      same facts about a summed family -- that it is well-formed, separable,
      that its support is the join of the supports, and that the two
      projections are normal -- so they are proved once here. As with
      [cqs_fam] in [Semantics.v] the single hypothesis is joint summability of
      the traces over (index, memory); everything else follows by Tonelli. *)

  Lemma tcp_sep_sum {X Y J} (G : J -> tcp (X * Y)) :
    tcp_summable G -> (forall j, tcp_sep (G j)) -> tcp_sep (tcp_sum G).
  Proof.
    intros Hs HGsep.
    assert (Hdec : forall j : J,
              { K : Type & { fg : (K -> tcp X) * (K -> tcp Y) |
                  tcp_summable (fun k => tcp_tensor (fst fg k) (snd fg k))
                  /\ G j
                     = tcp_sum (fun k => tcp_tensor (fst fg k) (snd fg k)) } }).
    { intros j.
      destruct (constructive_indefinite_description _ (HGsep j)) as [K HK].
      destruct (constructive_indefinite_description _ HK) as [f Hf].
      destruct (constructive_indefinite_description _ Hf) as [g Hg].
      exists K, (f, g); exact Hg. }
    exists (sigT (fun j : J => projT1 (Hdec j))),
           (fun p => fst (proj1_sig (projT2 (Hdec (projT1 p)))) (projT2 p)),
           (fun p => snd (proj1_sig (projT2 (Hdec (projT1 p)))) (projT2 p)).
    set (F := fun (j : J) (k : projT1 (Hdec j)) =>
                tcp_tensor (fst (proj1_sig (projT2 (Hdec j))) k)
                           (snd (proj1_sig (projT2 (Hdec j))) k)).
    assert (HFa : forall j, tcp_summable (F j))
      by (intros j; apply (proj1 (proj2_sig (projT2 (Hdec j))))).
    assert (HFs : forall j, G j = tcp_sum (F j))
      by (intros j; apply (proj2 (proj2_sig (projT2 (Hdec j))))).
    assert (HGs : tcp_summable (fun j => tcp_sum (F j))).
    { assert (HGeq : (fun j => tcp_sum (F j)) = G)
        by (apply funext; intros j; symmetry; apply HFs).
      rewrite HGeq; exact Hs. }
    destruct (tcp_sum_sigma _ _ _ F HFa HGs) as [Hsig Heqsig].
    split.
    - exact Hsig.
    - transitivity (tcp_sum (fun j => tcp_sum (F j)));
        [ f_equal; apply funext; intros j; apply HFs | exact Heqsig ].
  Qed.

  Lemma rsep_sum {J} (G : J -> tcp rqmem) :
    tcp_summable G -> (forall j, rsep (G j)) -> rsep (tcp_sum G).
  Proof.
    intros Hs HG; unfold rsep.
    rewrite (tcp_conj_sum _ _ _ _ _ Hs).
    apply tcp_sep_sum;
      [ apply (tcp_summable_conj _ _ (proj1 Urqpair_unitary) Hs) | exact HG ].
  Qed.

  Definition rcqs_sum {J : Type} (F : J -> rcqs) : rcqs :=
    fun rm => tcp_sum (fun j => F j rm).

  Definition rcqs_fam {J : Type} (F : J -> rcqs) : Prop :=
    summable (fun p : J * rcmem => tcp_trace (F (fst p) (snd p))).

  Lemma rcqs_fam_wf {J} (F : J -> rcqs) :
    rcqs_fam F -> forall j, rcqs_wf (F j).
  Proof.
    intros H j; apply tcp_summable_trace.
    apply (summable_inj (fun rm : rcmem => (j, rm))
                        (fun p : J * rcmem => tcp_trace (F (fst p) (snd p))));
      [ intros a b Hab; congruence | exact H ].
  Qed.

  Lemma rcqs_fam_ptwise {J} (F : J -> rcqs) :
    rcqs_fam F -> forall rm, tcp_summable (fun j => F j rm).
  Proof.
    intros H rm; apply tcp_summable_trace.
    apply (summable_inj (fun j : J => (j, rm))
                        (fun p : J * rcmem => tcp_trace (F (fst p) (snd p))));
      [ intros a b Hab; congruence | exact H ].
  Qed.

  Lemma rcqs_fam_trace {J} (F : J -> rcqs) :
    rcqs_fam F -> summable (fun j => rcqs_trace (F j)).
  Proof.
    intros H.
    destruct (tsum_iter_le_pairs (fun (j : J) (rm : rcmem) => tcp_trace (F j rm))
                (fun p => tcp_trace_nonneg _ _) H) as [Hit _].
    exact Hit.
  Qed.

  Lemma rcqs_sum_wf {J} (F : J -> rcqs) : rcqs_fam F -> rcqs_wf (rcqs_sum F).
  Proof.
    intros H; apply tcp_summable_trace.
    assert (Heq : (fun rm => tcp_trace (rcqs_sum F rm))
                  = (fun rm : rcmem => tsum (fun j => tcp_trace (F j rm))))
      by (apply funext; intros rm; unfold rcqs_sum;
          apply (tcp_trace_sum _ _ _ (rcqs_fam_ptwise F H rm))).
    rewrite Heq.
    assert (Hsw : summable
                    (fun q : rcmem * J => tcp_trace (F (snd q) (fst q)))).
    { apply (summable_inj (fun q : rcmem * J => (snd q, fst q))
                          (fun p : J * rcmem => tcp_trace (F (fst p) (snd p)))).
      - intros [m1 j1] [m2 j2] Hq; cbn in Hq; congruence.
      - exact H. }
    destruct (tsum_iter_le_pairs
                (fun (rm : rcmem) (j : J) => tcp_trace (F j rm))
                (fun q => tcp_trace_nonneg _ _) Hsw) as [Hit _].
    exact Hit.
  Qed.

  Lemma rcqs_sum_sep {J} (F : J -> rcqs) :
    rcqs_fam F -> (forall j, rcqs_sep (F j)) -> rcqs_sep (rcqs_sum F).
  Proof.
    intros HF Hsep rm; unfold rcqs_sum.
    apply rsep_sum; [ apply (rcqs_fam_ptwise F HF) | intros j; apply Hsep ].
  Qed.

  Lemma rcqs_sum_psat {J} (F : J -> rcqs) (B : pred) :
    rcqs_fam F -> (forall j, psat (F j) B) -> psat (rcqs_sum F) B.
  Proof.
    intros HF Hsat rm; unfold rcqs_sum.
    rewrite (tcp_supp_sum _ _ _ (rcqs_fam_ptwise F HF rm)).
    apply hSup_lub; intros j; apply Hsat.
  Qed.

  (** The total trace of a relational state is the total trace of either of
      its projections: the partial traces do not lose anything. *)
  Lemma rcqs_trace_projL (r : rcqs) :
    rcqs_wf r -> cqs_trace (rcqs_projL r) = rcqs_trace r.
  Proof.
    intros Hr; unfold cqs_trace, rcqs_trace.
    assert (Hsl : forall m1, summable (fun m2 => tcp_trace (r (m1, m2)))).
    { intros m1.
      apply (summable_inj (fun m2 : cmem => (m1, m2))
                          (fun rm : rcmem => tcp_trace (r rm)));
        [ intros a b Hab; congruence | apply tcp_summable_trace; exact Hr ]. }
    assert (Heq : (fun m1 => tcp_trace (rcqs_projL r m1))
                  = (fun m1 : cmem => tsum (fun m2 => tcp_trace (r (m1, m2)))))
      by (apply funext; intros m1; apply rcqs_projL_trace; exact Hr).
    assert (Hit : summable
                    (fun m1 : cmem => tsum (fun m2 => tcp_trace (r (m1, m2))))).
    { rewrite <- Heq; apply tcp_summable_trace, rcqs_projL_wf; exact Hr. }
    rewrite Heq.
    destruct (tsum_tonelli (fun (m1 m2 : cmem) => tcp_trace (r (m1, m2)))
                (fun m1 m2 => tcp_trace_nonneg _ _) Hsl Hit) as [_ Hval].
    rewrite <- Hval.
    f_equal; apply funext; intros [u v]; reflexivity.
  Qed.

  Lemma rcqs_trace_projR (r : rcqs) :
    rcqs_wf r -> cqs_trace (rcqs_projR r) = rcqs_trace r.
  Proof.
    intros Hr; unfold cqs_trace, rcqs_trace.
    assert (Hsl : forall m2, summable (fun m1 => tcp_trace (r (m1, m2)))).
    { intros m2.
      apply (summable_inj (fun m1 : cmem => (m1, m2))
                          (fun rm : rcmem => tcp_trace (r rm)));
        [ intros a b Hab; congruence | apply tcp_summable_trace; exact Hr ]. }
    assert (Heq : (fun m2 => tcp_trace (rcqs_projR r m2))
                  = (fun m2 : cmem => tsum (fun m1 => tcp_trace (r (m1, m2)))))
      by (apply funext; intros m2; apply rcqs_projR_trace; exact Hr).
    assert (Hit : summable
                    (fun m2 : cmem => tsum (fun m1 => tcp_trace (r (m1, m2))))).
    { rewrite <- Heq; apply tcp_summable_trace, rcqs_projR_wf; exact Hr. }
    rewrite Heq.
    destruct (tsum_tonelli (fun (m2 m1 : cmem) => tcp_trace (r (m1, m2)))
                (fun m2 m1 => tcp_trace_nonneg _ _) Hsl Hit) as [_ Hval].
    rewrite <- Hval.
    apply (tsum_swap_pair (fun rm : rcmem => tcp_trace (r rm))).
    apply tcp_summable_trace; exact Hr.
  Qed.

  (** Normality of the two projections. The double sum -- over the family and
      over the other side's memory -- has to be exchanged, which is
      [tcp_sum_swap]. *)

  Lemma rcqs_projL_sum {J} (F : J -> rcqs) :
    rcqs_fam F ->
    rcqs_projL (rcqs_sum F) = cqs_sum (fun j => rcqs_projL (F j)).
  Proof.
    intros HF; apply funext; intros m1.
    set (G := fun (m2 : cmem) (j : J) => rtcpL (F j (m1, m2))).
    assert (H1 : forall m2, tcp_summable (G m2))
      by (intros m2; apply rtcpL_summable, (rcqs_fam_ptwise F HF)).
    assert (H3 : forall j, tcp_summable (fun m2 => G m2 j))
      by (intros j; apply (rcqs_slice_wf (F j) m1 (rcqs_fam_wf F HF j))).
    assert (Hslice : forall m2,
               tcp_sum (G m2) = rtcpL (rcqs_sum F (m1, m2))).
    { intros m2; unfold G, rcqs_sum; symmetry.
      apply (rtcpL_sum _ (rcqs_fam_ptwise F HF (m1, m2))). }
    assert (H2 : tcp_summable (fun m2 => tcp_sum (G m2))).
    { assert (Heq : (fun m2 => tcp_sum (G m2))
                    = (fun m2 : cmem => rtcpL (rcqs_sum F (m1, m2))))
        by (apply funext; exact Hslice).
      rewrite Heq; apply (rcqs_slice_wf (rcqs_sum F) m1 (rcqs_sum_wf F HF)). }
    assert (H4 : tcp_summable (fun j => tcp_sum (fun m2 => G m2 j))).
    { apply tcp_summable_trace.
      apply (summable_mono _ (fun j => rcqs_trace (F j)));
        [ apply rcqs_fam_trace; exact HF |].
      intros j; rewrite (tcp_trace_sum _ _ _ (H3 j)).
      assert (Heq : (fun m2 : cmem => tcp_trace (G m2 j))
                    = (fun m2 : cmem => tcp_trace (F j (m1, m2))))
        by (apply funext; intros m2; unfold G; apply rtcpL_trace).
      rewrite Heq; unfold rcqs_trace.
      apply (tsum_inj_le (fun m2 : cmem => ((m1, m2) : rcmem))
               (fun rm : rcmem => tcp_trace (F j rm)));
        [ intros a b Hab; congruence
        | apply tcp_summable_trace, (rcqs_fam_wf F HF j) ]. }
    unfold rcqs_projL at 1, cqs_sum.
    transitivity (tcp_sum (fun m2 : cmem => tcp_sum (G m2)));
      [ f_equal; apply funext; intros m2; symmetry; apply Hslice |].
    rewrite (tcp_sum_swap G H1 H2 H3 H4); reflexivity.
  Qed.

  Lemma rcqs_projR_sum {J} (F : J -> rcqs) :
    rcqs_fam F ->
    rcqs_projR (rcqs_sum F) = cqs_sum (fun j => rcqs_projR (F j)).
  Proof.
    intros HF; apply funext; intros m2.
    set (G := fun (m1 : cmem) (j : J) => rtcpR (F j (m1, m2))).
    assert (H1 : forall m1, tcp_summable (G m1))
      by (intros m1; apply rtcpR_summable, (rcqs_fam_ptwise F HF)).
    assert (H3 : forall j, tcp_summable (fun m1 => G m1 j))
      by (intros j; apply (rcqs_slice_wf_R (F j) m2 (rcqs_fam_wf F HF j))).
    assert (Hslice : forall m1,
               tcp_sum (G m1) = rtcpR (rcqs_sum F (m1, m2))).
    { intros m1; unfold G, rcqs_sum; symmetry.
      apply (rtcpR_sum _ (rcqs_fam_ptwise F HF (m1, m2))). }
    assert (H2 : tcp_summable (fun m1 => tcp_sum (G m1))).
    { assert (Heq : (fun m1 => tcp_sum (G m1))
                    = (fun m1 : cmem => rtcpR (rcqs_sum F (m1, m2))))
        by (apply funext; exact Hslice).
      rewrite Heq; apply (rcqs_slice_wf_R (rcqs_sum F) m2 (rcqs_sum_wf F HF)). }
    assert (H4 : tcp_summable (fun j => tcp_sum (fun m1 => G m1 j))).
    { apply tcp_summable_trace.
      apply (summable_mono _ (fun j => rcqs_trace (F j)));
        [ apply rcqs_fam_trace; exact HF |].
      intros j; rewrite (tcp_trace_sum _ _ _ (H3 j)).
      assert (Heq : (fun m1 : cmem => tcp_trace (G m1 j))
                    = (fun m1 : cmem => tcp_trace (F j (m1, m2))))
        by (apply funext; intros m1; unfold G; apply rtcpR_trace).
      rewrite Heq; unfold rcqs_trace.
      apply (tsum_inj_le (fun m1 : cmem => ((m1, m2) : rcmem))
               (fun rm : rcmem => tcp_trace (F j rm)));
        [ intros a b Hab; congruence
        | apply tcp_summable_trace, (rcqs_fam_wf F HF j) ]. }
    unfold rcqs_projR at 1, cqs_sum.
    transitivity (tcp_sum (fun m1 : cmem => tcp_sum (G m1)));
      [ f_equal; apply funext; intros m1; symmetry; apply Hslice |].
    rewrite (tcp_sum_swap G H1 H2 H3 H4); reflexivity.
  Qed.

  (** A family of relational states projects to a family of cq-states, which
      is what lets [denote_sum] be applied to the projections. *)

  Lemma rcqs_fam_projL {J} (F : J -> rcqs) :
    rcqs_fam F -> cqs_fam (fun j => rcqs_projL (F j)).
  Proof.
    intros HF; unfold cqs_fam.
    refine (proj1 (tsum_pairs_le_iter
                     (fun (j : J) (m1 : cmem) =>
                        tcp_trace (rcqs_projL (F j) m1)) _ _)).
    - intros j; apply tcp_summable_trace, rcqs_projL_wf, (rcqs_fam_wf F HF j).
    - apply (summable_mono _ (fun j => rcqs_trace (F j)));
        [ apply rcqs_fam_trace; exact HF |].
      intros j; apply Req_le, rcqs_trace_projL, (rcqs_fam_wf F HF j).
  Qed.

  Lemma rcqs_fam_projR {J} (F : J -> rcqs) :
    rcqs_fam F -> cqs_fam (fun j => rcqs_projR (F j)).
  Proof.
    intros HF; unfold cqs_fam.
    refine (proj1 (tsum_pairs_le_iter
                     (fun (j : J) (m2 : cmem) =>
                        tcp_trace (rcqs_projR (F j) m2)) _ _)).
    - intros j; apply tcp_summable_trace, rcqs_projR_wf, (rcqs_fam_wf F HF j).
    - apply (summable_mono _ (fun j => rcqs_trace (F j)));
        [ apply rcqs_fam_trace; exact HF |].
      intros j; apply Req_le, rcqs_trace_projR, (rcqs_fam_wf F HF j).
  Qed.

  (** ** Point masses and pure product states

      Lemma 36 reduces the judgment to states of this shape, and the rule
      proofs work with them throughout. *)

  Definition rdirac (rm : rcmem) (rho : tcp rqmem) : rcqs :=
    fun rm' => if excluded_middle_informative (rm' = rm) then rho else tcp_zero.

  Lemma rdirac_same rm rho : rdirac rm rho rm = rho.
  Proof.
    unfold rdirac; destruct (excluded_middle_informative (rm = rm));
      [ reflexivity | congruence ].
  Qed.

  Lemma rdirac_other rm rm' rho : rm' <> rm -> rdirac rm rho rm' = tcp_zero.
  Proof.
    intros H; unfold rdirac;
      destruct (excluded_middle_informative (rm' = rm));
      [ contradiction | reflexivity ].
  Qed.

  Lemma rdirac_wf rm rho : rcqs_wf (rdirac rm rho).
  Proof.
    apply (tcp_summable_singleton _ rm); intros rm' H; apply rdirac_other; exact H.
  Qed.

  Lemma rdirac_sep rm rho : rsep rho -> rcqs_sep (rdirac rm rho).
  Proof.
    intros Hs rm'; destruct (excluded_middle_informative (rm' = rm)) as [-> | Hne].
    - rewrite rdirac_same; exact Hs.
    - rewrite rdirac_other by exact Hne; apply rsep_zero.
  Qed.

  (** A pure product state across the two sides: the paper's [psi_1 (x) psi_2]
      viewed in [l2[V1^qu V2^qu]]. *)
  Definition rprod (v w : l2 qmem) : l2 rqmem :=
    oapp (oadj Urqpair) (tensorv v w).

  Lemma tcp_conj_Urqpair_rprod (v w : l2 qmem) :
    tcp_conj Urqpair (tcp_proj (rprod v w))
    = tcp_tensor (tcp_proj v) (tcp_proj w).
  Proof.
    unfold rprod; rewrite tcp_conj_proj, <- oapp_ocomp.
    rewrite (proj2 Urqpair_unitary), oapp_oid.
    symmetry; apply tcp_tensor_proj.
  Qed.

  Lemma rsep_rprod (v w : l2 qmem) : rsep (tcp_proj (rprod v w)).
  Proof.
    unfold rsep; rewrite tcp_conj_Urqpair_rprod; apply tcp_sep_tensor.
  Qed.

  (** Tracing out one side of a normalized pure product leaves the other
      side's pure state -- which is what makes Lemma 36's two conclusions come
      out as point masses. *)
  Lemma rtcpL_rprod (v w : l2 qmem) :
    inner w w = C1 -> rtcpL (tcp_proj (rprod v w)) = tcp_proj v.
  Proof.
    intros Hw; unfold rtcpL.
    rewrite tcp_conj_Urqpair_rprod, tcp_ptrace_tensor, tcp_trace_proj, Hw.
    replace (Cre C1) with 1%R by reflexivity.
    apply tcp_scale_1.
  Qed.

  Lemma rtcpR_rprod (v w : l2 qmem) :
    inner v v = C1 -> rtcpR (tcp_proj (rprod v w)) = tcp_proj w.
  Proof.
    intros Hv; unfold rtcpR.
    rewrite tcp_conj_Urqpair_rprod, tcp_ptraceL_tensor, tcp_trace_proj, Hv.
    replace (Cre C1) with 1%R by reflexivity.
    apply tcp_scale_1.
  Qed.

  (** The converse of [tcp_conj_Urqpair_rprod]: a pure product's projection
      read back from the tensor side. Needed by Lemma 36's converse to move
      the per-factor normalization ([tcp_proj_decompose_unit]) across
      [rprod]. *)
  Lemma rprod_proj (v w : l2 qmem) :
    tcp_proj (rprod v w) = tcp_conj (oadj Urqpair) (tcp_tensor (tcp_proj v) (tcp_proj w)).
  Proof.
    unfold rprod; rewrite <- tcp_conj_proj, tcp_tensor_proj; reflexivity.
  Qed.

  (** Every pure product state's projection is a nonnegatively-scaled
      *normalized* pure product's projection -- total, so the converse of
      Lemma 36 never has to case-split on which factor (if either) was
      already zero. *)
  Lemma rprod_normalize_total (v w : l2 qmem) :
    exists (u u' : l2 qmem) (a : R),
      inner u u = C1 /\ inner u' u' = C1 /\ (0 <= a)%R /\
      tcp_proj (rprod v w) = tcp_scale a (tcp_proj (rprod u u')).
  Proof.
    destruct (tcp_proj_decompose_unit qmem0 v) as [av [u [Hav [Hu Hveq]]]].
    destruct (tcp_proj_decompose_unit qmem0 w) as [aw [u' [Haw [Hu' Hweq]]]].
    exists u, u', (av * aw)%R; repeat split; try assumption.
    - apply Rmult_le_pos; assumption.
    - rewrite rprod_proj, Hveq, Hweq.
      assert (Htens : tcp_tensor (tcp_scale av (tcp_proj u)) (tcp_scale aw (tcp_proj u'))
                       = tcp_scale (av * aw) (tcp_tensor (tcp_proj u) (tcp_proj u'))).
      { rewrite <- tcp_scale_tensor_l, <- tcp_scale_tensor_r, tcp_scale_assoc.
        reflexivity. }
      rewrite Htens, tcp_conj_scale, <- rprod_proj.
      reflexivity.
  Qed.

  (** The spectral theorem, pushed through separability: a separable
      [rho in T^+[V1 V2]] is a (possibly infinite) sum of pure products.
      [tcp_decompose] gives each tensor factor as a sum of rank-one
      projections ([tcp_decompose]); [tcp_tensor_sum_sum] flattens the
      resulting tensor of two sums into one sum over the pair of indices;
      [tcp_sum_sigma] flattens that, in turn, against the outer sum
      [tcp_sep] itself provides. Needed by the converse of Lemma 36 to turn
      an arbitrary separable state satisfying [A] into a family of pure
      states each satisfying [A], to which [qrhl_pure] applies. *)
  Lemma rsep_pure_decompose (rho : tcp rqmem) :
    rsep rho ->
    exists (K : Type) (phi psi : K -> l2 qmem),
      tcp_summable (fun k => tcp_proj (rprod (phi k) (psi k)))
      /\ rho = tcp_sum (fun k => tcp_proj (rprod (phi k) (psi k))).
  Proof.
    intros [J [f [g [Hfg Heq]]]].
    assert (Hdecf : forall j : J,
      { A : Type & { phi0 : A -> l2 qmem |
          tcp_summable (fun a => tcp_proj (phi0 a)) /\
          f j = tcp_sum (fun a => tcp_proj (phi0 a)) } }).
    { intros j.
      destruct (constructive_indefinite_description _ (tcp_decompose qmem (f j))) as [A HA].
      destruct (constructive_indefinite_description _ HA) as [phi0 Hphi0].
      exists A, phi0; exact Hphi0. }
    assert (Hdecg : forall j : J,
      { B : Type & { psi0 : B -> l2 qmem |
          tcp_summable (fun b => tcp_proj (psi0 b)) /\
          g j = tcp_sum (fun b => tcp_proj (psi0 b)) } }).
    { intros j.
      destruct (constructive_indefinite_description _ (tcp_decompose qmem (g j))) as [B HB].
      destruct (constructive_indefinite_description _ HB) as [psi0 Hpsi0].
      exists B, psi0; exact Hpsi0. }
    set (A := fun j => projT1 (Hdecf j)).
    set (phi0 := fun j => proj1_sig (projT2 (Hdecf j))).
    set (B := fun j => projT1 (Hdecg j)).
    set (psi0 := fun j => proj1_sig (projT2 (Hdecg j))).
    assert (HphiA : forall j, tcp_summable (fun a : A j => tcp_proj (phi0 j a)))
      by (intros j; apply (proj1 (proj2_sig (projT2 (Hdecf j))))).
    assert (Hfj : forall j, f j = tcp_sum (fun a : A j => tcp_proj (phi0 j a)))
      by (intros j; apply (proj2 (proj2_sig (projT2 (Hdecf j))))).
    assert (HpsiB : forall j, tcp_summable (fun b : B j => tcp_proj (psi0 j b)))
      by (intros j; apply (proj1 (proj2_sig (projT2 (Hdecg j))))).
    assert (Hgj : forall j, g j = tcp_sum (fun b : B j => tcp_proj (psi0 j b)))
      by (intros j; apply (proj2 (proj2_sig (projT2 (Hdecg j))))).
    set (K1 := fun j : J => sigT (fun _ : A j => B j)).
    set (Phi1 := fun (j : J) (p : K1 j) => phi0 j (projT1 p)).
    set (Psi1 := fun (j : J) (p : K1 j) => psi0 j (projT2 p)).
    assert (HF1 : forall j,
      tcp_summable (fun p : K1 j => tcp_proj (tensorv (Phi1 j p) (Psi1 j p)))
      /\ tcp_tensor (f j) (g j)
         = tcp_sum (fun p : K1 j => tcp_proj (tensorv (Phi1 j p) (Psi1 j p)))).
    { intros j.
      destruct (tcp_tensor_sum_sum (fun a : A j => tcp_proj (phi0 j a))
                  (fun b : B j => tcp_proj (psi0 j b)) (HphiA j) (HpsiB j))
        as [Hsum Heqten].
      assert (Heq3 : (fun p : K1 j => tcp_tensor (tcp_proj (Phi1 j p)) (tcp_proj (Psi1 j p)))
                     = (fun p : K1 j => tcp_proj (tensorv (Phi1 j p) (Psi1 j p))))
        by (apply funext; intros p; apply tcp_tensor_proj).
      rewrite <- Heq3; split; [ exact Hsum |].
      rewrite Hfj, Hgj; exact Heqten. }
    assert (Hjsum : forall j, tcp_summable (fun p : K1 j => tcp_proj (tensorv (Phi1 j p) (Psi1 j p))))
      by (intros j; apply (proj1 (HF1 j))).
    assert (Hjeq : forall j, tcp_tensor (f j) (g j)
                   = tcp_sum (fun p : K1 j => tcp_proj (tensorv (Phi1 j p) (Psi1 j p))))
      by (intros j; apply (proj2 (HF1 j))).
    assert (Houter : tcp_summable
      (fun j => tcp_sum (fun p : K1 j => tcp_proj (tensorv (Phi1 j p) (Psi1 j p))))).
    { assert (Heq4 : (fun j => tcp_sum (fun p : K1 j => tcp_proj (tensorv (Phi1 j p) (Psi1 j p))))
                     = (fun j => tcp_tensor (f j) (g j)))
        by (apply funext; intros j; symmetry; apply Hjeq).
      rewrite Heq4; exact Hfg. }
    destruct (tcp_sum_sigma (qmem * qmem) J K1
                (fun j (p : K1 j) => tcp_proj (tensorv (Phi1 j p) (Psi1 j p)))
                Hjsum Houter) as [Hsig Heqsig].
    set (K := sigT K1).
    set (phi := fun k : K => Phi1 (projT1 k) (projT2 k)).
    set (psi := fun k : K => Psi1 (projT1 k) (projT2 k)).
    exists K, phi, psi.
    assert (Hrho2 : tcp_conj Urqpair rho
                    = tcp_sum (fun k : K => tcp_proj (tensorv (phi k) (psi k)))).
    { rewrite Heq.
      assert (Heq5 : (fun j => tcp_tensor (f j) (g j))
                     = (fun j => tcp_sum (fun p : K1 j => tcp_proj (tensorv (Phi1 j p) (Psi1 j p)))))
        by (apply funext; exact Hjeq).
      rewrite Heq5; exact Heqsig. }
    assert (Hconv : forall k : K,
      tcp_conj (oadj Urqpair) (tcp_proj (tensorv (phi k) (psi k)))
      = tcp_proj (rprod (phi k) (psi k))).
    { intros k; rewrite <- tcp_tensor_proj, <- rprod_proj; reflexivity. }
    split.
    - assert (Heq7 : (fun k : K => tcp_proj (rprod (phi k) (psi k)))
                     = (fun k : K => tcp_conj (oadj Urqpair) (tcp_proj (tensorv (phi k) (psi k)))))
        by (apply funext; intros k; symmetry; apply Hconv).
      rewrite Heq7.
      apply (tcp_summable_conj (oadj Urqpair) _ (oisometry_oadj Urqpair Urqpair_unitary)).
      exact Hsig.
    - assert (Heq8 : rho = tcp_conj (oadj Urqpair) (tcp_conj Urqpair rho))
        by (symmetry; apply tcp_conj_adjUrqpair_roundtrip).
      rewrite Heq8, Hrho2.
      rewrite (tcp_conj_sum _ _ _ _ _ Hsig).
      f_equal; apply funext; intros k; apply Hconv.
  Qed.

  (** The two projections of a point mass are point masses. *)
  Lemma rcqs_projL_rdirac (m1 m2 : cmem) (rho : tcp rqmem) :
    rcqs_projL (rdirac (m1, m2) rho) = cqdirac m1 (rtcpL rho).
  Proof.
    apply funext; intros m1'; unfold rcqs_projL.
    destruct (excluded_middle_informative (m1' = m1)) as [-> | Hne].
    - rewrite cqdirac_same, (tcp_sum_singleton _ m2).
      + rewrite rdirac_same; reflexivity.
      + intros m2' Hm; rewrite rdirac_other by congruence; apply rtcpL_zero.
    - rewrite cqdirac_other by exact Hne.
      apply tcp_sum_zero; intros m2'.
      rewrite rdirac_other by congruence; apply rtcpL_zero.
  Qed.

  Lemma rcqs_projR_rdirac (m1 m2 : cmem) (rho : tcp rqmem) :
    rcqs_projR (rdirac (m1, m2) rho) = cqdirac m2 (rtcpR rho).
  Proof.
    apply funext; intros m2'; unfold rcqs_projR.
    destruct (excluded_middle_informative (m2' = m2)) as [-> | Hne].
    - rewrite cqdirac_same, (tcp_sum_singleton _ m1).
      + rewrite rdirac_same; reflexivity.
      + intros m1' Hm; rewrite rdirac_other by congruence; apply rtcpR_zero.
    - rewrite cqdirac_other by exact Hne.
      apply tcp_sum_zero; intros m1'.
      rewrite rdirac_other by congruence; apply rtcpR_zero.
  Qed.

  (** Satisfaction by a pure point mass is membership of the vector. *)
  Lemma psat_rdirac_proj (rm : rcmem) (x : l2 rqmem) (A : pred) :
    psat (rdirac rm (tcp_proj x)) A <-> hmem x (ev A rm).
  Proof.
    split.
    - intros H; specialize (H rm); rewrite rdirac_same, tcp_supp_proj in H.
      apply H, hspan_ub; reflexivity.
    - intros Hin rm'.
      destruct (excluded_middle_informative (rm' = rm)) as [-> | Hne].
      + rewrite rdirac_same, tcp_supp_proj.
        apply hspan_le; intros u ->; exact Hin.
      + rewrite rdirac_other by exact Hne.
        rewrite (proj2 (tcp_supp_eq0 _ _) eq_refl); apply hbot_le.
  Qed.

  (* ================================================================= *)
  (** ** Definition 35 *)

  Definition qrhl (A : pred) (c d : prog) (B : pred) : Prop :=
    forall r : rcqs,
      rcqs_wf r -> rcqs_sep r -> psat r A ->
      exists r' : rcqs,
        rcqs_wf r' /\ rcqs_sep r' /\ psat r' B /\
        rcqs_projL r' = denote c (rcqs_projL r) /\
        rcqs_projR r' = denote d (rcqs_projR r).

  Declare Scope qrhl_scope.
  Delimit Scope qrhl_scope with qrhl.
  Open Scope qrhl_scope.

  Notation "{{ A }} c '~~' d {{ B }}" := (qrhl A c d B)
    (at level 90, c at level 85, d at level 85) : qrhl_scope.

  (* ================================================================= *)
  (** ** Monotonicity

      Weakening the precondition and strengthening the postcondition. This is
      the content of rule Conseq (Lemma 46), and most other rule proofs use it
      as a step; [Rules/General.v] presents it under the rule's name. *)

  Lemma qrhl_mono (A A' B B' : pred) (c d : prog) :
    ple A A' -> ple B' B -> qrhl A' c d B' -> qrhl A c d B.
  Proof.
    intros HA HB H r Hwf Hsep Hsat.
    destruct (H r Hwf Hsep (psat_mono r A A' HA Hsat))
      as [r' [Hwf' [Hsep' [Hsat' [HL HR]]]]].
    exists r'; repeat split; try assumption.
    apply (psat_mono r' B' B HB Hsat').
  Qed.

  (* ================================================================= *)
  (** ** Lemma 36, forward direction

      "[{A} c ~ d {B}] holds iff: for all [m1], [m2] and all normalized
      [psi1 in l2[V1^qu]], [psi2 in l2[V2^qu]] such that
      [psi1 (x) psi2 in [A]_{m1 m2}], there exists a separable
      [rho' in T^+_cq[V1 V2]] such that [rho'] satisfies [B], and
      [tr^[V1]_V2 rho' = [idx_1 c](proj(|m1>) (x) proj(psi1))], and
      [tr^[V2]_V1 rho' = [idx_2 d](proj(|m2>) (x) proj(psi2))]."

      The forward direction is the paper's: instantiate the judgment at the
      pure product point mass. *)

  Definition qrhl_pure (A : pred) (c d : prog) (B : pred) : Prop :=
    forall (m1 m2 : cmem) (v w : l2 qmem),
      inner v v = C1 -> inner w w = C1 ->
      hmem (rprod v w) (ev A (m1, m2)) ->
      exists r' : rcqs,
        rcqs_wf r' /\ rcqs_sep r' /\ psat r' B /\
        rcqs_projL r' = denote c (cqdirac m1 (tcp_proj v)) /\
        rcqs_projR r' = denote d (cqdirac m2 (tcp_proj w)).

  Theorem qrhl_to_pure (A : pred) (c d : prog) (B : pred) :
    qrhl A c d B -> qrhl_pure A c d B.
  Proof.
    intros H m1 m2 v w Hv Hw Hin.
    (* the pure product point mass at [(m1, m2)] *)
    set (r := rdirac (m1, m2) (tcp_proj (rprod v w))).
    destruct (H r (rdirac_wf _ _)
                (rdirac_sep _ _ (rsep_rprod v w))
                (proj2 (psat_rdirac_proj (m1, m2) (rprod v w) A) Hin))
      as [r' [Hwf' [Hsep' [Hsat' [HL HR]]]]].
    exists r'; repeat split; try assumption.
    - rewrite HL; unfold r.
      rewrite rcqs_projL_rdirac, (rtcpL_rprod v w Hw); reflexivity.
    - rewrite HR; unfold r.
      rewrite rcqs_projR_rdirac, (rtcpR_rprod v w Hv); reflexivity.
  Qed.

  (* ================================================================= *)
  (** ** Lemma 36, converse direction -- OUTSTANDING

      [qrhl_pure A c d B -> qrhl A c d B] is the direction one uses to
      *establish* a judgment, and it is not proved here.

      The paper's argument: decompose an arbitrary separable [rho] satisfying
      [A] as [rho = sum_{m1 m2 i} lambda_{m1 m2 i}
      proj(|m1 m2>) (x) proj(psi^(1)_{m1 m2 i} (x) psi^(2)_{m1 m2 i})], apply
      the hypothesis to each pure component to get witnesses
      [rho'_{m1 m2 i}], and set [rho' := sum lambda_{m1 m2 i} rho'_{m1 m2 i}].

      Two things are missing for that. The decomposition itself is available --
      it is the substrate's [tcp_decompose] (the spectral theorem for positive
      trace-class operators) combined with separability. What is missing is the
      bookkeeping on the assembled sum: showing [rho'] is summable, that its
      trace is bounded, and that the two partial traces of a sum of witnesses
      are the sums of their partial traces, all of which need the rearrangement
      theorem for unordered nonnegative sums that [Semantics.v] already flags
      for [denote_summable]. The paper does this bookkeeping explicitly --
      equations (11) through (14) of its proof are exactly that computation.

      So this is the third item waiting on the same piece of analysis, after
      [denote_summable] and rule JointSample's marginals. It is now clearly the
      highest-value gap in the development: it blocks the converse of Lemma 36,
      and most rule soundness proofs go through that converse. *)

End JudgmentTheory.
