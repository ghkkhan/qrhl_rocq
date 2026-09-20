(** * Rules for quantum statements (Figure 3).

    Section 5.1, "Rules for quantum statements". As with the classical rules,
    each one-sided rule comes in a left and a right variant; the paper lists
    only the left ones ("there is also an analogous symmetric rule that we do
    not list explicitly") and derives the others from rule Sym.

    Each theorem below carries the paper's rule name, the lemma number that
    proves it, and the page. *)

From Stdlib Require Import List Lra.
From QRHL.Substrate Require Import Ambient Cnum Sums Interface Theory.
From QRHL.Core Require Import
  Vars Expr Registers Syntax Semantics Predicate QEq Judgment.

Module QuantumRules (S : HILBERT_SUBSTRATE) (V : PROGRAM_VARS).
  Include JudgmentTheory S V.

  (* ================================================================= *)
  (** ** Witnesses that act on one side

      Every one-sided rule builds its witness by applying the statement's
      operation to side 1 of the given state and leaving side 2 alone. The
      three facts such a witness needs -- that it is well-formed, that it stays
      separable, and what its two projections are -- do not depend on which
      rule it came from, so they are proved once here. *)

  Section OneSided.
    Context (P : qset) (U : rcmem -> op (qsub P) (qsub P))
            (HU : forall rm, oisometry (U rm)).

    Definition actL (r : rcqs) : rcqs :=
      fun rm => tcp_conj (roliftL P (U rm)) (r rm).

    Lemma actL_trace (r : rcqs) (rm : rcmem) :
      tcp_trace (actL r rm) = tcp_trace (r rm).
    Proof.
      unfold actL; apply tcp_trace_conj_isometry.
      apply (roliftL_isometry P (U rm) (HU rm)).
    Qed.

    Lemma actL_wf (r : rcqs) : rcqs_wf r -> rcqs_wf (actL r).
    Proof.
      intros Hr; apply tcp_summable_trace.
      apply (summable_mono _ (fun rm => tcp_trace (r rm))).
      - apply tcp_summable_trace; exact Hr.
      - intros rm; rewrite actL_trace; apply Rle_refl.
    Qed.

    (** Separability is preserved: acting on one tensor factor sends a sum of
        products to a sum of products. *)
    Lemma actL_sep (r : rcqs) : rcqs_sep r -> rcqs_sep (actL r).
    Proof.
      intros Hr rm; unfold rsep, actL; rewrite conj_roliftL.
      destruct (Hr rm) as [J [f [g [Hs Heq]]]].
      exists J, (fun j => tcp_conj (olift P (U rm)) (f j)), g.
      assert (Hiso : oisometry (olift P (U rm)))
        by apply (wolift_isometry qvar qtype P (U rm) (HU rm)).
      assert (Htr : forall j,
                 tcp_trace (tcp_tensor (tcp_conj (olift P (U rm)) (f j)) (g j))
                 = tcp_trace (tcp_tensor (f j) (g j))).
      { intros j; rewrite !tcp_trace_tensor,
                          (tcp_trace_conj_isometry _ _ _ _ Hiso); reflexivity. }
      split.
      - apply tcp_summable_trace.
        apply (summable_mono _ (fun j => tcp_trace (tcp_tensor (f j) (g j)))).
        + apply tcp_summable_trace; exact Hs.
        + intros j; rewrite Htr; apply Rle_refl.
      - rewrite Heq, (tcp_conj_sum _ _ _ _ _ Hs).
        f_equal; apply funext; intros j.
        rewrite tcp_conj_tensor, tcp_conj_oid; reflexivity.
    Qed.

    (** The right projection does not see a left-hand action. *)
    Lemma rcqs_projR_actL (r : rcqs) : rcqs_projR (actL r) = rcqs_projR r.
    Proof.
      apply funext; intros m2; unfold rcqs_projR.
      f_equal; apply funext; intros m1.
      unfold actL; apply rtcpR_roliftL, HU.
    Qed.

  End OneSided.

  (* ================================================================= *)
  (** ** QApply1  [Figure 3, Lemma 65, p. 74]

<<
         e' := idx_1 e » idx_1 Q
        ------------------------------------------------------
         {e'^* . (B cap im e')} apply e to Q ~ skip {B}
>>

      "If [e] (and thus [e'] which is lifted using Definition 19) is unitary,
      then the precondition can be [e'^* . B], because after applying [e] on
      [Q] in a state in [e'^* . B], we get a state in [e' . e'^* . B = B]. But
      since we also allow isometries [e] in quantum applications, we need to
      restrict [B] to those states that are in the image [im e'] of [e'],
      leading to the precondition [e'^* . (B cap im e')]."

      Note the paper's remark that there is no joint rule: "we can simply apply
      rules QApply1 and QApply2 and get the same result". *)

  Definition eL (P : qset) (e : expr (op (qsub P) (qsub P))) (rm : rcmem)
    : op rqmem rqmem :=
    roliftL P (ev e (csel SL rm)).

  Definition QApply1_pre (P : qset) (e : expr (op (qsub P) (qsub P)))
             (B : pred) : pred :=
    gmap2 (fun (b : hspace rqmem) (Uop : op (qsub P) (qsub P)) =>
             himg (oadj (roliftL P Uop)) (hmeet b (oim (roliftL P Uop))))
          B (idx SL e).

  Lemma ev_QApply1_pre (P : qset) e B rm :
    ev (QApply1_pre P e B) rm
    = himg (oadj (eL P e rm)) (hmeet (ev B rm) (oim (eL P e rm))).
  Proof. reflexivity. Qed.

  Theorem rule_QApply1 (P : qset) (e : expr (op (qsub P) (qsub P))) (B : pred) :
    (forall m, oisometry (ev e m)) ->
    qrhl (QApply1_pre P e B) (QApply P e) Skip B.
  Proof.
    intros Hiso r Hwf Hsep Hsat.
    pose (U := fun rm : rcmem => ev e (csel SL rm)).
    assert (HU : forall rm, oisometry (U rm)) by (intros rm; apply Hiso).
    exists (actL P U r).
    assert (Hwf' : rcqs_wf (actL P U r)) by (apply (actL_wf P U HU); exact Hwf).
    assert (Hsep' : rcqs_sep (actL P U r))
      by (apply (actL_sep P U HU); exact Hsep).
    repeat split.
    - exact Hwf'.
    - exact Hsep'.
    - (* the postcondition *)
      intros rm; unfold actL.
      rewrite tcp_supp_conj.
      change (hspan (fun w => exists v, hmem v (tcp_supp (r rm))
                                        /\ w = oapp (roliftL P (U rm)) v))
        with (himg (roliftL P (U rm)) (tcp_supp (r rm))).
      eapply hle_trans.
      + apply himg_mono, (Hsat rm).
      + rewrite ev_QApply1_pre.
        apply himg_isometry_meet_oim, (roliftL_isometry P (U rm) (HU rm)).
    - (* the left projection: the action is visible *)
      apply funext; intros m1.
      assert (Hsum : tcp_summable (fun m2 : cmem => rtcpL (r (m1, m2)))).
      { apply tcp_summable_trace.
        apply (summable_mono _ (fun m2 => tcp_trace (r (m1, m2)))).
        - apply (summable_inj (fun m2 : cmem => (m1, m2))
                              (fun rm => tcp_trace (r rm)));
            [ intros a b Hab; congruence
            | apply tcp_summable_trace; exact Hwf ].
        - intros m2; rewrite rtcpL_trace; apply Rle_refl. }
      cbn [denote]; unfold sem_qapply, rcqs_projL, actL.
      transitivity (tcp_sum (fun m2 : cmem =>
                      tcp_conj (olift P (ev e m1)) (rtcpL (r (m1, m2))))).
      + f_equal; apply funext; intros m2.
        apply (rtcpL_roliftL P (U (m1, m2)) (r (m1, m2))).
      + symmetry.
        apply (tcp_conj_sum _ _ _ (olift P (ev e m1))
                 (fun m2 : cmem => rtcpL (r (m1, m2))) Hsum).
    - (* the right projection: the action is invisible *)
      cbn [denote]; apply (rcqs_projR_actL P U HU).
  Qed.

  (** [QApply2] is the mirror image; it is what rule Sym would give, and is
      proved directly here for the same reason the paper states QApply1
      directly. *)

  Definition QApply2_pre (P : qset) (e : expr (op (qsub P) (qsub P)))
             (B : pred) : pred :=
    gmap2 (fun (b : hspace rqmem) (Uop : op (qsub P) (qsub P)) =>
             himg (oadj (roliftR P Uop)) (hmeet b (oim (roliftR P Uop))))
          B (idx SR e).

  (* ================================================================= *)
  (** ** The rest of Figure 3

      - [QInit1] (Lemma 66) needs Definition 20's division to interact with the
        register split, and Lemma 21 to simplify the precondition it produces.
      - [Measure1] (Lemma 62) and the two joint measurement rules need the
        post-measurement states of the individual outcomes to be reassembled,
        i.e. the same sum bookkeeping as the converse of Lemma 36. *)

End QuantumRules.
