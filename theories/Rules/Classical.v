(** * Rules for classical statements (Figure 2).

    Section 5.1, "Rules for classical statements": "For each classical
    statement of the language (skip, assignment, sampling, if, and while) we
    provide one or several rules. Rules ending with 1 operate only on the left
    program and assume that the right program is skip. The rules can be applied
    to a larger program by combining them with rule Seq."

    Each theorem below carries the paper's rule name, the lemma number that
    proves it, and the page. *)

From Stdlib Require Import List Lra.
From QRHL.Substrate Require Import Ambient Cnum Sums Interface Theory.
From QRHL.Core Require Import
  Vars Expr Registers Syntax Semantics Predicate QEq Judgment.

Module ClassicalRules (S : HILBERT_SUBSTRATE) (V : PROGRAM_VARS).
  Include JudgmentTheory S V.

  (* ================================================================= *)
  (** ** Assign1  [Figure 2, Lemma 55, p. 62]

<<
        ---------------------------------------
         {B{idx_1 e / x_1}} x <- e ~ skip {B}
>>

      The witness is the given state pushed forward along the assignment on
      side 1. As in the semantics of assignment, the pushforward at a target
      memory sums over the old values of [x], guarded by
      [m x = [e](m(x := a))].

      The guard is *not* satisfied at a single value -- if [e] is constant, it
      holds for every [a]. What is true is that the pair (target, old value) is
      in bijection with (source, the target's old [x]), and under that
      bijection the guard becomes "this value of [x] is what [e] says of the
      source", which *is* satisfied at exactly one value. So the sum collapses
      after reindexing, not before; that is the whole content of the rule, and
      it is what makes the right-hand projection come back unchanged. *)

  Section Assign1.
    Context (x : cvar) (e : expr (ctype x)).

    Definition assignL (r : rcqs) : rcqs :=
      fun rm =>
        tcp_sum (fun a : ctype x =>
                   if excluded_middle_informative (acond x e (csel SL rm) a)
                   then r (rcupd rm (SL, x) a) else tcp_zero).

    (** The reindexing [rbeta] and the injectivity of [rcupd] live in
        [Core/Judgment.v]; every one-sided rule uses them. *)

    (* --------------------------------------------------------------- *)
    (** *** Summability at a fixed target, and the trace formula *)

    Lemma assignL_inner_wf (r : rcqs) (rm : rcmem) :
      rcqs_wf r ->
      tcp_summable (fun a : ctype x =>
                      if excluded_middle_informative (acond x e (csel SL rm) a)
                      then r (rcupd rm (SL, x) a) else tcp_zero).
    Proof.
      intros Hr; apply tcp_summable_trace.
      apply (summable_mono _ (fun a : ctype x =>
                                tcp_trace (r (rcupd rm (SL, x) a)))).
      - apply (summable_inj (fun a : ctype x => rcupd rm (SL, x) a)
                            (fun rm' => tcp_trace (r rm')));
          [ apply (rcupd_inj x rm) | apply tcp_summable_trace; exact Hr ].
      - intros a;
          destruct (excluded_middle_informative (acond x e (csel SL rm) a));
          [ apply Rle_refl | rewrite tcp_trace_zero; apply tcp_trace_nonneg ].
    Qed.

    Lemma assignL_trace (r : rcqs) (rm : rcmem) :
      rcqs_wf r ->
      tcp_trace (assignL r rm)
      = tsum (fun a : ctype x =>
                if excluded_middle_informative (acond x e (csel SL rm) a)
                then tcp_trace (r (rcupd rm (SL, x) a)) else 0%R).
    Proof.
      intros Hr; unfold assignL.
      rewrite (tcp_trace_sum _ _ _ (assignL_inner_wf r rm Hr)).
      f_equal; apply funext; intros a.
      destruct (excluded_middle_informative (acond x e (csel SL rm) a));
        [ reflexivity | apply tcp_trace_zero ].
    Qed.

    (* --------------------------------------------------------------- *)
    (** *** Well-formedness

        Exactly the pattern of [sem_assign_wf_trace] in [Semantics.v], with
        [rbeta] in place of [sbeta]. *)

    Lemma assignL_wf (r : rcqs) : rcqs_wf r -> rcqs_wf (assignL r).
    Proof.
      intros Hr.
      pose (Ga := fun (rm : rcmem) (a : ctype x) =>
                    if excluded_middle_informative (acond x e (csel SL rm) a)
                    then tcp_trace (r (rcupd rm (SL, x) a)) else 0%R).
      pose (Hsrc := fun (rm' : rcmem) (z : ctype x) =>
                      if excluded_middle_informative (z = ev e (csel SL rm'))
                      then tcp_trace (r rm') else 0%R).
      assert (HGH : (fun p : rcmem * ctype x => Ga (fst p) (snd p))
                    = (fun p : rcmem * ctype x =>
                         Hsrc (fst (rbeta x p)) (snd (rbeta x p)))).
      { apply funext; intros p; unfold Ga, Hsrc, rbeta, acond; cbn [fst snd].
        rewrite csel_rcupd_L; reflexivity. }
      assert (HsrcS : forall rm', summable (Hsrc rm'))
        by (intros rm';
            apply (proj1 (tsum_single_val (ev e (csel SL rm'))
                            (tcp_trace (r rm')) (tcp_trace_nonneg _ _)))).
      assert (HsrcB : forall rm', tsum (Hsrc rm') = tcp_trace (r rm'))
        by (intros rm';
            apply (proj2 (tsum_single_val (ev e (csel SL rm'))
                            (tcp_trace (r rm')) (tcp_trace_nonneg _ _)))).
      assert (HsrcIt : summable (fun rm' => tsum (Hsrc rm'))).
      { apply (summable_mono _ (fun rm' => tcp_trace (r rm')));
          [ apply tcp_summable_trace; exact Hr
          | intros rm'; rewrite HsrcB; apply Rle_refl ]. }
      destruct (tsum_pairs_le_iter Hsrc HsrcS HsrcIt) as [HsrcPS _].
      assert (HGS : summable (fun p : rcmem * ctype x => Ga (fst p) (snd p))).
      { rewrite HGH.
        apply (summable_inj (rbeta x)
                 (fun q : rcmem * ctype x => Hsrc (fst q) (snd q)));
          [ apply (rbeta_inj x) | exact HsrcPS ]. }
      assert (HGpos : nonneg (fun p : rcmem * ctype x => Ga (fst p) (snd p))).
      { intros p; unfold Ga.
        destruct (excluded_middle_informative
                    (acond x e (csel SL (fst p)) (snd p)));
          [ apply tcp_trace_nonneg | apply Rle_refl ]. }
      destruct (tsum_iter_le_pairs Ga HGpos HGS) as [HGit _].
      apply tcp_summable_trace.
      assert (Heq : (fun rm => tcp_trace (assignL r rm))
                    = (fun rm => tsum (Ga rm)))
        by (apply funext; intros rm; apply assignL_trace; exact Hr).
      rewrite Heq; exact HGit.
    Qed.

    (* --------------------------------------------------------------- *)
    (** *** Separability

        Each block of the sum is separable; the decompositions are flattened
        into one by [tcp_sum_sigma]. *)

    Lemma assignL_sep (r : rcqs) :
      rcqs_wf r -> rcqs_sep r -> rcqs_sep (assignL r).
    Proof.
      intros Hwf Hsep rm; unfold rsep, assignL.
      rewrite (tcp_conj_sum _ _ _ Urqpair _ (assignL_inner_wf r rm Hwf)).
      set (G := fun a : ctype x =>
                  tcp_conj Urqpair
                    (if excluded_middle_informative (acond x e (csel SL rm) a)
                     then r (rcupd rm (SL, x) a) else tcp_zero)).
      assert (HGsep : forall a, tcp_sep (G a)).
      { intros a; unfold G.
        destruct (excluded_middle_informative (acond x e (csel SL rm) a)).
        - apply (Hsep (rcupd rm (SL, x) a)).
        - rewrite tcp_conj_zero; apply tcp_sep_zero. }
      assert (Hdec : forall a : ctype x,
                { J : Type & { fg : (J -> tcp qmem) * (J -> tcp qmem) |
                    tcp_summable (fun j => tcp_tensor (fst fg j) (snd fg j))
                    /\ G a = tcp_sum (fun j => tcp_tensor (fst fg j) (snd fg j)) } }).
      { intros a.
        destruct (constructive_indefinite_description _ (HGsep a)) as [J HJ].
        destruct (constructive_indefinite_description _ HJ) as [f Hf].
        destruct (constructive_indefinite_description _ Hf) as [g Hg].
        exists J, (f, g); exact Hg. }
      exists (sigT (fun a : ctype x => projT1 (Hdec a))),
             (fun p => fst (proj1_sig (projT2 (Hdec (projT1 p)))) (projT2 p)),
             (fun p => snd (proj1_sig (projT2 (Hdec (projT1 p)))) (projT2 p)).
      set (F := fun (a : ctype x) (j : projT1 (Hdec a)) =>
                  tcp_tensor (fst (proj1_sig (projT2 (Hdec a))) j)
                             (snd (proj1_sig (projT2 (Hdec a))) j)).
      assert (HFa : forall a, tcp_summable (F a))
        by (intros a; apply (proj1 (proj2_sig (projT2 (Hdec a))))).
      assert (HFs : forall a, G a = tcp_sum (F a))
        by (intros a; apply (proj2 (proj2_sig (projT2 (Hdec a))))).
      assert (HGs : tcp_summable (fun a => tcp_sum (F a))).
      { assert (HGeq : (fun a => tcp_sum (F a)) = G)
          by (apply funext; intros a; symmetry; apply HFs).
        rewrite HGeq; unfold G.
        apply (tcp_summable_conj Urqpair _ (proj1 Urqpair_unitary)
                 (assignL_inner_wf r rm Hwf)). }
      destruct (tcp_sum_sigma _ _ _ F HFa HGs) as [Hsig Heqsig].
      split.
      - exact Hsig.
      - transitivity (tcp_sum (fun a => tcp_sum (F a))).
        + f_equal; apply funext; intros a; apply HFs.
        + exact Heqsig.
    Qed.

    (* --------------------------------------------------------------- *)
    (** *** The postcondition

        The guard is what turns the substituted precondition back into [B]:
        at a surviving old value, updating [x_1] by [[e]] of the updated
        memory puts it back where it was. *)

    Lemma assignL_psat (r : rcqs) (B : pred) :
      rcqs_wf r ->
      psat r (rsubst B (SL, x) (idx SL e)) -> psat (assignL r) B.
    Proof.
      intros Hwf Hsat rm; unfold assignL.
      rewrite (tcp_supp_sum _ _ _ (assignL_inner_wf r rm Hwf)).
      apply hSup_lub; intros a.
      destruct (excluded_middle_informative (acond x e (csel SL rm) a))
        as [Hc | _].
      - eapply hle_trans; [ apply (Hsat (rcupd rm (SL, x) a)) |].
        (* [ev] of the substituted predicate, at the updated memory *)
        unfold rsubst, gsubst, idx; cbn [ev].
        rewrite rcupd_rcupd_L, csel_rcupd_L.
        unfold acond in Hc; rewrite <- Hc, rcupd_id_L.
        apply hle_refl.
      - rewrite (proj2 (tcp_supp_eq0 _ _) eq_refl); apply hbot_le.
    Qed.

    (* --------------------------------------------------------------- *)
    (** *** The two projections *)

    Lemma assignL_slice_wf (r : rcqs) (m1 : cmem) (a : ctype x) :
      rcqs_wf r ->
      tcp_summable (fun m2 : cmem => rtcpL (r (cupd m1 x a, m2))).
    Proof. intros Hr; apply (rcqs_slice_wf r (cupd m1 x a) Hr). Qed.

    Lemma assignL_projL (r : rcqs) :
      rcqs_wf r ->
      rcqs_projL (assignL r) = sem_assign x e (rcqs_projL r).
    Proof.
      intros Hwf; apply funext; intros m1.
      pose (F := fun (m2 : cmem) (a : ctype x) =>
                   if excluded_middle_informative (acond x e m1 a)
                   then rtcpL (r (cupd m1 x a, m2)) else tcp_zero).
      assert (HFm : forall m2, tcp_summable (F m2)).
      { intros m2; unfold F.
        apply (tcp_summable_trace _ _
                 (fun a : ctype x =>
                    if excluded_middle_informative (acond x e m1 a)
                    then rtcpL (r (cupd m1 x a, m2)) else tcp_zero)).
        apply (summable_mono _ (fun a : ctype x =>
                                  tcp_trace (r (cupd m1 x a, m2)))).
        - apply (summable_inj (fun a : ctype x => (cupd m1 x a, m2))
                              (fun rm => tcp_trace (r rm))).
          + intros u v Huv.
            assert (H : cupd m1 x u = cupd m1 x v) by congruence.
            rewrite <- (cupd_same m1 x u), H, cupd_same; reflexivity.
          + apply tcp_summable_trace; exact Hwf.
        - intros a;
            destruct (excluded_middle_informative (acond x e m1 a));
            [ rewrite rtcpL_trace; apply Rle_refl
            | rewrite tcp_trace_zero; apply tcp_trace_nonneg ]. }
      assert (HFa : forall a, tcp_summable (fun m2 => F m2 a)).
      { intros a; unfold F.
        destruct (excluded_middle_informative (acond x e m1 a)).
        - apply (assignL_slice_wf r m1 a Hwf).
        - apply (tcp_summable_singleton _ cmem0); intros m2 _; reflexivity. }
      assert (HFit : tcp_summable (fun m2 => tcp_sum (F m2))).
      { apply (tcp_summable_trace _ _ (fun m2 => tcp_sum (F m2))).
        apply (summable_mono _ (fun m2 => tcp_trace (assignL r (m1, m2)))).
        - apply (summable_inj (fun m2 : cmem => (m1, m2))
                              (fun rm => tcp_trace (assignL r rm)));
            [ intros u v Huv; congruence
            | apply tcp_summable_trace, assignL_wf; exact Hwf ].
        - intros m2; rewrite (tcp_trace_sum _ _ _ (HFm m2)).
          rewrite (assignL_trace r (m1, m2) Hwf).
          apply Req_le; f_equal; apply funext; intros a; unfold F; cbn [csel fst snd].
          destruct (excluded_middle_informative (acond x e m1 a));
            [ apply rtcpL_trace | apply tcp_trace_zero ]. }
      assert (HFat : tcp_summable (fun a => tcp_sum (fun m2 => F m2 a))).
      { apply (tcp_summable_trace _ _ (fun a => tcp_sum (fun m2 => F m2 a))).
        apply (summable_mono _ (fun a : ctype x =>
                                  tcp_trace (rcqs_projL r (cupd m1 x a)))).
        - apply (summable_inj (fun a : ctype x => cupd m1 x a)
                              (fun m => tcp_trace (rcqs_projL r m))).
          + intros u v Huv.
            rewrite <- (cupd_same m1 x u), Huv, cupd_same; reflexivity.
          + apply tcp_summable_trace, rcqs_projL_wf; exact Hwf.
        - intros a; unfold F.
          destruct (excluded_middle_informative (acond x e m1 a)).
          + apply Req_le; reflexivity.
          + rewrite (tcp_sum_zero (fun _ : cmem => tcp_zero)
                       (fun _ => eq_refl)), tcp_trace_zero.
            apply tcp_trace_nonneg. }
      (* now the computation *)
      unfold rcqs_projL at 1, assignL, sem_assign.
      transitivity (tcp_sum (fun m2 : cmem => tcp_sum (F m2))).
      { f_equal; apply funext; intros m2.
        rewrite (rtcpL_sum _ (assignL_inner_wf r (m1, m2) Hwf)).
        f_equal; apply funext; intros a; unfold F; cbn [csel fst snd].
        destruct (excluded_middle_informative (acond x e m1 a));
          [ reflexivity | apply rtcpL_zero ]. }
      rewrite (tcp_sum_swap F HFm HFit HFa HFat).
      f_equal; apply funext; intros a; unfold F.
      destruct (excluded_middle_informative (acond x e m1 a)).
      - reflexivity.
      - apply (tcp_sum_zero (fun _ : cmem => tcp_zero) (fun _ => eq_refl)).
    Qed.


    (** The right projection. Here the reindexing does its real work: the
        source memories are hit exactly once, so the projection comes back
        unchanged -- which is what the rule needs, the right program being
        [skip]. *)

    Lemma assignL_projR (r : rcqs) :
      rcqs_wf r -> rcqs_projR (assignL r) = rcqs_projR r.
    Proof.
      intros Hwf; apply funext; intros m2.
      pose (Ga := fun (m1 : cmem) (a : ctype x) =>
                    if excluded_middle_informative (acond x e m1 a)
                    then rtcpR (r (cupd m1 x a, m2)) else tcp_zero).
      pose (Hsrc := fun (m : cmem) (z : ctype x) =>
                      if excluded_middle_informative (z = ev e m)
                      then rtcpR (r (m, m2)) else tcp_zero).
      assert (HGH : (fun p : cmem * ctype x => Ga (fst p) (snd p))
                    = (fun p : cmem * ctype x =>
                         Hsrc (fst (sbeta x p)) (snd (sbeta x p))))
        by (apply funext; intros p; reflexivity).
      assert (HsrcS : forall m, tcp_summable (Hsrc m)).
      { intros m; apply (tcp_summable_singleton _ (ev e m)).
        intros z Hz; unfold Hsrc;
          destruct (excluded_middle_informative (z = ev e m)); congruence. }
      assert (HsrcV : forall m, tcp_sum (Hsrc m) = rtcpR (r (m, m2))).
      { intros m; rewrite (tcp_sum_singleton _ (ev e m)).
        - unfold Hsrc;
            destruct (excluded_middle_informative (ev e m = ev e m));
            congruence.
        - intros z Hz; unfold Hsrc;
            destruct (excluded_middle_informative (z = ev e m)); congruence. }
      assert (HsrcIt : tcp_summable (fun m => tcp_sum (Hsrc m))).
      { assert (Heq : (fun m => tcp_sum (Hsrc m))
                      = (fun m => rtcpR (r (m, m2))))
          by (apply funext; exact HsrcV).
        rewrite Heq; apply (rcqs_slice_wf_R r m2 Hwf). }
      assert (HGa : forall m1, tcp_summable (Ga m1)).
      { intros m1; apply tcp_summable_trace.
        apply (summable_mono _ (fun a : ctype x =>
                                  tcp_trace (r (cupd m1 x a, m2)))).
        - apply (summable_inj (fun a : ctype x => (cupd m1 x a, m2))
                              (fun rm => tcp_trace (r rm))).
          + intros u v Huv.
            assert (H : cupd m1 x u = cupd m1 x v) by congruence.
            rewrite <- (cupd_same m1 x u), H, cupd_same; reflexivity.
          + apply tcp_summable_trace; exact Hwf.
        - intros a; unfold Ga;
            destruct (excluded_middle_informative (acond x e m1 a));
            [ rewrite rtcpR_trace; apply Rle_refl
            | rewrite tcp_trace_zero; apply tcp_trace_nonneg ]. }
      assert (HGeq : forall m1, tcp_sum (Ga m1) = rtcpR (assignL r (m1, m2))).
      { intros m1; unfold assignL.
        rewrite (rtcpR_sum _ (assignL_inner_wf r (m1, m2) Hwf)).
        f_equal; apply funext; intros a; unfold Ga; cbn [csel fst snd].
        destruct (excluded_middle_informative (acond x e m1 a));
          [ reflexivity | symmetry; apply rtcpR_zero ]. }
      assert (HGit : tcp_summable (fun m1 => tcp_sum (Ga m1))).
      { assert (Heq : (fun m1 => tcp_sum (Ga m1))
                      = (fun m1 => rtcpR (assignL r (m1, m2))))
          by (apply funext; exact HGeq).
        rewrite Heq.
        apply (rcqs_slice_wf_R (assignL r) m2), assignL_wf; exact Hwf. }
      unfold rcqs_projR at 1.
      transitivity (tcp_sum (fun m1 : cmem => tcp_sum (Ga m1))).
      { f_equal; apply funext; intros m1; symmetry; apply HGeq. }
      destruct (tcp_sum_pair Ga HGa HGit) as [_ HGeq2].
      rewrite HGeq2, HGH.
      destruct (tcp_sum_pair Hsrc HsrcS HsrcIt) as [HsrcP HsrcEq].
      destruct (tcp_sum_bij _ _ _ (sbeta x) (sbeta x)
                  (fun q : cmem * ctype x => Hsrc (fst q) (snd q))
                  (sbeta_invol x) (sbeta_invol x) HsrcP) as [_ Hbij].
      rewrite Hbij, <- HsrcEq.
      unfold rcqs_projR; f_equal; apply funext; intros m; apply HsrcV.
    Qed.

    (* --------------------------------------------------------------- *)
    (** *** The rule *)

    Theorem rule_Assign1 (B : pred) :
      qrhl (rsubst B (SL, x) (idx SL e)) (Assign x e) Skip B.
    Proof.
      intros r Hwf Hsep Hsat.
      exists (assignL r); repeat split.
      - apply assignL_wf; exact Hwf.
      - apply assignL_sep; assumption.
      - apply assignL_psat; assumption.
      - cbn [denote]; apply assignL_projL; exact Hwf.
      - cbn [denote]; apply assignL_projR; exact Hwf.
    Qed.

  End Assign1.

  (* ================================================================= *)
  (** ** If1  [Figure 2, Lemma 58, p. 64]

<<
         {Cla[idx_1 e] cap A} c ~ skip {B}
         {Cla[~ idx_1 e] cap A} d ~ skip {B}
        ------------------------------------------
         {A} if e then c else d ~ skip {B}
>>

      Split the given state by the value of the condition on side 1, apply one
      premise to each half, and add the two witnesses. Two things make this go
      through without any new machinery:

      - the condition is a *left-hand* expression, so its value does not depend
        on the right-hand memory; it therefore passes straight through the left
        projection ([rcqs_projL_rrestr]), which is exactly what matches the
        [Cond] clause of the semantics;
      - the two halves add back up to the original state, and both projections
        are additive, so the right projection comes back unchanged. *)

  Theorem rule_If1 (e : expr bool) (c d : prog) (A B : pred) :
    qrhl (pmeet (Cla (idx SL e)) A) c Skip B ->
    qrhl (pmeet (Cla (gmap negb (idx SL e))) A) d Skip B ->
    qrhl A (Cond e c d) Skip B.
  Proof.
    intros H1 H2 r Hwf Hsep Hsat.
    (* the two halves *)
    set (rt := rrestr (idx SL e) r).
    set (rf := rrestrn (idx SL e) r).
    assert (Hwft : rcqs_wf rt) by (apply rrestr_wf; exact Hwf).
    assert (Hwff : rcqs_wf rf) by (apply rrestrn_wf; exact Hwf).
    destruct (H1 rt Hwft (rrestr_sep _ _ Hsep)
                (proj2 (psat_pmeet rt _ A)
                   (conj (rrestr_psat_Cla (idx SL e) r)
                         (rrestr_psat _ _ A Hsat))))
      as [r1 [Hwf1 [Hsep1 [Hsat1 [HL1 HR1]]]]].
    destruct (H2 rf Hwff (rrestrn_sep _ _ Hsep)
                (proj2 (psat_pmeet rf _ A)
                   (conj (rrestrn_psat_Cla (idx SL e) r)
                         (rrestrn_psat _ _ A Hsat))))
      as [r2 [Hwf2 [Hsep2 [Hsat2 [HL2 HR2]]]]].
    exists (rcqs_add r1 r2); repeat split.
    - apply rcqs_add_wf; assumption.
    - apply rcqs_add_sep; assumption.
    - (* the postcondition survives the sum: supports join *)
      intros rm; unfold rcqs_add.
      rewrite (tcp_supp_add _ (r1 rm) (r2 rm)).
      apply hSup_lub; intros [|]; [ apply Hsat1 | apply Hsat2 ].
    - (* left projection: the two halves are the two branches *)
      rewrite (rcqs_projL_add r1 r2 Hwf1 Hwf2), HL1, HL2.
      cbn [denote].
      unfold rt, rf; rewrite rcqs_projL_rrestr, rcqs_projL_rrestrn; reflexivity.
    - (* right projection: the halves add back up *)
      rewrite (rcqs_projR_add r1 r2 Hwf1 Hwf2).
      cbn [denote] in HR1, HR2 |- *.
      rewrite HR1, HR2, <- (rcqs_projR_add rt rf Hwft Hwff).
      unfold rt, rf; rewrite rrestr_split; reflexivity.
  Qed.

  (* ================================================================= *)
  (** ** Sample1  [Figure 2, Lemma 56, p. 62] -- infrastructure

      The witness is the given state pushed forward along the sampling on
      side 1: the same shape as [Assign1], with the subdistribution's weights
      in place of the guard. The reindexing [rbeta] is reused verbatim, and
      under it the weight at (target, old value) becomes the weight the source
      distribution assigns to the target's old [x] -- which is what makes the
      right projection collapse, given totality. *)

  Section Sample1.
    Context (x : cvar) (e : expr (distr (ctype x))).

    Definition swt (rm : rcmem) (a : ctype x) : R :=
      ev e (cupd (csel SL rm) x a) (csel SL rm x).

    Definition sampleL (r : rcqs) : rcqs :=
      fun rm => tcp_sum (fun a : ctype x =>
                           tcp_scale (swt rm a) (r (rcupd rm (SL, x) a))).

    Lemma swt_nonneg (rm : rcmem) (a : ctype x) : (0 <= swt rm a)%R.
    Proof. apply dfun_nonneg. Qed.

    Lemma swt_le1 (rm : rcmem) (a : ctype x) : (swt rm a <= 1)%R.
    Proof. apply dfun_le1_pt. Qed.

    Lemma sampleL_inner_wf (r : rcqs) (rm : rcmem) :
      rcqs_wf r ->
      tcp_summable (fun a : ctype x =>
                      tcp_scale (swt rm a) (r (rcupd rm (SL, x) a))).
    Proof.
      intros Hr; apply tcp_summable_trace.
      apply (summable_mono _ (fun a : ctype x =>
                                tcp_trace (r (rcupd rm (SL, x) a)))).
      - apply (summable_inj (fun a : ctype x => rcupd rm (SL, x) a)
                            (fun rm' => tcp_trace (r rm')));
          [ apply (rcupd_inj x rm) | apply tcp_summable_trace; exact Hr ].
      - intros a; rewrite tcp_trace_scale.
        rewrite <- (Rmult_1_l (tcp_trace (r (rcupd rm (SL, x) a)))) at 2.
        apply Rmult_le_compat_r; [ apply tcp_trace_nonneg | apply swt_le1 ].
    Qed.

    Lemma sampleL_trace (r : rcqs) (rm : rcmem) :
      rcqs_wf r ->
      tcp_trace (sampleL r rm)
      = tsum (fun a : ctype x =>
                (swt rm a * tcp_trace (r (rcupd rm (SL, x) a)))%R).
    Proof.
      intros Hr; unfold sampleL.
      rewrite (tcp_trace_sum _ _ _ (sampleL_inner_wf r rm Hr)).
      f_equal; apply funext; intros a; apply tcp_trace_scale.
    Qed.

    (** Under [rbeta], the weight becomes the source distribution evaluated at
        the target's old [x]. *)
    Definition ssrc (r : rcqs) (rm' : rcmem) (z : ctype x) : R :=
      (tcp_trace (r rm') * ev e (csel SL rm') z)%R.

    Lemma sampleL_reindex (r : rcqs) :
      (fun p : rcmem * ctype x =>
         (swt (fst p) (snd p)
          * tcp_trace (r (rcupd (fst p) (SL, x) (snd p))))%R)
      = (fun p : rcmem * ctype x =>
           ssrc r (fst (rbeta x p)) (snd (rbeta x p))).
    Proof.
      apply funext; intros p; unfold ssrc, swt, rbeta;
        cbn [fst snd csel rcupd]; ring.
    Qed.

    Lemma ssrc_summable (r : rcqs) (rm' : rcmem) : summable (ssrc r rm').
    Proof.
      apply summable_scale;
        [ apply tcp_trace_nonneg | apply dfun_nonneg | apply dfun_summable ].
    Qed.

    Lemma ssrc_le (r : rcqs) (rm' : rcmem) :
      (tsum (ssrc r rm') <= tcp_trace (r rm'))%R.
    Proof.
      unfold ssrc.
      rewrite (tsum_scale (tcp_trace (r rm')) (ev e (csel SL rm'))
                 (tcp_trace_nonneg _ _) (dfun_nonneg _) (dfun_summable _)).
      rewrite <- (Rmult_1_r (tcp_trace (r rm'))) at 2.
      apply Rmult_le_compat_l; [ apply tcp_trace_nonneg | apply dfun_le1 ].
    Qed.

    Lemma sampleL_wf (r : rcqs) : rcqs_wf r -> rcqs_wf (sampleL r).
    Proof.
      intros Hr.
      pose (Ga := fun (rm : rcmem) (a : ctype x) =>
                    (swt rm a * tcp_trace (r (rcupd rm (SL, x) a)))%R).
      assert (HsrcIt : summable (fun rm' => tsum (ssrc r rm'))).
      { apply (summable_mono _ (fun rm' => tcp_trace (r rm')));
          [ apply tcp_summable_trace; exact Hr | apply ssrc_le ]. }
      destruct (tsum_pairs_le_iter (ssrc r) (ssrc_summable r) HsrcIt)
        as [HsrcPS _].
      assert (HGS : summable (fun p : rcmem * ctype x => Ga (fst p) (snd p))).
      { unfold Ga; rewrite sampleL_reindex.
        apply (summable_inj (rbeta x)
                 (fun q : rcmem * ctype x => ssrc r (fst q) (snd q)));
          [ apply (rbeta_inj x) | exact HsrcPS ]. }
      assert (HGpos : nonneg (fun p : rcmem * ctype x => Ga (fst p) (snd p))).
      { intros p; unfold Ga; apply Rmult_le_pos;
          [ apply swt_nonneg | apply tcp_trace_nonneg ]. }
      destruct (tsum_iter_le_pairs Ga HGpos HGS) as [HGit _].
      apply tcp_summable_trace.
      assert (Heq : (fun rm => tcp_trace (sampleL r rm))
                    = (fun rm => tsum (Ga rm)))
        by (apply funext; intros rm; apply sampleL_trace; exact Hr).
      rewrite Heq; exact HGit.
    Qed.

    Lemma sampleL_sep (r : rcqs) :
      rcqs_wf r -> rcqs_sep r -> rcqs_sep (sampleL r).
    Proof.
      intros Hwf Hsep rm; unfold rsep, sampleL.
      rewrite (tcp_conj_sum _ _ _ Urqpair _ (sampleL_inner_wf r rm Hwf)).
      set (G := fun a : ctype x =>
                  tcp_conj Urqpair
                    (tcp_scale (swt rm a) (r (rcupd rm (SL, x) a)))).
      assert (HGsep : forall a, tcp_sep (G a)).
      { intros a; unfold G; rewrite tcp_conj_scale.
        apply tcp_sep_scale, (Hsep (rcupd rm (SL, x) a)). }
      assert (Hdec : forall a : ctype x,
                { J : Type & { fg : (J -> tcp qmem) * (J -> tcp qmem) |
                    tcp_summable (fun j => tcp_tensor (fst fg j) (snd fg j))
                    /\ G a = tcp_sum (fun j => tcp_tensor (fst fg j) (snd fg j)) } }).
      { intros a.
        destruct (constructive_indefinite_description _ (HGsep a)) as [J HJ].
        destruct (constructive_indefinite_description _ HJ) as [f Hf].
        destruct (constructive_indefinite_description _ Hf) as [g Hg].
        exists J, (f, g); exact Hg. }
      exists (sigT (fun a : ctype x => projT1 (Hdec a))),
             (fun p => fst (proj1_sig (projT2 (Hdec (projT1 p)))) (projT2 p)),
             (fun p => snd (proj1_sig (projT2 (Hdec (projT1 p)))) (projT2 p)).
      set (F := fun (a : ctype x) (j : projT1 (Hdec a)) =>
                  tcp_tensor (fst (proj1_sig (projT2 (Hdec a))) j)
                             (snd (proj1_sig (projT2 (Hdec a))) j)).
      assert (HFa : forall a, tcp_summable (F a))
        by (intros a; apply (proj1 (proj2_sig (projT2 (Hdec a))))).
      assert (HFs : forall a, G a = tcp_sum (F a))
        by (intros a; apply (proj2 (proj2_sig (projT2 (Hdec a))))).
      assert (HGs : tcp_summable (fun a => tcp_sum (F a))).
      { assert (HGeq : (fun a => tcp_sum (F a)) = G)
          by (apply funext; intros a; symmetry; apply HFs).
        rewrite HGeq; unfold G.
        apply (tcp_summable_conj Urqpair _ (proj1 Urqpair_unitary)
                 (sampleL_inner_wf r rm Hwf)). }
      destruct (tcp_sum_sigma _ _ _ F HFa HGs) as [Hsig Heqsig].
      split.
      - exact Hsig.
      - transitivity (tcp_sum (fun a => tcp_sum (F a))).
        + f_equal; apply funext; intros a; apply HFs.
        + exact Heqsig.
    Qed.


    (* --------------------------------------------------------------- *)
    (** *** The precondition

        [A := Cla[e' is total] cap Inter_{z in supp e'} B{z/x_1}], with
        [e' := idx_1 e]. The intersection is over the *support*, which depends
        on the memory, so it is written as an intersection over all of
        [ctype x] whose conjunct is the full space off the support. *)

    Definition Sample1_pre (B : pred) : pred :=
      pmeet
        (Cla (gmap (fun mu : distr (ctype x) =>
                      if excluded_middle_informative (dtotal mu)
                      then true else false)
                   (idx SL e)))
        (pInf (fun z : ctype x =>
                 gmap2 (fun (mu : distr (ctype x)) (b : hspace rqmem) =>
                          if excluded_middle_informative (0 < mu z)%R
                          then b else htop)
                       (idx SL e) (rsubst_val B (SL, x) z))).

    Lemma sampleL_psat (r : rcqs) (B : pred) :
      rcqs_wf r -> psat r (Sample1_pre B) -> psat (sampleL r) B.
    Proof.
      intros Hwf Hsat rm; unfold sampleL.
      rewrite (tcp_supp_sum _ _ _ (sampleL_inner_wf r rm Hwf)).
      apply hSup_lub; intros a.
      destruct (Rle_lt_or_eq_dec 0 (swt rm a) (swt_nonneg rm a))
        as [Hpos | Hzero].
      - rewrite (tcp_supp_scale _ _ _ Hpos).
        eapply hle_trans; [ apply (Hsat (rcupd rm (SL, x) a)) |].
        eapply hle_trans; [ apply hmeet_ler |].
        eapply hle_trans;
          [ apply (hInf_lb
                     (fun z : ctype x =>
                        ev (gmap2 (fun (mu : distr (ctype x)) (b : hspace rqmem) =>
                                     if excluded_middle_informative (0 < mu z)%R
                                     then b else htop)
                                  (idx SL e) (rsubst_val B (SL, x) z))
                           (rcupd rm (SL, x) a))
                     (csel SL rm x)) |].
        cbn [ev gmap2].
        destruct (excluded_middle_informative
                    (0 < ev (idx SL e) (rcupd rm (SL, x) a) (csel SL rm x))%R)
          as [_ | Hno].
        + rewrite ev_rsubst_val, rcupd_rcupd_L, rcupd_id_L; apply hle_refl.
        + exfalso; apply Hno; exact Hpos.
      - rewrite <- Hzero, tcp_scale_0.
        rewrite (proj2 (tcp_supp_eq0 _ _) eq_refl); apply hbot_le.
    Qed.

    (* --------------------------------------------------------------- *)
    (** *** The two projections *)

    Lemma sampleL_projL (r : rcqs) :
      rcqs_wf r -> rcqs_projL (sampleL r) = sem_sample x e (rcqs_projL r).
    Proof.
      intros Hwf; apply funext; intros m1.
      pose (F := fun (m2 : cmem) (a : ctype x) =>
                   tcp_scale (ev e (cupd m1 x a) (m1 x))
                             (rtcpL (r (cupd m1 x a, m2)))).
      assert (Hslice : forall a : ctype x,
                 tcp_summable (fun m2 : cmem => rtcpL (r (cupd m1 x a, m2))))
        by (intros a; apply (rcqs_slice_wf r (cupd m1 x a) Hwf)).
      assert (HFm : forall m2, tcp_summable (F m2)).
      { intros m2; unfold F; apply tcp_summable_trace.
        apply (summable_mono _ (fun a : ctype x =>
                                  tcp_trace (r (cupd m1 x a, m2)))).
        - apply (summable_inj (fun a : ctype x => (cupd m1 x a, m2))
                              (fun rm => tcp_trace (r rm))).
          + intros u v Huv.
            assert (H : cupd m1 x u = cupd m1 x v) by congruence.
            rewrite <- (cupd_same m1 x u), H, cupd_same; reflexivity.
          + apply tcp_summable_trace; exact Hwf.
        - intros a; rewrite tcp_trace_scale, rtcpL_trace.
          rewrite <- (Rmult_1_l (tcp_trace (r (cupd m1 x a, m2)))) at 2.
          apply Rmult_le_compat_r;
            [ apply tcp_trace_nonneg | apply dfun_le1_pt ]. }
      assert (HFa : forall a, tcp_summable (fun m2 => F m2 a)).
      { intros a; unfold F.
        apply tcp_summable_trace.
        apply (summable_mono _ (fun m2 : cmem =>
                                  tcp_trace (rtcpL (r (cupd m1 x a, m2))))).
        - apply tcp_summable_trace, Hslice.
        - intros m2; rewrite tcp_trace_scale.
          rewrite <- (Rmult_1_l (tcp_trace (rtcpL (r (cupd m1 x a, m2))))) at 2.
          apply Rmult_le_compat_r;
            [ apply tcp_trace_nonneg | apply dfun_le1_pt ]. }
      assert (HFit : tcp_summable (fun m2 => tcp_sum (F m2))).
      { apply tcp_summable_trace.
        apply (summable_mono _ (fun m2 => tcp_trace (sampleL r (m1, m2)))).
        - apply (summable_inj (fun m2 : cmem => (m1, m2))
                              (fun rm => tcp_trace (sampleL r rm)));
            [ intros u v Huv; congruence
            | apply tcp_summable_trace, sampleL_wf; exact Hwf ].
        - intros m2; rewrite (tcp_trace_sum _ _ _ (HFm m2)).
          rewrite (sampleL_trace r (m1, m2) Hwf).
          apply Req_le; f_equal; apply funext; intros a; unfold F, swt.
          rewrite tcp_trace_scale, rtcpL_trace; reflexivity. }
      assert (HFat : tcp_summable (fun a => tcp_sum (fun m2 => F m2 a))).
      { apply tcp_summable_trace.
        apply (summable_mono _ (fun a : ctype x =>
                                  tcp_trace (rcqs_projL r (cupd m1 x a)))).
        - apply (summable_inj (fun a : ctype x => cupd m1 x a)
                              (fun m => tcp_trace (rcqs_projL r m))).
          + intros u v Huv.
            rewrite <- (cupd_same m1 x u), Huv, cupd_same; reflexivity.
          + apply tcp_summable_trace, rcqs_projL_wf; exact Hwf.
        - intros a; unfold F, rcqs_projL.
          rewrite <- (tcp_scale_sum _ _ _ _ (Hslice a)), tcp_trace_scale.
          rewrite <- (Rmult_1_l (tcp_trace (tcp_sum
                        (fun m2 : cmem => rtcpL (r (cupd m1 x a, m2)))))) at 2.
          apply Rmult_le_compat_r;
            [ apply tcp_trace_nonneg | apply dfun_le1_pt ]. }
      unfold rcqs_projL at 1, sampleL, sem_sample.
      transitivity (tcp_sum (fun m2 : cmem => tcp_sum (F m2))).
      { f_equal; apply funext; intros m2.
        rewrite (rtcpL_sum _ (sampleL_inner_wf r (m1, m2) Hwf)).
        f_equal; apply funext; intros a; unfold F, swt; cbn [csel fst snd].
        apply rtcpL_scale. }
      rewrite (tcp_sum_swap F HFm HFit HFa HFat).
      f_equal; apply funext; intros a; unfold F.
      rewrite <- (tcp_scale_sum _ _ _ _ (Hslice a)); reflexivity.
    Qed.

    Lemma sampleL_projR (r : rcqs) (B : pred) :
      rcqs_wf r ->
      (forall rm, r rm <> tcp_zero -> dtotal (ev e (csel SL rm))) ->
      rcqs_projR (sampleL r) = rcqs_projR r.
    Proof.
      intros Hwf Htot; apply funext; intros m2.
      pose (Ga := fun (m1 : cmem) (a : ctype x) =>
                    tcp_scale (ev e (cupd m1 x a) (m1 x))
                              (rtcpR (r (cupd m1 x a, m2)))).
      pose (Hsrc := fun (m : cmem) (z : ctype x) =>
                      tcp_scale (ev e m z) (rtcpR (r (m, m2)))).
      assert (HGH : (fun p : cmem * ctype x => Ga (fst p) (snd p))
                    = (fun p : cmem * ctype x =>
                         Hsrc (fst (sbeta x p)) (snd (sbeta x p))))
        by (apply funext; intros p; reflexivity).
      assert (HsrcS : forall m, tcp_summable (Hsrc m)).
      { intros m; unfold Hsrc; apply tcp_summable_trace.
        apply (summable_mono _ (fun z : ctype x =>
                 (tcp_trace (rtcpR (r (m, m2))) * ev e m z)%R)).
        - apply summable_scale;
            [ apply tcp_trace_nonneg | apply dfun_nonneg | apply dfun_summable ].
        - intros z; rewrite tcp_trace_scale; apply Req_le; ring. }
      assert (HsrcV : forall m, tcp_sum (Hsrc m) = rtcpR (r (m, m2))).
      { intros m; unfold Hsrc.
        rewrite (tcp_sum_scale_const _ _ (ev e m) _
                   (fun z => dfun_nonneg _ z) (dfun_summable _)).
        destruct (classic (r (m, m2) = tcp_zero)) as [Hz | Hz].
        - rewrite Hz, rtcpR_zero, tcp_scale_zero; reflexivity.
        - rewrite (Htot (m, m2) Hz); apply tcp_scale_1. }
      assert (HsrcIt : tcp_summable (fun m => tcp_sum (Hsrc m))).
      { assert (Heq : (fun m => tcp_sum (Hsrc m))
                      = (fun m => rtcpR (r (m, m2))))
          by (apply funext; exact HsrcV).
        rewrite Heq; apply (rcqs_slice_wf_R r m2 Hwf). }
      assert (HGa : forall m1, tcp_summable (Ga m1)).
      { intros m1; unfold Ga; apply tcp_summable_trace.
        apply (summable_mono _ (fun a : ctype x =>
                                  tcp_trace (r (cupd m1 x a, m2)))).
        - apply (summable_inj (fun a : ctype x => (cupd m1 x a, m2))
                              (fun rm => tcp_trace (r rm))).
          + intros u v Huv.
            assert (H : cupd m1 x u = cupd m1 x v) by congruence.
            rewrite <- (cupd_same m1 x u), H, cupd_same; reflexivity.
          + apply tcp_summable_trace; exact Hwf.
        - intros a; rewrite tcp_trace_scale, rtcpR_trace.
          rewrite <- (Rmult_1_l (tcp_trace (r (cupd m1 x a, m2)))) at 2.
          apply Rmult_le_compat_r;
            [ apply tcp_trace_nonneg | apply dfun_le1_pt ]. }
      assert (HGeq : forall m1, tcp_sum (Ga m1) = rtcpR (sampleL r (m1, m2))).
      { intros m1; unfold sampleL.
        rewrite (rtcpR_sum _ (sampleL_inner_wf r (m1, m2) Hwf)).
        f_equal; apply funext; intros a; unfold Ga, swt; cbn [csel fst snd].
        symmetry; apply rtcpR_scale. }
      assert (HGit : tcp_summable (fun m1 => tcp_sum (Ga m1))).
      { assert (Heq : (fun m1 => tcp_sum (Ga m1))
                      = (fun m1 => rtcpR (sampleL r (m1, m2))))
          by (apply funext; exact HGeq).
        rewrite Heq.
        apply (rcqs_slice_wf_R (sampleL r) m2), sampleL_wf; exact Hwf. }
      unfold rcqs_projR at 1.
      transitivity (tcp_sum (fun m1 : cmem => tcp_sum (Ga m1))).
      { f_equal; apply funext; intros m1; symmetry; apply HGeq. }
      destruct (tcp_sum_pair Ga HGa HGit) as [_ HGeq2].
      rewrite HGeq2, HGH.
      destruct (tcp_sum_pair Hsrc HsrcS HsrcIt) as [HsrcP HsrcEq].
      destruct (tcp_sum_bij _ _ _ (sbeta x) (sbeta x)
                  (fun q : cmem * ctype x => Hsrc (fst q) (snd q))
                  (sbeta_invol x) (sbeta_invol x) HsrcP) as [_ Hbij].
      rewrite Hbij, <- HsrcEq.
      unfold rcqs_projR; f_equal; apply funext; intros m; apply HsrcV.
    Qed.

    (* --------------------------------------------------------------- *)
    (** *** The rule *)

    Theorem rule_Sample1 (B : pred) :
      qrhl (Sample1_pre B) (Sample x e) Skip B.
    Proof.
      intros r Hwf Hsep Hsat.
      assert (Htot : forall rm, r rm <> tcp_zero -> dtotal (ev e (csel SL rm))).
      { intros rm Hnz.
        pose proof (proj1 (psat_Cla r _)
                      (psat_mono r (Sample1_pre B) _ (fun rm' => hmeet_lel _ _)
                         Hsat) rm Hnz) as Hc.
        cbn [ev gmap] in Hc; unfold idx in Hc; cbn [ev] in Hc.
        destruct (excluded_middle_informative (dtotal (ev e (csel SL rm))));
          [ assumption | discriminate Hc ]. }
      exists (sampleL r); repeat split.
      - apply sampleL_wf; exact Hwf.
      - apply sampleL_sep; assumption.
      - apply sampleL_psat; assumption.
      - cbn [denote]; apply sampleL_projL; exact Hwf.
      - cbn [denote]; apply sampleL_projR; assumption.
    Qed.

  End Sample1.


  (* ================================================================= *)
  (** ** JointSample  [Figure 2, Lemma 57, p. 63]

<<
         f : Type^exp_f subseteq D_{<=1}(Type_x x Type_y)
         A := Cla[marginal_1(f) = idx_1 e_1 /\ marginal_2(f) = idx_2 e_2]
              cap Inter_{(z1,z2) in supp f} B{z1/x_1, z2/y_2}
        -----------------------------------------------------------------
         {A} x <- e_1 ~ y <- e_2 {B}
>>

      "We need to provide a joint distribution [f] as a witness, such that
      [e1], [e2] are the marginals of [f], and [B] holds for any [(x1, y2)]
      chosen according to [f]." Unlike [Sample1] -- where the projection that
      is *not* the sampled side needs totality to collapse -- here *both*
      sides are sampled, so both projections need a marginal identity, not
      just one.

      The witness's weight [jwt] mirrors [swt]'s exact shape but for the
      *joint* distribution: it evaluates [f] at the source memory (the one
      [r]'s argument names, with [x, y] guessed to have been [p]) and applies
      the resulting subdistribution to the target's *own* values of [x] and
      [y] -- the two-sided analogue of "the probability that a source
      distribution assigns to the observed outcome". *)

  Section JointSample.
    Context (x : cvar) (e1 : expr (distr (ctype x)))
            (y : cvar) (e2 : expr (distr (ctype y)))
            (f : rexpr (distr (ctype x * ctype y))).

    Definition jwt (rm : rcmem) (p : ctype x * ctype y) : R :=
      ev f (rcupd (rcupd rm (SL, x) (fst p)) (SR, y) (snd p))
         (csel SL rm x, csel SR rm y).

    Definition sampleLR (r : rcqs) : rcqs :=
      fun rm => tcp_sum (fun p : ctype x * ctype y =>
                   tcp_scale (jwt rm p)
                     (r (rcupd (rcupd rm (SL, x) (fst p)) (SR, y) (snd p)))).

    Lemma jwt_nonneg (rm : rcmem) (p : ctype x * ctype y) : (0 <= jwt rm p)%R.
    Proof. apply dfun_nonneg. Qed.

    Lemma jwt_le1 (rm : rcmem) (p : ctype x * ctype y) : (jwt rm p <= 1)%R.
    Proof. apply dfun_le1_pt. Qed.

    Lemma sampleLR_inner_wf (r : rcqs) (rm : rcmem) :
      rcqs_wf r ->
      tcp_summable (fun p : ctype x * ctype y =>
                      tcp_scale (jwt rm p)
                        (r (rcupd (rcupd rm (SL, x) (fst p)) (SR, y) (snd p)))).
    Proof.
      intros Hr; apply tcp_summable_trace.
      apply (summable_mono _ (fun p : ctype x * ctype y =>
                tcp_trace (r (rcupd (rcupd rm (SL, x) (fst p)) (SR, y) (snd p))))).
      - apply (summable_inj
                 (fun p : ctype x * ctype y =>
                    rcupd (rcupd rm (SL, x) (fst p)) (SR, y) (snd p))
                 (fun rm' => tcp_trace (r rm')));
          [ apply (rcupd2_inj x y rm) | apply tcp_summable_trace; exact Hr ].
      - intros p; rewrite tcp_trace_scale.
        rewrite <- (Rmult_1_l
          (tcp_trace (r (rcupd (rcupd rm (SL, x) (fst p)) (SR, y) (snd p))))) at 2.
        apply Rmult_le_compat_r; [ apply tcp_trace_nonneg | apply jwt_le1 ].
    Qed.

    Lemma sampleLR_trace (r : rcqs) (rm : rcmem) :
      rcqs_wf r ->
      tcp_trace (sampleLR r rm)
      = tsum (fun p : ctype x * ctype y =>
                (jwt rm p
                 * tcp_trace
                     (r (rcupd (rcupd rm (SL, x) (fst p)) (SR, y) (snd p))))%R).
    Proof.
      intros Hr; unfold sampleLR.
      rewrite (tcp_trace_sum _ _ _ (sampleLR_inner_wf r rm Hr)).
      f_equal; apply funext; intros p; apply tcp_trace_scale.
    Qed.

    (** Under [rbeta2], the weight becomes [f] evaluated at the (unchanged)
        source memory and applied to the reindexed value -- the two-sided
        analogue of [ssrc]. *)
    Definition jsrc (r : rcqs) (rm' : rcmem) (z : ctype x * ctype y) : R :=
      (tcp_trace (r rm') * ev f rm' z)%R.

    Lemma sampleLR_reindex (r : rcqs) :
      (fun q : rcmem * (ctype x * ctype y) =>
         (jwt (fst q) (snd q)
          * tcp_trace
              (r (rcupd (rcupd (fst q) (SL, x) (fst (snd q)))
                        (SR, y) (snd (snd q)))))%R)
      = (fun q : rcmem * (ctype x * ctype y) =>
           jsrc r (fst (rbeta2 x y q)) (snd (rbeta2 x y q))).
    Proof.
      apply funext; intros [rm p]; unfold jsrc, jwt, rbeta2; cbn [fst snd]; ring.
    Qed.

    Lemma jsrc_summable (r : rcqs) (rm' : rcmem) : summable (jsrc r rm').
    Proof.
      apply summable_scale;
        [ apply tcp_trace_nonneg | apply dfun_nonneg | apply dfun_summable ].
    Qed.

    Lemma jsrc_le (r : rcqs) (rm' : rcmem) :
      (tsum (jsrc r rm') <= tcp_trace (r rm'))%R.
    Proof.
      unfold jsrc.
      rewrite (tsum_scale (tcp_trace (r rm')) (ev f rm')
                 (tcp_trace_nonneg _ _) (dfun_nonneg _) (dfun_summable _)).
      rewrite <- (Rmult_1_r (tcp_trace (r rm'))) at 2.
      apply Rmult_le_compat_l; [ apply tcp_trace_nonneg | apply dfun_le1 ].
    Qed.

    Lemma sampleLR_wf (r : rcqs) : rcqs_wf r -> rcqs_wf (sampleLR r).
    Proof.
      intros Hr.
      pose (Ga := fun (rm : rcmem) (p : ctype x * ctype y) =>
                    (jwt rm p
                     * tcp_trace
                         (r (rcupd (rcupd rm (SL, x) (fst p))
                                   (SR, y) (snd p))))%R).
      assert (HsrcIt : summable (fun rm' => tsum (jsrc r rm'))).
      { apply (summable_mono _ (fun rm' => tcp_trace (r rm')));
          [ apply tcp_summable_trace; exact Hr | apply jsrc_le ]. }
      destruct (tsum_pairs_le_iter (jsrc r) (jsrc_summable r) HsrcIt)
        as [HsrcPS _].
      assert (HGS : summable
                      (fun q : rcmem * (ctype x * ctype y) => Ga (fst q) (snd q))).
      { unfold Ga; rewrite sampleLR_reindex.
        apply (summable_inj (rbeta2 x y)
                 (fun q : rcmem * (ctype x * ctype y) => jsrc r (fst q) (snd q)));
          [ apply (rbeta2_inj x y) | exact HsrcPS ]. }
      assert (HGpos : nonneg
                        (fun q : rcmem * (ctype x * ctype y) => Ga (fst q) (snd q))).
      { intros q; unfold Ga; apply Rmult_le_pos;
          [ apply jwt_nonneg | apply tcp_trace_nonneg ]. }
      destruct (tsum_iter_le_pairs Ga HGpos HGS) as [HGit _].
      apply tcp_summable_trace.
      assert (Heq : (fun rm => tcp_trace (sampleLR r rm)) = (fun rm => tsum (Ga rm)))
        by (apply funext; intros rm; apply sampleLR_trace; exact Hr).
      rewrite Heq; exact HGit.
    Qed.

    Lemma sampleLR_sep (r : rcqs) :
      rcqs_wf r -> rcqs_sep r -> rcqs_sep (sampleLR r).
    Proof.
      intros Hwf Hsep rm; unfold rsep, sampleLR.
      rewrite (tcp_conj_sum _ _ _ Urqpair _ (sampleLR_inner_wf r rm Hwf)).
      set (G := fun p : ctype x * ctype y =>
                  tcp_conj Urqpair
                    (tcp_scale (jwt rm p)
                       (r (rcupd (rcupd rm (SL, x) (fst p)) (SR, y) (snd p))))).
      assert (HGsep : forall p, tcp_sep (G p)).
      { intros p; unfold G; rewrite tcp_conj_scale.
        apply tcp_sep_scale,
          (Hsep (rcupd (rcupd rm (SL, x) (fst p)) (SR, y) (snd p))). }
      assert (Hdec : forall p : ctype x * ctype y,
                { J : Type & { fg : (J -> tcp qmem) * (J -> tcp qmem) |
                    tcp_summable (fun j => tcp_tensor (fst fg j) (snd fg j))
                    /\ G p
                       = tcp_sum (fun j => tcp_tensor (fst fg j) (snd fg j)) } }).
      { intros p.
        destruct (constructive_indefinite_description _ (HGsep p)) as [J HJ].
        destruct (constructive_indefinite_description _ HJ) as [f' Hf'].
        destruct (constructive_indefinite_description _ Hf') as [g Hg].
        exists J, (f', g); exact Hg. }
      exists (sigT (fun p : ctype x * ctype y => projT1 (Hdec p))),
             (fun q => fst (proj1_sig (projT2 (Hdec (projT1 q)))) (projT2 q)),
             (fun q => snd (proj1_sig (projT2 (Hdec (projT1 q)))) (projT2 q)).
      set (F := fun (p : ctype x * ctype y) (j : projT1 (Hdec p)) =>
                  tcp_tensor (fst (proj1_sig (projT2 (Hdec p))) j)
                             (snd (proj1_sig (projT2 (Hdec p))) j)).
      assert (HFa : forall p, tcp_summable (F p))
        by (intros p; apply (proj1 (proj2_sig (projT2 (Hdec p))))).
      assert (HFs : forall p, G p = tcp_sum (F p))
        by (intros p; apply (proj2 (proj2_sig (projT2 (Hdec p))))).
      assert (HGs : tcp_summable (fun p => tcp_sum (F p))).
      { assert (HGeq : (fun p => tcp_sum (F p)) = G)
          by (apply funext; intros p; symmetry; apply HFs).
        rewrite HGeq; unfold G.
        apply (tcp_summable_conj Urqpair _ (proj1 Urqpair_unitary)
                 (sampleLR_inner_wf r rm Hwf)). }
      destruct (tcp_sum_sigma _ _ _ F HFa HGs) as [Hsig Heqsig].
      split.
      - exact Hsig.
      - transitivity (tcp_sum (fun p => tcp_sum (F p))).
        + f_equal; apply funext; intros p; apply HFs.
        + exact Heqsig.
    Qed.

    (* --------------------------------------------------------------- *)
    (** *** The precondition

        [A := Cla[marginal_1(f) = idx_1 e_1] cap Cla[marginal_2(f) = idx_2 e_2]
              cap Inter_{(z1,z2)} B{z1/x_1, z2/y_2}], the intersection again
        written as an intersection over *all* of [ctype x * ctype y] with an
        [htop] conjunct off the support -- the same device [Sample1_pre]
        uses. *)

    Definition JointSample_pre (B : pred) : pred :=
      pmeet
        (pmeet
           (Cla (gmap2
                   (fun (mu : distr (ctype x * ctype y)) (mu1 : distr (ctype x)) =>
                      if excluded_middle_informative (dmarginal1 mu = mu1)
                      then true else false)
                   f (idx SL e1)))
           (Cla (gmap2
                   (fun (mu : distr (ctype x * ctype y)) (mu2 : distr (ctype y)) =>
                      if excluded_middle_informative (dmarginal2 mu = mu2)
                      then true else false)
                   f (idx SR e2))))
        (pInf (fun z : ctype x * ctype y =>
                 gmap2 (fun (mu : distr (ctype x * ctype y)) (b : hspace rqmem) =>
                          if excluded_middle_informative (0 < mu z)%R
                          then b else htop)
                       f (rsubst_val (rsubst_val B (SL, x) (fst z))
                                     (SR, y) (snd z)))).

    Lemma sampleLR_psat (r : rcqs) (B : pred) :
      rcqs_wf r -> psat r (JointSample_pre B) -> psat (sampleLR r) B.
    Proof.
      intros Hwf Hsat rm; unfold sampleLR.
      rewrite (tcp_supp_sum _ _ _ (sampleLR_inner_wf r rm Hwf)).
      apply hSup_lub; intros p.
      destruct (Rle_lt_or_eq_dec 0 (jwt rm p) (jwt_nonneg rm p))
        as [Hpos | Hzero].
      - rewrite (tcp_supp_scale _ _ _ Hpos).
        eapply hle_trans;
          [ apply (Hsat (rcupd (rcupd rm (SL, x) (fst p)) (SR, y) (snd p))) |].
        eapply hle_trans; [ apply hmeet_ler |].
        eapply hle_trans;
          [ apply (hInf_lb
                     (fun z : ctype x * ctype y =>
                        ev (gmap2
                              (fun (mu : distr (ctype x * ctype y))
                                   (b : hspace rqmem) =>
                                 if excluded_middle_informative (0 < mu z)%R
                                 then b else htop)
                              f (rsubst_val (rsubst_val B (SL, x) (fst z))
                                            (SR, y) (snd z)))
                           (rcupd (rcupd rm (SL, x) (fst p)) (SR, y) (snd p)))
                     (csel SL rm x, csel SR rm y)) |].
        cbn [ev gmap2].
        destruct (excluded_middle_informative
                    (0 < ev f (rcupd (rcupd rm (SL, x) (fst p)) (SR, y) (snd p))
                           (csel SL rm x, csel SR rm y))%R)
          as [_ | Hno].
        + rewrite ev_rsubst_val, ev_rsubst_val, rcupd2_id; apply hle_refl.
        + exfalso; apply Hno; exact Hpos.
      - rewrite <- Hzero, tcp_scale_0.
        rewrite (proj2 (tcp_supp_eq0 _ _) eq_refl); apply hbot_le.
    Qed.


    (* --------------------------------------------------------------- *)
    (** *** The two projections

        Unlike [Sample1] -- where the un-sampled side is free, and only the
        sampled side needs a marginal identity -- here *both* sides need one:
        [x] is sampled on the left and [y] on the right, so marginalizing
        either one out of [f] needs the precondition's marginal equation. The
        proof of each projection has two layers: for each *kept* value
        ([a] for the left projection, [b] for the right), the *other*
        variable and the other side's classical memory collapse together via
        [sbeta] and the marginal identity (mirroring [sampleL_projR]'s
        totality collapse); then the kept values are brought to the front via
        [tcp_sum_pair]/[tcp_sum_swap] (mirroring [sampleL_projL]). *)

    Lemma sampleLR_projL_inner (r : rcqs) :
      rcqs_wf r ->
      (forall rm, r rm <> tcp_zero -> dmarginal1 (ev f rm) = ev e1 (csel SL rm)) ->
      forall (m1 : cmem) (a : ctype x),
        tcp_summable (fun p : cmem * ctype y =>
                        tcp_scale (jwt (m1, fst p) (a, snd p))
                          (rtcpL (r (cupd m1 x a, cupd (fst p) y (snd p)))))
        /\ tcp_sum (fun p : cmem * ctype y =>
                   tcp_scale (jwt (m1, fst p) (a, snd p))
                             (rtcpL (r (cupd m1 x a, cupd (fst p) y (snd p)))))
        = tcp_scale (ev e1 (cupd m1 x a) (m1 x)) (rcqs_projL r (cupd m1 x a)).
    Proof.
      intros Hwf Htot1 m1 a.
      set (Hsrc := fun (m2' : cmem) (z : ctype y) =>
                     tcp_scale (ev f (cupd m1 x a, m2') (m1 x, z))
                               (rtcpL (r (cupd m1 x a, m2')))).
      assert (HGH : (fun p : cmem * ctype y =>
                       tcp_scale (jwt (m1, fst p) (a, snd p))
                                 (rtcpL (r (cupd m1 x a, cupd (fst p) y (snd p)))))
                    = (fun p : cmem * ctype y =>
                         Hsrc (fst (sbeta y p)) (snd (sbeta y p))))
        by (apply funext; intros p; reflexivity).
      assert (Hbsum1 : forall m2', summable (fun z : ctype y =>
                        ev f (cupd m1 x a, m2') (m1 x, z))).
      { intros m2'; apply (summable_inj (fun z : ctype y => (m1 x, z))
                   (dfun (ev f (cupd m1 x a, m2'))));
          [ intros u v Huv; exact (f_equal snd Huv) | apply dfun_summable ]. }
      assert (Hbnn1 : forall m2' z, (0 <= ev f (cupd m1 x a, m2') (m1 x, z))%R)
        by (intros m2' z; apply (dfun_nonneg (ev f (cupd m1 x a, m2')) (m1 x, z))).
      assert (HsrcS : forall m2', tcp_summable (fun z => Hsrc m2' z)).
      { intros m2'; apply tcp_summable_trace.
        apply (summable_mono _ (fun z : ctype y =>
                 (tcp_trace (rtcpL (r (cupd m1 x a, m2')))
                  * ev f (cupd m1 x a, m2') (m1 x, z))%R)).
        - exact (summable_scale (tcp_trace (rtcpL (r (cupd m1 x a, m2'))))
                   (fun z : ctype y => ev f (cupd m1 x a, m2') (m1 x, z))
                   (tcp_trace_nonneg _ _) (Hbnn1 m2') (Hbsum1 m2')).
        - intros z; unfold Hsrc; rewrite tcp_trace_scale; apply Req_le; ring. }
      assert (HsrcV : forall m2',
                 tcp_sum (fun z => Hsrc m2' z)
                 = tcp_scale (ev e1 (cupd m1 x a) (m1 x))
                             (rtcpL (r (cupd m1 x a, m2')))).
      { intros m2'; unfold Hsrc.
        rewrite (tcp_sum_scale_const _ _
                   (fun z => ev f (cupd m1 x a, m2') (m1 x, z)) _
                   (Hbnn1 m2') (Hbsum1 m2')).
        destruct (classic (r (cupd m1 x a, m2') = tcp_zero)) as [Hz | Hz].
        - rewrite Hz, rtcpL_zero, !tcp_scale_zero; reflexivity.
        - assert (Hmarg : dmarginal1 (ev f (cupd m1 x a, m2'))
                          = ev e1 (csel SL (cupd m1 x a, m2')))
            by (apply Htot1; exact Hz).
          assert (Heq : tsum (fun z => ev f (cupd m1 x a, m2') (m1 x, z))
                        = ev e1 (cupd m1 x a) (m1 x)).
          { transitivity (dmarginal1 (ev f (cupd m1 x a, m2')) (m1 x));
              [ reflexivity |].
            exact (f_equal (fun mu : distr (ctype x) => mu (m1 x)) Hmarg). }
          rewrite Heq; reflexivity. }
      assert (HsrcIt : tcp_summable (fun m2' => tcp_sum (fun z => Hsrc m2' z))).
      { assert (Heq : (fun m2' => tcp_sum (fun z => Hsrc m2' z))
                      = (fun m2' => tcp_scale (ev e1 (cupd m1 x a) (m1 x))
                                              (rtcpL (r (cupd m1 x a, m2')))))
          by (apply funext; intros m2'; apply HsrcV).
        rewrite Heq; apply tcp_summable_trace.
        apply (summable_mono _ (fun m2' => tcp_trace (rtcpL (r (cupd m1 x a, m2'))))).
        - apply tcp_summable_trace, (rcqs_slice_wf r (cupd m1 x a) Hwf).
        - intros m2'; rewrite tcp_trace_scale.
          rewrite <- (Rmult_1_l (tcp_trace (rtcpL (r (cupd m1 x a, m2'))))) at 2.
          apply Rmult_le_compat_r;
            [ apply tcp_trace_nonneg | apply dfun_le1_pt ]. }
      destruct (tcp_sum_pair Hsrc HsrcS HsrcIt) as [HsrcP HsrcEq].
      destruct (tcp_sum_bij _ _ _ (sbeta y) (sbeta y)
                  (fun q : cmem * ctype y => Hsrc (fst q) (snd q))
                  (sbeta_invol y) (sbeta_invol y) HsrcP) as [HJ Hbij].
      split.
      - rewrite HGH; exact HJ.
      - rewrite HGH, Hbij, <- HsrcEq.
        transitivity (tcp_sum (fun m2' => tcp_scale (ev e1 (cupd m1 x a) (m1 x))
                                                     (rtcpL (r (cupd m1 x a, m2'))))).
        { f_equal; apply funext; intros m2'; apply HsrcV. }
        rewrite <- (tcp_scale_sum _ _ _ _ (rcqs_slice_wf r (cupd m1 x a) Hwf)).
        reflexivity.
    Qed.


    Lemma sampleLR_projL (r : rcqs) :
      rcqs_wf r ->
      (forall rm, r rm <> tcp_zero -> dmarginal1 (ev f rm) = ev e1 (csel SL rm)) ->
      rcqs_projL (sampleLR r) = sem_sample x e1 (rcqs_projL r).
    Proof.
      intros Hwf Htot1; apply funext; intros m1.
      set (Fab := fun (m2 : cmem) (a : ctype x) (b : ctype y) =>
                    tcp_scale (jwt (m1, m2) (a, b))
                              (rtcpL (r (cupd m1 x a, cupd m2 y b)))).
      (* [rtcpL (sampleLR r (m1,m2))], unfolded into [Fab] *)
      assert (HA : forall m2,
                 rtcpL (sampleLR r (m1, m2))
                 = tcp_sum (fun p : ctype x * ctype y => Fab m2 (fst p) (snd p))).
      { intros m2; unfold sampleLR.
        rewrite (rtcpL_sum _ (sampleLR_inner_wf r (m1, m2) Hwf)).
        f_equal; apply funext; intros [a b]; unfold Fab; cbn [fst snd].
        apply rtcpL_scale. }
      (* summability of [Fab m2 -] over (a,b), for each fixed m2 *)
      assert (Hpwf : forall m2, tcp_summable
                        (fun p : ctype x * ctype y => Fab m2 (fst p) (snd p))).
      { intros m2.
        assert (Heq : (fun p : ctype x * ctype y => Fab m2 (fst p) (snd p))
                      = (fun p : ctype x * ctype y =>
                           rtcpL (tcp_scale (jwt (m1, m2) p)
                                   (r (rcupd (rcupd (m1, m2) (SL, x) (fst p))
                                              (SR, y) (snd p))))))
          by (apply funext; intros [a b]; unfold Fab; cbn [fst snd];
              symmetry; apply rtcpL_scale).
        rewrite Heq; apply rtcpL_summable, (sampleLR_inner_wf r (m1, m2) Hwf). }
      (* summability of the m2-indexed outer sum *)
      assert (HmIt : tcp_summable
                       (fun m2 => tcp_sum (fun p => Fab m2 (fst p) (snd p)))).
      { assert (Heq : (fun m2 => tcp_sum (fun p => Fab m2 (fst p) (snd p)))
                      = (fun m2 => rtcpL (sampleLR r (m1, m2))))
          by (apply funext; intros m2; symmetry; apply HA).
        rewrite Heq; apply (rcqs_slice_wf (sampleLR r) m1 (sampleLR_wf r Hwf)). }
      (* the pair-flattened, [cmem * (ctype x * ctype y)]-indexed, version *)
      destruct (tcp_sum_pair
                  (fun m2 p => Fab m2 (fst p) (snd p)) Hpwf HmIt) as [HQ HQeq].
      (* regroup: [cmem * (X * Y)] and [X * (cmem * Y)] are in bijection *)
      set (sig1 := fun q : cmem * (ctype x * ctype y) =>
                     (fst (snd q), (fst q, snd (snd q)))
                   : ctype x * (cmem * ctype y)).
      set (sig2 := fun j : ctype x * (cmem * ctype y) =>
                     (fst (snd j), (fst j, snd (snd j)))
                   : cmem * (ctype x * ctype y)).
      assert (Hs12 : forall q, sig2 (sig1 q) = q)
        by (intros [m2 [a b]]; reflexivity).
      assert (Hs21 : forall j, sig1 (sig2 j) = j)
        by (intros [a [m2 b]]; reflexivity).
      destruct (tcp_sum_bij _ _ _ sig2 sig1
                  (fun q : cmem * (ctype x * ctype y) =>
                     Fab (fst q) (fst (snd q)) (snd (snd q)))
                  Hs21 Hs12 HQ) as [HJ HJeq].
      (* the [X * (cmem * Y)]-indexed sum, uncurried into a outer, (m2,b) inner *)
      assert (Hqwf : forall a : ctype x,
                 tcp_summable (fun q : cmem * ctype y => Fab (fst q) a (snd q))).
      { intros a.
        assert (Heq : (fun q : cmem * ctype y => Fab (fst q) a (snd q))
                      = (fun p : cmem * ctype y =>
                           tcp_scale (jwt (m1, fst p) (a, snd p))
                             (rtcpL (r (cupd m1 x a, cupd (fst p) y (snd p))))))
          by (apply funext; intros [m2 b]; reflexivity).
        rewrite Heq; apply (proj1 (sampleLR_projL_inner r Hwf Htot1 m1 a)). }
      assert (HqIt : tcp_summable
                       (fun a : ctype x => tcp_sum
                          (fun q : cmem * ctype y => Fab (fst q) a (snd q)))).
      { apply tcp_summable_trace.
        apply (summable_mono _ (fun a : ctype x =>
                 tcp_trace (rcqs_projL r (cupd m1 x a)))).
        - apply (summable_inj (fun a : ctype x => cupd m1 x a)
                              (fun m => tcp_trace (rcqs_projL r m))).
          + intros u v Huv.
            rewrite <- (cupd_same m1 x u), Huv, cupd_same; reflexivity.
          + apply tcp_summable_trace, rcqs_projL_wf; exact Hwf.
        - intros a.
          transitivity (tcp_trace
                          (tcp_scale (ev e1 (cupd m1 x a) (m1 x))
                             (rcqs_projL r (cupd m1 x a)))).
          + apply Req_le; f_equal;
              apply (proj2 (sampleLR_projL_inner r Hwf Htot1 m1 a)).
          + rewrite tcp_trace_scale.
            rewrite <- (Rmult_1_l (tcp_trace (rcqs_projL r (cupd m1 x a)))) at 2.
            apply Rmult_le_compat_r;
              [ apply tcp_trace_nonneg | apply dfun_le1_pt ]. }
      destruct (tcp_sum_pair
                  (fun a q => Fab (fst q) a (snd q)) Hqwf HqIt) as [_ HKeq].
      (* chain everything together *)
      unfold rcqs_projL at 1, sem_sample.
      transitivity (tcp_sum (fun m2 => tcp_sum (fun p => Fab m2 (fst p) (snd p)))).
      { f_equal; apply funext; apply HA. }
      rewrite HQeq.
      transitivity (tcp_sum (fun j : ctype x * (cmem * ctype y) =>
                      Fab (fst (snd j)) (fst j) (snd (snd j)))).
      { transitivity (tcp_sum (fun j : ctype x * (cmem * ctype y) =>
                        Fab (fst (sig2 j)) (fst (snd (sig2 j))) (snd (snd (sig2 j))))).
        - symmetry; exact HJeq.
        - f_equal; apply funext; intros [a [m2 b]]; reflexivity. }
      rewrite <- HKeq.
      f_equal; apply funext; intros a.
      apply (proj2 (sampleLR_projL_inner r Hwf Htot1 m1 a)).
    Qed.

    Lemma sampleLR_projR_inner (r : rcqs) :
      rcqs_wf r ->
      (forall rm, r rm <> tcp_zero -> dmarginal2 (ev f rm) = ev e2 (csel SR rm)) ->
      forall (m2 : cmem) (b : ctype y),
        tcp_summable (fun p : cmem * ctype x =>
                        tcp_scale (jwt (fst p, m2) (snd p, b))
                          (rtcpR (r (cupd (fst p) x (snd p), cupd m2 y b))))
        /\ tcp_sum (fun p : cmem * ctype x =>
                   tcp_scale (jwt (fst p, m2) (snd p, b))
                             (rtcpR (r (cupd (fst p) x (snd p), cupd m2 y b))))
        = tcp_scale (ev e2 (cupd m2 y b) (m2 y)) (rcqs_projR r (cupd m2 y b)).
    Proof.
      intros Hwf Htot2 m2 b.
      set (Hsrc := fun (m1' : cmem) (z : ctype x) =>
                     tcp_scale (ev f (m1', cupd m2 y b) (z, m2 y))
                               (rtcpR (r (m1', cupd m2 y b)))).
      assert (HGH : (fun p : cmem * ctype x =>
                       tcp_scale (jwt (fst p, m2) (snd p, b))
                                 (rtcpR (r (cupd (fst p) x (snd p), cupd m2 y b))))
                    = (fun p : cmem * ctype x =>
                         Hsrc (fst (sbeta x p)) (snd (sbeta x p))))
        by (apply funext; intros p; reflexivity).
      assert (Hbsum2 : forall m1', summable (fun z : ctype x =>
                        ev f (m1', cupd m2 y b) (z, m2 y))).
      { intros m1'; apply (summable_inj (fun z : ctype x => (z, m2 y))
                   (dfun (ev f (m1', cupd m2 y b))));
          [ intros u v Huv; exact (f_equal fst Huv) | apply dfun_summable ]. }
      assert (Hbnn2 : forall m1' z, (0 <= ev f (m1', cupd m2 y b) (z, m2 y))%R)
        by (intros m1' z; apply (dfun_nonneg (ev f (m1', cupd m2 y b)) (z, m2 y))).
      assert (HsrcS : forall m1', tcp_summable (fun z => Hsrc m1' z)).
      { intros m1'; apply tcp_summable_trace.
        apply (summable_mono _ (fun z : ctype x =>
                 (tcp_trace (rtcpR (r (m1', cupd m2 y b)))
                  * ev f (m1', cupd m2 y b) (z, m2 y))%R)).
        - exact (summable_scale (tcp_trace (rtcpR (r (m1', cupd m2 y b))))
                   (fun z : ctype x => ev f (m1', cupd m2 y b) (z, m2 y))
                   (tcp_trace_nonneg _ _) (Hbnn2 m1') (Hbsum2 m1')).
        - intros z; unfold Hsrc; rewrite tcp_trace_scale; apply Req_le; ring. }
      assert (HsrcV : forall m1',
                 tcp_sum (fun z => Hsrc m1' z)
                 = tcp_scale (ev e2 (cupd m2 y b) (m2 y))
                             (rtcpR (r (m1', cupd m2 y b)))).
      { intros m1'; unfold Hsrc.
        rewrite (tcp_sum_scale_const _ _
                   (fun z => ev f (m1', cupd m2 y b) (z, m2 y)) _
                   (Hbnn2 m1') (Hbsum2 m1')).
        destruct (classic (r (m1', cupd m2 y b) = tcp_zero)) as [Hz | Hz].
        - rewrite Hz, rtcpR_zero, !tcp_scale_zero; reflexivity.
        - assert (Hmarg : dmarginal2 (ev f (m1', cupd m2 y b))
                          = ev e2 (csel SR (m1', cupd m2 y b)))
            by (apply Htot2; exact Hz).
          assert (Heq : tsum (fun z => ev f (m1', cupd m2 y b) (z, m2 y))
                        = ev e2 (cupd m2 y b) (m2 y)).
          { transitivity (dmarginal2 (ev f (m1', cupd m2 y b)) (m2 y));
              [ reflexivity |].
            exact (f_equal (fun mu : distr (ctype y) => mu (m2 y)) Hmarg). }
          rewrite Heq; reflexivity. }
      assert (HsrcIt : tcp_summable (fun m1' => tcp_sum (fun z => Hsrc m1' z))).
      { assert (Heq : (fun m1' => tcp_sum (fun z => Hsrc m1' z))
                      = (fun m1' => tcp_scale (ev e2 (cupd m2 y b) (m2 y))
                                              (rtcpR (r (m1', cupd m2 y b)))))
          by (apply funext; intros m1'; apply HsrcV).
        rewrite Heq; apply tcp_summable_trace.
        apply (summable_mono _ (fun m1' => tcp_trace (rtcpR (r (m1', cupd m2 y b))))).
        - apply tcp_summable_trace, (rcqs_slice_wf_R r (cupd m2 y b) Hwf).
        - intros m1'; rewrite tcp_trace_scale.
          rewrite <- (Rmult_1_l (tcp_trace (rtcpR (r (m1', cupd m2 y b))))) at 2.
          apply Rmult_le_compat_r;
            [ apply tcp_trace_nonneg | apply dfun_le1_pt ]. }
      destruct (tcp_sum_pair Hsrc HsrcS HsrcIt) as [HsrcP HsrcEq].
      destruct (tcp_sum_bij _ _ _ (sbeta x) (sbeta x)
                  (fun q : cmem * ctype x => Hsrc (fst q) (snd q))
                  (sbeta_invol x) (sbeta_invol x) HsrcP) as [HJ Hbij].
      split.
      - rewrite HGH; exact HJ.
      - rewrite HGH, Hbij, <- HsrcEq.
        transitivity (tcp_sum (fun m1' => tcp_scale (ev e2 (cupd m2 y b) (m2 y))
                                                     (rtcpR (r (m1', cupd m2 y b))))).
        { f_equal; apply funext; intros m1'; apply HsrcV. }
        rewrite <- (tcp_scale_sum _ _ _ _ (rcqs_slice_wf_R r (cupd m2 y b) Hwf)).
        reflexivity.
    Qed.

    Lemma sampleLR_projR (r : rcqs) :
      rcqs_wf r ->
      (forall rm, r rm <> tcp_zero -> dmarginal2 (ev f rm) = ev e2 (csel SR rm)) ->
      rcqs_projR (sampleLR r) = sem_sample y e2 (rcqs_projR r).
    Proof.
      intros Hwf Htot2; apply funext; intros m2.
      set (Fab := fun (m1 : cmem) (a : ctype x) (b : ctype y) =>
                    tcp_scale (jwt (m1, m2) (a, b))
                              (rtcpR (r (cupd m1 x a, cupd m2 y b)))).
      assert (HA : forall m1,
                 rtcpR (sampleLR r (m1, m2))
                 = tcp_sum (fun p : ctype x * ctype y => Fab m1 (fst p) (snd p))).
      { intros m1; unfold sampleLR.
        rewrite (rtcpR_sum _ (sampleLR_inner_wf r (m1, m2) Hwf)).
        f_equal; apply funext; intros [a b]; unfold Fab; cbn [fst snd].
        apply rtcpR_scale. }
      assert (Hpwf : forall m1, tcp_summable
                        (fun p : ctype x * ctype y => Fab m1 (fst p) (snd p))).
      { intros m1.
        assert (Heq : (fun p : ctype x * ctype y => Fab m1 (fst p) (snd p))
                      = (fun p : ctype x * ctype y =>
                           rtcpR (tcp_scale (jwt (m1, m2) p)
                                   (r (rcupd (rcupd (m1, m2) (SL, x) (fst p))
                                              (SR, y) (snd p))))))
          by (apply funext; intros [a b]; unfold Fab; cbn [fst snd];
              symmetry; apply rtcpR_scale).
        rewrite Heq; apply rtcpR_summable, (sampleLR_inner_wf r (m1, m2) Hwf). }
      assert (HmIt : tcp_summable
                       (fun m1 => tcp_sum (fun p => Fab m1 (fst p) (snd p)))).
      { assert (Heq : (fun m1 => tcp_sum (fun p => Fab m1 (fst p) (snd p)))
                      = (fun m1 => rtcpR (sampleLR r (m1, m2))))
          by (apply funext; intros m1; symmetry; apply HA).
        rewrite Heq; apply (rcqs_slice_wf_R (sampleLR r) m2 (sampleLR_wf r Hwf)). }
      destruct (tcp_sum_pair
                  (fun m1 p => Fab m1 (fst p) (snd p)) Hpwf HmIt) as [HQ HQeq].
      set (sig1 := fun q : cmem * (ctype x * ctype y) =>
                     (snd (snd q), (fst q, fst (snd q)))
                   : ctype y * (cmem * ctype x)).
      set (sig2 := fun j : ctype y * (cmem * ctype x) =>
                     (fst (snd j), (snd (snd j), fst j))
                   : cmem * (ctype x * ctype y)).
      assert (Hs12 : forall q, sig2 (sig1 q) = q)
        by (intros [m1 [a b]]; reflexivity).
      assert (Hs21 : forall j, sig1 (sig2 j) = j)
        by (intros [b [m1 a]]; reflexivity).
      destruct (tcp_sum_bij _ _ _ sig2 sig1
                  (fun q : cmem * (ctype x * ctype y) =>
                     Fab (fst q) (fst (snd q)) (snd (snd q)))
                  Hs21 Hs12 HQ) as [HJ HJeq].
      assert (Hqwf : forall b : ctype y,
                 tcp_summable (fun q : cmem * ctype x => Fab (fst q) (snd q) b)).
      { intros b.
        assert (Heq : (fun q : cmem * ctype x => Fab (fst q) (snd q) b)
                      = (fun p : cmem * ctype x =>
                           tcp_scale (jwt (fst p, m2) (snd p, b))
                             (rtcpR (r (cupd (fst p) x (snd p), cupd m2 y b)))))
          by (apply funext; intros [m1 a]; reflexivity).
        rewrite Heq; apply (proj1 (sampleLR_projR_inner r Hwf Htot2 m2 b)). }
      assert (HqIt : tcp_summable
                       (fun b : ctype y => tcp_sum
                          (fun q : cmem * ctype x => Fab (fst q) (snd q) b))).
      { apply tcp_summable_trace.
        apply (summable_mono _ (fun b : ctype y =>
                 tcp_trace (rcqs_projR r (cupd m2 y b)))).
        - apply (summable_inj (fun b : ctype y => cupd m2 y b)
                              (fun m => tcp_trace (rcqs_projR r m))).
          + intros u v Huv.
            rewrite <- (cupd_same m2 y u), Huv, cupd_same; reflexivity.
          + apply tcp_summable_trace, rcqs_projR_wf; exact Hwf.
        - intros b.
          transitivity (tcp_trace
                          (tcp_scale (ev e2 (cupd m2 y b) (m2 y))
                             (rcqs_projR r (cupd m2 y b)))).
          + apply Req_le; f_equal;
              apply (proj2 (sampleLR_projR_inner r Hwf Htot2 m2 b)).
          + rewrite tcp_trace_scale.
            rewrite <- (Rmult_1_l (tcp_trace (rcqs_projR r (cupd m2 y b)))) at 2.
            apply Rmult_le_compat_r;
              [ apply tcp_trace_nonneg | apply dfun_le1_pt ]. }
      destruct (tcp_sum_pair
                  (fun b q => Fab (fst q) (snd q) b) Hqwf HqIt) as [_ HKeq].
      unfold rcqs_projR at 1, sem_sample.
      transitivity (tcp_sum (fun m1 => tcp_sum (fun p => Fab m1 (fst p) (snd p)))).
      { f_equal; apply funext; apply HA. }
      rewrite HQeq.
      transitivity (tcp_sum (fun j : ctype y * (cmem * ctype x) =>
                      Fab (fst (snd j)) (snd (snd j)) (fst j))).
      { transitivity (tcp_sum (fun j : ctype y * (cmem * ctype x) =>
                        Fab (fst (sig2 j)) (fst (snd (sig2 j))) (snd (snd (sig2 j))))).
        - symmetry; exact HJeq.
        - f_equal; apply funext; intros [b [m1 a]]; reflexivity. }
      rewrite <- HKeq.
      f_equal; apply funext; intros b.
      apply (proj2 (sampleLR_projR_inner r Hwf Htot2 m2 b)).
    Qed.


    (* --------------------------------------------------------------- *)
    (** *** The rule *)

    Theorem rule_JointSample (B : pred) :
      qrhl (JointSample_pre B) (Sample x e1) (Sample y e2) B.
    Proof.
      intros r Hwf Hsep Hsat.
      assert (Hple1 : ple (JointSample_pre B)
                (Cla (gmap2
                        (fun (mu : distr (ctype x * ctype y)) (mu1 : distr (ctype x)) =>
                           if excluded_middle_informative (dmarginal1 mu = mu1)
                           then true else false)
                        f (idx SL e1)))).
      { intros rm'; eapply hle_trans; [ apply hmeet_lel | apply hmeet_lel ]. }
      assert (Hple2 : ple (JointSample_pre B)
                (Cla (gmap2
                        (fun (mu : distr (ctype x * ctype y)) (mu2 : distr (ctype y)) =>
                           if excluded_middle_informative (dmarginal2 mu = mu2)
                           then true else false)
                        f (idx SR e2)))).
      { intros rm'; eapply hle_trans; [ apply hmeet_lel | apply hmeet_ler ]. }
      assert (Htot1 : forall rm, r rm <> tcp_zero ->
                                 dmarginal1 (ev f rm) = ev e1 (csel SL rm)).
      { intros rm Hnz.
        pose proof (proj1 (psat_Cla r _)
                      (psat_mono r (JointSample_pre B) _ Hple1 Hsat) rm Hnz) as Hc.
        cbn [ev gmap2] in Hc; unfold idx in Hc; cbn [ev] in Hc.
        destruct (excluded_middle_informative (dmarginal1 (ev f rm) = ev e1 (csel SL rm)));
          [ assumption | discriminate Hc ]. }
      assert (Htot2 : forall rm, r rm <> tcp_zero ->
                                 dmarginal2 (ev f rm) = ev e2 (csel SR rm)).
      { intros rm Hnz.
        pose proof (proj1 (psat_Cla r _)
                      (psat_mono r (JointSample_pre B) _ Hple2 Hsat) rm Hnz) as Hc.
        cbn [ev gmap2] in Hc; unfold idx in Hc; cbn [ev] in Hc.
        destruct (excluded_middle_informative (dmarginal2 (ev f rm) = ev e2 (csel SR rm)));
          [ assumption | discriminate Hc ]. }
      exists (sampleLR r); repeat split.
      - apply sampleLR_wf; exact Hwf.
      - apply sampleLR_sep; assumption.
      - apply sampleLR_psat; assumption.
      - cbn [denote]; apply sampleLR_projL; assumption.
      - cbn [denote]; apply sampleLR_projR; assumption.
    Qed.

  End JointSample.

  (* ================================================================= *)
  (** ** JointIf  [Figure 2, Lemma 59, p. 64]

<<
         A subseteq Cla[idx_1 e_1 = idx_2 e_2]
         {Cla[idx_1 e_1 /\ idx_2 e_2] cap A} c1 ~ c2 {B}
         {Cla[~idx_1 e_1 /\ ~idx_2 e_2] cap A} d1 ~ d2 {B}
        --------------------------------------------------------
         {A} if e1 then c1 else d1 ~ if e2 then c2 else d2 {B}
>>

      The two programs are "in sync": the precondition forces the two guards to
      agree wherever the state is nonzero, so a single split -- by the left
      guard -- serves both sides. That is what
      [rcqs_projR_rrestr_swap] expresses, and it is the only thing this rule
      needs beyond [If1]. *)

  Definition guards_agree (e1 e2 : expr bool) : pred :=
    Cla (gmap2 Bool.eqb (idx SL e1) (idx SR e2)).

  Theorem rule_JointIf (e1 e2 : expr bool) (c1 c2 d1 d2 : prog) (A B : pred) :
    ple A (guards_agree e1 e2) ->
    qrhl (pmeet (Cla (gmap2 andb (idx SL e1) (idx SR e2))) A) c1 c2 B ->
    qrhl (pmeet (Cla (gmap2 andb (gmap negb (idx SL e1))
                                 (gmap negb (idx SR e2)))) A) d1 d2 B ->
    qrhl A (Cond e1 c1 d1) (Cond e2 c2 d2) B.
  Proof.
    intros HA H1 H2 r Hwf Hsep Hsat.
    (* the guards agree on the support *)
    assert (Hag : forall rm, r rm <> tcp_zero ->
                  ev e1 (csel SL rm) = ev e2 (csel SR rm)).
    { intros rm Hnz.
      pose proof (proj1 (psat_Cla r _)
                    (psat_mono r A (guards_agree e1 e2) HA Hsat) rm Hnz) as Hc.
      change (ev (gmap2 Bool.eqb (idx SL e1) (idx SR e2)) rm)
        with (Bool.eqb (ev e1 (csel SL rm)) (ev e2 (csel SR rm))) in Hc.
      destruct (ev e1 (csel SL rm)), (ev e2 (csel SR rm));
        solve [ reflexivity | discriminate Hc ]. }
    set (rt := rrestr (idx SL e1) r).
    set (rf := rrestrn (idx SL e1) r).
    assert (Hwft : rcqs_wf rt) by (apply rrestr_wf; exact Hwf).
    assert (Hwff : rcqs_wf rf) by (apply rrestrn_wf; exact Hwf).
    (* each half satisfies its branch's precondition *)
    assert (Hpt : psat rt (Cla (gmap2 andb (idx SL e1) (idx SR e2)))).
    { apply psat_Cla; intros rm Hnz.
      destruct (rrestr_nz _ _ _ Hnz) as [Hg Hrn].
      change (ev (idx SL e1) rm) with (ev e1 (csel SL rm)) in Hg.
      change (ev (gmap2 andb (idx SL e1) (idx SR e2)) rm)
        with (andb (ev e1 (csel SL rm)) (ev e2 (csel SR rm))).
      rewrite <- (Hag rm Hrn), Hg; reflexivity. }
    assert (Hpf : psat rf (Cla (gmap2 andb (gmap negb (idx SL e1))
                                           (gmap negb (idx SR e2))))).
    { apply psat_Cla; intros rm Hnz.
      destruct (rrestrn_nz _ _ _ Hnz) as [Hg Hrn].
      change (ev (idx SL e1) rm) with (ev e1 (csel SL rm)) in Hg.
      change (ev (gmap2 andb (gmap negb (idx SL e1))
                             (gmap negb (idx SR e2))) rm)
        with (andb (negb (ev e1 (csel SL rm))) (negb (ev e2 (csel SR rm)))).
      rewrite <- (Hag rm Hrn), Hg; reflexivity. }
    destruct (H1 rt Hwft (rrestr_sep _ _ Hsep)
                (proj2 (psat_pmeet rt _ A)
                   (conj Hpt (rrestr_psat _ _ A Hsat))))
      as [r1 [Hwf1 [Hsep1 [Hsat1 [HL1 HR1]]]]].
    destruct (H2 rf Hwff (rrestrn_sep _ _ Hsep)
                (proj2 (psat_pmeet rf _ A)
                   (conj Hpf (rrestrn_psat _ _ A Hsat))))
      as [r2 [Hwf2 [Hsep2 [Hsat2 [HL2 HR2]]]]].
    exists (rcqs_add r1 r2); repeat split.
    - apply rcqs_add_wf; assumption.
    - apply rcqs_add_sep; assumption.
    - intros rm; unfold rcqs_add.
      rewrite (tcp_supp_add _ (r1 rm) (r2 rm)).
      apply hSup_lub; intros [|]; [ apply Hsat1 | apply Hsat2 ].
    - rewrite (rcqs_projL_add r1 r2 Hwf1 Hwf2), HL1, HL2; cbn [denote].
      unfold rt, rf; rewrite rcqs_projL_rrestr, rcqs_projL_rrestrn; reflexivity.
    - rewrite (rcqs_projR_add r1 r2 Hwf1 Hwf2), HR1, HR2; cbn [denote].
      unfold rt, rf.
      rewrite (rcqs_projR_rrestr_swap e1 e2 r Hag),
              (rcqs_projR_rrestrn_swap e1 e2 r Hag); reflexivity.
  Qed.

  (* ================================================================= *)
  (** ** JointWhile  [Figure 2, Lemma 61, p. 68]

<<
         A subseteq Cla[idx_1 e_1 = idx_2 e_2]
         {Cla[idx_1 e_1 /\ idx_2 e_2] cap A} c ~ d {A}
        ------------------------------------------------------------
         {A} while e1 do c ~ while e2 do d
             {Cla[~idx_1 e_1 /\ ~idx_2 e_2] cap A}
>>

      Unlike [While1], this rule asks for no termination condition: the two
      loops run in lockstep, so whatever probability mass fails to leave the
      loop fails to leave it on both sides, and the two marginals stay equal
      to each other without either having to be total.

      [A] is the loop invariant. Starting from the given state, one turn of
      the loop is: restrict to where the guard holds, hand that to the
      hypothesis, and take the witness -- which again satisfies [A], so the
      turn can be repeated. What leaves the loop at each turn is the part
      where the guard fails, and the witness for the whole judgment is the sum
      of those exits over all turns.

      The trace bookkeeping is exactly the telescoping estimate that
      [sem_while_wf_trace] uses, one level up: the exits at all turns together
      weigh no more than the state we started with, because the body does not
      increase the trace and a witness has the total trace of its own left
      projection. *)

  Definition good (A : pred) (s : rcqs) : Prop :=
    rcqs_wf s /\ rcqs_sep s /\ psat s A.

  Theorem rule_JointWhile (e1 e2 : expr bool) (c d : prog) (A : pred) :
    wt c -> wt d ->
    ple A (guards_agree e1 e2) ->
    qrhl (pmeet (Cla (gmap2 andb (idx SL e1) (idx SR e2))) A) c d A ->
    qrhl A (While e1 c) (While e2 d)
         (pmeet (Cla (gmap2 andb (gmap negb (idx SL e1))
                                 (gmap negb (idx SR e2)))) A).
  Proof.
    intros Hwtc Hwtd HA Hbody r Hwf0 Hsep0 Hsat0.
    (* the guards agree wherever a state satisfying [A] is nonzero *)
    assert (Hag : forall s, psat s A -> forall rm, s rm <> tcp_zero ->
                            ev e1 (csel SL rm) = ev e2 (csel SR rm)).
    { intros s Hs rm Hnz.
      pose proof (proj1 (psat_Cla s _)
                    (psat_mono s A (guards_agree e1 e2) HA Hs) rm Hnz) as Hc.
      change (ev (gmap2 Bool.eqb (idx SL e1) (idx SR e2)) rm)
        with (Bool.eqb (ev e1 (csel SL rm)) (ev e2 (csel SR rm))) in Hc.
      destruct (ev e1 (csel SL rm)), (ev e2 (csel SR rm));
        solve [ reflexivity | discriminate Hc ]. }
    (* ------------------------------------------------------------- *)
    (* one turn of the loop *)
    assert (Hnext : forall s : rcqs, good A s ->
              { s' : rcqs | good A s'
                /\ rcqs_projL s' = denote c (restr e1 (rcqs_projL s))
                /\ rcqs_projR s' = denote d (restr e2 (rcqs_projR s)) }).
    { intros s [Hwfs [Hseps Hsats]].
      apply constructive_indefinite_description.
      assert (Hpt : psat (rrestr (idx SL e1) s)
                         (Cla (gmap2 andb (idx SL e1) (idx SR e2)))).
      { apply psat_Cla; intros rm Hnz.
        destruct (rrestr_nz _ _ _ Hnz) as [Hg Hrn].
        change (ev (idx SL e1) rm) with (ev e1 (csel SL rm)) in Hg.
        change (ev (gmap2 andb (idx SL e1) (idx SR e2)) rm)
          with (andb (ev e1 (csel SL rm)) (ev e2 (csel SR rm))).
        rewrite <- (Hag s Hsats rm Hrn), Hg; reflexivity. }
      destruct (Hbody (rrestr (idx SL e1) s) (rrestr_wf _ _ Hwfs)
                  (rrestr_sep _ _ Hseps)
                  (proj2 (psat_pmeet _ _ A)
                     (conj Hpt (rrestr_psat _ _ A Hsats))))
        as [s' [Hwf' [Hsep' [Hsat' [HL HR]]]]].
      exists s'; split; [ split; [ exact Hwf' | split; assumption ] |].
      split.
      - rewrite HL, rcqs_projL_rrestr; reflexivity.
      - rewrite HR, (rcqs_projR_rrestr_swap e1 e2 s (Hag s Hsats)); reflexivity. }
    (* ------------------------------------------------------------- *)
    (* the sequence of states at the top of each turn *)
    pose (nxt := fun p : sig (good A) =>
                   exist (good A)
                     (proj1_sig (Hnext (proj1_sig p) (proj2_sig p)))
                     (proj1 (proj2_sig
                               (Hnext (proj1_sig p) (proj2_sig p))))).
    pose (P := fun i : nat =>
                 Nat.iter i nxt
                   (exist (good A) r (conj Hwf0 (conj Hsep0 Hsat0)))).
    pose (R := fun i : nat => proj1_sig (P i)).
    assert (HgoodR : forall i, good A (R i)) by (intros i; apply (proj2_sig (P i))).
    assert (HwfR : forall i, rcqs_wf (R i)) by (intros i; apply (HgoodR i)).
    assert (HsatR : forall i, psat (R i) A)
      by (intros i; apply (proj2 (proj2 (HgoodR i)))).
    assert (HLstep : forall i,
               rcqs_projL (R (S i)) = denote c (restr e1 (rcqs_projL (R i))))
      by (intros i;
          exact (proj1 (proj2 (proj2_sig (Hnext (R i) (proj2_sig (P i))))))).
    assert (HRstep : forall i,
               rcqs_projR (R (S i)) = denote d (restr e2 (rcqs_projR (R i))))
      by (intros i;
          exact (proj2 (proj2 (proj2_sig (Hnext (R i) (proj2_sig (P i))))))).
    assert (HLiter : forall i,
               rcqs_projL (R i) = witer e1 (denote c) (rcqs_projL r) i).
    { intros i; induction i as [| n IH]; [ reflexivity |].
      rewrite HLstep, IH; reflexivity. }
    assert (HRiter : forall i,
               rcqs_projR (R i) = witer e2 (denote d) (rcqs_projR r) i).
    { intros i; induction i as [| n IH]; [ reflexivity |].
      rewrite HRstep, IH; reflexivity. }
    (* ------------------------------------------------------------- *)
    (* the exits, and the telescoping bound on their total weight *)
    pose (X := fun i : nat => rrestrn (idx SL e1) (R i)).
    assert (Hstep : forall i,
               (rcqs_trace (X i) + rcqs_trace (R (S i))
                <= rcqs_trace (R i))%R).
    { intros i.
      pose proof (rcqs_trace_rrestr_split (idx SL e1) (R i) (HwfR i)) as Hsp.
      assert (Hb : (rcqs_trace (R (S i))
                    <= rcqs_trace (rrestr (idx SL e1) (R i)))%R).
      { rewrite <- (rcqs_trace_projL (R (S i)) (HwfR (S i))).
        rewrite <- (rcqs_trace_projL _ (rrestr_wf (idx SL e1) (R i) (HwfR i))).
        rewrite rcqs_projL_rrestr, HLstep.
        apply (denote_trace_le c Hwtc), restr_wf, rcqs_projL_wf, HwfR. }
      unfold X; lra. }
    assert (Htel : forall n,
               (lsum (fun i => rcqs_trace (X i)) (seq 0 n)
                + rcqs_trace (R n) <= rcqs_trace r)%R).
    { intros n; induction n as [| n IH]; [ cbn; unfold R, P; cbn; lra |].
      rewrite seq_S, lsum_app; cbn [lsum].
      pose proof (Hstep n) as Hs.
      replace (0 + n)%nat with n by apply Nat.add_0_l.
      lra. }
    assert (Hfam : rcqs_fam X).
    { unfold rcqs_fam.
      refine (proj1 (tsum_pairs_le_iter
                       (fun (i : nat) (rm : rcmem) => tcp_trace (X i rm)) _ _)).
      - intros i; apply tcp_summable_trace, rrestrn_wf, HwfR.
      - apply (proj1 (nat_summable_of_seq
                        (fun i : nat => rcqs_trace (X i)) (rcqs_trace r)
                        (fun i => tsum_nonneg _ (fun rm => tcp_trace_nonneg _ _))
                        (fun n => ltac:(pose proof (Htel n);
                                        pose proof (tsum_nonneg
                                          (fun rm => tcp_trace (R n rm))
                                          (fun rm => tcp_trace_nonneg _ _));
                                        unfold rcqs_trace in *; lra)))). }
    (* ------------------------------------------------------------- *)
    exists (rcqs_sum X); repeat split.
    - apply rcqs_sum_wf; exact Hfam.
    - apply rcqs_sum_sep; [ exact Hfam | intros i; apply rrestrn_sep, (HgoodR i) ].
    - apply rcqs_sum_psat; [ exact Hfam |].
      intros i; apply psat_pmeet; split.
      + apply psat_Cla; intros rm Hnz.
        destruct (rrestrn_nz _ _ _ Hnz) as [Hg Hrn].
        change (ev (idx SL e1) rm) with (ev e1 (csel SL rm)) in Hg.
        change (ev (gmap2 andb (gmap negb (idx SL e1))
                               (gmap negb (idx SR e2))) rm)
          with (andb (negb (ev e1 (csel SL rm))) (negb (ev e2 (csel SR rm)))).
        rewrite <- (Hag (R i) (HsatR i) rm Hrn), Hg; reflexivity.
      + apply rrestrn_psat, (HsatR i).
    - rewrite (rcqs_projL_sum X Hfam); cbn [denote].
      rewrite (sem_while_sum e1 (denote c) (rcqs_projL r)).
      f_equal; apply funext; intros i; unfold X.
      rewrite rcqs_projL_rrestrn, HLiter; reflexivity.
    - rewrite (rcqs_projR_sum X Hfam); cbn [denote].
      rewrite (sem_while_sum e2 (denote d) (rcqs_projR r)).
      f_equal; apply funext; intros i; unfold X.
      rewrite (rcqs_projR_rrestrn_swap e1 e2 (R i) (Hag (R i) (HsatR i))),
              HRiter; reflexivity.
  Qed.

  (* ================================================================= *)
  (** ** Still to come in Figure 2

      The right-hand projection of [assignL], and with it rule [Assign1]
      itself, needs the reindexing above applied on the *other* side: the
      source memories are hit exactly once, so the projection comes back
      unchanged. [Sample1] and [JointSample] follow the same pattern with the
      weights of a subdistribution. [If1] and [JointIf] split the state by a
      classical condition and recombine, which is [Case]'s machinery.
      [While1] and [JointWhile] are Phase 2. *)

End ClassicalRules.
