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

    (* --------------------------------------------------------------- *)
    (** *** The reindexing

        [(rm, a) |-> (rm with x_1 := a, the old x_1)], an involution. *)

    Definition rbeta (p : rcmem * ctype x) : rcmem * ctype x :=
      (rcupd (fst p) (SL, x) (snd p), csel SL (fst p) x).

    Lemma rbeta_invol (p : rcmem * ctype x) : rbeta (rbeta p) = p.
    Proof.
      destruct p as [rm a]; unfold rbeta; cbn [fst snd].
      rewrite rcupd_rcupd_L, rcupd_id_L, csel_rcupd_L, cupd_same; reflexivity.
    Qed.

    Lemma rbeta_inj (p q : rcmem * ctype x) : rbeta p = rbeta q -> p = q.
    Proof.
      intros H; rewrite <- (rbeta_invol p), <- (rbeta_invol q), H; reflexivity.
    Qed.

    Lemma rcupd_inj (rm : rcmem) (a b : ctype x) :
      rcupd rm (SL, x) a = rcupd rm (SL, x) b -> a = b.
    Proof.
      intros Hab.
      assert (H : csel SL (rcupd rm (SL, x) a) x
                  = csel SL (rcupd rm (SL, x) b) x)
        by (rewrite Hab; reflexivity).
      rewrite !csel_rcupd_L, !cupd_same in H; exact H.
    Qed.

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
          [ apply rcupd_inj | apply tcp_summable_trace; exact Hr ].
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
                         Hsrc (fst (rbeta p)) (snd (rbeta p)))).
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
        apply (summable_inj rbeta
                 (fun q : rcmem * ctype x => Hsrc (fst q) (snd q)));
          [ apply rbeta_inj | exact HsrcPS ]. }
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
  (** ** Still to come in Figure 2

      The right-hand projection of [assignL], and with it rule [Assign1]
      itself, needs the reindexing above applied on the *other* side: the
      source memories are hit exactly once, so the projection comes back
      unchanged. [Sample1] and [JointSample] follow the same pattern with the
      weights of a subdistribution. [If1] and [JointIf] split the state by a
      classical condition and recombine, which is [Case]'s machinery.
      [While1] and [JointWhile] are Phase 2. *)

End ClassicalRules.
