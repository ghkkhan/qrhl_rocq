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
  (** ** Witnesses that discard a register and replace it

      [QInit1]'s witness, unlike every rule in [OneSided], is not a
      conjugation: it discards side 1's copy of the register [P] and tensors
      in a fresh state, mirroring [sem_qinit] itself. [qinit_tcp] is exactly
      that formula lifted from [cqs] to a bare [tcp qmem]: it stays entirely
      within [qmem] (a plain two-level [qsub P * qsub (qneg P)] split, never
      a nested product), so unlike an earlier draft of this section, no
      associator is needed here at all. The witness acts on one factor of
      the *relational* state not by conjugating a global operator on
      [qmem * qmem], but by applying [qinit_tcp] to each piece of the
      separability witness [rsep] already provides and re-tensoring the
      untouched side back in -- the same move [rule_Case] makes for its
      witness, and see HANDOFF.md S7d for the dead end (needing the
      associator's action on a general entangled tensor argument) this
      replaced. *)

  Section OneSidedDiscard.
    Context (P : qset) (psi : rcmem -> l2 (qsub P))
            (Hpsi : forall rm, inner (psi rm) (psi rm) = C1).

    Definition qinit_tcp (rm : rcmem) (f : tcp qmem) : tcp qmem :=
      tcp_conj (Usplit P)
        (tcp_tensor (tcp_proj (psi rm)) (tcp_ptrace2 (tcp_conj (oadj (Usplit P)) f))).

    (** Trace-preserving (not merely non-increasing): conjugation by an
        isometry on both sides, and the fresh state's normalization is
        exactly what makes the middle step contribute a factor of [1]. *)
    Lemma qinit_tcp_trace (rm : rcmem) (f : tcp qmem) :
      tcp_trace (qinit_tcp rm f) = tcp_trace f.
    Proof.
      unfold qinit_tcp.
      rewrite (tcp_trace_conj_isometry _ _ _ _
                 (ounitary_isometry _ (Wsplit_unitary qvar qtype P))).
      rewrite tcp_trace_tensor, tcp_trace_proj, (Hpsi rm).
      replace (Cre C1) with 1%R by reflexivity; rewrite Rmult_1_l.
      rewrite tcp_ptrace2_trace.
      apply (tcp_trace_conj_isometry _ _ _ _
               (oisometry_oadj (Usplit P) (Wsplit_unitary qvar qtype P))).
    Qed.

    Lemma qinit_tcp_scale (rm : rcmem) (a : R) (f : tcp qmem) :
      qinit_tcp rm (tcp_scale a f) = tcp_scale a (qinit_tcp rm f).
    Proof.
      unfold qinit_tcp; rewrite tcp_conj_scale, tcp_ptrace2_scale, <- tcp_scale_tensor_r,
        tcp_conj_scale; reflexivity.
    Qed.

    Lemma qinit_tcp_sum (rm : rcmem) {J} (F : J -> tcp qmem) :
      tcp_summable F ->
      qinit_tcp rm (tcp_sum F) = tcp_sum (fun j => qinit_tcp rm (F j)).
    Proof.
      intros HF.
      set (A := oadj (Usplit P)).
      assert (HA : oisometry A) by (apply oisometry_oadj, Wsplit_unitary).
      assert (HFA : tcp_summable (fun j => tcp_conj A (F j)))
        by (apply (tcp_summable_conj A _ HA HF)).
      assert (HFP : tcp_summable (fun j => tcp_ptrace2 (tcp_conj A (F j)))).
      { apply tcp_summable_trace.
        apply (summable_mono _ (fun j => tcp_trace (tcp_conj A (F j)))).
        - apply tcp_summable_trace; exact HFA.
        - intros j; rewrite tcp_ptrace2_trace; apply Rle_refl. }
      unfold qinit_tcp; fold A.
      transitivity (tcp_conj (Usplit P)
        (tcp_tensor (tcp_proj (psi rm)) (tcp_sum (fun j => tcp_ptrace2 (tcp_conj A (F j)))))).
      { f_equal; f_equal; f_equal.
        transitivity (tcp_ptrace2 (tcp_sum (fun j => tcp_conj A (F j)))).
        - f_equal; apply (tcp_conj_sum _ _ _ _ _ HF).
        - apply (tcp_ptrace2_sum _ _ _ _ HFA). }
      transitivity (tcp_conj (Usplit P)
        (tcp_sum (fun j => tcp_tensor (tcp_proj (psi rm)) (tcp_ptrace2 (tcp_conj A (F j)))))).
      { f_equal; apply (tcp_tensor_sum_r _ _ _ (tcp_proj (psi rm)) _ HFP). }
      apply (tcp_conj_sum _ _ _ (Usplit P) _
               (tcp_summable_tensor_r (tcp_proj (psi rm)) _ HFP)).
    Qed.

  End OneSidedDiscard.

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
  (** ** Measurement on one side: what the substrate supplies

      [tcp_trace_meas_tensor] and [tcp_ptrace2_meas_tensor] are stated in the
      tensor picture, because that is where the measurement bound is a
      statement about operators rather than about registers. These two lemmas
      transport them to the relational memory, through [Urqpair] (unitary, so
      it preserves traces) and [olift_meas] / [olift_meas_total] (which carry
      the bound from the register to the whole single-sided memory). *)

  Lemma rmeas_trace_bound (P : qset) (D : Type) (M : D -> op (qsub P) (qsub P))
        (r : tcp rqmem) :
    is_meas M ->
    summable (fun z => tcp_trace (tcp_conj (roliftL P (M z)) r))
    /\ (tsum (fun z => tcp_trace (tcp_conj (roliftL P (M z)) r))
        <= tcp_trace r)%R.
  Proof.
    intros Hm.
    assert (Hstep : (fun z => tcp_trace (tcp_conj (roliftL P (M z)) r))
                    = (fun z => tcp_trace
                                  (tcp_conj (tensoro (olift P (M z)) oid)
                                            (tcp_conj Urqpair r)))).
    { apply funext; intros z; rewrite <- conj_roliftL; symmetry.
      apply tcp_trace_conj_isometry, (proj1 Urqpair_unitary). }
    destruct (olift_meas P D M Hm) as [Hproj [Hsum Hbd]].
    destruct (tcp_trace_meas_tensor _ _ _ (fun z => olift P (M z))
                (tcp_conj Urqpair r)
                (fun z => proj1 (Hproj z)) (fun z => proj2 (Hproj z))
                Hsum Hbd) as [Hs Hb].
    rewrite Hstep; split; [ exact Hs |].
    eapply Rle_trans; [ exact Hb |].
    apply Req_le, tcp_trace_conj_isometry, (proj1 Urqpair_unitary).
  Qed.

  (** The right-hand projection of a *total* measurement on the left is the
      identity: a total measurement is trace-preserving, so the other side's
      reduced state does not move. This is exactly why rule Measure1 asks for
      totality -- see the paper's discussion on p. 31. *)
  Lemma rtcpR_meas_total (P : qset) (D : Type)
        (M : D -> op (qsub P) (qsub P)) (r : tcp rqmem) :
    is_total_meas M ->
    rtcpR (tcp_sum (fun z => tcp_conj (roliftL P (M z)) r)) = rtcpR r.
  Proof.
    intros Ht.
    assert (Hs : tcp_summable (fun z => tcp_conj (roliftL P (M z)) r)).
    { apply tcp_summable_trace.
      apply (proj1 (rmeas_trace_bound P D M r (total_meas_is_meas M Ht))). }
    unfold rtcpR.
    rewrite (tcp_conj_sum _ _ _ Urqpair _ Hs).
    assert (Heq : (fun z => tcp_conj Urqpair (tcp_conj (roliftL P (M z)) r))
                  = (fun z => tcp_conj (tensoro (olift P (M z)) oid)
                                       (tcp_conj Urqpair r)))
      by (apply funext; intros z; apply conj_roliftL).
    rewrite Heq.
    destruct (olift_meas_total P D M Ht) as [Hproj [Hsum Hbd]].
    unfold tcp_ptraceL.
    apply (tcp_ptrace2_meas_tensor _ _ _ (fun z => olift P (M z))
             (tcp_conj Urqpair r)
             (fun z => proj1 (Hproj z)) (fun z => proj2 (Hproj z)) Hsum Hbd).
  Qed.

  (* ================================================================= *)
  (** ** Measure1  [Figure 3, Lemma 62, p. 70]

<<
         e'_z := idx_1 e(z) >> idx_1 Q
         A := Cla[idx_1 e is a total measurement]
              cap Inter_{z in Type_x1}
                    ((B{z/x_1} cap im e'_z) + (im e'_z)^perp)
        ---------------------------------------------------------------
         {A} x <- measure Q with e ~ skip {B}
>>

      Two things have to hold in the precondition (p. 31):

      - "[e] needs to be a total measurement. Otherwise, the probability that
        the left program terminates might be < 1, and the right program
        terminates with probability = 1". That is [rtcpR_meas_total] above.

      - "For any possible outcome [z], we need that the post-measurement state
        after outcome [z] is in [B{z/x_1}]. This is the case if the initial
        state lies in the complement of the image [im e'_z] (then the
        measurement will not pass), or if it lies in [B cap im e'_z] (then it
        will pass and stay in [B]), or if it is a sum of states satisfying
        those two [conditions]." That is [himg_proj_meet_oim] in
        [Substrate/Theory.v].

      The witness is the given state pushed forward along the measurement on
      side 1, so the shape is [Sample1]'s with a conjugation by the outcome's
      projector in place of the subdistribution's weight; the reindexing
      [rbeta] is reused verbatim. *)

  Section Measure1.
    Context (x : cvar) (P : qset)
            (e : expr (ctype x -> op (qsub P) (qsub P)))
            (Hmeas : forall m, is_meas (ev e m)).

    (** The projector applied at a target memory: at [rm] the recorded outcome
        is [rm]'s own [x_1], and the measurement is the one the *source*
        memory selects. *)
    Definition mop (rm : rcmem) (a : ctype x) : op (qsub P) (qsub P) :=
      ev e (cupd (csel SL rm) x a) (csel SL rm x).

    Definition measureL (r : rcqs) : rcqs :=
      fun rm =>
        tcp_sum (fun a : ctype x =>
                   tcp_conj (roliftL P (mop rm a)) (r (rcupd rm (SL, x) a))).

    Lemma mop_projector (rm : rcmem) (a : ctype x) : oprojector (mop rm a).
    Proof. apply (proj1 (Hmeas (cupd (csel SL rm) x a))). Qed.

    Lemma measure_term_le_r (rm : rcmem) (a : ctype x) (rho : tcp rqmem) :
      (tcp_trace (tcp_conj (roliftL P (mop rm a)) rho) <= tcp_trace rho)%R.
    Proof.
      destruct (roliftL_projector P (mop rm a) (mop_projector rm a)) as [H1 H2].
      apply tcp_trace_conj_proj_le; assumption.
    Qed.

    Lemma meas_conj_summable (m : cmem) (rho : tcp rqmem) :
      tcp_summable (fun z : ctype x => tcp_conj (roliftL P (ev e m z)) rho).
    Proof.
      apply tcp_summable_trace.
      apply (proj1 (rmeas_trace_bound P (ctype x) (ev e m) rho (Hmeas m))).
    Qed.

    Lemma measureL_inner_wf (r : rcqs) (rm : rcmem) :
      rcqs_wf r ->
      tcp_summable (fun a : ctype x =>
                      tcp_conj (roliftL P (mop rm a)) (r (rcupd rm (SL, x) a))).
    Proof.
      intros Hr; apply tcp_summable_trace.
      apply (summable_mono _ (fun a : ctype x =>
                                tcp_trace (r (rcupd rm (SL, x) a)))).
      - apply (summable_inj (fun a : ctype x => rcupd rm (SL, x) a)
                            (fun rm' => tcp_trace (r rm')));
          [ apply (rcupd_inj x rm) | apply tcp_summable_trace; exact Hr ].
      - intros a; apply measure_term_le_r.
    Qed.

    Lemma measureL_trace (r : rcqs) (rm : rcmem) :
      rcqs_wf r ->
      tcp_trace (measureL r rm)
      = tsum (fun a : ctype x =>
                tcp_trace (tcp_conj (roliftL P (mop rm a))
                                    (r (rcupd rm (SL, x) a)))).
    Proof.
      intros Hr; unfold measureL.
      apply (tcp_trace_sum _ _ _ (measureL_inner_wf r rm Hr)).
    Qed.

    (** Under [rbeta] the (target, index) pair becomes (source, the target's
        old [x]), and there the outcomes of one fixed measurement are summed
        over a fixed state -- which is where the measurement bound applies. *)
    Definition msrc (r : rcqs) (rm' : rcmem) (z : ctype x) : R :=
      tcp_trace (tcp_conj (roliftL P (ev e (csel SL rm') z)) (r rm')).

    Lemma measureL_reindex (r : rcqs) :
      (fun p : rcmem * ctype x =>
         tcp_trace (tcp_conj (roliftL P (mop (fst p) (snd p)))
                             (r (rcupd (fst p) (SL, x) (snd p)))))
      = (fun p : rcmem * ctype x =>
           msrc r (fst (rbeta x p)) (snd (rbeta x p))).
    Proof. apply funext; intros p; reflexivity. Qed.

    Lemma msrc_summable (r : rcqs) (rm' : rcmem) : summable (msrc r rm').
    Proof.
      apply (proj1 (rmeas_trace_bound P (ctype x) (ev e (csel SL rm'))
                      (r rm') (Hmeas (csel SL rm')))).
    Qed.

    Lemma msrc_le (r : rcqs) (rm' : rcmem) :
      (tsum (msrc r rm') <= tcp_trace (r rm'))%R.
    Proof.
      apply (proj2 (rmeas_trace_bound P (ctype x) (ev e (csel SL rm'))
                      (r rm') (Hmeas (csel SL rm')))).
    Qed.

    Lemma measureL_wf (r : rcqs) : rcqs_wf r -> rcqs_wf (measureL r).
    Proof.
      intros Hr.
      pose (Ga := fun (rm : rcmem) (a : ctype x) =>
                    tcp_trace (tcp_conj (roliftL P (mop rm a))
                                        (r (rcupd rm (SL, x) a)))).
      assert (HsrcIt : summable (fun rm' => tsum (msrc r rm'))).
      { apply (summable_mono _ (fun rm' => tcp_trace (r rm')));
          [ apply tcp_summable_trace; exact Hr | apply msrc_le ]. }
      destruct (tsum_pairs_le_iter (msrc r) (msrc_summable r) HsrcIt)
        as [HsrcPS _].
      assert (HGS : summable (fun p : rcmem * ctype x => Ga (fst p) (snd p))).
      { unfold Ga; rewrite measureL_reindex.
        apply (summable_inj (rbeta x)
                 (fun q : rcmem * ctype x => msrc r (fst q) (snd q)));
          [ apply (rbeta_inj x) | exact HsrcPS ]. }
      assert (HGpos : nonneg (fun p : rcmem * ctype x => Ga (fst p) (snd p)))
        by (intros p; apply tcp_trace_nonneg).
      destruct (tsum_iter_le_pairs Ga HGpos HGS) as [HGit _].
      apply tcp_summable_trace.
      assert (Heq : (fun rm => tcp_trace (measureL r rm))
                    = (fun rm => tsum (Ga rm)))
        by (apply funext; intros rm; apply measureL_trace; exact Hr).
      rewrite Heq; exact HGit.
    Qed.

    Lemma measureL_sep (r : rcqs) :
      rcqs_wf r -> rcqs_sep r -> rcqs_sep (measureL r).
    Proof.
      intros Hwf Hsep rm; unfold rsep, measureL.
      rewrite (tcp_conj_sum _ _ _ Urqpair _ (measureL_inner_wf r rm Hwf)).
      set (G := fun a : ctype x =>
                  tcp_conj Urqpair
                    (tcp_conj (roliftL P (mop rm a))
                              (r (rcupd rm (SL, x) a)))).
      assert (HGsep : forall a, tcp_sep (G a)).
      { intros a; unfold G; rewrite conj_roliftL.
        apply tcp_sep_conj_tensorL; [| apply (Hsep (rcupd rm (SL, x) a)) ].
        intros s.
        destruct (wolift_projector qvar qtype P (mop rm a) (mop_projector rm a))
          as [H1 H2].
        apply tcp_trace_conj_proj_le; assumption. }
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
                 (measureL_inner_wf r rm Hwf)). }
      destruct (tcp_sum_sigma _ _ _ F HFa HGs) as [Hsig Heqsig].
      split.
      - exact Hsig.
      - transitivity (tcp_sum (fun a => tcp_sum (F a))).
        + f_equal; apply funext; intros a; apply HFs.
        + exact Heqsig.
    Qed.

    (* --------------------------------------------------------------- *)
    (** *** The precondition *)

    Definition Measure1_pre (B : pred) : pred :=
      pmeet
        (Cla (gmap (fun M : ctype x -> op (qsub P) (qsub P) =>
                      if excluded_middle_informative (is_total_meas M)
                      then true else false)
                   (idx SL e)))
        (pInf (fun z : ctype x =>
                 gmap2 (fun (M : ctype x -> op (qsub P) (qsub P))
                            (b : hspace rqmem) =>
                          hjoin (hmeet b (oim (roliftL P (M z))))
                                (hocompl (oim (roliftL P (M z)))))
                       (idx SL e) (rsubst_val B (SL, x) z))).

    Lemma measureL_psat (r : rcqs) (B : pred) :
      rcqs_wf r -> psat r (Measure1_pre B) -> psat (measureL r) B.
    Proof.
      intros Hwf Hsat rm; unfold measureL.
      rewrite (tcp_supp_sum _ _ _ (measureL_inner_wf r rm Hwf)).
      apply hSup_lub; intros a.
      rewrite tcp_supp_conj.
      change (hspan (fun w => exists v,
                         hmem v (tcp_supp (r (rcupd rm (SL, x) a)))
                         /\ w = oapp (roliftL P (mop rm a)) v))
        with (himg (roliftL P (mop rm a))
                   (tcp_supp (r (rcupd rm (SL, x) a)))).
      eapply hle_trans; [ apply himg_mono, (Hsat (rcupd rm (SL, x) a)) |].
      eapply hle_trans; [ apply himg_mono, hmeet_ler |].
      eapply hle_trans;
        [ apply himg_mono,
            (hInf_lb
               (fun z : ctype x =>
                  ev (gmap2 (fun (M : ctype x -> op (qsub P) (qsub P))
                                 (b : hspace rqmem) =>
                               hjoin (hmeet b (oim (roliftL P (M z))))
                                     (hocompl (oim (roliftL P (M z)))))
                            (idx SL e) (rsubst_val B (SL, x) z))
                     (rcupd rm (SL, x) a))
               (csel SL rm x)) |].
      cbn [ev gmap2].
      rewrite ev_rsubst_val, rcupd_rcupd_L, rcupd_id_L.
      apply himg_proj_meet_oim, roliftL_projector, mop_projector.
    Qed.

    (* --------------------------------------------------------------- *)
    (** *** The two projections *)

    Lemma measureL_projL (r : rcqs) :
      rcqs_wf r -> rcqs_projL (measureL r) = sem_measure x P e (rcqs_projL r).
    Proof.
      intros Hwf; apply funext; intros m1.
      pose (F := fun (m2 : cmem) (a : ctype x) =>
                   tcp_conj (olift P (ev e (cupd m1 x a) (m1 x)))
                            (rtcpL (r (cupd m1 x a, m2)))).
      assert (Hslice : forall a : ctype x,
                 tcp_summable (fun m2 : cmem => rtcpL (r (cupd m1 x a, m2))))
        by (intros a; apply (rcqs_slice_wf r (cupd m1 x a) Hwf)).
      assert (Hinj : forall m2 : cmem,
                 forall u v : ctype x, (cupd m1 x u, m2) = (cupd m1 x v, m2) -> u = v).
      { intros m2 u v Huv.
        assert (H : cupd m1 x u = cupd m1 x v) by congruence.
        rewrite <- (cupd_same m1 x u), H, cupd_same; reflexivity. }
      assert (HFm : forall m2, tcp_summable (F m2)).
      { intros m2; unfold F; apply tcp_summable_trace.
        apply (summable_mono _ (fun a : ctype x =>
                                  tcp_trace (r (cupd m1 x a, m2)))).
        - apply (summable_inj (fun a : ctype x => (cupd m1 x a, m2))
                              (fun rm => tcp_trace (r rm)));
            [ apply (Hinj m2) | apply tcp_summable_trace; exact Hwf ].
        - intros a; rewrite <- (rtcpL_trace (r (cupd m1 x a, m2))).
          apply (measure_term_le x P e Hmeas). }
      assert (HFa : forall a, tcp_summable (fun m2 => F m2 a)).
      { intros a; unfold F; apply tcp_summable_trace.
        apply (summable_mono _ (fun m2 : cmem =>
                                  tcp_trace (rtcpL (r (cupd m1 x a, m2))))).
        - apply tcp_summable_trace, Hslice.
        - intros m2; apply (measure_term_le x P e Hmeas). }
      assert (HFit : tcp_summable (fun m2 => tcp_sum (F m2))).
      { apply tcp_summable_trace.
        apply (summable_mono _ (fun m2 => tcp_trace (measureL r (m1, m2)))).
        - apply (summable_inj (fun m2 : cmem => (m1, m2))
                              (fun rm => tcp_trace (measureL r rm)));
            [ intros u v Huv; congruence
            | apply tcp_summable_trace, measureL_wf; exact Hwf ].
        - intros m2; rewrite (tcp_trace_sum _ _ _ (HFm m2)).
          rewrite (measureL_trace r (m1, m2) Hwf).
          apply Req_le; f_equal; apply funext; intros a; unfold F, mop.
          cbn [csel fst snd].
          rewrite <- rtcpL_roliftL, rtcpL_trace; reflexivity. }
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
          rewrite <- (tcp_conj_sum _ _ _ _ _ (Hslice a)).
          apply (measure_term_le x P e Hmeas). }
      unfold rcqs_projL at 1, measureL, sem_measure.
      transitivity (tcp_sum (fun m2 : cmem => tcp_sum (F m2))).
      { f_equal; apply funext; intros m2.
        rewrite (rtcpL_sum _ (measureL_inner_wf r (m1, m2) Hwf)).
        f_equal; apply funext; intros a; unfold F, mop; cbn [csel fst snd].
        apply rtcpL_roliftL. }
      rewrite (tcp_sum_swap F HFm HFit HFa HFat).
      f_equal; apply funext; intros a; unfold F, rcqs_projL.
      rewrite <- (tcp_conj_sum _ _ _ _ _ (Hslice a)); reflexivity.
    Qed.

    Lemma measureL_projR (r : rcqs) :
      rcqs_wf r ->
      (forall rm, r rm <> tcp_zero -> is_total_meas (ev e (csel SL rm))) ->
      rcqs_projR (measureL r) = rcqs_projR r.
    Proof.
      intros Hwf Htot; apply funext; intros m2.
      pose (Ga := fun (m1 : cmem) (a : ctype x) =>
                    rtcpR (tcp_conj (roliftL P (ev e (cupd m1 x a) (m1 x)))
                                    (r (cupd m1 x a, m2)))).
      pose (Hsrc := fun (m : cmem) (z : ctype x) =>
                      rtcpR (tcp_conj (roliftL P (ev e m z)) (r (m, m2)))).
      assert (HGH : (fun p : cmem * ctype x => Ga (fst p) (snd p))
                    = (fun p : cmem * ctype x =>
                         Hsrc (fst (sbeta x p)) (snd (sbeta x p))))
        by (apply funext; intros p; reflexivity).
      assert (HsrcS : forall m, tcp_summable (Hsrc m))
        by (intros m; apply rtcpR_summable, meas_conj_summable).
      assert (HsrcV : forall m, tcp_sum (Hsrc m) = rtcpR (r (m, m2))).
      { intros m; unfold Hsrc.
        destruct (classic (r (m, m2) = tcp_zero)) as [Hz | Hz].
        - rewrite Hz, rtcpR_zero.
          apply tcp_sum_zero; intros z; rewrite tcp_conj_zero; apply rtcpR_zero.
        - rewrite <- (rtcpR_sum _ (meas_conj_summable m (r (m, m2)))).
          apply (rtcpR_meas_total P (ctype x) (ev e m) (r (m, m2))),
                (Htot (m, m2) Hz). }
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
        - intros a; rewrite rtcpR_trace.
          apply (measure_term_le_r (m1, m2) a). }
      assert (HGeq : forall m1, tcp_sum (Ga m1) = rtcpR (measureL r (m1, m2))).
      { intros m1; unfold measureL.
        rewrite (rtcpR_sum _ (measureL_inner_wf r (m1, m2) Hwf)).
        f_equal; apply funext; intros a; unfold Ga, mop; cbn [csel fst snd];
          reflexivity. }
      assert (HGit : tcp_summable (fun m1 => tcp_sum (Ga m1))).
      { assert (Heq : (fun m1 => tcp_sum (Ga m1))
                      = (fun m1 => rtcpR (measureL r (m1, m2))))
          by (apply funext; exact HGeq).
        rewrite Heq.
        apply (rcqs_slice_wf_R (measureL r) m2), measureL_wf; exact Hwf. }
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

    Theorem rule_Measure1 (B : pred) :
      qrhl (Measure1_pre B) (Measure x P e) Skip B.
    Proof.
      intros r Hwf Hsep Hsat.
      assert (Htot : forall rm, r rm <> tcp_zero ->
                                is_total_meas (ev e (csel SL rm))).
      { intros rm Hnz.
        pose proof (proj1 (psat_Cla r _)
                      (psat_mono r (Measure1_pre B) _ (fun rm' => hmeet_lel _ _)
                         Hsat) rm Hnz) as Hc.
        cbn [ev gmap] in Hc; unfold idx in Hc; cbn [ev] in Hc.
        destruct (excluded_middle_informative
                    (is_total_meas (ev e (csel SL rm))));
          [ assumption | discriminate Hc ]. }
      exists (measureL r); repeat split.
      - apply measureL_wf; exact Hwf.
      - apply measureL_sep; assumption.
      - apply measureL_psat; assumption.
      - cbn [denote]; apply measureL_projL; exact Hwf.
      - cbn [denote]; apply measureL_projR; assumption.
    Qed.

  End Measure1.

  (* ================================================================= *)
  (** ** The rest of Figure 3

      - [QInit1] (Lemma 66) needs Definition 20's division to interact with the
        register split, and Lemma 21 to simplify the precondition it produces.
      - [Measure1] (Lemma 62) and the two joint measurement rules need the
        post-measurement states of the individual outcomes to be reassembled,
        i.e. the same sum bookkeeping as the converse of Lemma 36. *)

End QuantumRules.
