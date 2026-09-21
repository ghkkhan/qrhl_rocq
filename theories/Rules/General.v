(** * General rules (Figure 1), part one.

    Section 5.1: "From the definition of qRHL judgments, we can derive a number
    of reasoning rules. Our reasoning rules are sound (each rule follows from
    the definition of qRHL judgments), but we make no claim that they are
    complete."

    Theorem 37 asserts the soundness of Figures 1, 2 and 3. This file starts on
    Figure 1. Each theorem below carries the paper's rule name, the lemma
    number that proves it, and the page.

    The three rules here are exactly the ones that follow from Definition 35
    without any analysis: they rearrange witnesses rather than construct new
    ones. Everything else in Figure 1 needs either the converse of Lemma 36 or
    locality machinery; see the note at the end. *)

From Stdlib Require Import List Lra.
From QRHL.Substrate Require Import Ambient Cnum Sums Interface Theory.
From QRHL.Core Require Import
  Vars Expr Registers Syntax Semantics Predicate QEq Judgment.

Module GeneralRules (S : HILBERT_SUBSTRATE) (V : PROGRAM_VARS).
  Include JudgmentTheory S V.

  (* ================================================================= *)
  (** ** Skip  [Figure 2, Lemma 54, p. 62]

<<
        -----------------------
         {A} skip ~ skip {A}
>>

      The given state is its own witness. *)

  Theorem rule_Skip (A : pred) : qrhl A Skip Skip A.
  Proof.
    intros r Hwf Hsep Hsat.
    exists r; repeat split; assumption.
  Qed.

  (* ================================================================= *)
  (** ** Conseq  [Figure 1, Lemma 46, p. 47]

<<
         A <= A'    B' <= B    {A'} c ~ d {B'}
        ---------------------------------------
                  {A} c ~ d {B}
>>

      "Rule Conseq allows us to weaken the precondition and strengthen the
      postcondition of a qRHL judgment (when doing backwards reasoning)."

      Proved as [qrhl_mono] in [Core/Judgment.v], where several other proofs
      use it as a step; restated here under the paper's name. *)

  Theorem rule_Conseq (A A' B B' : pred) (c d : prog) :
    ple A A' -> ple B' B -> qrhl A' c d B' -> qrhl A c d B.
  Proof. apply qrhl_mono. Qed.

  (* ================================================================= *)
  (** ** Seq  [Figure 1, Lemma 47, p. 47]

<<
         {A} c1 ~ c2 {B}    {B} d1 ~ d2 {C}
        ------------------------------------
             {A} c1; d1 ~ c2; d2 {C}
>>

      "Rule Seq allows us to reason about the sequential composition of
      programs by introducing a predicate that has to hold in the middle of the
      execution of the two programs."

      The witness for the composite is the second rule's witness applied to the
      first rule's witness -- which is exactly why Definition 35 quantifies over
      *all* states satisfying the precondition rather than a particular one. *)

  Theorem rule_Seq (A B C : pred) (c1 c2 d1 d2 : prog) :
    qrhl A c1 c2 B -> qrhl B d1 d2 C -> qrhl A (Seq c1 d1) (Seq c2 d2) C.
  Proof.
    intros H1 H2 r Hwf Hsep Hsat.
    destruct (H1 r Hwf Hsep Hsat) as [r' [Hwf' [Hsep' [Hsat' [HL HR]]]]].
    destruct (H2 r' Hwf' Hsep' Hsat')
      as [r'' [Hwf'' [Hsep'' [Hsat'' [HL' HR']]]]].
    exists r''; repeat split; try assumption.
    - rewrite HL', HL; reflexivity.
    - rewrite HR', HR; reflexivity.
  Qed.

  (** The paper uses these silently when chaining (footnotes 16 and 20);
      [Semantics.v] proves the underlying denotational facts. *)

  Theorem rule_Seq_skip_l (A B : pred) (c d : prog) :
    qrhl A c d B -> qrhl A (Seq Skip c) (Seq Skip d) B.
  Proof.
    intros H; apply (rule_Seq A A B); [ apply rule_Skip | exact H ].
  Qed.

  Theorem rule_Seq_skip_r (A B : pred) (c d : prog) :
    qrhl A c d B -> qrhl A (Seq c Skip) (Seq d Skip) B.
  Proof.
    intros H; apply (rule_Seq A B B); [ exact H | apply rule_Skip ].
  Qed.

  (* ================================================================= *)
  (** ** Case  [Figure 1, Lemma 48, p. 48]

<<
         forall z in Type^exp_e. {Cla[e = z] cap A} c ~ d {B}
        ------------------------------------------------------
                        {A} c ~ d {B}
>>

      "Rule Case allows us to perform a case distinction depending on the
      value of some expression e."

      The state is cut into the pieces on which [e] takes each value. At a
      given memory exactly one piece is nonzero, so the pieces sum back to the
      original; the hypothesis supplies a witness for each piece, and the
      witnesses are summed.

      That last step is why this rule needs [[c]] to be *normal* and not
      merely additive: the split is indexed by an arbitrary result type, not
      by two branches. Normality is [denote_sum] in [Core/Semantics.v], which
      like [denote_add] is proved for loop-free programs -- hence the two
      extra side conditions, which will disappear when the semantics of
      [while] is brought into those inductions. *)

  Definition case_guard {Z : Type} (e : rexpr Z) (z : Z) : rexpr bool :=
    gmap (fun v => if excluded_middle_informative (z = v) then true else false)
         e.

  Definition case_part {Z : Type} (e : rexpr Z) (r : rcqs) (z : Z) : rcqs :=
    rrestr (case_guard e z) r.

  Lemma case_part_val {Z} (e : rexpr Z) (r : rcqs) (z : Z) (rm : rcmem) :
    case_part e r z rm
    = if excluded_middle_informative (z = ev e rm) then r rm else tcp_zero.
  Proof.
    unfold case_part, rrestr, case_guard; cbn [ev gmap].
    destruct (excluded_middle_informative (z = ev e rm)); reflexivity.
  Qed.

  (** At each memory exactly one piece survives, so the pieces sum back. *)
  Lemma case_part_sum {Z} (e : rexpr Z) (r : rcqs) :
    rcqs_sum (case_part e r) = r.
  Proof.
    apply funext; intros rm; unfold rcqs_sum.
    rewrite (tcp_sum_singleton _ (ev e rm)).
    - rewrite case_part_val.
      destruct (excluded_middle_informative (ev e rm = ev e rm));
        [ reflexivity | contradiction ].
    - intros z Hz; rewrite case_part_val.
      destruct (excluded_middle_informative (z = ev e rm));
        [ contradiction | reflexivity ].
  Qed.

  Lemma case_part_trace {Z} (e : rexpr Z) (r : rcqs) (rm : rcmem) :
    (fun z : Z => tcp_trace (case_part e r z rm))
    = (fun z : Z => if excluded_middle_informative (z = ev e rm)
                    then tcp_trace (r rm) else 0%R).
  Proof.
    apply funext; intros z; rewrite case_part_val.
    destruct (excluded_middle_informative (z = ev e rm));
      [ reflexivity | apply tcp_trace_zero ].
  Qed.

  Lemma case_part_fam {Z} (e : rexpr Z) (r : rcqs) :
    rcqs_wf r -> rcqs_fam (case_part e r).
  Proof.
    intros Hr; unfold rcqs_fam.
    assert (Hsw : summable (fun q : rcmem * Z =>
                              tcp_trace (case_part e r (snd q) (fst q)))).
    { refine (proj1 (tsum_pairs_le_iter
                       (fun (rm : rcmem) (z : Z) =>
                          tcp_trace (case_part e r z rm)) _ _)).
      - intros rm; rewrite case_part_trace.
        apply (proj1 (tsum_single_val (ev e rm) (tcp_trace (r rm))
                        (tcp_trace_nonneg _ _))).
      - apply (summable_mono _ (fun rm => tcp_trace (r rm)));
          [ apply tcp_summable_trace; exact Hr |].
        intros rm; rewrite case_part_trace.
        rewrite (proj2 (tsum_single_val (ev e rm) (tcp_trace (r rm))
                          (tcp_trace_nonneg _ _))).
        apply Rle_refl. }
    apply (summable_inj
             (fun p : Z * rcmem => ((snd p, fst p) : rcmem * Z))
             (fun q : rcmem * Z => tcp_trace (case_part e r (snd q) (fst q))));
      [ intros [a b] [x y] H; cbn in H; congruence | exact Hsw ].
  Qed.

  Theorem rule_Case (Z : Type) (e : rexpr Z) (A B : pred) (c d : prog) :
    wt c -> loopfree c -> wt d -> loopfree d ->
    (forall z : Z, qrhl (pmeet (Cla (case_guard e z)) A) c d B) ->
    qrhl A c d B.
  Proof.
    intros Hwtc Hlfc Hwtd Hlfd H r Hwf Hsep Hsat.
    pose (rz := case_part e r).
    assert (Hfamz : rcqs_fam rz) by (apply case_part_fam; exact Hwf).
    assert (Hwfz : forall z, rcqs_wf (rz z)) by (apply rcqs_fam_wf; exact Hfamz).
    (* each piece satisfies the hypothesis's precondition *)
    assert (Hpre : forall z, psat (rz z) (pmeet (Cla (case_guard e z)) A)).
    { intros z; apply psat_pmeet; split;
        [ apply rrestr_psat_Cla | apply rrestr_psat; exact Hsat ]. }
    (* ... so choose a witness for each *)
    assert (Hw : forall z : Z,
               { r' : rcqs | rcqs_wf r' /\ rcqs_sep r' /\ psat r' B
                             /\ rcqs_projL r' = denote c (rcqs_projL (rz z))
                             /\ rcqs_projR r' = denote d (rcqs_projR (rz z)) }).
    { intros z; apply constructive_indefinite_description.
      apply (H z (rz z) (Hwfz z) (rrestr_sep _ _ Hsep) (Hpre z)). }
    pose (r' := fun z : Z => proj1_sig (Hw z)).
    assert (Hwf' : forall z, rcqs_wf (r' z))
      by (intros z; apply (proj1 (proj2_sig (Hw z)))).
    assert (Hsep' : forall z, rcqs_sep (r' z))
      by (intros z; apply (proj1 (proj2 (proj2_sig (Hw z))))).
    assert (Hsat' : forall z, psat (r' z) B)
      by (intros z; apply (proj1 (proj2 (proj2 (proj2_sig (Hw z)))))).
    assert (HL : forall z, rcqs_projL (r' z) = denote c (rcqs_projL (rz z)))
      by (intros z; apply (proj1 (proj2 (proj2 (proj2 (proj2_sig (Hw z))))))).
    assert (HR : forall z, rcqs_projR (r' z) = denote d (rcqs_projR (rz z)))
      by (intros z; apply (proj2 (proj2 (proj2 (proj2 (proj2_sig (Hw z))))))).
    (* the witnesses are jointly summable: a witness has the total trace of
       its own left projection, which [[c]] does not increase *)
    assert (Hbound : forall z, (rcqs_trace (r' z) <= rcqs_trace (rz z))%R).
    { intros z.
      rewrite <- (rcqs_trace_projL (r' z) (Hwf' z)),
              <- (rcqs_trace_projL (rz z) (Hwfz z)), (HL z).
      apply (proj2 (denote_wf_trace c Hwtc Hlfc _
                      (rcqs_projL_wf _ (Hwfz z)))). }
    assert (Hfam' : rcqs_fam r').
    { unfold rcqs_fam.
      refine (proj1 (tsum_pairs_le_iter
                       (fun (z : Z) (rm : rcmem) => tcp_trace (r' z rm)) _ _)).
      - intros z; apply tcp_summable_trace, (Hwf' z).
      - apply (summable_mono _ (fun z => rcqs_trace (rz z)));
          [ apply rcqs_fam_trace; exact Hfamz | apply Hbound ]. }
    exists (rcqs_sum r'); repeat split.
    - apply rcqs_sum_wf; exact Hfam'.
    - apply rcqs_sum_sep; assumption.
    - apply rcqs_sum_psat; assumption.
    - rewrite (rcqs_projL_sum r' Hfam').
      assert (Heq : (fun z => rcqs_projL (r' z))
                    = (fun z => denote c (rcqs_projL (rz z))))
        by (apply funext; exact HL).
      rewrite Heq.
      rewrite <- (denote_sum c Hwtc Hlfc Z _ (rcqs_fam_projL rz Hfamz)).
      rewrite <- (rcqs_projL_sum rz Hfamz).
      unfold rz; rewrite case_part_sum; reflexivity.
    - rewrite (rcqs_projR_sum r' Hfam').
      assert (Heq : (fun z => rcqs_projR (r' z))
                    = (fun z => denote d (rcqs_projR (rz z))))
        by (apply funext; exact HR).
      rewrite Heq.
      rewrite <- (denote_sum d Hwtd Hlfd Z _ (rcqs_fam_projR rz Hfamz)).
      rewrite <- (rcqs_projR_sum rz Hfamz).
      unfold rz; rewrite case_part_sum; reflexivity.
  Qed.

  (* ================================================================= *)
  (** ** The rest of Figure 1

      Every remaining general rule needs something this file does not have
      yet:

      - [Case] (Lemma 48) splits the initial state according to the value of a
        classical expression and reassembles the witnesses, so it needs the
        converse of Lemma 36 (or, equivalently, the same sum bookkeeping).
      - [Sym] (Lemma 44) needs the action of the side swap on states and
        predicates. The pieces are present ([rcmem_swap], [rqmem_swap],
        [rswap]); what is missing is that swapping commutes with the two
        partial traces.
      - [Equal] (Lemma 49) and [Frame] (Lemma 45) need locality: Definition 10
        for programs, which needs an abstract superoperator notion in the
        substrate, and Definition 18 for predicates, which is in
        [Predicate.v] but has no lemmas yet.
      - [QrhlElim] / [QrhlElimEq] (Lemmas 50, 51) connect judgments to
        probabilities and need [Pr] to interact with the partial traces.
      - [Trans] / [TransSimple] (Lemmas 52, 53) are the most technical rules in
        the paper and are Phase 3. *)

End GeneralRules.
