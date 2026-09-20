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
