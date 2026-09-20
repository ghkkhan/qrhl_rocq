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

  (** A cq-state is separable when each of its blocks is. The classical part of
      a cq-operator is already block-diagonal across the two sides, so nothing
      more is needed. *)
  Definition rcqs_sep (r : rcqs) : Prop := forall rm, rsep (r rm).

  (* ================================================================= *)
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
