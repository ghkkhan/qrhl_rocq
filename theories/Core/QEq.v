(** * Quantum equality.

    Section 4.4. The predicate that is specific to qRHL, and the one the paper
    calls out in its abstract as a challenge unique to the quantum setting.

    The idea (section 4.4): [Q1 =quant Q2] should say that the registers [Q1]
    and [Q2] hold the same state. If that is to be a *subspace* -- and
    Definition 13 says predicates are subspaces -- then

      "there seems to be only one possible definition, namely, [Q1 =quant Q2]
       is the space of all quantum states that are invariant under swapping the
       content of [Q1] and [Q2]."

    Definition 27 generalizes: [U1 Q1 =quant U2 Q2] is the subspace fixed by the
    operator that swaps the two registers while applying [U2^* U1] one way and
    [U1^* U2] the other. The generalization is what makes the rules usable --
    rule QApply1 produces preconditions like [(H (x) id) q1 r1 =quant q2 r2].

    Three ingredients, all now in place:

    - the three-way split of the memory into [Q1], [Q2] and the rest, built by
      composing [Wsplit] with the disjoint-union split [Wsplit2] of
      [Registers.v];
    - [Uswap], which exchanges the two register factors;
    - [hfix], the fixed subspace of an operator, which is a preimage and so
      needs no new assumption.

    Note that [U1] and [U2] are arbitrary bounded operators, not isometries.
    The paper is deliberate about this: "it turns out to be convenient to allow
    non-isometries [U1], [U2] in the definition because some simplification
    rules [...] can then be stated without extra premises (e.g., Lemma 31), and
    nothing is lost by the additional generality." Lemma [qeq_shift] below is
    that Lemma 31, and indeed it needs no premise on [A]. *)

From Stdlib Require Import List Bool.
From QRHL.Substrate Require Import Ambient Cnum Sums Interface Theory.
From QRHL.Core Require Import Vars Expr Registers Syntax Semantics Predicate.

Module QEqTheory (S : HILBERT_SUBSTRATE) (V : PROGRAM_VARS).
  Include PredTheory S V.

  Notation rqunion  := (wunion rqvar).
  Notation rqdisj   := (wdisj rqvar).
  Notation rWsplit2 := (Wsplit2 rqvar rqtype).

  (* ================================================================= *)
  (** ** Definition 27 *)

  (** The operator that Definition 27 takes the fixed space of.

      Read from the inside out: split the combined register [Q1 u Q2] into its
      two halves, apply [U2^* U1] to the first and [U1^* U2] to the second,
      exchange the two factors, and put the register back together --- all of
      it extended by the identity on the variables outside [Q1 u Q2], which is
      what [rolift] does.

      The paper writes this as a single tensor expression
      [U_vars,Q2 U2^* U1 U_vars,Q1^*  (x)  U_vars,Q1 U1^* U2 U_vars,Q2^*  (x)  id];
      the [U_vars] there are exactly the register isomorphisms that [rWsplit2]
      and [rolift] supply here. *)
  Definition qeqOp {Z : Type} (Q1 Q2 : rqset) (Hd : rqdisj Q1 Q2)
             (U1 : op (rqsub Q1) Z) (U2 : op (rqsub Q2) Z) : op rqmem rqmem :=
    rolift (rqunion Q1 Q2)
      (ocomp (rWsplit2 Q1 Q2 Hd)
        (ocomp Uswap
          (ocomp (tensoro (ocomp (oadj U2) U1) (ocomp (oadj U1) U2))
                 (oadj (rWsplit2 Q1 Q2 Hd))))).

  (** Definition 27: "[(U1 Q1 =quant U2 Q2) subseteq l2[V^qu]] is defined as the
      subspace fixed by [...]". *)
  Definition qeq {Z : Type} (Q1 Q2 : rqset) (Hd : rqdisj Q1 Q2)
             (U1 : op (rqsub Q1) Z) (U2 : op (rqsub Q2) Z) : hspace rqmem :=
    hfix (qeqOp Q1 Q2 Hd U1 U2).

  Lemma hmem_qeq {Z} Q1 Q2 Hd (U1 : op (rqsub Q1) Z) (U2 : op (rqsub Q2) Z) v :
    hmem v (qeq Q1 Q2 Hd U1 U2) <-> oapp (qeqOp Q1 Q2 Hd U1 U2) v = v.
  Proof. apply hmem_hfix. Qed.

  (** As a predicate (Definition 13): quantum equality does not depend on the
      classical memory, so it is a constant expression. *)
  Definition pqeq {Z} Q1 Q2 Hd (U1 : op (rqsub Q1) Z) (U2 : op (rqsub Q2) Z)
    : pred := gconst (qeq Q1 Q2 Hd U1 U2).

  (* ================================================================= *)
  (** ** Lemma 31

      "[(A U1) Q1 =quant U2 Q2  =  U1 Q1 =quant (A^* U2) Q2]"

      "This is especially useful for canceling out terms, e.g., we get
       [(A Q1 =quant A Q2) = (id Q1 =quant A^* A Q2) = (Q1 =quant Q2)] for
       isometries [A]."

      The paper's proof is one line -- the two defining operators are literally
      the same -- and so is this one, once the adjoint laws are available. Note
      there is no hypothesis on [A]; that is the payoff of Definition 27
      allowing arbitrary bounded operators. *)

  Lemma qeq_shift {Y Z : Type} (Q1 Q2 : rqset) (Hd : rqdisj Q1 Q2)
        (U1 : op (rqsub Q1) Y) (U2 : op (rqsub Q2) Z) (A : op Y Z) :
    qeq Q1 Q2 Hd (ocomp A U1) U2 = qeq Q1 Q2 Hd U1 (ocomp (oadj A) U2).
  Proof.
    unfold qeq, qeqOp.
    assert (H1 : ocomp (oadj U2) (ocomp A U1)
                 = ocomp (oadj (ocomp (oadj A) U2)) U1).
    { rewrite oadj_ocomp, oadj_invol, ocomp_assoc; reflexivity. }
    assert (H2 : ocomp (oadj (ocomp A U1)) U2
                 = ocomp (oadj U1) (ocomp (oadj A) U2)).
    { rewrite oadj_ocomp, ocomp_assoc; reflexivity. }
    rewrite H1, H2; reflexivity.
  Qed.

  (** The cancellation the paper highlights, in the form it is used:
      an isometry applied to *both* sides cancels. *)
  Corollary qeq_cancel_isometry {Z : Type} (Q1 Q2 : rqset) (Hd : rqdisj Q1 Q2)
        (U1 : op (rqsub Q1) Z) (U2 : op (rqsub Q2) Z) (A : op Z Z) :
    oisometry A ->
    qeq Q1 Q2 Hd (ocomp A U1) (ocomp A U2) = qeq Q1 Q2 Hd U1 U2.
  Proof.
    intros HA.
    rewrite qeq_shift.
    (* [A^* (A U2) = (A^* A) U2 = U2] *)
    rewrite ocomp_assoc, HA, ocomp_oid_l; reflexivity.
  Qed.

  (* ================================================================= *)
  (** ** Definition 28, concretely

      Definition 28 sets [U1 = U2 = id] and requires
      [Type^list_Q1 = Type^list_Q2]. Here the two register types [rqsub Q1] and
      [rqsub Q2] are never literally equal -- they are indexed by disjoint sets
      of variables -- so the identification has to be named. That is exactly
      what the paper does one step later, in Corollary 30, where the condition
      becomes [psi_1^Q = U_rename,sigma psi_2^Q].

      The case that matters is a single-sided variable set [Y] taken on both
      sides: [Y_1 =quant Y_2], as used by rules Equal, QrhlElimEq and
      TransSimple, and by the EPR example. The renaming is then the evident
      [qsub Y ~= rqsub (qidx s Y)] on each side. *)

  Definition YsubL (Y : qset) (f : qsub Y) : rqsub (qidx SL Y) :=
    fun w => match w as w'
                   return (if qidx SL Y w' then rqtype w' else unit) with
             | (s, q) =>
                 match s as s'
                       return (if qidx SL Y (s', q) then rqtype (s', q) else unit) with
                 | SL => f q
                 | SR => tt
                 end
             end.

  Definition YsubL_inv (Y : qset) (g : rqsub (qidx SL Y)) : qsub Y :=
    fun q => g (SL, q).

  Definition YsubR (Y : qset) (f : qsub Y) : rqsub (qidx SR Y) :=
    fun w => match w as w'
                   return (if qidx SR Y w' then rqtype w' else unit) with
             | (s, q) =>
                 match s as s'
                       return (if qidx SR Y (s', q) then rqtype (s', q) else unit) with
                 | SL => tt
                 | SR => f q
                 end
             end.

  Definition YsubR_inv (Y : qset) (g : rqsub (qidx SR Y)) : qsub Y :=
    fun q => g (SR, q).

  Lemma YsubL_inv_YsubL (Y : qset) (f : qsub Y) : YsubL_inv Y (YsubL Y f) = f.
  Proof. reflexivity. Qed.

  Lemma YsubL_YsubL_inv (Y : qset) (g : rqsub (qidx SL Y)) :
    YsubL Y (YsubL_inv Y g) = g.
  Proof.
    apply funext; intros [s q]; destruct s; cbn.
    - reflexivity.
    - destruct (g (SR, q)); reflexivity.
  Qed.

  Lemma YsubR_inv_YsubR (Y : qset) (f : qsub Y) : YsubR_inv Y (YsubR Y f) = f.
  Proof. reflexivity. Qed.

  Lemma YsubR_YsubR_inv (Y : qset) (g : rqsub (qidx SR Y)) :
    YsubR Y (YsubR_inv Y g) = g.
  Proof.
    apply funext; intros [s q]; destruct s; cbn.
    - destruct (g (SL, q)); reflexivity.
    - reflexivity.
  Qed.

  (** The register isomorphisms, as unitaries. These are the paper's
      [U_rename,sigma] for the renaming that maps side-2 variables to their
      side-1 counterparts. *)
  Definition UYL (Y : qset) : op (qsub Y) (rqsub (qidx SL Y)) :=
    Ubij (YsubL Y) (YsubL_inv Y) (YsubL_inv_YsubL Y) (YsubL_YsubL_inv Y).

  Definition UYR (Y : qset) : op (qsub Y) (rqsub (qidx SR Y)) :=
    Ubij (YsubR Y) (YsubR_inv Y) (YsubR_inv_YsubR Y) (YsubR_YsubR_inv Y).

  Lemma UYL_unitary (Y : qset) : ounitary (UYL Y).
  Proof. apply Ubij_ounitary. Qed.

  Lemma UYR_unitary (Y : qset) : ounitary (UYR Y).
  Proof. apply Ubij_ounitary. Qed.

  (** [Y_1 =quant Y_2]: Definition 28 for a variable set taken on both sides. *)
  Definition qeqY (Y : qset) : hspace rqmem :=
    @qeq (rqsub (qidx SL Y)) (qidx SL Y) (qidx SR Y) (qidx_disjoint Y Y)
         oid (ocomp (UYL Y) (oadj (UYR Y))).

  Definition pqeqY (Y : qset) : pred := gconst (qeqY Y).

  (* ================================================================= *)
  (** ** Not yet here

      The two substantial results of section 4.4 are deferred, each for a
      specific reason, and each is wanted by the EPR example rather than by the
      definitions above.

      - Lemma 29 (and Corollary 30), the characterization of quantum equality
        on separable states:
          if [psi1 (x) psi2 in (U1 Q1 =quant U2 Q2)] then the registers
          factor out, [psi_i = psi_i^Q (x) psi_i^Y], with
          [U1 U_vars,Q1^* psi_1^Q = U2 U_vars,Q2^* psi_2^Q].
        The paper's proof runs on a Schmidt decomposition (its Lemma 7).
        **Update: the substrate capability for Schmidt itself is landed** --
        [vsum]/[vsummable]/[schmidt_decompose]/[hmem_tensor_span_component]
        (`Substrate/Interface.v`/`Theory.v`; see HANDOFF.md S6/S7f for the
        design and why a coherent countable vector sum, not one more axiom
        in the existing vocabulary, was needed). **But this lemma is blocked
        on two further things, checked against the paper's actual proof
        text, in *both* directions, not just the converse:**
        (1) the "P2 x = x" eigenvector step (`P2 := U2-hat U2-hat^adj`, a
        positive operator with operator norm at most 1) has no available
        machinery at all -- this signature has no operator-norm primitive
        and no spectral theorem for a general bounded operator (`opositive`
        has zero derived lemmas; `tcp_decompose` is the wrong type, since
        `P2 : op X X` is not a `tcp X`); the algebraic route
        (`<x,(P2-P2^2)x> = 0`) only closes if `P2` is a projector, which
        needs `U2-hat` isometric, which the *forward* direction's hypothesis
        (`U1`, `U2` merely bounded by 1, not isometries) does not give. (2)
        the paper's own proof regroups `(psi1^Q (x) psi1^Y) (x) (psi2^Q (x)
        psi2^Y)` into `psi1^Q (x) psi2^Q (x) psi1^Y (x) psi2^Y`, waved
        through as "the tensor product is commutative in our formalism" --
        in this encoding that regrouping *is* the [rWsplit2] combined-
        register coherence layer (below), so **the forward direction needs
        it too**, not just the converse. (An earlier version of this comment
        said otherwise; that was wrong, corrected here and in HANDOFF.md
        S7f.) [qeqOp] routes through [rWsplit2] (the combined-register split
        of [Q1] and [Q2] together), and relating [rprod v1 v2] (built from
        [Urqpair] plus the two *individual* splits [Usplit Q1]/[Usplit Q2])
        to that combined split is a register coherence layer comparable in
        size to [rUsplit_qidx_SL] (`Registers.v`), not a one-liner. See
        HANDOFF.md S7f for both findings in full, including that [Urelab]
        (`Registers.v`) and [UYL]/[UYR] just below are the same construction
        in opposite directions -- reuse one rather than building a third
        copy.

      - Lemma 32, [(A1»Q1) . (U1 Q1 =quant U2 Q2) = (U1 A1^adj) Q1 =quant U2 Q2]
        for unitary [A1], which is how rule QApply1's preconditions get
        simplified (and is used twice in the EPR derivation). The obstruction
        is not the paper's argument, which is short, but a missing piece of
        register theory: it relates [rolift Q1], a lift over one register, to
        [rolift (Q1 u Q2)], a lift over the combined one, and the coherence
        between nested lifts is not proved yet -- the same [rWsplit2] gap
        Lemma 29's converse hits above. That coherence is worth having on
        its own account -- rules Frame and Equal will need it too.

      Lemmas 33 and 34 build on 29 and are further out. *)

End QEqTheory.
