(** * Quantum predicates.

    Sections 4.1, 4.2 and 4.3.

    Definition 13: "A (quantum) predicate [A] over [V] is an expression with
    [fv(A) subseteq V^cl] and [Type^exp_A subseteq {S : S is a subspace of
    l2[V^qu]}]."

    So a predicate is literally an expression valued in subspaces -- which is
    why [Expr.v] was built generically. The motivation (section 4.1) is worth
    keeping in mind: a predicate could have been a single subspace of
    [l2[V]], but splitting off the classical part as an index makes it possible
    "to express the properties of the quantum variables in terms of the values
    of the classical variables", and that is what [Cla[...]] below trades on.

    Predicates here are *relational*: indexed by [rcmem] and valued in
    subspaces of [l2 rqmem], i.e. over the paper's [V1 V2]. That is what
    Definition 35 needs. The single-sided specialization is only required by
    Definition 22 (total) and Definition 26 (readonly), which rules While1 and
    Frame use in Phase 2; it is not built yet. *)

From Stdlib Require Import List Lra.
From QRHL.Substrate Require Import Ambient Cnum Sums Interface Theory.
From QRHL.Core Require Import Vars Expr Registers Syntax Semantics.

Module PredTheory (S : HILBERT_SUBSTRATE) (V : PROGRAM_VARS).
  Include SemTheory S V.

  (* ================================================================= *)
  (** ** Relational cq-states

      [T^+_cq[V1 V2]], as a family indexed by relational classical memories --
      the same representation choice as [cqs] in [Semantics.v]. *)

  Definition rcqs : Type := rcmem -> tcp rqmem.

  Definition rcqs_wf (r : rcqs) : Prop := tcp_summable r.

  Definition rcqs_trace (r : rcqs) : R := tsum (fun rm => tcp_trace (r rm)).

  (** The two partial traces of Definition 35, as cq-states on each side. The
      quantum part is [rtcpL]/[rtcpR] from [Registers.v]; the classical part is
      obtained by summing out the other side's memory. *)
  Definition rcqs_projL (r : rcqs) : cqs :=
    fun m1 => tcp_sum (fun m2 : cmem => rtcpL (r (m1, m2))).

  Definition rcqs_projR (r : rcqs) : cqs :=
    fun m2 => tcp_sum (fun m1 : cmem => rtcpR (r (m1, m2))).

  (* ================================================================= *)
  (** ** Predicates (Definition 13) *)

  Definition pred : Type := rexpr (hspace rqmem).

  (** Definition 14: "A state [rho in T^+_cq[V]] satisfies [A] iff
      [supp rho_m subseteq [A]_m] for all [m]." *)
  Definition psat (r : rcqs) (A : pred) : Prop :=
    forall rm, hle (tcp_supp (r rm)) (ev A rm).

  (** Definition 16: "We say [A subseteq B] iff [[A]_m subseteq [B]_m] for all
      [m]." *)
  Definition ple (A B : pred) : Prop :=
    forall rm, hle (ev A rm) (ev B rm).

  Lemma ple_refl (A : pred) : ple A A.
  Proof. intros rm; apply hle_refl. Qed.

  Lemma ple_trans (A B C : pred) : ple A B -> ple B C -> ple A C.
  Proof. intros H1 H2 rm; eapply hle_trans; [ apply H1 | apply H2 ]. Qed.

  (** Lemma 17: "If [A subseteq B], and [rho] satisfies [A], then [rho]
      satisfies [B]." *)
  Lemma psat_mono (r : rcqs) (A B : pred) : ple A B -> psat r A -> psat r B.
  Proof.
    intros Hle Hsat rm; eapply hle_trans; [ apply Hsat | apply Hle ].
  Qed.

  (* ================================================================= *)
  (** ** Operations on predicates (section 4.2)

      "First, any operation that can be performed on subspaces is meaningful on
      predicates, too. [...] when we write [C := A (op) B] [...] we mean the
      predicate [C] with [[C]_m = [A]_m (op) [B]_m for all m]."

      So every operation is [gmap]/[gmap2] of the corresponding lattice
      operation, and [+]/[cap] are Birkhoff-von Neumann disjunction and
      conjunction. *)

  Definition pmeet (A B : pred) : pred := gmap2 hmeet A B.
  Definition pjoin (A B : pred) : pred := gmap2 hjoin A B.
  Definition pocompl (A : pred) : pred := gmap hocompl A.
  Definition ptop : pred := gconst htop.
  Definition pbot : pred := gconst hbot.

  (** Arbitrary meets. Rules Measure1, Sample1 and JointMeasure all intersect
      over an index set that need not be finite, so this is not optional. *)
  Program Definition pInf {J : Type} (F : J -> pred) : pred :=
    mkGexpr (fun rm => hInf (fun j => ev (F j) rm))
            (fun rx => exists j, efv (F j) rx) _.
  Next Obligation.
    f_equal; apply funext; intros j.
    apply (ev_local (F j)); intros rx Hx; apply H; exists j; exact Hx.
  Qed.

  Program Definition pSup {J : Type} (F : J -> pred) : pred :=
    mkGexpr (fun rm => hSup (fun j => ev (F j) rm))
            (fun rx => exists j, efv (F j) rx) _.
  Next Obligation.
    f_equal; apply funext; intros j.
    apply (ev_local (F j)); intros rx Hx; apply H; exists j; exact Hx.
  Qed.

  Lemma ev_pmeet (A B : pred) rm : ev (pmeet A B) rm = hmeet (ev A rm) (ev B rm).
  Proof. reflexivity. Qed.

  Lemma ev_pInf {J} (F : J -> pred) rm :
    ev (pInf F) rm = hInf (fun j => ev (F j) rm).
  Proof. reflexivity. Qed.

  (** Lemma 15: "A cq-density operator [rho] satisfies [A cap B] iff [rho]
      satisfies [A] and [rho] satisfies [B]."

      Note the paper's parenthetical: "the analogue for [A + B] does not hold."
      That asymmetry is the whole reason quantum predicates are subspaces
      rather than sets of states. *)
  Lemma psat_pmeet (r : rcqs) (A B : pred) :
    psat r (pmeet A B) <-> psat r A /\ psat r B.
  Proof.
    split.
    - intros H; split; intros rm;
        eapply hle_trans; [ apply H | rewrite ev_pmeet; apply hmeet_lel
                          | apply H | rewrite ev_pmeet; apply hmeet_ler ].
    - intros [H1 H2] rm; rewrite ev_pmeet; apply hmeet_glb;
        [ apply H1 | apply H2 ].
  Qed.

  Lemma psat_pInf (r : rcqs) {J} (F : J -> pred) :
    psat r (pInf F) <-> forall j, psat r (F j).
  Proof.
    split.
    - intros H j rm; eapply hle_trans; [ apply H |].
      rewrite ev_pInf; apply (hInf_lb (fun j => ev (F j) rm) j).
    - intros H rm; rewrite ev_pInf; apply hInf_glb; intros j; apply H.
  Qed.

  Lemma psat_ptop (r : rcqs) : psat r ptop.
  Proof. intros rm; apply hle_htop. Qed.

  (* ================================================================= *)
  (** ** Classical predicates (section 4.3)

      Definition 23: "[Cla[true] := l2[V^qu]] and [Cla[false] := 0]." *)

  Definition Cla (e : rexpr bool) : pred :=
    gmap (fun b : bool => if b then htop else hbot) e.

  Lemma ev_Cla (e : rexpr bool) rm :
    ev (Cla e) rm = if ev e rm then htop else hbot.
  Proof. reflexivity. Qed.

  Definition Cla_true : pred := Cla (gconst true).

  Lemma Cla_true_top rm : ev Cla_true rm = htop.
  Proof. reflexivity. Qed.

  (** Lemma 24: "[rho] satisfies [Cla[e]] iff [[e]_m = true] for all [m] with
      [rho_m <> 0]." *)
  Lemma psat_Cla (r : rcqs) (e : rexpr bool) :
    psat r (Cla e) <-> (forall rm, r rm <> tcp_zero -> ev e rm = true).
  Proof.
    split.
    - intros H rm Hnz.
      specialize (H rm); rewrite ev_Cla in H.
      destruct (ev e rm) eqn:He; [ reflexivity |].
      exfalso; apply Hnz, tcp_supp_eq0.
      apply hle_antisym; [ exact H | apply hbot_le ].
    - intros H rm; rewrite ev_Cla.
      destruct (ev e rm) eqn:He; [ apply hle_htop |].
      (* [e] false here forces the block to be zero *)
      destruct (classic (r rm = tcp_zero)) as [Hz | Hz].
      + rewrite Hz, (proj2 (tcp_supp_eq0 _ _) eq_refl); apply hle_refl.
      + rewrite (H rm Hz) in He; discriminate.
  Qed.

  (** Lemma 25. Stated as [ev_eq], pointwise equality of denotations: the
      free-variable field of an expression is an over-approximation carried for
      the locality reasoning of rules Frame and Equal, not part of a
      predicate's meaning. *)

  Lemma Cla_and (e f : rexpr bool) :
    ev_eq (pmeet (Cla e) (Cla f)) (Cla (gmap2 andb e f)).
  Proof.
    intros rm; rewrite ev_pmeet, !ev_Cla; cbn [ev gmap2].
    destruct (ev e rm), (ev f rm); cbn.
    - apply hmeet_htop.
    - apply hmeet_hbot.
    - rewrite hmeet_comm; apply hmeet_hbot.
    - apply hmeet_idem.
  Qed.

  Lemma Cla_or (e f : rexpr bool) :
    ev_eq (pjoin (Cla e) (Cla f)) (Cla (gmap2 orb e f)).
  Proof.
    intros rm; unfold pjoin; cbn [ev gmap2]; rewrite !ev_Cla; cbn [ev gmap2].
    destruct (ev e rm), (ev f rm); cbn.
    - apply hjoin_htop.
    - apply hjoin_hbot.
    - rewrite hjoin_comm; apply hjoin_hbot.
    - apply hjoin_hbot.
  Qed.

  Lemma Cla_not (e : rexpr bool) :
    ev_eq (pocompl (Cla e)) (Cla (gmap negb e)).
  Proof.
    intros rm; unfold pocompl; cbn [ev gmap]; rewrite !ev_Cla; cbn [ev gmap].
    destruct (ev e rm); cbn; [ apply hocompl_htop | apply hocompl_hbot ].
  Qed.

  (** Universal quantification over an arbitrary index type, the form
      Lemma 25 (iv) takes here. Classical, so the quantified statement is again
      a Boolean expression. *)
  Program Definition ball {J : Type} (F : J -> rexpr bool) : rexpr bool :=
    mkGexpr (fun rm =>
               if excluded_middle_informative (forall j, ev (F j) rm = true)
               then true else false)
            (fun rx => exists j, efv (F j) rx) _.
  Next Obligation.
    (* the two quantified propositions are equal, by locality plus propext *)
    assert (Hj : forall j, ev (F j) m = ev (F j) m').
    { intros j; apply (ev_local (F j)); intros rx Hx; apply H; exists j; exact Hx. }
    assert (Heq : (forall j, ev (F j) m = true) = (forall j, ev (F j) m' = true)).
    { apply propositional_extensionality; split; intros HH j;
        [ rewrite <- (Hj j) | rewrite (Hj j) ]; apply HH. }
    rewrite Heq; reflexivity.
  Qed.

  Lemma Cla_forall {J : Type} (F : J -> rexpr bool) :
    ev_eq (pInf (fun j => Cla (F j))) (Cla (ball F)).
  Proof.
    intros rm; rewrite ev_pInf, ev_Cla; unfold ball; cbn [ev].
    destruct (excluded_middle_informative (forall j, ev (F j) rm = true))
      as [Hall | Hex].
    - (* every conjunct is the full space *)
      apply hle_antisym; [ apply hle_htop |].
      apply hInf_glb; intros j; rewrite ev_Cla, (Hall j); apply hle_refl.
    - (* some conjunct is zero, so the meet is zero *)
      apply hle_antisym; [| apply hbot_le ].
      apply not_all_ex_not in Hex; destruct Hex as [j Hj].
      eapply hle_trans; [ apply (hInf_lb (fun j => ev (Cla (F j)) rm) j) |].
      rewrite ev_Cla; destruct (ev (F j) rm); [ congruence | apply hle_refl ].
  Qed.

  (* ================================================================= *)
  (** ** Lifting to a register (Definition 19)

      [S»Q], for [Q] a set of relational quantum variables. *)

  Definition plift (P : rqset) (T : rexpr (hspace (rqsub P))) : pred :=
    gmap (rhlift P) T.

  Lemma ev_plift (P : rqset) T rm :
    ev (plift P T) rm = rhlift P (ev T rm).
  Proof. reflexivity. Qed.

  (** Lifting a constant subspace, the common case. *)
  Definition plift_const (P : rqset) (T : hspace (rqsub P)) : pred :=
    gconst (rhlift P T).

  Lemma plift_top (P : rqset) : ev_eq (plift_const P htop) ptop.
  Proof. intros rm; cbn [ev gconst]; apply whlift_htop. Qed.

  (* ================================================================= *)
  (** ** Division (Definition 20)

      "Fix variables [W subseteq V], let [A subseteq l2[V]] be a subspace, and
      let [psi in l2[W]]. Then [A / psi subseteq l2[V \ W]] is defined by
      [phi in A / psi iff phi (x) psi in A]."

      The register [P] plays the role of [W]. Because the substrate has
      preimages of closed subspaces under bounded operators, this is a
      definition rather than a construction. *)

  Definition hdivReg (P : rqset) (A : hspace rqmem) (v : l2 (rqsub P))
    : hspace (rqsub (rqneg P)) :=
    hdivL (hpreim (rUsplit P) A) v.

  Lemma hmem_hdivReg (P : rqset) A v w :
    hmem w (hdivReg P A v) <-> hmem (oapp (rUsplit P) (tensorv v w)) A.
  Proof.
    unfold hdivReg; rewrite hmem_hdivL, hmem_hpreim; reflexivity.
  Qed.

  Lemma hdivReg_mono (P : rqset) (A B : hspace rqmem) (v : l2 (rqsub P)) :
    hle A B -> hle (hdivReg P A v) (hdivReg P B v).
  Proof.
    intros H w Hw; apply hmem_hdivReg; apply H; apply hmem_hdivReg; exact Hw.
  Qed.

  (** The precondition shape of rule QInit1: [(A / e') (x) l2[Q']]. *)
  Definition pdiv (P : rqset) (A : pred) (e : rexpr (l2 (rqsub P))) : pred :=
    gmap2 (fun (a : hspace rqmem) (v : l2 (rqsub P)) =>
             rhlift (rqneg P) (hdivReg P a v)) A e.

  Lemma ev_pdiv (P : rqset) A e rm :
    ev (pdiv P A e) rm = rhlift (rqneg P) (hdivReg P (ev A rm) (ev e rm)).
  Proof. reflexivity. Qed.

  (* ================================================================= *)
  (** ** Locality (Definition 18)

      "Fix variables [X subseteq V]. A predicate [A] on [V] is X-local iff
      [fv(A) subseteq X^cl], and for all [m], [[A]_m = S_m (x) l2[V^qu \ X^qu]]
      for some subspace [S_m] of [l2[X^qu]]."

      "Intuitively, a predicate is X-local if we only need to look at classical
      and quantum variables in [X] to decide whether the predicate is
      satisfied." Used by rules Frame, Equal and QrhlElimEq. *)

  Definition plocal (Xc : rcvar -> Prop) (Xq : rqset) (A : pred) : Prop :=
    (forall rx, efv A rx -> Xc rx) /\
    (forall rm, exists T : hspace (rqsub Xq), ev A rm = rhlift Xq T).

  Lemma plocal_Cla (Xq : rqset) (e : rexpr bool) :
    plocal (efv e) Xq (Cla e).
  Proof.
    split; [ intros rx H; exact H |].
    intros rm; rewrite ev_Cla; destruct (ev e rm).
    - exists htop; symmetry; apply whlift_htop.
    - (* the zero subspace lifts to the zero subspace *)
      exists hbot; symmetry; apply whlift_hbot.
  Qed.

  (* ================================================================= *)
  (** ** Not yet here

      - Lemma 21, the simplification rule for the preconditions rule QInit1
        produces. Its proof decomposes an [X]-local subspace as
        [A_0 (x) l2[Q]] and needs a spanning argument inside the tensor; it is
        wanted first by the EPR example, and is written when that is.
      - Definition 22 (total programs) and Definition 26 (readonly variables).
        Both are single-sided, and are needed first by rules While1 and Frame
        in Phase 2. *)

End PredTheory.
