(** * Degeneracy canaries for the substrate signature.

    The substrate is assumed, not constructed, so nothing inside Rocq can tell
    us it is consistent. What we *can* do cheaply is check that it is not
    degenerate: that it does not collapse the subspace lattice, does not make
    every vector zero, does not make the orthocomplement the identity, and does
    not flatten the tensor product. A signature with a typo that made it
    contradictory would very likely fail one of these, because each derives a
    concrete *inequality* from the axioms.

    This is a canary, not a consistency proof, and it is not a substitute for
    Phase 4. Stated plainly: these lemmas rule out the cheap failure modes; only
    exhibiting a model rules out the expensive one.

    Everything below is proved from the signature alone, with no instance of
    [HILBERT_SUBSTRATE] in existence. *)

From QRHL.Substrate Require Import Ambient Cnum Interface Theory.

Module Sanity (S : HILBERT_SUBSTRATE).
  Include HTheory S.

  (** A two-element index type: the qubit. *)
  Local Notation Q := bool.

  (* ------------------------------------------------------------------ *)
  (** ** 1. The space is not zero *)

  (** If the signature forced [l2 X] to be trivial, this would fail. *)
  Theorem canary_ket_nonzero : ket true <> (@vzero Q).
  Proof. apply ket_neq_vzero. Qed.

  (** ... and therefore the lattice has at least two elements. *)
  Theorem canary_lattice_nontrivial : (@hbot Q) <> (@htop Q).
  Proof.
    intros Heq.
    apply canary_ket_nonzero.
    apply hmem_hbot.
    rewrite Heq; apply hmem_htop.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 2. Distinct basis vectors span distinct lines *)

  Lemma inner_ket_neq {X} (x y : X) : x <> y -> inner (ket x) (ket y) = C0.
  Proof.
    intros Hxy; rewrite inner_ket.
    destruct (excluded_middle_informative (x = y)); [ contradiction | reflexivity ].
  Qed.

  Lemma inner_ket_same {X} (x : X) : inner (ket x) (ket x) = C1.
  Proof.
    rewrite inner_ket.
    destruct (excluded_middle_informative (x = x)); [ reflexivity | tauto ].
  Qed.

  (** [|true>] is orthogonal to the line through [|false>], but not to its own.
      Hence the two lines are different -- the lattice distinguishes states. *)
  Theorem canary_lines_distinct :
    hspan1 (ket true) <> hspan1 (@ket Q false).
  Proof.
    intros Heq.
    (* [|true>] lies in the complement of the [|false>] line ... *)
    assert (Hin : hmem (ket true) (hocompl (hspan1 (@ket Q false)))).
    { apply hmem_hocompl_hspan1, inner_ket_neq; discriminate. }
    (* ... so, if the lines agreed, in the complement of its own line. *)
    rewrite <- Heq in Hin.
    apply hmem_hocompl_hspan1 in Hin.
    rewrite inner_ket_same in Hin.
    exact (C1_neq_C0 Hin).
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 3. The orthocomplement is not the identity, and meets can be trivial
             between two nonzero subspaces *)

  Theorem canary_hocompl_not_id :
    hocompl (hspan1 (@ket Q true)) <> hspan1 (@ket Q true).
  Proof.
    intros Heq.
    assert (Hin : hmem (ket true) (hocompl (hspan1 (@ket Q true)))).
    { rewrite Heq; apply hmem_hspan1. }
    apply hmem_hocompl_hspan1 in Hin.
    rewrite inner_ket_same in Hin.
    exact (C1_neq_C0 Hin).
  Qed.

  (** Two subspaces, both nonzero, whose meet is zero. In a collapsed lattice
      (everything equal) this is impossible. *)
  Theorem canary_nontrivial_orthogonal_pair :
    let Sp := hspan1 (@ket Q true) in
    Sp <> hbot /\ hocompl Sp <> hbot /\ hmeet Sp (hocompl Sp) = hbot.
  Proof.
    intros Sp; repeat split.
    - (* [|true>] is in [Sp] and is nonzero *)
      intros Heq.
      apply (ket_neq_vzero true), hmem_hbot.
      rewrite <- Heq; apply hmem_hspan1.
    - (* [|false>] is orthogonal to [|true>], hence in the complement *)
      intros Heq.
      apply (ket_neq_vzero false), hmem_hbot.
      rewrite <- Heq.
      apply hmem_hocompl_hspan1, inner_ket_neq; discriminate.
    - apply hmeet_hocompl.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 4. The tensor product does not collapse *)

  (** If [tensorv] identified distinct product states, [l2 (X * Y)] would not
      be a tensor product. *)
  Theorem canary_tensor_nondegenerate :
    tensorv (ket true) (ket true) <> tensorv (@ket Q true) (@ket Q false).
  Proof.
    intros Heq.
    assert (Hc : inner (tensorv (@ket Q true) (@ket Q true))
                       (tensorv (@ket Q true) (@ket Q false)) = C1).
    { rewrite <- Heq, inner_tensorv, !inner_ket_same; ring. }
    rewrite inner_tensorv, inner_ket_same in Hc.
    rewrite (inner_ket_neq true false) in Hc by discriminate.
    (* [Hc : C1 * C0 = C1], i.e. [C0 = C1] *)
    apply C1_neq_C0; rewrite <- Hc; ring.
  Qed.

End Sanity.
