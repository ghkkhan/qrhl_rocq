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

  (* ------------------------------------------------------------------ *)
  (** ** 5. [op_ext_ket] does not collapse distinct reindexings

      [op_ext_ket] forces two operators to be equal whenever they agree on
      *every* ket. A degenerate pairing with some other axiom could in
      principle satisfy that hypothesis vacuously (e.g. if the basis
      collapsed, or if [Ubij] failed to distinguish maps). It does not:
      [Uswap], which exchanges the two factors of [Q * Q], really is
      different from [oid], because they send [(true, false)] to different
      kets and distinct basis vectors span distinct lines (canary 2). *)
  Theorem canary_op_ext_ket_nondegenerate : @Uswap Q Q <> oid.
  Proof.
    intros Heq.
    assert (Hc : ket (false, true) = ket (true, false) :> l2 (Q * Q)).
    { transitivity (oapp (@Uswap Q Q) (ket (true, false))).
      - rewrite Uswap_ket; reflexivity.
      - rewrite Heq; apply oapp_oid. }
    assert (Hcontra := f_equal (fun v => inner (ket (false, true)) v) Hc).
    cbn beta in Hcontra.
    rewrite inner_ket_same, inner_ket in Hcontra.
    destruct (excluded_middle_informative ((false, true) = (true, false)))
      as [Habs | _]; [ discriminate Habs |].
    apply C1_neq_C0; exact Hcontra.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 6. [vsum]/[schmidt_decompose] do not collapse to [vzero]

      [vsum] is characterized only indirectly (its value is pinned down by
      [schmidt_decompose] and [hmem_tensor_span_component], never given a
      general formula), so a degenerate signature could in principle make
      every summable family sum to [vzero] without contradicting either
      axiom's *type*. It cannot: [schmidt_decompose] applied to the (plainly
      nonzero) product ket [tensorv (ket true) (ket true)] returns a family
      whose [vsum] *is* that ket, by the axiom's own equation, so [vsum]
      genuinely reconstructs a nonzero vector here. *)
  Theorem canary_vsum_nondegenerate :
    exists (I : Type) (F : I -> l2 (Q * Q)), vsum F <> vzero.
  Proof.
    set (psi := tensorv (@ket Q true) (ket true)).
    assert (Hpsi : psi <> vzero).
    { intros Heq.
      assert (Hc : inner psi psi = C0) by (rewrite Heq; apply inner_vzero_r).
      unfold psi in Hc; rewrite inner_tensorv, inner_ket_same in Hc.
      apply C1_neq_C0; rewrite <- Hc; ring.
    }
    destruct (schmidt_decompose Q Q psi)
      as [I [lam [a [b [_ [_ [_ [_ [_ [_ Heq]]]]]]]]]].
    exists I, (fun i => vscale (RtoC (lam i)) (tensorv (a i) (b i))).
    rewrite <- Heq; exact Hpsi.
  Qed.

End Sanity.
