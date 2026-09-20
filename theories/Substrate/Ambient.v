(** * Ambient logic.

    This file fixes, in one place, the logical setting the whole development
    works in: classical higher-order logic with choice and extensionality.

    This is a deliberate choice, not a leak. Unruh's proofs (and his
    [qrhl-tool]) live in Isabelle/HOL, which is exactly classical HOL with
    Hilbert choice and extensionality. Reproducing those proofs in a
    constructive setting would not be more faithful -- it would be a different
    theorem. Section 2 of the paper is classical throughout: arbitrary
    decompositions of positive operators into rank-one projections, suprema of
    uncountable families, the non-separable Schmidt decomposition, and the
    definition of [supp] as a least projector all presuppose it.

    Nothing here is specific to qRHL, and nothing here is declared by us: these
    are the Rocq standard library's own axioms. [make assumptions] reports them
    explicitly rather than hiding them.

    The axioms this pulls in:
      - [Raxioms]:            completeness of the reals, via [Reals]
      - [FunctionalExtensionality]: functional extensionality
      - [PropExtensionality]:  propositional extensionality
      - [ClassicalEpsilon]:    excluded middle + Hilbert's epsilon (choice)

    Consequences we re-export for convenience are proved, not assumed. *)

From Stdlib Require Export
  Reals
  FunctionalExtensionality
  PropExtensionality
  ClassicalEpsilon
  Classical_Prop.

(** Proof irrelevance comes from [Classical_Prop], where it is derived from
    excluded middle rather than assumed. Restated here so that the name is
    stable and its provenance is visible. *)
Lemma proof_irrel (P : Prop) (p q : P) : p = q.
Proof. apply Classical_Prop.proof_irrelevance. Qed.

(** Dependent functional extensionality, restated under a stable name. *)
Lemma funext {A} {B : A -> Type} (f g : forall a, B a) :
  (forall a, f a = g a) -> f = g.
Proof. apply functional_extensionality_dep. Qed.

(** Predicate extensionality, the form we use for subspaces and predicates. *)
Lemma predext {A} (P Q : A -> Prop) : (forall a, P a <-> Q a) -> P = Q.
Proof.
  intros H; apply funext; intros a.
  apply propositional_extensionality; apply H.
Qed.

(** Elements of a subset type are equal when their witnesses are: the proof
    components are irrelevant. Used wherever a sum is indexed by a subset. *)
Lemma sig_eq {A : Type} {P : A -> Prop} (x y : sig P) :
  proj1_sig x = proj1_sig y -> x = y.
Proof.
  destruct x as [a Ha], y as [b Hb]; simpl; intros ->; f_equal; apply proof_irrel.
Qed.

(** Classical case analysis as a tactic, for readability in the analytic
    proofs where it is used constantly. *)
Ltac classical_cases P :=
  destruct (classic P).
