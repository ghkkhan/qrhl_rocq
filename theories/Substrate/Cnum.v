(** * Complex numbers over the Rocq standard library reals.

    The Rocq standard library has no complex numbers, and the whole point of
    depending on stdlib alone (see the project README) is to keep the
    dependency set empty while the substrate is abstract. So we build [C] here.

    This file is ordinary, uncontroversial algebra: it contains no axioms and
    is not part of the trusted surface. Everything in it is proved.

    Contents: the field structure (with [ring]/[field] tactic support),
    conjugation, modulus, and the "nonnegative real" predicate that the
    substrate uses to state positivity of operators. *)

From Stdlib Require Import Reals Lra.
From Stdlib Require Export Ring Field.

Local Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(** ** Carrier and operations *)

Definition C : Set := (R * R)%type.

Definition Cre (z : C) : R := fst z.
Definition Cim (z : C) : R := snd z.

Definition RtoC (x : R) : C := (x, 0).
Coercion RtoC : R >-> C.

Definition C0 : C := (0, 0).
Definition C1 : C := (1, 0).
Definition Ci : C := (0, 1).

Definition Cplus (z w : C) : C := (Cre z + Cre w, Cim z + Cim w).
Definition Copp  (z : C)   : C := (- Cre z, - Cim z).
Definition Cminus (z w : C) : C := Cplus z (Copp w).
Definition Cmult (z w : C) : C :=
  (Cre z * Cre w - Cim z * Cim w, Cre z * Cim w + Cim z * Cre w).

(** Squared modulus, kept separate because it is the recurring side condition. *)
Definition Csqmod (z : C) : R := Cre z ^ 2 + Cim z ^ 2.

Definition Cinv (z : C) : C := (Cre z / Csqmod z, - Cim z / Csqmod z).
Definition Cdiv (z w : C) : C := Cmult z (Cinv w).

Definition Cconj (z : C) : C := (Cre z, - Cim z).
Definition Cmod (z : C) : R := sqrt (Csqmod z).

Declare Scope C_scope.
Delimit Scope C_scope with C.
Bind Scope C_scope with C.
Local Open Scope C_scope.

Infix "+" := Cplus : C_scope.
Infix "-" := Cminus : C_scope.
Infix "*" := Cmult : C_scope.
Infix "/" := Cdiv : C_scope.
Notation "- z" := (Copp z) : C_scope.
Notation "/ z" := (Cinv z) : C_scope.
Notation "z ^*" := (Cconj z) (at level 20, left associativity) : C_scope.

(* ------------------------------------------------------------------ *)
(** ** Extensionality *)

Lemma Ceq_iff (z w : C) : z = w <-> Cre z = Cre w /\ Cim z = Cim w.
Proof.
  split.
  - intros ->; split; reflexivity.
  - destruct z as [a b], w as [c d]; simpl; intros [-> ->]; reflexivity.
Qed.

Lemma Ceq_intro (z w : C) : Cre z = Cre w -> Cim z = Cim w -> z = w.
Proof. intros H1 H2; apply Ceq_iff; split; assumption. Qed.

(** Discharge a goal between complex expressions by splitting into the two
    real components and calling [ring] / [lra] on each. *)
Ltac Cdestruct :=
  repeat match goal with
         | z : C |- _ => destruct z
         end.

Ltac Cring :=
  Cdestruct;
  apply Ceq_intro;
  unfold Cplus, Copp, Cminus, Cmult, Cinv, Cdiv, Cconj, RtoC,
         C0, C1, Ci, Cre, Cim, Csqmod in *;
  simpl; try ring.

(* ------------------------------------------------------------------ *)
(** ** Ring structure *)

Lemma C_ring_theory :
  ring_theory C0 C1 Cplus Cmult Cminus Copp eq.
Proof.
  constructor; intros; Cring.
Qed.

Add Ring Cring : C_ring_theory.

(* ------------------------------------------------------------------ *)
(** ** Field structure *)

Lemma Csqmod_nonneg (z : C) : 0 <= Csqmod z.
Proof. unfold Csqmod; nra. Qed.

Lemma Csqmod_eq0 (z : C) : Csqmod z = 0 <-> z = C0.
Proof.
  unfold Csqmod, C0; destruct z as [a b]; simpl; split.
  - intros H; apply Ceq_intro; simpl; nra.
  - intros H; apply Ceq_iff in H; destruct H as [H1 H2]; simpl in H1, H2.
    rewrite H1, H2; ring.
Qed.

Lemma Csqmod_neq0 (z : C) : z <> C0 -> Csqmod z <> 0.
Proof. intros Hz Hc; apply Hz, Csqmod_eq0; exact Hc. Qed.

Lemma C1_neq_C0 : C1 <> C0.
Proof.
  intros H; apply Ceq_iff in H; destruct H as [H1 _].
  unfold C1, C0, Cre in H1; simpl in H1; lra.
Qed.

Lemma Cinv_l (z : C) : z <> C0 -> Cmult (Cinv z) z = C1.
Proof.
  intros Hz.
  assert (Hs : Csqmod z <> 0) by (apply Csqmod_neq0; exact Hz).
  destruct z as [a b].
  unfold Csqmod, Cre, Cim in Hs; simpl in Hs.
  apply Ceq_intro; unfold Cmult, Cinv, C1, Csqmod, Cre, Cim; simpl;
    field; intro Hc; apply Hs; nra.
Qed.

Lemma C_field_theory :
  field_theory C0 C1 Cplus Cmult Cminus Copp Cdiv Cinv eq.
Proof.
  constructor.
  - exact C_ring_theory.
  - exact C1_neq_C0.
  - reflexivity.
  - exact Cinv_l.
Qed.

Add Field Cfield : C_field_theory.

(* ------------------------------------------------------------------ *)
(** ** Conjugation *)

Lemma Cconj_involutive (z : C) : (z^*)^* = z.
Proof. Cring. Qed.

Lemma Cconj_plus (z w : C) : (z + w)^* = z^* + w^*.
Proof. Cring. Qed.

Lemma Cconj_opp (z : C) : (- z)^* = - (z^*).
Proof. Cring. Qed.

Lemma Cconj_mult (z w : C) : (z * w)^* = z^* * w^*.
Proof. Cring. Qed.

Lemma Cconj_C0 : C0^* = C0.
Proof. Cring. Qed.

Lemma Cconj_C1 : C1^* = C1.
Proof. Cring. Qed.

Lemma Cconj_RtoC (x : R) : (RtoC x)^* = RtoC x.
Proof. Cring. Qed.

(** The identity that makes conjugation useful: [z * z^*] is the squared
    modulus, in particular a nonnegative real. *)
Lemma Cmult_conj_sqmod (z : C) : z * z^* = RtoC (Csqmod z).
Proof. unfold Csqmod; Cring. Qed.

(* ------------------------------------------------------------------ *)
(** ** Modulus *)

Lemma Cmod_nonneg (z : C) : 0 <= Cmod z.
Proof. unfold Cmod; apply sqrt_pos. Qed.

Lemma Cmod_sqr (z : C) : Cmod z ^ 2 = Csqmod z.
Proof.
  unfold Cmod; rewrite <- Rsqr_pow2; apply Rsqr_sqrt, Csqmod_nonneg.
Qed.

Lemma Cmod_eq0 (z : C) : Cmod z = 0 <-> z = C0.
Proof.
  split.
  - intros H; apply Csqmod_eq0.
    rewrite <- Cmod_sqr, H; ring.
  - intros ->; unfold Cmod, Csqmod, C0, Cre, Cim; simpl.
    transitivity (sqrt 0); [ f_equal; ring | apply sqrt_0 ].
Qed.

Lemma Cmod_conj (z : C) : Cmod (z^*) = Cmod z.
Proof.
  unfold Cmod, Csqmod, Cconj, Cre, Cim; simpl; f_equal; ring.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Real and nonnegative-real predicates

    The substrate states positivity of operators through inner products, which
    live in [C]; these are the predicates it uses. *)

Definition Cis_real (z : C) : Prop := Cim z = 0.
Definition Cge0 (z : C) : Prop := Cim z = 0 /\ 0 <= Cre z.

Lemma Cge0_real (z : C) : Cge0 z -> Cis_real z.
Proof. intros [H _]; exact H. Qed.

Lemma Cge0_C0 : Cge0 C0.
Proof. split; [ reflexivity | right; reflexivity ]. Qed.

Lemma Cge0_RtoC (x : R) : 0 <= x -> Cge0 (RtoC x).
Proof. intros H; split; [ reflexivity | exact H ]. Qed.

Lemma Cge0_plus (z w : C) : Cge0 z -> Cge0 w -> Cge0 (z + w).
Proof.
  intros [H1 H2] [H3 H4]; split; unfold Cplus, Cre, Cim in *; simpl in *.
  - rewrite H1, H3; ring.
  - lra.
Qed.

Lemma Cge0_sqmod (z : C) : Cge0 (z * z^*).
Proof.
  rewrite Cmult_conj_sqmod; apply Cge0_RtoC, Csqmod_nonneg.
Qed.

(** A real number is recoverable from its embedding, so [Cis_real] loses
    nothing. *)
Lemma Cis_real_RtoC (z : C) : Cis_real z -> z = RtoC (Cre z).
Proof.
  intros H; apply Ceq_intro; [ reflexivity | simpl; exact H ].
Qed.
