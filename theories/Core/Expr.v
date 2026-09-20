(** * Expressions.

    Section 3.1. The paper is explicit that expressions should be modelled
    semantically rather than syntactically, and says so precisely because of
    this use case (footnote 11):

      "This formalization is more suitable for modeling expressions in a formal
       logical system (and thus for implementing in a theorem prover such as
       Isabelle or Coq)."

    So an expression is a triple: a set of free variables, a result type, and
    an evaluation function that depends only on the free variables.

      "Formally, an expression simply consists of a finite set [fv(e) ⊆ V^cl],
       a set [Type^exp_e], and a function [⟦e⟧ : Type^set_V -> Type^exp_e]
       (with its argument written as subscript) such that
       [m|fv(e) = m'|fv(e) ==> ⟦e⟧_m = ⟦e⟧_m']."

    We drop the finiteness requirement on [fv(e)], which is a harmless
    generalization: every lemma that uses free variables uses the locality
    property, never finiteness. It can be added if a proof ever needs it.

    Note also: "expressions never contain quantum variables, nor are they
    probabilistic".

    Everything is stated once, generically, and instantiated twice: for
    ordinary expressions over [cmem] and for relational ones over [rcmem]. In
    the paper these are related by the renamings [idx_1], [idx_2]; here the
    relational instance is the same construction over a different variable
    type, and [idx] is a projection. *)

From QRHL.Substrate Require Import Ambient.
From QRHL.Core Require Import Vars.

(* ==================================================================== *)
(** ** The generic expression record *)

Record gexpr (Var Mem : Type) (vty : Var -> Type)
             (get : forall v : Var, Mem -> vty v) (T : Type) : Type := mkGexpr {
  ev   : Mem -> T;
  efv  : Var -> Prop;
  ev_local : forall m m',
      (forall v, efv v -> get v m = get v m') -> ev m = ev m'
}.

Arguments mkGexpr {Var Mem vty get T} _ _ _.
Arguments ev {Var Mem vty get T} _ _.
Arguments efv {Var Mem vty get T} _ _.
Arguments ev_local {Var Mem vty get T} _ {m m'} _.

(** Expressions are equal when they evaluate alike. The free-variable set is
    an over-approximation carried for the locality reasoning in rules Frame and
    Equal; it is not part of an expression's meaning, so we do *not* make it
    part of equality. Where a proof needs two expressions to be
    interchangeable, [ev_eq] is the right notion. *)
Definition ev_eq {Var Mem vty get T}
           (e f : gexpr Var Mem vty get T) : Prop :=
  forall m, ev e m = ev f m.

Section GenericOps.
  Context {Var Mem : Type} {vty : Var -> Type}
          {get : forall v : Var, Mem -> vty v}.

  (** A constant. *)
  Definition gconst {T} (a : T) : gexpr Var Mem vty get T :=
    mkGexpr (fun _ => a) (fun _ => False) (fun _ _ _ => eq_refl).

  (** Reading a variable. *)
  Definition gread (v : Var) : gexpr Var Mem vty get (vty v) :=
    mkGexpr (get v) (fun w => w = v) (fun _ _ H => H v eq_refl).

  (** Applying a function pointwise: the paper writes expressions as formulas,
      e.g. [e + f], which is this. *)
  Program Definition gmap {T U} (f : T -> U) (e : gexpr Var Mem vty get T)
    : gexpr Var Mem vty get U :=
    mkGexpr (fun m => f (ev e m)) (efv e) _.
  Next Obligation. f_equal; apply (ev_local e); exact H. Qed.

  Program Definition gmap2 {T U W} (f : T -> U -> W)
          (e : gexpr Var Mem vty get T) (d : gexpr Var Mem vty get U)
    : gexpr Var Mem vty get W :=
    mkGexpr (fun m => f (ev e m) (ev d m))
            (fun v => efv e v \/ efv d v) _.
  Next Obligation.
    f_equal.
    - apply (ev_local e); intros v Hv; apply H; left; exact Hv.
    - apply (ev_local d); intros v Hv; apply H; right; exact Hv.
  Qed.

  (** "[e] holds iff [⟦e⟧_m = true] for all [m]" (section 3.1). *)
  Definition gholds (e : gexpr Var Mem vty get bool) : Prop :=
    forall m, ev e m = true.

End GenericOps.

(* ==================================================================== *)
(** ** Substitution

    [e{e_1/x_1, ..., e_n/x_n}], formally
    [⟦e{e'/x}⟧_m := ⟦e⟧_{m(x := ⟦e'⟧_m)}] (section 3.1). Stated once against
    an abstract update operation so that it serves both the classical and the
    relational instance; rule Measure1's [B{z/x_1}] is the relational one. *)

Section GenericSubst.
  Context {Var Mem : Type} {vty : Var -> Type}
          {get : forall v : Var, Mem -> vty v}
          (upd : forall (m : Mem) (v : Var), vty v -> Mem)
          (veq_dec : forall v w : Var, {v = w} + {v <> w})
          (upd_same  : forall m v a, get v (upd m v a) = a)
          (upd_other : forall m v w a, w <> v -> get w (upd m v a) = get w m).

  Program Definition gsubst {T} (e : gexpr Var Mem vty get T)
          (x : Var) (d : gexpr Var Mem vty get (vty x))
    : gexpr Var Mem vty get T :=
    mkGexpr (fun m => ev e (upd m x (ev d m)))
            (fun v => (efv e v /\ v <> x) \/ efv d v) _.
  Next Obligation.
    (* the substituted value is the same on both memories ... *)
    assert (Hd : ev d m = ev d m').
    { apply (ev_local d); intros v Hv; apply H; right; exact Hv. }
    rewrite Hd.
    (* ... and the two updated memories agree on [efv e] *)
    apply (ev_local e); intros v Hv.
    destruct (veq_dec v x) as [-> | Hvx].
    - rewrite !upd_same; reflexivity.
    - rewrite !upd_other by exact Hvx.
      apply H; left; split; [ exact Hv | exact Hvx ].
  Qed.

  (** Substituting a constant, the form the measurement rules use:
      [B{z/x}] for a fixed outcome [z]. *)
  Definition gsubst_const {T} (e : gexpr Var Mem vty get T)
             (x : Var) (a : vty x) : gexpr Var Mem vty get T :=
    gsubst e x (gconst a).

  Lemma ev_gsubst_const {T} (e : gexpr Var Mem vty get T) (x : Var) (a : vty x) m :
    ev (gsubst_const e x a) m = ev e (upd m x a).
  Proof. reflexivity. Qed.

End GenericSubst.

(* ==================================================================== *)
(** ** The two instances *)

Module ExprTheory (V : PROGRAM_VARS).
  Include VarTheory V.

  (** Ordinary expressions: free classical variables of [V], evaluated in a
      classical memory. *)
  Definition expr (T : Type) : Type :=
    gexpr cvar cmem ctype (fun x m => m x) T.

  (** Relational expressions: the paper's expressions over [V1 V2]. Predicates
      (Definition 13) are these, valued in subspaces. *)
  Definition rexpr (T : Type) : Type :=
    gexpr rcvar rcmem rctype rcget T.

  (** *** Update laws, so that [gsubst] can be instantiated *)

  Lemma cget_cupd_same (m : cmem) (x : cvar) (a : ctype x) : cupd m x a x = a.
  Proof. apply cupd_same. Qed.

  Lemma cget_cupd_other (m : cmem) (x y : cvar) (a : ctype x) :
    y <> x -> cupd m x a y = m y.
  Proof. intros H; apply cupd_other; congruence. Qed.

  Lemma rcget_rcupd_same (rm : rcmem) (rx : rcvar) (a : rctype rx) :
    rcget rx (rcupd rm rx a) = a.
  Proof.
    destruct rx as [s x]; destruct s; simpl; unfold rcget; simpl; apply cupd_same.
  Qed.

  Lemma rcget_rcupd_other (rm : rcmem) (rx ry : rcvar) (a : rctype rx) :
    ry <> rx -> rcget ry (rcupd rm rx a) = rcget ry rm.
  Proof.
    intros Hne; destruct rx as [s x], ry as [t y].
    unfold rcget, rcupd; destruct s, t; simpl; try reflexivity;
      apply cupd_other; congruence.
  Qed.

  (** *** Substitution, specialized *)

  Definition esubst {T} (e : expr T) (x : cvar) (d : expr (ctype x)) : expr T :=
    gsubst cupd cvar_eq_dec cget_cupd_same cget_cupd_other e x d.

  Definition rsubst {T} (e : rexpr T) (rx : rcvar) (d : rexpr (rctype rx))
    : rexpr T :=
    gsubst rcupd rcvar_eq_dec rcget_rcupd_same rcget_rcupd_other e rx d.

  (** [B{z/x_1}]: substitution of a fixed value, as used by rules Sample1,
      Measure1, JointMeasure and JointSample. *)
  Definition rsubst_val {T} (e : rexpr T) (rx : rcvar) (a : rctype rx) : rexpr T :=
    rsubst e rx (gconst a).

  Lemma ev_rsubst_val {T} (e : rexpr T) (rx : rcvar) (a : rctype rx) rm :
    ev (rsubst_val e rx a) rm = ev e (rcupd rm rx a).
  Proof. reflexivity. Qed.

  (* ================================================================= *)
  (** ** Indexing

      The paper's [idx_i e]: "the expression [e] with every classical variable
      [x] replaced by [x_i]", formally [⟦idx_i e⟧_m := ⟦e⟧_{m ∘ (idx_i)^-1}].

      Here this is a projection. That is the whole content of the
      "tagging is a product" design. *)

  Program Definition idx {T} (s : side) (e : expr T) : rexpr T :=
    mkGexpr (fun rm => ev e (csel s rm))
            (fun rx => fst rx = s /\ efv e (snd rx)) _.
  Next Obligation.
    apply (ev_local e); intros x Hx.
    exact (H (s, x) (conj eq_refl Hx)).
  Qed.

  Lemma ev_idx {T} (s : side) (e : expr T) (rm : rcmem) :
    ev (idx s e) rm = ev e (csel s rm).
  Proof. reflexivity. Qed.

  (** Rule Sym's renaming [sigma = idx_1 ∘ idx_2^-1 ∪ idx_2 ∘ idx_1^-1] is,
      on expressions, precomposition with [rcmem_swap]. *)
  Program Definition rswap {T} (e : rexpr T) : rexpr T :=
    mkGexpr (fun rm => ev e (rcmem_swap rm))
            (fun rx => efv e (swap (fst rx), snd rx)) _.
  Next Obligation.
    apply (ev_local e); intros rx Hx; destruct rx as [t y].
    unfold rcget; cbn [fst snd].
    rewrite !csel_swap.
    specialize (H (swap t, y)).
    unfold rcget in H; cbn [fst snd] in H.
    rewrite swap_invol in H.
    exact (H Hx).
  Qed.

  Lemma ev_rswap {T} (e : rexpr T) (rm : rcmem) :
    ev (rswap e) rm = ev e (rcmem_swap rm).
  Proof. reflexivity. Qed.

  Lemma rswap_invol {T} (e : rexpr T) : ev_eq (rswap (rswap e)) e.
  Proof.
    intros rm; rewrite !ev_rswap, rcmem_swap_invol; reflexivity.
  Qed.

  (** [idx] and [rswap] interact the way rule Sym needs. *)
  Lemma rswap_idx {T} (s : side) (e : expr T) :
    ev_eq (rswap (idx s e)) (idx (swap s) e).
  Proof.
    intros rm; rewrite ev_rswap, !ev_idx, csel_swap; reflexivity.
  Qed.

End ExprTheory.
