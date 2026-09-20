(** * Program variables, memories, and the two sides of a judgment.

    Section 2 ("Variables") and the opening of section 5 ("Tagged variables").

    The paper fixes a set [V] of program variables and then works with two
    disjoint tagged copies [V1], [V2], related to [V] by variable renamings
    [idx_1], [idx_2]. It also warns the reader (section 2, "A note on
    notation") that the resulting isomorphisms are pure overhead:

      "We recommend, upon first reading, to ignore all these isomorphisms
       (specifically [idx_1], [idx_2], [U_rename,...], [E_rename,...]), i.e.,
       assume that they are the identity."

    We make that literally true. Rather than building [V1] and [V2] as fresh
    variable sets, we index the relational memory by [side * var]. Then:

      - [idx_1] and [idx_2] are projections, not renamings;
      - the renaming [sigma] of rule Sym is the involution [swap] on [side];
      - [l2[V1^qu V2^qu]] is [l2 (qmem * qmem)], which is exactly the shape the
        substrate's [tensorv] produces, so no reindexing is needed to talk
        about the two sides as tensor factors.

    A large fraction of Appendix A's notational overhead disappears with this. *)

From QRHL.Substrate Require Import Ambient.

(** The variable context. A program is verified against a fixed, global set of
    variables, exactly as in the paper: "Fix some set V of variables relative
    to which the semantics will be defined". *)
Module Type PROGRAM_VARS.

  Parameter cvar : Type.
  Parameter qvar : Type.

  (** "A program variable x is an identifier annotated with a set [Type_x]".
      For classical [x], [ctype x] is the set of values it can store; for
      quantum [q], [qtype q] is the set [q] can hold superpositions of. *)
  Parameter ctype : cvar -> Type.
  Parameter qtype : qvar -> Type.

  (** Needed to define memory update. *)
  Parameter cvar_eq_dec : forall x y : cvar, {x = y} + {x <> y}.
  Parameter qvar_eq_dec : forall q r : qvar, {q = r} + {q <> r}.

  (** "[Type_x] <> {}" -- variable types are nonempty. *)
  Parameter ctype_inhab : forall x, ctype x.
  Parameter qtype_inhab : forall q, qtype q.

End PROGRAM_VARS.

Module VarTheory (V : PROGRAM_VARS).
  Include V.

  (* ================================================================= *)
  (** ** Memories

      [Type^set_V], the dependent product [prod_{x in V} Type_x]. Because [V]
      is global and fixed, memories are *total* functions and no dependent
      subsets are needed anywhere. *)

  Definition cmem : Type := forall x : cvar, ctype x.
  Definition qmem : Type := forall q : qvar, qtype q.

  (** Memories exist: needed to know [cmem] is inhabited when reasoning about
      expressions. *)
  Definition cmem0 : cmem := fun x => ctype_inhab x.
  Definition qmem0 : qmem := fun q => qtype_inhab q.

  (** *** Update

      The paper's [f(x := y)]: "[f(x := y)](x) = y and [f(x := y)](x') = f(x')
      for [x' <> x]". *)

  Definition cupd (m : cmem) (x : cvar) (a : ctype x) : cmem :=
    fun y =>
      match cvar_eq_dec x y with
      | left H  => eq_rect x ctype a y H
      | right _ => m y
      end.

  Lemma cupd_same (m : cmem) (x : cvar) (a : ctype x) : cupd m x a x = a.
  Proof.
    unfold cupd; destruct (cvar_eq_dec x x) as [H | H]; [| congruence ].
    (* [H : x = x] is [eq_refl] by proof irrelevance, so the transport is trivial *)
    rewrite (proof_irrel _ H eq_refl); reflexivity.
  Qed.

  Lemma cupd_other (m : cmem) (x y : cvar) (a : ctype x) :
    x <> y -> cupd m x a y = m y.
  Proof.
    intros Hxy; unfold cupd.
    destruct (cvar_eq_dec x y) as [H | H]; [ contradiction | reflexivity ].
  Qed.

  (** Updating with the value already there changes nothing. *)
  Lemma cupd_id (m : cmem) (x : cvar) : cupd m x (m x) = m.
  Proof.
    apply funext; intros y; unfold cupd.
    destruct (cvar_eq_dec x y) as [H | H]; [| reflexivity ].
    destruct H; reflexivity.
  Qed.

  Lemma cupd_cupd (m : cmem) (x : cvar) (a b : ctype x) :
    cupd (cupd m x a) x b = cupd m x b.
  Proof.
    apply funext; intros y; unfold cupd.
    destruct (cvar_eq_dec x y); reflexivity.
  Qed.

  (* ================================================================= *)
  (** ** The two sides

      In place of the paper's tagged variable sets [V1], [V2]. *)

  Inductive side : Set := SL | SR.

  Definition swap (s : side) : side := match s with SL => SR | SR => SL end.

  Lemma swap_invol (s : side) : swap (swap s) = s.
  Proof. destruct s; reflexivity. Qed.

  Lemma side_eq_dec (s t : side) : {s = t} + {s <> t}.
  Proof. destruct s, t; auto; right; discriminate. Defined.

  (** A boolean side test. Sets of variables are boolean predicates, and a
      [sumbool] produced by a tactic script does not reduce, so tagging a
      variable set with a side wants this rather than [side_eq_dec]. *)
  Definition side_eqb (s t : side) : bool :=
    match s, t with
    | SL, SL => true
    | SR, SR => true
    | _, _   => false
    end.

  Lemma side_eqb_spec (s t : side) : side_eqb s t = true <-> s = t.
  Proof. destruct s, t; split; intros H; try reflexivity; discriminate. Qed.

  (** Relational memories.

      The classical side stays a plain pair: classical memories are only ever
      used as *indices* (of expressions and of cq-state families), so nothing
      is gained by making them dependent.

      The quantum side is a dependent product over [side * qvar], matching the
      shape of [qmem]. That is what lets the *same* register machinery
      (Registers.v) serve both [qmem] and [rqmem]: a register is a set of
      variables of whatever the ambient variable type is. The bijection
      [rqmem ~= qmem * qmem], needed for the partial traces of Definition 35,
      is then a two-line case split rather than another padded encoding. *)

  Definition rcmem : Type := (cmem * cmem)%type.

  Definition rqvar : Type := (side * qvar)%type.
  Definition rqtype (w : rqvar) : Type := qtype (snd w).
  Definition rqmem : Type := forall w : rqvar, rqtype w.

  Definition csel (s : side) (rm : rcmem) : cmem :=
    match s with SL => fst rm | SR => snd rm end.
  Definition qsel (s : side) (rm : rqmem) : qmem := fun q => rm (s, q).

  (** [rqmem ~= qmem * qmem]. *)
  Definition rq_pair (m : rqmem) : qmem * qmem := (qsel SL m, qsel SR m).

  Definition rq_unpair (fg : qmem * qmem) : rqmem :=
    fun w => match w as w' return rqtype w' with
             | (SL, q) => fst fg q
             | (SR, q) => snd fg q
             end.

  Lemma rq_pair_unpair (fg : qmem * qmem) : rq_pair (rq_unpair fg) = fg.
  Proof. destruct fg; reflexivity. Qed.

  Lemma rq_unpair_pair (m : rqmem) : rq_unpair (rq_pair m) = m.
  Proof.
    apply funext; intros [s q]; destruct s; reflexivity.
  Qed.

  Definition rcmem_swap (rm : rcmem) : rcmem := (snd rm, fst rm).
  Definition rqmem_swap (rm : rqmem) : rqmem :=
    fun w => rm (swap (fst w), snd w).

  Lemma csel_swap (s : side) (rm : rcmem) :
    csel s (rcmem_swap rm) = csel (swap s) rm.
  Proof. destruct s, rm; reflexivity. Qed.

  Lemma rcmem_swap_invol (rm : rcmem) : rcmem_swap (rcmem_swap rm) = rm.
  Proof. destruct rm; reflexivity. Qed.

  Lemma rqmem_swap_invol (rm : rqmem) : rqmem_swap (rqmem_swap rm) = rm.
  Proof.
    apply funext; intros [s q]; unfold rqmem_swap; cbn [fst snd].
    rewrite swap_invol; reflexivity.
  Qed.

  (** *** Relational variables

      A variable of the combined context [V1 V2] is a variable of [V] tagged
      with a side. The paper writes [x_1] for [idx_1(x)]; here that is
      [(SL, x)]. *)

  Definition rcvar : Type := (side * cvar)%type.
  Definition rctype (rx : rcvar) : Type := ctype (snd rx).

  (** [rqvar] and [rqtype] are declared above, with [rqmem]. *)

  Definition rcget (rx : rcvar) (rm : rcmem) : rctype rx :=
    csel (fst rx) rm (snd rx).

  Lemma rcvar_eq_dec (rx ry : rcvar) : {rx = ry} + {rx <> ry}.
  Proof.
    destruct rx as [s x], ry as [t y].
    destruct (side_eq_dec s t) as [-> |]; [| right; congruence ].
    destruct (cvar_eq_dec x y) as [-> |]; [ left; reflexivity | right; congruence ].
  Qed.

  Lemma rqvar_eq_dec (w w' : rqvar) : {w = w'} + {w <> w'}.
  Proof.
    destruct w as [s q], w' as [t r].
    destruct (side_eq_dec s t) as [-> |]; [| right; congruence ].
    destruct (qvar_eq_dec q r) as [-> |]; [ left; reflexivity | right; congruence ].
  Qed.

  (** Update of a relational memory on one side. *)
  Definition rcupd (rm : rcmem) (rx : rcvar) (a : rctype rx) : rcmem :=
    match fst rx as s return rcmem with
    | SL => (cupd (fst rm) (snd rx) a, snd rm)
    | SR => (fst rm, cupd (snd rm) (snd rx) a)
    end.

End VarTheory.
