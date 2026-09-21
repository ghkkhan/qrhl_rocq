(** * Program syntax, typing, and free variables.

    Section 3.2. The grammar:

<<
      c, d ::= skip                            (no operation)
             |  x <- e                         (classical assignment)
             |  x <-$ e                        (classical sampling)
             |  if e then c else d             (conditional)
             |  while e do c                   (loop)
             |  c; d                           (sequential composition)
             |  q1...qn <-q e                  (initialization of q. registers)
             |  apply e to q1...qn             (quantum application)
             |  x <- measure q1...qn with e    (measurement)
>>

    Programs are deep-embedded: the rules are syntax-directed, so the syntax
    has to be a datatype we can recurse on. Expressions, by contrast, are
    shallow (see [Expr.v]) -- which is what the paper itself recommends.

    The paper's typing rules split in two. The *shape* constraints
    ([Type^exp_e ⊆ Type_x] for assignment, [⊆ D≤1(Type_x)] for sampling, and so
    on) are carried by the constructor types, so an ill-shaped program does not
    typecheck. The *analytic* side conditions -- that an initialization state is
    normalized, that an applied operator is an isometry, that a measurement is
    a projective measurement -- cannot live in a type, so they are collected in
    the predicate [wt]. The paper handles this the same way:

      "In this paper, we will only consider well-typed programs. That is,
       'program' implicitly means 'well-typed program', and all derivation
       rules hold under the implicit assumption that the programs in premises
       and conclusions are well-typed." *)

From Stdlib Require Import List.
From QRHL.Substrate Require Import Ambient Cnum Sums Interface Theory.
From QRHL.Core Require Import Vars Expr Registers.

Module SyntaxTheory (S : HILBERT_SUBSTRATE) (V : PROGRAM_VARS).
  Include RegTheory S V.

  (* ================================================================= *)
  (** ** Quantum statements are indexed by variable *sets*

      DESIGN NOTE, and a deliberate departure from the paper's presentation.

      The paper types the operator in [apply e to Q] as acting on
      [Type^list_Q], an *ordered* tuple, and then inserts the canonical
      isomorphism [U_vars,Q : l2(Type^list_Q) -> l2[Q]] into the semantics to
      move it onto the set-indexed space where the rest of the memory lives:

          U := U_vars,Q [e]_m U_vars,Q^*  (x)  id

      We index quantum statements by a [qset] instead, so the operator already
      acts on [qsub P] and that conjugation is the identity. The paper itself
      treats these conversions as noise -- "Similar natural conversions occur
      in the following rules as well, we will ignore them in our informal
      discussions" (section 5.1, on rule QInit1).

      Two things fall out. First, [Type^list_Q] required [Q] to be a list of
      *distinct* variables, a side condition on every quantum statement and
      every quantum rule; a set has no duplicates, so the condition disappears.
      Second, [U_vars,Q] is no longer part of the semantics at all -- it
      becomes a convenience layer for *writing* concrete programs, needed only
      where an example supplies a gate as a matrix on an ordered tuple.

      [qtlist] is kept because it is the paper's notion and the target of that
      convenience layer. *)

  Fixpoint qtlist (Q : list qvar) : Type :=
    match Q with
    | nil     => unit
    | q :: Qs => (qtype q * qtlist Qs)%type
    end.

  (* ================================================================= *)
  (** ** Measurements

      [Meas(D, E)] (section 2): "the set of functions [M : D -> B(E)] such that
      [M(z)] is a projector for all [z], and [sum_z M(z) <= id]. We call a
      measurement total iff [sum_z M(z) = id]."

      The bound is stated through inner products rather than through a sum of
      operators. It is equivalent, and it means the substrate needs sums of
      nonnegative reals (which [Sums.v] already provides) instead of sums of
      operators -- keeping the trusted surface smaller. *)

  Definition meas_bound {D E} (M : D -> op E E) (v : l2 E) : R :=
    tsum (fun z => Cre (inner v (oapp (M z) v))).

  Definition is_meas {D E} (M : D -> op E E) : Prop :=
    (forall z, oprojector (M z)) /\
    (forall v, summable (fun z => Cre (inner v (oapp (M z) v)))) /\
    (forall v, (meas_bound M v <= Cre (inner v v))%R).

  Definition is_total_meas {D E} (M : D -> op E E) : Prop :=
    (forall z, oprojector (M z)) /\
    (forall v, summable (fun z => Cre (inner v (oapp (M z) v)))) /\
    (forall v, meas_bound M v = Cre (inner v v)).

  Lemma total_meas_is_meas {D E} (M : D -> op E E) :
    is_total_meas M -> is_meas M.
  Proof.
    intros [H1 [H2 H3]]; split; [ exact H1 |]; split; [ exact H2 |].
    intros v; rewrite (H3 v); apply Rle_refl.
  Qed.

  (* ================================================================= *)
  (** ** The grammar *)

  Inductive prog : Type :=
  | Skip   : prog
  (** [x <- e] *)
  | Assign : forall (x : cvar), expr (ctype x) -> prog
  (** [x <-$ e]; "[e] evaluates to a distribution" *)
  | Sample : forall (x : cvar), expr (distr (ctype x)) -> prog
  (** [if e then c else d] *)
  | Cond   : expr bool -> prog -> prog -> prog
  (** [while e do c] *)
  | While  : expr bool -> prog -> prog
  (** [c; d] *)
  | Seq    : prog -> prog -> prog
  (** [Q <-q e]; "[e] evaluates to a pure quantum state, [q1...qn] are jointly
      initialized to that state" *)
  | QInit  : forall (P : qset), expr (l2 (qsub P)) -> prog
  (** [apply e to Q]; "[e] evaluates to an isometry that is applied to
      [q1...qn]" *)
  | QApply : forall (P : qset), expr (op (qsub P) (qsub P)) -> prog
  (** [x <- measure Q with e]; "[e] evaluates to a projective measurement, the
      outcome is stored in [x]" *)
  | Measure : forall (x : cvar) (P : qset),
      expr (ctype x -> op (qsub P) (qsub P)) -> prog.

  (* ================================================================= *)
  (** ** Well-typedness

      The analytic side conditions of section 3.2, plus distinctness of the
      variable lists (which the paper builds into the notion of a quantum
      register). *)

  Fixpoint wt (c : prog) : Prop :=
    match c with
    | Skip           => True
    | Assign _ _     => True
    | Sample _ _     => True
    | Cond _ c1 c2   => wt c1 /\ wt c2
    | While _ c1     => wt c1
    | Seq c1 c2      => wt c1 /\ wt c2
    (** "[‖psi‖ = 1] for all [psi in Type^exp_e]" *)
    | QInit _ e      => forall m, inner (ev e m) (ev e m) = C1
    (** "[Type^exp_e ⊆ Iso(Type^list_Q)]" *)
    | QApply _ e     => forall m, oisometry (ev e m)
    (** "[Type^exp_e ⊆ Meas(Type_x, l2(Type^list_Q))]" *)
    | Measure _ _ e  => forall m, is_meas (ev e m)
    end.

  (* ================================================================= *)
  (** ** Free variables

      Section 3.2: [fv(c)] "consists of the classical variables [fv(e)] for all
      expressions [e] occurring in [c], the classical variables [x] in subterms
      [x <- e], [x <-$ e], [x <- measure Q with e], and all quantum variables
      [Q] in subterms [Q <-q e], [apply e to Q], [x <- measure Q with e]."

      Split into its classical and quantum halves, since every rule that uses
      free variables (Frame, Equal, QrhlElimEq) treats them differently:
      read-only classical variables may occur in a frame, quantum variables may
      not -- "Measuring a quantum variable modifies it, so there is no obvious
      concept of a read-only quantum variable" (footnote 15). *)

  Fixpoint cfv (c : prog) : cvar -> Prop :=
    match c with
    | Skip            => fun _ => False
    | Assign x e      => fun y => y = x \/ efv e y
    | Sample x e      => fun y => y = x \/ efv e y
    | Cond e c1 c2    => fun y => efv e y \/ cfv c1 y \/ cfv c2 y
    | While e c1      => fun y => efv e y \/ cfv c1 y
    | Seq c1 c2       => fun y => cfv c1 y \/ cfv c2 y
    | QInit _ e       => fun y => efv e y
    | QApply _ e      => fun y => efv e y
    | Measure x _ e   => fun y => y = x \/ efv e y
    end.

  Fixpoint qfv (c : prog) : qset :=
    match c with
    | Skip            => fun _ => false
    | Assign _ _      => fun _ => false
    | Sample _ _      => fun _ => false
    | Cond _ c1 c2    => fun r => orb (qfv c1 r) (qfv c2 r)
    | While _ c1      => qfv c1
    | Seq c1 c2       => fun r => orb (qfv c1 r) (qfv c2 r)
    | QInit P _       => P
    | QApply P _      => P
    | Measure _ P _   => P
    end.

  (** The classical variables a program can *write*. Rule Frame allows a frame
      to mention classical variables the programs only read, so the read/write
      distinction has to be available separately from [cfv]. *)
  Fixpoint cwritten (c : prog) : cvar -> Prop :=
    match c with
    | Skip            => fun _ => False
    | Assign x _      => fun y => y = x
    | Sample x _      => fun y => y = x
    | Cond _ c1 c2    => fun y => cwritten c1 y \/ cwritten c2 y
    | While _ c1      => fun y => cwritten c1 y
    | Seq c1 c2       => fun y => cwritten c1 y \/ cwritten c2 y
    | QInit _ _       => fun _ => False
    | QApply _ _      => fun _ => False
    | Measure x _ _   => fun y => y = x
    end.

  Lemma cwritten_cfv (c : prog) (x : cvar) : cwritten c x -> cfv c x.
  Proof. induction c; simpl; tauto. Qed.

  (** Loop-free programs. No longer needed by the semantics: the denotation of
      a loop is an infinite sum of iterates, and the telescoping argument that
      bounds its trace is now in [Semantics.v], so [denote_wf_trace],
      [denote_add] and [denote_sum] hold for every well-typed program. Kept
      because rules that genuinely depend on termination will want it. *)
  Fixpoint loopfree (c : prog) : Prop :=
    match c with
    | While _ _                  => False
    | Cond _ c1 c2 | Seq c1 c2   => loopfree c1 /\ loopfree c2
    | _                          => True
    end.

  (** "We call a program classical iff it does not contain the constructions
      [Q <-q e], [apply e to Q], or [x <- measure Q with e]" (section 3.3). *)
  Fixpoint classical (c : prog) : Prop :=
    match c with
    | Skip | Assign _ _ | Sample _ _ => True
    | Cond _ c1 c2 | Seq c1 c2       => classical c1 /\ classical c2
    | While _ c1                     => classical c1
    | QInit _ _ | QApply _ _ | Measure _ _ _ => False
    end.

  Lemma classical_no_qfv (c : prog) :
    classical c -> forall r, qfv c r = false.
  Proof.
    induction c; simpl; intros Hc r; try reflexivity; try tauto.
    - destruct Hc as [Hc1 Hc2]; rewrite IHc1, IHc2 by assumption; reflexivity.
    - apply IHc; exact Hc.
    - destruct Hc as [Hc1 Hc2]; rewrite IHc1, IHc2 by assumption; reflexivity.
  Qed.

  (* ================================================================= *)
  (** ** Notation

      Close to the paper's, so that the examples read like the paper's
      programs. *)

  Declare Scope prog_scope.
  Delimit Scope prog_scope with prog.
  Open Scope prog_scope.

  Notation "c ';;' d" := (Seq c d)
    (at level 80, right associativity) : prog_scope.
  Notation "x '<-' e" := (Assign x e)
    (at level 75, no associativity) : prog_scope.
  Notation "x '<$-' e" := (Sample x e)
    (at level 75, no associativity) : prog_scope.
  Notation "'IFC' e 'THEN' c 'ELSE' d" := (Cond e c d)
    (at level 78, right associativity) : prog_scope.
  Notation "'WHILE' e 'DO' c" := (While e c)
    (at level 78, right associativity) : prog_scope.
  Notation "P '<q-' e" := (QInit P e)
    (at level 75, no associativity) : prog_scope.
  Notation "'APPLY' e 'TO' P" := (QApply P e)
    (at level 75, no associativity) : prog_scope.
  Notation "x '<-measure' P 'with' e" := (Measure x P e)
    (at level 75, no associativity) : prog_scope.

End SyntaxTheory.
