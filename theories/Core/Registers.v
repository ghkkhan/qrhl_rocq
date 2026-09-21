(** * Quantum registers: splitting the memory, and the lifting [A»Q].

    Definition 19 and the [U_vars,Q] of section 2.

    This is the plumbing the whole development rests on, and the part the plan
    flagged as most likely to go badly. The paper needs, for a set [Q] of
    quantum variables, the canonical isomorphism [l2[V^qu] ~= l2[Q] (x) l2[V\Q]]
    and then defines

        S»Q := U_vars,Q S (x) l2[V^qu \ Q]
        A»Q := U_vars,Q A U_vars,Q^*  (x)  id_{V^qu \ Q}

    Done naively -- by recursion over a list of variables, reassociating tensor
    factors as you go -- this drowns in dependent-type transport. Three choices
    avoid that:

    1. The complement of a set of variables is described by a *predicate*, not
       a list, and the memory splits pointwise:

           wsub P  :=  forall w, if P w then wty w else unit

       so [wsub P * wsub (negb o P) ~= wmem] is proved once, by case analysis on
       [P w] under a [funext], with no recursion at all. The hard-looking
       isomorphism is pointwise-trivial.

    2. Every isomorphism becomes a unitary through the substrate's single
       [Ubij] combinator, so there is one set of laws rather than one per
       reassociation.

    3. The construction is generic in the variable type. qRHL needs registers
       on two different memories -- [qmem], indexed by [qvar], and the
       relational [rqmem], indexed by [side * qvar] -- and a predicate on
       [side * qvar] is exactly what a rule like Equal means by "the variables
       [Y_1 Y_2]". One section, two instantiations. *)

From Stdlib Require Import List Bool.
From QRHL.Substrate Require Import Ambient Cnum Sums Interface Theory.
From QRHL.Core Require Import Vars Expr.

Module RegTheory (S : HILBERT_SUBSTRATE) (V : PROGRAM_VARS).
  Include HTheory S.
  Include ExprTheory V.

  (* ================================================================= *)
  (** ** Boolean-indexed helpers

      Used by the disjoint-union split below. Each abstracts over *both*
      booleans at once and takes the value as an argument, which is what makes
      the dependent types reduce: a match on one boolean alone would not
      change the type of a value indexed by their disjunction. *)

  Definition bmerge (b b' : bool) (T : Type)
    (x : if b then T else unit) (y : if b' then T else unit)
    : (if orb b b' then T else unit) :=
    match b as bb, b' as bb'
          return (if bb then T else unit) -> (if bb' then T else unit) ->
                 (if orb bb bb' then T else unit) with
    | true,  _     => fun a _ => a
    | false, true  => fun _ c => c
    | false, false => fun _ _ => tt
    end x y.

  Definition bpickl (b b' : bool) (T : Type)
    (x : if orb b b' then T else unit) : (if b then T else unit) :=
    match b as bb, b' as bb'
          return (if orb bb bb' then T else unit) -> (if bb then T else unit) with
    | true,  _ => fun y => y
    | false, _ => fun _ => tt
    end x.

  Definition bpickr (b b' : bool) (T : Type)
    (x : if orb b b' then T else unit) : (if b' then T else unit) :=
    match b as bb, b' as bb'
          return (if orb bb bb' then T else unit) -> (if bb' then T else unit) with
    | true,  true  => fun y => y
    | true,  false => fun _ => tt
    | false, true  => fun y => y
    | false, false => fun _ => tt
    end x.

  (* ================================================================= *)
  (** ** Registers, generically in the variable type *)

  Section GenericRegisters.
    Context (W : Type) (wty : W -> Type).

    (** A memory over the variable type [W]: the paper's [Type^set_V]. *)
    Definition wmem : Type := forall w : W, wty w.

    (** A set of variables. *)
    Definition wset : Type := W -> bool.

    Definition wneg (P : wset) : wset := fun w => negb (P w).

    (** The memory restricted to [P], padded with [unit] outside it. The
        padding is what keeps this a plain function type -- not a dependent
        function over a subset -- and so makes the split below pointwise. *)
    Definition wsub (P : wset) : Type :=
      forall w : W, if P w then wty w else unit.

    (* ---------------------------------------------------------------- *)
    (** *** The split *)

    Definition wjoin (P : wset) (fg : wsub P * wsub (wneg P)) : wmem :=
      fun w =>
        match P w as b
              return (if b then wty w else unit) ->
                     (if negb b then wty w else unit) -> wty w with
        | true  => fun a _ => a
        | false => fun _ b => b
        end (fst fg w) (snd fg w).

    Definition wsplitL (P : wset) (m : wmem) : wsub P :=
      fun w => match P w as b return (if b then wty w else unit) with
               | true  => m w
               | false => tt
               end.

    Definition wsplitR (P : wset) (m : wmem) : wsub (wneg P) :=
      fun w => match P w as b return (if negb b then wty w else unit) with
               | true  => tt
               | false => m w
               end.

    Definition wsplit (P : wset) (m : wmem) : wsub P * wsub (wneg P) :=
      (wsplitL P m, wsplitR P m).

    Lemma wsplit_wjoin (P : wset) (fg : wsub P * wsub (wneg P)) :
      wsplit P (wjoin P fg) = fg.
    Proof.
      destruct fg as [f g].
      (* [wneg] and [wsub] must be unfolded *in the types of f and g* before the
         case analysis, or abstracting over [P w] leaves [wneg P w] behind and
         the dependent match no longer typechecks. *)
      cbv [wsplit wsplitL wsplitR wjoin wneg wsub] in *; cbn [fst snd].
      f_equal; apply funext; intros w; generalize (f w), (g w);
        destruct (P w); intros a b; cbn;
        solve [ reflexivity | destruct a; reflexivity | destruct b; reflexivity ].
    Qed.

    Lemma wjoin_wsplit (P : wset) (m : wmem) : wjoin P (wsplit P m) = m.
    Proof.
      apply funext; intros w.
      unfold wjoin, wsplit, wsplitL, wsplitR; cbn [fst snd].
      destruct (P w); reflexivity.
    Qed.

    (* ---------------------------------------------------------------- *)
    (** *** Disjoint union of two registers

        Definition 27 needs the memory split *three* ways -- into [Q1], [Q2]
        and the rest -- because quantum equality swaps the contents of two
        registers. [wsplit] above splits a memory in two; this splits a
        register in two, and composing them gives the three-way split. *)

    Definition wunion (P P' : wset) : wset := fun w => orb (P w) (P' w).

    Definition wdisj (P P' : wset) : Prop :=
      forall w, P w = true -> P' w = false.

    Definition wjoin2 (P P' : wset) (fg : wsub P * wsub P')
      : wsub (wunion P P') :=
      fun w => bmerge (P w) (P' w) (wty w) (fst fg w) (snd fg w).

    Definition wsplit2 (P P' : wset) (m : wsub (wunion P P'))
      : wsub P * wsub P' :=
      (fun w => bpickl (P w) (P' w) (wty w) (m w),
       fun w => bpickr (P w) (P' w) (wty w) (m w)).

    Lemma wsplit2_wjoin2 (P P' : wset) (Hd : wdisj P P') fg :
      wsplit2 P P' (wjoin2 P P' fg) = fg.
    Proof.
      destruct fg as [f g].
      cbv [wsplit2 wjoin2 wunion wsub] in *; cbn [fst snd].
      f_equal; apply funext; intros w;
        specialize (Hd w); generalize (f w) (g w); revert Hd;
        destruct (P w), (P' w); intros Hd a b; cbn in *;
        solve [ reflexivity
              | destruct a; reflexivity
              | destruct b; reflexivity
              | discriminate (Hd eq_refl) ].
    Qed.

    Lemma wjoin2_wsplit2 (P P' : wset) (Hd : wdisj P P') m :
      wjoin2 P P' (wsplit2 P P' m) = m.
    Proof.
      cbv [wjoin2 wsplit2 wunion wsub] in *.
      apply funext; intros w; cbn [fst snd].
      specialize (Hd w); generalize (m w); revert Hd;
        destruct (P w), (P' w); intros Hd x; cbn in *;
        solve [ reflexivity
              | destruct x; reflexivity
              | discriminate (Hd eq_refl) ].
    Qed.

    Definition Wsplit2 (P P' : wset) (Hd : wdisj P P')
      : op (wsub P * wsub P') (wsub (wunion P P')) :=
      Ubij (wjoin2 P P') (wsplit2 P P')
           (wsplit2_wjoin2 P P' Hd) (wjoin2_wsplit2 P P' Hd).

    Lemma Wsplit2_unitary (P P' : wset) (Hd : wdisj P P') :
      ounitary (Wsplit2 P P' Hd).
    Proof. apply Ubij_ounitary. Qed.

    Lemma Wsplit2_adj (P P' : wset) (Hd : wdisj P P') :
      oadj (Wsplit2 P P' Hd)
      = Ubij (wsplit2 P P') (wjoin2 P P')
             (wjoin2_wsplit2 P P' Hd) (wsplit2_wjoin2 P P' Hd).
    Proof. apply Ubij_adj. Qed.

    (* ---------------------------------------------------------------- *)
    (** *** ... as a unitary

        The paper's [U_vars,Q]. *)

    Definition Wsplit (P : wset) : op (wsub P * wsub (wneg P)) wmem :=
      Ubij (wjoin P) (wsplit P) (wsplit_wjoin P) (wjoin_wsplit P).

    Lemma Wsplit_unitary (P : wset) : ounitary (Wsplit P).
    Proof. apply Ubij_ounitary. Qed.

    Lemma Wsplit_ket (P : wset) (fg : wsub P * wsub (wneg P)) :
      oapp (Wsplit P) (ket fg) = ket (wjoin P fg).
    Proof. apply Ubij_ket. Qed.

    Lemma Wsplit_adj (P : wset) :
      oadj (Wsplit P)
      = Ubij (wsplit P) (wjoin P) (wjoin_wsplit P) (wsplit_wjoin P).
    Proof. apply Ubij_adj. Qed.

    (* ---------------------------------------------------------------- *)
    (** *** Lifting (Definition 19)

        [A] acts on the variables in [P], is extended by the identity on the
        rest, and is transported to the whole memory by [Wsplit]. *)

    Definition wolift (P : wset) (A : op (wsub P) (wsub P)) : op wmem wmem :=
      ocomp (Wsplit P) (ocomp (tensoro A oid) (oadj (Wsplit P))).

    Definition whlift (P : wset) (T : hspace (wsub P)) : hspace wmem :=
      himg (Wsplit P) (htensor T htop).

    Lemma whlift_htop (P : wset) : whlift P htop = htop.
    Proof.
      unfold whlift; rewrite htensor_top.
      apply hle_antisym; [ apply hle_htop |].
      (* [Wsplit] is surjective, so the image of the full space is full *)
      intros v _.
      rewrite <- (oapp_oid _ v).
      destruct (Wsplit_unitary P) as [_ Hsurj].
      rewrite <- Hsurj, oapp_ocomp.
      apply hmem_himg, hmem_htop.
    Qed.

    Lemma whlift_hbot (P : wset) : whlift P hbot = hbot.
    Proof. unfold whlift; rewrite htensor_hbot_l; apply himg_hbot. Qed.

    Lemma whlift_mono (P : wset) (T U : hspace (wsub P)) :
      hle T U -> hle (whlift P T) (whlift P U).
    Proof.
      intros H; unfold whlift; apply himg_mono, htensor_mono;
        [ exact H | apply hle_refl ].
    Qed.

    Lemma wolift_oid (P : wset) : wolift P oid = oid.
    Proof.
      unfold wolift; rewrite tensoro_oid.
      destruct (Wsplit_unitary P) as [_ H].
      apply op_ext; intros v.
      rewrite !oapp_ocomp, oapp_oid, <- oapp_ocomp, H, oapp_oid; reflexivity.
    Qed.

    (** *** [wolift] is a unital [*]-homomorphism

        Conjugation by a unitary and tensoring with the identity are both
        [*]-homomorphisms, so the composite is one. These are what make a
        lifted isometry an isometry and a lifted projector a projector -- the
        facts the semantics of [apply] and of measurement need. *)

    Lemma oapp_wolift (P : wset) (A : op (wsub P) (wsub P)) (v : l2 wmem) :
      oapp (wolift P A) v
      = oapp (Wsplit P) (oapp (tensoro A oid) (oapp (oadj (Wsplit P)) v)).
    Proof. unfold wolift; rewrite !oapp_ocomp; reflexivity. Qed.

    Lemma wolift_ocomp (P : wset) (A B : op (wsub P) (wsub P)) :
      wolift P (ocomp A B) = ocomp (wolift P A) (wolift P B).
    Proof.
      destruct (Wsplit_unitary P) as [Hiso _].
      apply op_ext; intros v.
      rewrite oapp_ocomp, !oapp_wolift.
      rewrite <- (oapp_ocomp _ _ _ (oadj (Wsplit P)) (Wsplit P)), Hiso, oapp_oid.
      f_equal.
      transitivity (oapp (ocomp (tensoro A oid) (tensoro B oid))
                         (oapp (oadj (Wsplit P)) v)).
      - f_equal; rewrite <- tensoro_ocomp, ocomp_oid_l; reflexivity.
      - rewrite oapp_ocomp; reflexivity.
    Qed.

    Lemma wolift_oadj (P : wset) (A : op (wsub P) (wsub P)) :
      oadj (wolift P A) = wolift P (oadj A).
    Proof.
      unfold wolift.
      rewrite !oadj_ocomp, oadj_invol, tensoro_oadj, oadj_oid, ocomp_assoc.
      reflexivity.
    Qed.

    Lemma wolift_isometry (P : wset) (A : op (wsub P) (wsub P)) :
      oisometry A -> oisometry (wolift P A).
    Proof.
      unfold oisometry; intros HA.
      rewrite wolift_oadj, <- wolift_ocomp, HA; apply wolift_oid.
    Qed.

    Lemma wolift_projector (P : wset) (A : op (wsub P) (wsub P)) :
      oprojector A -> oprojector (wolift P A).
    Proof.
      intros [H1 H2]; split.
      - rewrite <- wolift_ocomp, H1; reflexivity.
      - rewrite wolift_oadj, H2; reflexivity.
    Qed.

    (** A lifted isometry preserves the trace. *)
    Lemma tcp_trace_conj_wolift (P : wset) (A : op (wsub P) (wsub P))
          (r : tcp wmem) :
      oisometry A -> tcp_trace (tcp_conj (wolift P A) r) = tcp_trace r.
    Proof.
      intros HA; apply tcp_trace_conj_isometry, wolift_isometry, HA.
    Qed.

  End GenericRegisters.

  (* ================================================================= *)
  (** ** The single-sided instance: registers on [qmem]

      [wmem qvar qtype] is [qmem] on the nose, so these are notations rather
      than definitions and every generic lemma above applies unchanged. *)

  Notation qset   := (wset qvar).
  Notation qsub   := (wsub qvar qtype).
  Notation qneg   := (wneg qvar).
  Notation Usplit := (Wsplit qvar qtype).
  Notation olift  := (wolift qvar qtype).
  Notation hlift  := (whlift qvar qtype).

  (** Membership in a list of variables, as a set. *)
  Definition qin (Q : list qvar) : qset :=
    fun q => if in_dec qvar_eq_dec q Q then true else false.

  Lemma qin_spec (Q : list qvar) (q : qvar) : qin Q q = true <-> In q Q.
  Proof.
    unfold qin; destruct (in_dec qvar_eq_dec q Q); split; auto; discriminate.
  Qed.

  (** The full memory is [wsub] of the always-true set, definitionally. *)
  Lemma qsub_true : qsub (fun _ => true) = qmem.
  Proof. reflexivity. Qed.

  (* ================================================================= *)
  (** ** The relational instance: registers on [rqmem]

      A relational quantum variable is a variable of [V] tagged with a side, so
      a relational register is a set of those -- which is exactly what rules
      like Equal and Frame mean by "the variables [Y_1 Y_2]". *)

  Notation rqset   := (wset rqvar).
  Notation rqsub   := (wsub rqvar rqtype).
  Notation rqneg   := (wneg rqvar).
  Notation rUsplit := (Wsplit rqvar rqtype).
  Notation rolift  := (wolift rqvar rqtype).
  Notation rhlift  := (whlift rqvar rqtype).

  (** Tag a single-sided set of variables with a side: the paper's [idx_i Y]. *)
  Definition qidx (s : side) (P : qset) : rqset :=
    fun w => andb (side_eqb (fst w) s) (P (snd w)).

  Lemma qidx_spec (s t : side) (P : qset) (q : qvar) :
    qidx s P (t, q) = andb (side_eqb t s) (P q).
  Proof. reflexivity. Qed.

  Lemma qidx_same (s : side) (P : qset) (q : qvar) :
    qidx s P (s, q) = P q.
  Proof. unfold qidx; cbn [fst snd]; destruct s; reflexivity. Qed.

  (** The two sides are disjoint registers. *)
  Lemma qidx_disjoint (P P' : qset) (w : rqvar) :
    qidx SL P w = true -> qidx SR P' w = false.
  Proof.
    destruct w as [s q]; unfold qidx; cbn [fst snd]; destruct s; cbn.
    - reflexivity.
    - discriminate.
  Qed.

  (** The complement of one side's copy of a register splits into that side's
      copy of the register's own complement, disjointly from the other side
      (which is untouched). This is the load-bearing identity for reconciling
      the relational register split with the side-split-then-register-split
      picture -- see [QInit1] / Lemma 32. *)
  Lemma rqneg_qidx (Q : qset) :
    rqneg (qidx SL Q) = wunion rqvar (qidx SL (qneg Q)) (qidx SR (fun _ => true)).
  Proof.
    apply funext; intros [s q]; unfold wneg, wunion, qidx, qneg;
      cbn [fst snd]; destruct s; cbn; destruct (Q q); reflexivity.
  Qed.

  (** One side's copy of a register is just that register, relabeled: the
      unit-padding a relational register carries over the *other* side is
      pure overhead, since [qidx s Q] is false everywhere on that side. This
      is the other piece the reassociation needs, alongside [rqneg_qidx]. *)
  Definition Urelab_fwd (s : side) (Q : qset) : rqsub (qidx s Q) -> qsub Q :=
    match s as s0 return rqsub (qidx s0 Q) -> qsub Q with
    | SL => fun m q => m (SL, q)
    | SR => fun m q => m (SR, q)
    end.

  Definition Urelab_bwd (s : side) (Q : qset) : qsub Q -> rqsub (qidx s Q) :=
    match s as s0 return qsub Q -> rqsub (qidx s0 Q) with
    | SL => fun m w => match w as w' return (if qidx SL Q w' then rqtype w' else unit) with
                        | (SL, q) => m q
                        | (SR, q) => tt
                        end
    | SR => fun m w => match w as w' return (if qidx SR Q w' then rqtype w' else unit) with
                        | (SL, q) => tt
                        | (SR, q) => m q
                        end
    end.

  Lemma Urelab_fwd_bwd (s : side) (Q : qset) (m : qsub Q) :
    Urelab_fwd s Q (Urelab_bwd s Q m) = m.
  Proof. destruct s; reflexivity. Qed.

  Lemma Urelab_bwd_fwd (s : side) (Q : qset) (m : rqsub (qidx s Q)) :
    Urelab_bwd s Q (Urelab_fwd s Q m) = m.
  Proof.
    destruct s; apply funext; intros [t q]; destruct t; try reflexivity;
      match goal with |- _ = ?x => destruct x; reflexivity end.
  Qed.

  Definition Urelab (s : side) (Q : qset) : op (rqsub (qidx s Q)) (qsub Q) :=
    Ubij (Urelab_fwd s Q) (Urelab_bwd s Q) (Urelab_bwd_fwd s Q) (Urelab_fwd_bwd s Q).

  Lemma Urelab_unitary (s : side) (Q : qset) : ounitary (Urelab s Q).
  Proof. apply Ubij_ounitary. Qed.

  (* ================================================================= *)
  (** ** Splitting the relational memory into its two sides

      Definition 35 takes partial traces [tr^{[V1]}_{V2}] and [tr^{[V2]}_{V1}],
      which need [l2[V1^qu V2^qu] ~= l2[V1^qu] (x) l2[V2^qu]]. Since [rqmem] is
      a dependent product over [side * qvar], that bijection is a case split on
      the side -- no padding, no recursion. *)

  Definition Urqpair : op rqmem (qmem * qmem) :=
    Ubij rq_pair rq_unpair rq_unpair_pair rq_pair_unpair.

  Lemma Urqpair_unitary : ounitary Urqpair.
  Proof. apply Ubij_ounitary. Qed.

  Lemma Urqpair_ket (m : rqmem) : oapp Urqpair (ket m) = ket (rq_pair m).
  Proof. apply Ubij_ket. Qed.

  (** The register-coherence identity [QInit1] needs (HANDOFF.md S7d):
      splitting [rqmem] directly along one side's copy of a register agrees,
      on kets, with splitting off that side first ([Urqpair]) and then
      splitting *its* register ([Usplit Q]). Unlike the monolithic dependent
      [Ubij] S7d anticipated, this needs no new bijection at all: both the
      register-half and the untouched-side-half of the complement land in
      their target types *by computation* once the side is concrete (compare
      [Urelab]), so the whole identity is a [wjoin] unfolding plus a
      [destruct] on the memory's side, exactly the [rq_pair_swap] pattern. *)
  Lemma wjoin_qidx_SL (Q : qset) (vq : rqsub (qidx SL Q)) (vw : rqsub (rqneg (qidx SL Q))) :
    wjoin rqvar rqtype (qidx SL Q) (vq, vw)
    = rq_unpair (wjoin qvar qtype Q (Urelab_fwd SL Q vq, fun q => vw (SL, q)), fun q => vw (SR, q)).
  Proof.
    apply funext; intros [t q]; destruct t; reflexivity.
  Qed.

  Lemma rUsplit_qidx_SL_ket (Q : qset) (vq : rqsub (qidx SL Q)) (vw : rqsub (rqneg (qidx SL Q))) :
    oapp (rUsplit (qidx SL Q)) (tensorv (ket vq) (ket vw))
    = oapp (oadj Urqpair)
        (oapp (tensoro (Usplit Q) oid)
           (tensorv (tensorv (oapp (Urelab SL Q) (ket vq)) (ket (fun q => vw (SL, q))))
                    (ket (fun q => vw (SR, q))))).
  Proof.
    set (qL := Urelab_fwd SL Q vq).
    set (qLc := fun q => vw (SL, q)).
    set (qR := fun q => vw (SR, q)).
    transitivity (ket (wjoin rqvar rqtype (qidx SL Q) (vq, vw))).
    { rewrite tensorv_ket; apply Wsplit_ket. }
    transitivity (ket (rq_unpair (wjoin qvar qtype Q (qL, qLc), qR))).
    { f_equal; apply wjoin_qidx_SL. }
    transitivity (oapp (oadj Urqpair) (ket (wjoin qvar qtype Q (qL, qLc), qR))).
    { unfold Urqpair; rewrite Ubij_adj; symmetry; apply Ubij_ket. }
    transitivity (oapp (oadj Urqpair) (tensorv (ket (wjoin qvar qtype Q (qL, qLc))) (ket qR))).
    { f_equal; symmetry; apply tensorv_ket. }
    transitivity (oapp (oadj Urqpair) (tensorv (oapp (Usplit Q) (ket (qL, qLc))) (ket qR))).
    { f_equal; f_equal; symmetry; apply Wsplit_ket. }
    transitivity (oapp (oadj Urqpair)
                    (tensorv (oapp (Usplit Q) (tensorv (ket qL) (ket qLc))) (ket qR))).
    { f_equal; f_equal; f_equal; symmetry; apply tensorv_ket. }
    transitivity (oapp (oadj Urqpair)
                    (tensorv (oapp (Usplit Q) (tensorv (ket qL) (ket qLc))) (oapp oid (ket qR)))).
    { f_equal; f_equal; symmetry; apply oapp_oid. }
    transitivity (oapp (oadj Urqpair)
                    (oapp (tensoro (Usplit Q) oid) (tensorv (tensorv (ket qL) (ket qLc)) (ket qR)))).
    { f_equal; symmetry; apply tensoro_app. }
    f_equal; f_equal; f_equal; f_equal.
    unfold qL; symmetry; apply Ubij_ket.
  Qed.

  (** The side swap on [rqmem], as a [Ubij]. Composing it with [Urqpair] and
      composing [Urqpair] with the factor swap [Uswap] agree -- both send
      [rqmem]'s [(V1,V2)] pairing to [(V2,V1)] -- which is an index
      computation via [op_ext_ket] once both sides are unfolded to their
      [ket] action. *)
  Definition Urqswap : op rqmem rqmem :=
    Ubij rqmem_swap rqmem_swap rqmem_swap_invol rqmem_swap_invol.

  Lemma Urqswap_ket (m : rqmem) : oapp Urqswap (ket m) = ket (rqmem_swap m).
  Proof. apply Ubij_ket. Qed.

  Lemma Urqswap_unitary : ounitary Urqswap.
  Proof. apply Ubij_ounitary. Qed.

  Lemma Urqswap_adj : oadj Urqswap = Urqswap.
  Proof. apply Ubij_adj. Qed.

  Lemma Urqswap_Urqswap : ocomp Urqswap Urqswap = oid.
  Proof.
    apply op_ext_ket; intros m.
    rewrite oapp_ocomp, !Urqswap_ket, rqmem_swap_invol, oapp_oid; reflexivity.
  Qed.

  (** [Urqswap] is onto: every ket [ket m] is [oapp Urqswap] of the ket at
      the swapped memory, so its image contains a spanning set and hence is
      everything. *)
  Lemma oim_Urqswap : oim Urqswap = htop.
  Proof.
    apply hle_antisym; [ apply hle_htop |].
    rewrite <- hspan_ket; apply hspan_le; intros v [m ->].
    assert (Heq : ket m = oapp Urqswap (ket (rqmem_swap m))).
    { rewrite Urqswap_ket, rqmem_swap_invol; reflexivity. }
    rewrite Heq; apply hmem_oim.
  Qed.

  (** Applying [Urqswap] twice to the image of a subspace lands back inside
      it -- the one direction [rule Sym]'s [psat] obligation needs. (The
      other direction, that this is an equality, would need more than the
      isometry-meet-image trick below supplies, and is not needed.) *)
  Lemma himg_Urqswap_shrink (S : hspace rqmem) :
    himg Urqswap (himg Urqswap S) <=h S.
  Proof.
    pose proof (himg_isometry_meet_oim Urqswap S
                  (ounitary_isometry Urqswap Urqswap_unitary)) as H.
    rewrite Urqswap_adj, oim_Urqswap, hmeet_htop in H; exact H.
  Qed.

  Lemma rq_pair_swap (m : rqmem) : rq_pair (rqmem_swap m) = pswap (rq_pair m).
  Proof.
    unfold rq_pair, pswap; cbn [fst snd]; f_equal;
      apply funext; intros q; unfold qsel, rqmem_swap; reflexivity.
  Qed.

  Lemma Urqpair_Urqswap : ocomp Urqpair Urqswap = ocomp Uswap Urqpair.
  Proof.
    apply op_ext_ket; intros m.
    rewrite !oapp_ocomp, Urqswap_ket, Urqpair_ket.
    rewrite Urqpair_ket, Uswap_ket.
    f_equal; apply rq_pair_swap.
  Qed.

  (** [tr^{[V1]}_{V2}]: keep the left side. *)
  Definition rtcpL (r : tcp rqmem) : tcp qmem :=
    tcp_ptrace (tcp_conj Urqpair r).

  (** [tr^{[V2]}_{V1}]: keep the right side. *)
  Definition rtcpR (r : tcp rqmem) : tcp qmem :=
    tcp_ptraceL (tcp_conj Urqpair r).

  Lemma rtcpL_zero : rtcpL tcp_zero = tcp_zero.
  Proof. unfold rtcpL; rewrite tcp_conj_zero; apply tcp_ptrace_zero. Qed.

  Lemma rtcpR_zero : rtcpR tcp_zero = tcp_zero.
  Proof. unfold rtcpR; rewrite tcp_conj_zero; apply tcp_ptraceL_zero. Qed.

  Lemma rtcpL_add (r s : tcp rqmem) :
    rtcpL (tcp_add r s) = tcp_add (rtcpL r) (rtcpL s).
  Proof. unfold rtcpL; rewrite tcp_conj_add, tcp_ptrace_add; reflexivity. Qed.

  Lemma rtcpR_add (r s : tcp rqmem) :
    rtcpR (tcp_add r s) = tcp_add (rtcpR r) (rtcpR s).
  Proof.
    unfold rtcpR; rewrite tcp_conj_add, tcp_ptraceL_add; reflexivity.
  Qed.

  (** Both partial traces preserve the total trace. *)
  Lemma rtcpL_trace (r : tcp rqmem) : tcp_trace (rtcpL r) = tcp_trace r.
  Proof.
    unfold rtcpL; rewrite tcp_ptrace_trace.
    apply tcp_trace_conj_isometry, (proj1 Urqpair_unitary).
  Qed.

  Lemma rtcpR_trace (r : tcp rqmem) : tcp_trace (rtcpR r) = tcp_trace r.
  Proof.
    unfold rtcpR; rewrite tcp_ptraceL_trace.
    apply tcp_trace_conj_isometry, (proj1 Urqpair_unitary).
  Qed.

  (** Swapping the two sides exchanges the two partial traces. *)
  Lemma rtcpL_Urqswap (r : tcp rqmem) :
    rtcpL (tcp_conj Urqswap r) = rtcpR r.
  Proof.
    unfold rtcpL, rtcpR, tcp_ptraceL.
    rewrite <- tcp_conj_ocomp, Urqpair_Urqswap, tcp_conj_ocomp.
    apply tcp_ptrace_Uswap.
  Qed.

  Lemma rtcpR_Urqswap (r : tcp rqmem) :
    rtcpR (tcp_conj Urqswap r) = rtcpL r.
  Proof.
    unfold rtcpL, rtcpR, tcp_ptraceL.
    rewrite <- tcp_conj_ocomp, Urqpair_Urqswap, tcp_conj_ocomp.
    apply tcp_ptrace2_Uswap.
  Qed.

  (** *** Normality

      Both projections commute with infinite sums, which is what lets a witness
      state built as a sum be pushed through them. *)

  Lemma rtcpL_summable {J} (F : J -> tcp rqmem) :
    tcp_summable F -> tcp_summable (fun j => rtcpL (F j)).
  Proof.
    intros Hs; apply tcp_summable_trace.
    apply (summable_mono _ (fun j => tcp_trace (F j))).
    - apply tcp_summable_trace; exact Hs.
    - intros j; rewrite rtcpL_trace; apply Rle_refl.
  Qed.

  Lemma rtcpR_summable {J} (F : J -> tcp rqmem) :
    tcp_summable F -> tcp_summable (fun j => rtcpR (F j)).
  Proof.
    intros Hs; apply tcp_summable_trace.
    apply (summable_mono _ (fun j => tcp_trace (F j))).
    - apply tcp_summable_trace; exact Hs.
    - intros j; rewrite rtcpR_trace; apply Rle_refl.
  Qed.

  Lemma rtcpL_scale (a : R) (r : tcp rqmem) :
    rtcpL (tcp_scale a r) = tcp_scale a (rtcpL r).
  Proof.
    unfold rtcpL; rewrite tcp_conj_scale, tcp_ptrace_scale; reflexivity.
  Qed.

  Lemma rtcpR_scale (a : R) (r : tcp rqmem) :
    rtcpR (tcp_scale a r) = tcp_scale a (rtcpR r).
  Proof.
    unfold rtcpR; rewrite tcp_conj_scale, tcp_ptraceL_scale; reflexivity.
  Qed.

  Lemma rtcpL_sum {J} (F : J -> tcp rqmem) :
    tcp_summable F -> rtcpL (tcp_sum F) = tcp_sum (fun j => rtcpL (F j)).
  Proof.
    intros Hs; unfold rtcpL.
    rewrite (tcp_conj_sum _ _ _ Urqpair F Hs).
    apply tcp_ptrace_sum,
      (tcp_summable_conj Urqpair F (proj1 Urqpair_unitary) Hs).
  Qed.

  Lemma rtcpR_sum {J} (F : J -> tcp rqmem) :
    tcp_summable F -> rtcpR (tcp_sum F) = tcp_sum (fun j => rtcpR (F j)).
  Proof.
    intros Hs; unfold rtcpR, tcp_ptraceL.
    rewrite (tcp_conj_sum _ _ _ Urqpair F Hs).
    apply tcp_ptrace2_sum,
      (tcp_summable_conj Urqpair F (proj1 Urqpair_unitary) Hs).
  Qed.

  (* ================================================================= *)
  (** ** Acting on one side

      The paper writes [A»(idx_1 Q)] for an operator applied to the side-1 copy
      of a register [Q]. Here that is: conjugate through
      [Urqpair : l2[V1^qu V2^qu] ~= l2[V1^qu] (x) l2[V2^qu]] and act on the
      corresponding tensor factor.

      DESIGN NOTE. This is *defined* through [Urqpair] rather than as
      [rolift (qidx SL P)], the relational register carrying the same
      variables. The two agree, but proving that means relating two different
      decompositions of the same memory -- register associativity -- which the
      current signature cannot express: [Wsplit] is built from [Ubij] and so
      has laws only on basis vectors, while the identity in question has a
      general vector in the middle.

      Defining it this way costs nothing for the rules. Every rule that acts on
      one side does so on one side, and "on side i" is exactly what the paper's
      [idx_i] means. The two notions have to be reconciled only for Lemma 32,
      which relates a one-sided lift to a quantum equality spanning both sides;
      that reconciliation is the register-associativity problem, deferred with
      it. *)

  Definition roliftL (P : qset) (A : op (qsub P) (qsub P)) : op rqmem rqmem :=
    ocomp (oadj Urqpair) (ocomp (tensoro (olift P A) oid) Urqpair).

  Definition roliftR (P : qset) (A : op (qsub P) (qsub P)) : op rqmem rqmem :=
    ocomp (oadj Urqpair) (ocomp (tensoro oid (olift P A)) Urqpair).

  Lemma tcp_conj_Urqpair_roundtrip (r : tcp (qmem * qmem)) :
    tcp_conj Urqpair (tcp_conj (oadj Urqpair) r) = r.
  Proof.
    rewrite <- tcp_conj_ocomp, (proj2 Urqpair_unitary); apply tcp_conj_oid.
  Qed.

  (** The other roundtrip, needed by the converse of Lemma 36 to pull a
      spectral decomposition taken on the [tcp_conj Urqpair] side back to
      [rqmem]. *)
  Lemma tcp_conj_adjUrqpair_roundtrip (r : tcp rqmem) :
    tcp_conj (oadj Urqpair) (tcp_conj Urqpair r) = r.
  Proof.
    rewrite <- tcp_conj_ocomp, (proj1 Urqpair_unitary); apply tcp_conj_oid.
  Qed.

  Lemma conj_roliftL (P : qset) (A : op (qsub P) (qsub P)) (r : tcp rqmem) :
    tcp_conj Urqpair (tcp_conj (roliftL P A) r)
    = tcp_conj (tensoro (olift P A) oid) (tcp_conj Urqpair r).
  Proof.
    unfold roliftL; rewrite !tcp_conj_ocomp, tcp_conj_Urqpair_roundtrip;
      reflexivity.
  Qed.

  Lemma conj_roliftR (P : qset) (A : op (qsub P) (qsub P)) (r : tcp rqmem) :
    tcp_conj Urqpair (tcp_conj (roliftR P A) r)
    = tcp_conj (tensoro oid (olift P A)) (tcp_conj Urqpair r).
  Proof.
    unfold roliftR; rewrite !tcp_conj_ocomp, tcp_conj_Urqpair_roundtrip;
      reflexivity.
  Qed.

  (** *** The projections of a one-sided action

      Acting on side L is visible in the left projection and invisible in the
      right one (for an isometry, which is all the rules apply). This is the
      computation every one-sided rule needs in order to show that its witness
      has the two partial traces Definition 35 demands. *)

  Lemma rtcpL_roliftL (P : qset) (A : op (qsub P) (qsub P)) (r : tcp rqmem) :
    rtcpL (tcp_conj (roliftL P A) r) = tcp_conj (olift P A) (rtcpL r).
  Proof.
    unfold rtcpL; rewrite conj_roliftL; apply tcp_ptrace_conj_tensorL.
  Qed.

  Lemma rtcpR_roliftL (P : qset) (A : op (qsub P) (qsub P)) (r : tcp rqmem) :
    oisometry A -> rtcpR (tcp_conj (roliftL P A) r) = rtcpR r.
  Proof.
    intros HA; unfold rtcpR, tcp_ptraceL; rewrite conj_roliftL.
    apply tcp_ptrace2_conj_tensorL, (wolift_isometry qvar qtype P A HA).
  Qed.

  Lemma rtcpR_roliftR (P : qset) (A : op (qsub P) (qsub P)) (r : tcp rqmem) :
    rtcpR (tcp_conj (roliftR P A) r) = tcp_conj (olift P A) (rtcpR r).
  Proof.
    unfold rtcpR, tcp_ptraceL; rewrite conj_roliftR;
      apply tcp_ptrace2_conj_tensorR.
  Qed.

  Lemma rtcpL_roliftR (P : qset) (A : op (qsub P) (qsub P)) (r : tcp rqmem) :
    oisometry A -> rtcpL (tcp_conj (roliftR P A) r) = rtcpL r.
  Proof.
    intros HA; unfold rtcpL; rewrite conj_roliftR.
    apply tcp_ptrace_conj_tensorR, (wolift_isometry qvar qtype P A HA).
  Qed.

  Lemma roliftL_isometry (P : qset) (A : op (qsub P) (qsub P)) :
    oisometry A -> oisometry (roliftL P A).
  Proof.
    intros HA; unfold roliftL.
    apply oisometry_conj;
      [ apply Urqpair_unitary
      | apply oisometry_tensoro_l, (wolift_isometry qvar qtype P A HA) ].
  Qed.

  Lemma roliftL_projector (P : qset) (A : op (qsub P) (qsub P)) :
    oprojector A -> oprojector (roliftL P A).
  Proof.
    intros HA; unfold roliftL.
    apply oprojector_conj;
      [ apply Urqpair_unitary
      | apply oprojector_tensoro_l, (wolift_projector qvar qtype P A HA) ].
  Qed.

  Lemma roliftR_isometry (P : qset) (A : op (qsub P) (qsub P)) :
    oisometry A -> oisometry (roliftR P A).
  Proof.
    intros HA; unfold roliftR.
    apply oisometry_conj;
      [ apply Urqpair_unitary
      | apply oisometry_tensoro_r, (wolift_isometry qvar qtype P A HA) ].
  Qed.

End RegTheory.
