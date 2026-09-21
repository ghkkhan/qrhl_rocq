(** * Denotational semantics.

    Sections 3.3, 3.4 and Definition 9.

    The paper gives [[c]] as a cq-superoperator on [T_cq[V]], specified on the
    cq basis elements [proj(|m>_{V^cl}) (x) rho_m] and extended by linearity --
    which is legitimate because "specifying [[c]] on operators
    [proj(|m>) (x) rho_m] specifies [[c]] on all [rho in T_cq[V]]" (section 3.4).

    We take that decomposition as the *representation* rather than as a
    theorem. A cq-state is a family

        cqs  :=  cmem -> tcp qmem

    indexed by classical memories, which is exactly the data [(rho_m)_m], and
    the semantics is defined directly on families. Two consequences:

    - The clauses below are the paper's, read off literally, with no appeal to
      linear extension.
    - Section 3.4's remark that "any operator in [T[V^qu]] can be written as a
      linear combination of four [rho_a in T^+[V^qu]]" -- the step that
      justifies the linear extension, and the only reason the paper needs the
      full space [T(X)] rather than the positive cone -- never arises. This is
      what lets the substrate axiomatize [T^+] alone (see AXIOMS.md).

    Summability is *not* bundled into [cqs]. Carrying a proof through a
    [Fixpoint] would make every clause a dependent construction; instead the
    clauses are plain functions, and summability is a separate property. See
    the note on [denote_summable] at the end of this file for what is and is
    not yet proved about it.

    Where the paper sums over the preimage of a memory update, we reindex by
    the *old* value of the assigned variable. If [m(x := z) = m'] then
    necessarily [z = m' x] and [m = m'(x := m x)], so the preimage is
    parameterized by [a := m x]; see [assign_preimage] below. This keeps the
    index sets concrete and the point-mass computations tractable. *)

From Stdlib Require Import List Lra.
From QRHL.Substrate Require Import Ambient Cnum Sums Interface Theory.
From QRHL.Core Require Import Vars Expr Registers Syntax.

Module SemTheory (S : HILBERT_SUBSTRATE) (V : PROGRAM_VARS).
  Include SyntaxTheory S V.

  (* ================================================================= *)
  (** ** cq-states

      The paper's [T_cq[V]]: "an operator [rho in T[V]] that can be written as
      [rho = sum_m proj(|m>_{V^cl}) (x) rho_m] with [rho_m in T[V^qu]]"
      (section 2). Here, that family. *)

  Definition cqs : Type := cmem -> tcp qmem.

  Definition cqs_zero : cqs := fun _ => tcp_zero.
  Definition cqs_add (r s : cqs) : cqs := fun m => tcp_add (r m) (s m).
  Definition cqs_scale (a : R) (r : cqs) : cqs := fun m => tcp_scale a (r m).
  Definition cqs_sum {J : Type} (F : J -> cqs) : cqs :=
    fun m => tcp_sum (fun j => F j m).

  (** [rho in T^+_cq[V]] is exactly a family whose traces are summable. *)
  Definition cqs_wf (r : cqs) : Prop := tcp_summable r.

  Definition cqs_trace (r : cqs) : R := tsum (fun m => tcp_trace (r m)).

  Lemma cqs_trace_nonneg (r : cqs) : (0 <= cqs_trace r)%R.
  Proof. apply tsum_nonneg; intros m; apply tcp_trace_nonneg. Qed.

  (** Point masses. The paper's [proj(|m>) (x) rho]: the state whose classical
      part is deterministically [m]. Lemma 36 reduces qRHL to these. *)
  Definition cqdirac (m : cmem) (rho : tcp qmem) : cqs :=
    fun m' => if excluded_middle_informative (m' = m) then rho else tcp_zero.

  Lemma cqdirac_same (m : cmem) (rho : tcp qmem) : cqdirac m rho m = rho.
  Proof.
    unfold cqdirac; destruct (excluded_middle_informative (m = m));
      [ reflexivity | congruence ].
  Qed.

  Lemma cqdirac_other (m m' : cmem) (rho : tcp qmem) :
    m' <> m -> cqdirac m rho m' = tcp_zero.
  Proof.
    intros H; unfold cqdirac;
      destruct (excluded_middle_informative (m' = m)); [ contradiction | reflexivity ].
  Qed.

  Lemma cqdirac_wf (m : cmem) (rho : tcp qmem) : cqs_wf (cqdirac m rho).
  Proof.
    apply (tcp_summable_singleton _ m); intros m' H; apply cqdirac_other; exact H.
  Qed.

  (* ================================================================= *)
  (** ** Restriction

      "[down_e (rho)] is the cq-density operator [rho] restricted to the parts
      where the expression [e] holds" (section 3.4):

          down_e (proj(|m>) (x) rho_m)  =  proj(|m>) (x) rho_m   if [e]_m = true
                                        =  0                     otherwise

      On families this is a pointwise filter. *)

  Definition restr (e : expr bool) (r : cqs) : cqs :=
    fun m => if ev e m then r m else tcp_zero.

  Definition restrn (e : expr bool) (r : cqs) : cqs :=
    fun m => if ev e m then tcp_zero else r m.

  Lemma restr_wf (e : expr bool) (r : cqs) : cqs_wf r -> cqs_wf (restr e r).
  Proof.
    intros Hr; apply tcp_summable_trace.
    apply (summable_mono (fun m => tcp_trace (restr e r m))
                         (fun m => tcp_trace (r m))).
    - apply tcp_summable_trace; exact Hr.
    - intros m; unfold restr; destruct (ev e m);
        [ apply Rle_refl | rewrite tcp_trace_zero; apply tcp_trace_nonneg ].
  Qed.

  Lemma restrn_wf (e : expr bool) (r : cqs) : cqs_wf r -> cqs_wf (restrn e r).
  Proof.
    intros Hr; apply tcp_summable_trace.
    apply (summable_mono (fun m => tcp_trace (restrn e r m))
                         (fun m => tcp_trace (r m))).
    - apply tcp_summable_trace; exact Hr.
    - intros m; unfold restrn; destruct (ev e m);
        [ rewrite tcp_trace_zero; apply tcp_trace_nonneg | apply Rle_refl ].
  Qed.

  (* ================================================================= *)
  (** ** Reindexing a memory update

      The clauses for assignment, sampling and measurement all sum over the
      memories that update to a given [m']. That preimage is parameterized by
      the old value of the assigned variable. *)

  Lemma assign_preimage (x : cvar) (m m' : cmem) (z : ctype x) :
    cupd m x z = m' -> m = cupd m' x (m x) /\ z = m' x.
  Proof.
    intros H; split.
    - apply funext; intros y.
      destruct (cvar_eq_dec x y) as [-> | Hne].
      + rewrite cupd_same; reflexivity.
      + rewrite cupd_other by exact Hne.
        rewrite <- H, cupd_other by exact Hne; reflexivity.
    - rewrite <- H, cupd_same; reflexivity.
  Qed.

  Lemma assign_preimage_conv (x : cvar) (m' : cmem) (a : ctype x) :
    cupd (cupd m' x a) x (m' x) = m'.
  Proof. rewrite cupd_cupd; apply cupd_id. Qed.

  (* ================================================================= *)
  (** ** The clauses *)

  (** [[x <- e]] (proj(|m>) (x) rho_m) := proj(|m(x := [e]_m)>) (x) rho_m.

      At target [m'], sum over the old values [a] of [x] that [e] sends back to
      [m' x]. The condition is carried as an [if] rather than as a subset type
      so that the index is uniformly [ctype x], the same as for sampling and
      measurement. That uniformity is what lets all three clauses be handled by
      the same reindexing, and it is what makes rule Assign1's projections
      provable without dependent-pair equality. *)

  Definition acond (x : cvar) (e : expr (ctype x)) (m' : cmem) (a : ctype x)
    : Prop := m' x = ev e (cupd m' x a).

  Definition sem_assign (x : cvar) (e : expr (ctype x)) (r : cqs) : cqs :=
    fun m' =>
      tcp_sum (fun a : ctype x =>
                 if excluded_middle_informative (acond x e m' a)
                 then r (cupd m' x a) else tcp_zero).

  (** [[x <-$ e]] (proj(|m>) (x) rho_m) := sum_z [e]_m(z) proj(|m(x := z)>) (x) rho_m. *)
  Definition sem_sample (x : cvar) (e : expr (distr (ctype x))) (r : cqs) : cqs :=
    fun m' =>
      tcp_sum (fun a : ctype x =>
                 tcp_scale (ev e (cupd m' x a) (m' x)) (r (cupd m' x a))).

  (** [[Q <-q e]] (proj(|m>) (x) rho_m)
        := proj(|m>) (x) (tr^{[V^qu \ Q]}_Q rho_m  (x)  proj([e]_m)).

      Discard the register, then tensor in the fresh state. [U_vars,Q] is
      absent because the expression already lives on [qsub P]. *)
  Definition sem_qinit (P : qset) (e : expr (l2 (qsub P))) (r : cqs) : cqs :=
    fun m =>
      tcp_conj (Usplit P)
        (tcp_tensor (tcp_proj (ev e m))
                    (tcp_ptraceL (tcp_conj (oadj (Usplit P)) (r m)))).

  (** [[apply e to Q]] (proj(|m>) (x) rho_m) := proj(|m>) (x) U rho_m U^*,
      with [U := ([e]_m)»Q]. *)
  Definition sem_qapply (P : qset) (e : expr (op (qsub P) (qsub P))) (r : cqs)
    : cqs :=
    fun m => tcp_conj (olift P (ev e m)) (r m).

  (** [[x <- measure Q with e]] (proj(|m>) (x) rho_m)
        := sum_z proj(|m(x := z)>) (x) P_z rho_m P_z,  [P_z := ([e]_m(z))»Q].

      Same reindexing as sampling: at [m'], the outcome is [m' x]. *)
  Definition sem_measure (x : cvar) (P : qset)
             (e : expr (ctype x -> op (qsub P) (qsub P))) (r : cqs) : cqs :=
    fun m' =>
      tcp_sum (fun a : ctype x =>
                 tcp_conj (olift P (ev e (cupd m' x a) (m' x)))
                          (r (cupd m' x a))).

  (** [[while e do c]](rho) := sum_{i=0}^oo down_{~e} (([[c]] o down_e)^i (rho)). *)
  Definition sem_while (e : expr bool) (F : cqs -> cqs) (r : cqs) : cqs :=
    cqs_sum (fun i : nat => restrn e (Nat.iter i (fun s => F (restr e s)) r)).

  (* ================================================================= *)
  (** ** The denotation *)

  Fixpoint denote (c : prog) : cqs -> cqs :=
    match c with
    | Skip           => fun r => r
    | Assign x e     => sem_assign x e
    | Sample x e     => sem_sample x e
    | Cond e c1 c2   => fun r => cqs_add (denote c1 (restr e r))
                                         (denote c2 (restrn e r))
    | While e c1     => sem_while e (denote c1)
    | Seq c1 c2      => fun r => denote c2 (denote c1 r)
    | QInit P e      => sem_qinit P e
    | QApply P e     => sem_qapply P e
    | Measure x P e  => sem_measure x P e
    end.

  (** The two structural equations, immediate from the definition. *)
  Lemma denote_skip (r : cqs) : denote Skip r = r.
  Proof. reflexivity. Qed.

  Lemma denote_seq (c d : prog) (r : cqs) :
    denote (Seq c d) r = denote d (denote c r).
  Proof. reflexivity. Qed.

  (** "skip; c = c = c; skip (w.r.t. the denotation of programs)" -- the fact
      footnote 16 and footnote 20 use silently when chaining rule Seq. *)
  Lemma denote_seq_skip_l (c : prog) (r : cqs) :
    denote (Seq Skip c) r = denote c r.
  Proof. reflexivity. Qed.

  Lemma denote_seq_skip_r (c : prog) (r : cqs) :
    denote (Seq c Skip) r = denote c r.
  Proof. reflexivity. Qed.

  Lemma denote_seq_assoc (c d e : prog) (r : cqs) :
    denote (Seq (Seq c d) e) r = denote (Seq c (Seq d e)) r.
  Proof. reflexivity. Qed.

  (* ================================================================= *)
  (** ** Computing on point masses

      What the rule proofs actually use: on a state with a definite classical
      memory, each clause collapses to a single term. Lemma 36 reduces qRHL to
      exactly this situation. *)

  Lemma denote_assign_dirac (x : cvar) (e : expr (ctype x)) m rho :
    denote (Assign x e) (cqdirac m rho) = cqdirac (cupd m x (ev e m)) rho.
  Proof.
    set (m0 := cupd m x (ev e m)).
    assert (Hm0x : m0 x = ev e m) by (unfold m0; apply cupd_same).
    assert (Hback : cupd m0 x (m x) = m)
      by (unfold m0; rewrite cupd_cupd; apply cupd_id).
    apply funext; intros m'; cbn [denote]; unfold sem_assign.
    destruct (excluded_middle_informative (m' = m0)) as [-> | Hne].
    - (* the image memory: the guard holds at exactly one old value *)
      rewrite cqdirac_same, (tcp_sum_singleton _ (m x)).
      + destruct (excluded_middle_informative (acond x e m0 (m x)))
          as [_ | Hno].
        * rewrite Hback; apply cqdirac_same.
        * exfalso; apply Hno; unfold acond; rewrite Hback, Hm0x; reflexivity.
      + intros a Hane.
        destruct (excluded_middle_informative (acond x e m0 a)) as [_ | _];
          [| reflexivity ].
        apply cqdirac_other; intros Heq.
        apply Hane; rewrite <- (cupd_same m0 x a), Heq; reflexivity.
    - (* any other memory: the guard and the point mass cannot both fire *)
      rewrite cqdirac_other by exact Hne.
      apply tcp_sum_zero; intros a.
      destruct (excluded_middle_informative (acond x e m' a)) as [Hc | _];
        [| reflexivity ].
      apply cqdirac_other; intros Heq.
      apply Hne; unfold acond in Hc.
      transitivity (cupd m x (m' x)).
      + rewrite <- Heq, cupd_cupd, cupd_id; reflexivity.
      + unfold m0; f_equal; rewrite Hc, Heq; reflexivity.
  Qed.

  Lemma denote_qapply_dirac (P : qset) (e : expr (op (qsub P) (qsub P))) m rho :
    denote (QApply P e) (cqdirac m rho)
    = cqdirac m (tcp_conj (olift P (ev e m)) rho).
  Proof.
    apply funext; intros m'; cbn [denote]; unfold sem_qapply.
    destruct (excluded_middle_informative (m' = m)) as [-> | Hne].
    - rewrite !cqdirac_same; reflexivity.
    - rewrite !cqdirac_other by exact Hne; apply tcp_conj_zero.
  Qed.

  Lemma denote_qinit_dirac (P : qset) (e : expr (l2 (qsub P))) m rho :
    denote (QInit P e) (cqdirac m rho)
    = cqdirac m (tcp_conj (Usplit P)
                   (tcp_tensor (tcp_proj (ev e m))
                      (tcp_ptraceL (tcp_conj (oadj (Usplit P)) rho)))).
  Proof.
    apply funext; intros m'; cbn [denote]; unfold sem_qinit.
    destruct (excluded_middle_informative (m' = m)) as [-> | Hne].
    - rewrite !cqdirac_same; reflexivity.
    - rewrite !cqdirac_other by exact Hne.
      rewrite tcp_conj_zero, tcp_ptraceL_zero, tcp_tensor_zero_r,
              tcp_conj_zero; reflexivity.
  Qed.

  (* ================================================================= *)
  (** ** Probabilities

      Definition 9: "[Pr[e : c(rho)] := sum_{m s.t. [e]_m = true} tr rho_m]
      where [[c]](rho) =: sum_m proj(|m>) (x) rho_m". *)

  Definition Pr (e : expr bool) (c : prog) (r : cqs) : R :=
    tsum (fun m => if ev e m then tcp_trace (denote c r m) else 0%R).

  Lemma Pr_nonneg (e : expr bool) (c : prog) (r : cqs) : (0 <= Pr e c r)%R.
  Proof.
    apply tsum_nonneg; intros m; destruct (ev e m);
      [ apply tcp_trace_nonneg | apply Rle_refl ].
  Qed.

  (* ================================================================= *)
  (** ** Preservation of summability and of the trace bound

      That [[c]] really is a cq-superoperator on [T^+_cq[V]]: it maps summable
      families to summable families, and does not increase the total trace.

      The interesting clauses are assignment, sampling and measurement, whose
      denotations sum over the preimage of a memory update, so that the total
      trace of the result is a sum *of sums*. Each is an instance of the
      rearrangement results in [Substrate/Sums.v]:

      - assignment reindexes along an injection, because the side condition on
        the preimage pins the target memory down;
      - sampling and measurement do not, because many targets share a source --
        instead the pair (target, sampled value) is in bijection with
        (source, sampled value), after which Tonelli applies. *)

  Lemma cqs_wf_iff (r : cqs) : cqs_wf r <-> summable (fun m => tcp_trace (r m)).
  Proof. apply tcp_summable_trace. Qed.

  Lemma cqs_trace_fn_nonneg (r : cqs) : nonneg (fun m => tcp_trace (r m)).
  Proof. intros m; apply tcp_trace_nonneg. Qed.

  (* ----------------------------------------------------------------- *)
  (** *** Restriction and addition *)

  Lemma restr_trace_split (e : expr bool) (r : cqs) (m : cmem) :
    (tcp_trace (restr e r m) + tcp_trace (restrn e r m))%R = tcp_trace (r m).
  Proof.
    unfold restr, restrn; destruct (ev e m); rewrite tcp_trace_zero; lra.
  Qed.

  Lemma cqs_trace_restr_split (e : expr bool) (r : cqs) :
    cqs_wf r ->
    (cqs_trace (restr e r) + cqs_trace (restrn e r))%R = cqs_trace r.
  Proof.
    intros Hr; unfold cqs_trace.
    rewrite <- (tsum_add (fun m => tcp_trace (restr e r m))
                         (fun m => tcp_trace (restrn e r m))
                         (cqs_trace_fn_nonneg _) (cqs_trace_fn_nonneg _)
                         (proj1 (cqs_wf_iff _) (restr_wf e r Hr))
                         (proj1 (cqs_wf_iff _) (restrn_wf e r Hr))).
    f_equal; apply funext; intros m; apply restr_trace_split.
  Qed.

  Lemma cqs_add_wf (a b : cqs) : cqs_wf a -> cqs_wf b -> cqs_wf (cqs_add a b).
  Proof.
    intros Ha Hb; apply cqs_wf_iff.
    apply (summable_mono _ (fun m => (tcp_trace (a m) + tcp_trace (b m))%R)).
    - apply summable_add; apply cqs_wf_iff; assumption.
    - intros m; unfold cqs_add; rewrite tcp_trace_add; apply Rle_refl.
  Qed.

  Lemma cqs_trace_add (a b : cqs) :
    cqs_wf a -> cqs_wf b ->
    cqs_trace (cqs_add a b) = (cqs_trace a + cqs_trace b)%R.
  Proof.
    intros Ha Hb; unfold cqs_trace.
    replace (fun m => tcp_trace (cqs_add a b m))
       with (fun m => (tcp_trace (a m) + tcp_trace (b m))%R)
       by (apply funext; intros m; symmetry; apply tcp_trace_add).
    apply tsum_add; solve [ apply cqs_trace_fn_nonneg
                          | apply cqs_wf_iff; assumption ].
  Qed.

  (* ----------------------------------------------------------------- *)
  (** *** The reindexing shared by sampling and measurement

      At target [m'] the summand is indexed by the old value [a] of [x], and
      the source memory is [m'(x := a)]. That map is *not* injective -- many
      targets share a source -- but the pair [(m', a)] is in bijection with
      [(source, sampled value)]:

          (m', a)  |->  (m'(x := a), m' x)

      which is an involution. After reindexing, the summand factors over the
      source and Tonelli applies. *)

  Definition sbeta (x : cvar) (p : cmem * ctype x) : cmem * ctype x :=
    (cupd (fst p) x (snd p), (fst p) x).

  Lemma sbeta_invol (x : cvar) (p : cmem * ctype x) : sbeta x (sbeta x p) = p.
  Proof.
    destruct p as [m' a]; unfold sbeta; cbn [fst snd].
    rewrite cupd_cupd, cupd_id, cupd_same; reflexivity.
  Qed.

  Lemma sbeta_inj (x : cvar) (p q : cmem * ctype x) : sbeta x p = sbeta x q -> p = q.
  Proof.
    intros H; rewrite <- (sbeta_invol x p), <- (sbeta_invol x q), H; reflexivity.
  Qed.

  Lemma cupd_inj (x : cvar) (m : cmem) (a b : ctype x) :
    cupd m x a = cupd m x b -> a = b.
  Proof.
    intros H; rewrite <- (cupd_same m x a), H, cupd_same; reflexivity.
  Qed.

  (* ----------------------------------------------------------------- *)
  (** *** Assignment

      Same shape as sampling below: at a target the summand is indexed by the
      old value of [x], and the pair (target, old value) is in bijection with
      (source, old value of the target's [x]) via [sbeta]. Under that
      bijection the guard [acond] becomes "the source's [x] is what [e] says",
      which is satisfied at exactly one value -- so the inner sum collapses. *)

  Section AssignWf.
    Context (x : cvar) (e : expr (ctype x)).

    Lemma assign_inner_wf (r : cqs) (m' : cmem) :
      cqs_wf r ->
      tcp_summable (fun a : ctype x =>
                      if excluded_middle_informative (acond x e m' a)
                      then r (cupd m' x a) else tcp_zero).
    Proof.
      intros Hr; apply tcp_summable_trace.
      apply (summable_mono _ (fun a : ctype x => tcp_trace (r (cupd m' x a)))).
      - apply (summable_inj (fun a : ctype x => cupd m' x a)
                            (fun m => tcp_trace (r m)));
          [ intros a b H; apply (cupd_inj x m'); exact H
          | apply cqs_wf_iff; exact Hr ].
      - intros a; destruct (excluded_middle_informative (acond x e m' a));
          [ apply Rle_refl | rewrite tcp_trace_zero; apply tcp_trace_nonneg ].
    Qed.

    Lemma assign_trace (r : cqs) (m' : cmem) :
      cqs_wf r ->
      tcp_trace (sem_assign x e r m')
      = tsum (fun a : ctype x =>
                if excluded_middle_informative (acond x e m' a)
                then tcp_trace (r (cupd m' x a)) else 0%R).
    Proof.
      intros Hr; unfold sem_assign.
      rewrite (tcp_trace_sum _ _ _ (assign_inner_wf r m' Hr)).
      f_equal; apply funext; intros a.
      destruct (excluded_middle_informative (acond x e m' a));
        [ reflexivity | apply tcp_trace_zero ].
    Qed.

    Lemma sem_assign_wf_trace (r : cqs) :
      cqs_wf r ->
      cqs_wf (sem_assign x e r)
      /\ (cqs_trace (sem_assign x e r) <= cqs_trace r)%R.
    Proof.
      intros Hr.
      pose (Ga := fun (m' : cmem) (a : ctype x) =>
                    if excluded_middle_informative (acond x e m' a)
                    then tcp_trace (r (cupd m' x a)) else 0%R).
      pose (Hsrc := fun (m : cmem) (z : ctype x) =>
                      if excluded_middle_informative (z = ev e m)
                      then tcp_trace (r m) else 0%R).
      assert (HGH : (fun p : cmem * ctype x => Ga (fst p) (snd p))
                    = (fun p : cmem * ctype x =>
                         Hsrc (fst (sbeta x p)) (snd (sbeta x p))))
        by (apply funext; intros p; reflexivity).
      assert (HsrcS : forall m, summable (Hsrc m))
        by (intros m; apply (proj1 (tsum_single_val (ev e m) (tcp_trace (r m))
                                      (tcp_trace_nonneg _ _)))).
      assert (HsrcB : forall m, tsum (Hsrc m) = tcp_trace (r m))
        by (intros m; apply (proj2 (tsum_single_val (ev e m) (tcp_trace (r m))
                                      (tcp_trace_nonneg _ _)))).
      assert (HsrcIt : summable (fun m => tsum (Hsrc m))).
      { apply (summable_mono _ (fun m => tcp_trace (r m)));
          [ apply cqs_wf_iff; exact Hr
          | intros m; rewrite HsrcB; apply Rle_refl ]. }
      destruct (tsum_pairs_le_iter Hsrc HsrcS HsrcIt) as [HsrcPS HsrcPB].
      assert (HGS : summable (fun p : cmem * ctype x => Ga (fst p) (snd p))).
      { rewrite HGH.
        apply (summable_inj (sbeta x)
                 (fun q : cmem * ctype x => Hsrc (fst q) (snd q)));
          [ apply sbeta_inj | exact HsrcPS ]. }
      assert (HGpos : nonneg (fun p : cmem * ctype x => Ga (fst p) (snd p))).
      { intros p; unfold Ga.
        destruct (excluded_middle_informative (acond x e (fst p) (snd p)));
          [ apply tcp_trace_nonneg | apply Rle_refl ]. }
      destruct (tsum_iter_le_pairs Ga HGpos HGS) as [HGit HGitB].
      assert (Heq : (fun m' => tcp_trace (sem_assign x e r m'))
                    = (fun m' => tsum (Ga m')))
        by (apply funext; intros m'; apply assign_trace; exact Hr).
      split.
      - apply cqs_wf_iff; rewrite Heq; exact HGit.
      - unfold cqs_trace; rewrite Heq.
        eapply Rle_trans; [ exact HGitB |].
        rewrite HGH.
        eapply Rle_trans.
        + apply (tsum_inj_le (sbeta x)
                   (fun q : cmem * ctype x => Hsrc (fst q) (snd q))
                   (sbeta_inj x) HsrcPS).
        + eapply Rle_trans; [ exact HsrcPB |].
          apply tsum_mono;
            [ intros m; rewrite HsrcB; apply tcp_trace_nonneg
            | apply cqs_wf_iff; exact Hr
            | intros m; rewrite HsrcB; apply Rle_refl ].
    Qed.

  End AssignWf.

  (* ----------------------------------------------------------------- *)
  (** *** Sampling *)

  Section SampleWf.
    Context (x : cvar) (e : expr (distr (ctype x))).

    Lemma sample_inner_wf (r : cqs) (m' : cmem) :
      cqs_wf r ->
      tcp_summable (fun a : ctype x =>
                      tcp_scale (ev e (cupd m' x a) (m' x)) (r (cupd m' x a))).
    Proof.
      intros Hr; apply tcp_summable_trace.
      apply (summable_mono _ (fun a : ctype x => tcp_trace (r (cupd m' x a)))).
      - apply (summable_inj (fun a : ctype x => cupd m' x a)
                            (fun m => tcp_trace (r m))).
        + intros a b H; apply (cupd_inj x m'); exact H.
        + apply cqs_wf_iff; exact Hr.
      - intros a; rewrite tcp_trace_scale.
        rewrite <- (Rmult_1_l (tcp_trace (r (cupd m' x a)))) at 2.
        apply Rmult_le_compat_r; [ apply tcp_trace_nonneg | apply dfun_le1_pt ].
    Qed.

    Lemma sample_trace (r : cqs) (m' : cmem) :
      cqs_wf r ->
      tcp_trace (sem_sample x e r m')
      = tsum (fun a : ctype x =>
                ((ev e (cupd m' x a) (m' x)) * tcp_trace (r (cupd m' x a)))%R).
    Proof.
      intros Hr; unfold sem_sample.
      rewrite (tcp_trace_sum _ _ _ (sample_inner_wf r m' Hr)).
      f_equal; apply funext; intros a; apply tcp_trace_scale.
    Qed.

    Lemma sem_sample_wf_trace (r : cqs) :
      cqs_wf r ->
      cqs_wf (sem_sample x e r)
      /\ (cqs_trace (sem_sample x e r) <= cqs_trace r)%R.
    Proof.
      intros Hr.
      (* the summand, grouped by target and by source *)
      pose (Gs := fun (m' : cmem) (a : ctype x) =>
                    ((ev e (cupd m' x a) (m' x))
                     * tcp_trace (r (cupd m' x a)))%R).
      pose (Hsrc := fun (m : cmem) (z : ctype x) =>
                      (tcp_trace (r m) * ev e m z)%R).
      assert (HGH : (fun p : cmem * ctype x => Gs (fst p) (snd p))
                    = (fun p : cmem * ctype x =>
                         Hsrc (fst (sbeta x p)) (snd (sbeta x p)))).
      { apply funext; intros p; unfold Gs, Hsrc, sbeta; cbn [fst snd]; ring. }
      (* each source contributes at most its own trace *)
      assert (HsrcS : forall m, summable (Hsrc m)).
      { intros m; apply summable_scale;
          [ apply tcp_trace_nonneg | apply dfun_nonneg | apply dfun_summable ]. }
      assert (HsrcB : forall m, (tsum (Hsrc m) <= tcp_trace (r m))%R).
      { intros m; unfold Hsrc.
        rewrite (tsum_scale (tcp_trace (r m)) (ev e m)
                   (tcp_trace_nonneg _ _) (dfun_nonneg _) (dfun_summable _)).
        rewrite <- (Rmult_1_r (tcp_trace (r m))) at 2.
        apply Rmult_le_compat_l; [ apply tcp_trace_nonneg | apply dfun_le1 ]. }
      assert (HsrcIt : summable (fun m => tsum (Hsrc m))).
      { apply (summable_mono _ (fun m => tcp_trace (r m)));
          [ apply cqs_wf_iff; exact Hr | exact HsrcB ]. }
      destruct (tsum_pairs_le_iter Hsrc HsrcS HsrcIt) as [HsrcPS HsrcPB].
      (* transport to the target grouping along the bijection *)
      assert (HGS : summable (fun p : cmem * ctype x => Gs (fst p) (snd p))).
      { rewrite HGH.
        apply (summable_inj (sbeta x)
                 (fun q : cmem * ctype x => Hsrc (fst q) (snd q)));
          [ apply sbeta_inj | exact HsrcPS ]. }
      assert (HGpos : nonneg (fun p : cmem * ctype x => Gs (fst p) (snd p))).
      { intros p; unfold Gs; apply Rmult_le_pos;
          [ apply dfun_nonneg | apply tcp_trace_nonneg ]. }
      destruct (tsum_iter_le_pairs Gs HGpos HGS) as [HGit HGitB].
      assert (Heq : (fun m' => tcp_trace (sem_sample x e r m'))
                    = (fun m' => tsum (Gs m')))
        by (apply funext; intros m'; apply sample_trace; exact Hr).
      split.
      - apply cqs_wf_iff; rewrite Heq; exact HGit.
      - unfold cqs_trace; rewrite Heq.
        eapply Rle_trans; [ exact HGitB |].
        rewrite HGH.
        eapply Rle_trans.
        + apply (tsum_inj_le (sbeta x)
                   (fun q : cmem * ctype x => Hsrc (fst q) (snd q))
                   (sbeta_inj x) HsrcPS).
        + eapply Rle_trans; [ exact HsrcPB |].
          apply tsum_mono;
            [ intros m; apply tsum_nonneg; intros z;
              unfold Hsrc; apply Rmult_le_pos;
              [ apply tcp_trace_nonneg | apply dfun_nonneg ]
            | apply cqs_wf_iff; exact Hr
            | exact HsrcB ].
    Qed.

  End SampleWf.

  (* ----------------------------------------------------------------- *)
  (** *** Measurement

      For a fixed state, a projective measurement is trace-non-increasing;
      that is the substrate's [tcp_trace_meas_tensor], transported through the
      register split. The rest of the clause follows the sampling pattern. *)

  (** A projective measurement stays one after being lifted from a register to
      the whole quantum memory. The projector conditions are
      [wolift_projector]; the bound is the substrate's [meas_bound_tensor]
      (resp. [meas_total_tensor]) read through the register split, which is
      unitary and so leaves inner products alone. *)
  Lemma olift_inner (P : qset) (A : op (qsub P) (qsub P)) (v : l2 qmem) :
    inner v (oapp (olift P A) v)
    = inner (oapp (oadj (Usplit P)) v)
            (oapp (tensoro A oid) (oapp (oadj (Usplit P)) v)).
  Proof. rewrite oapp_wolift, <- inner_oadj; reflexivity. Qed.

  Lemma olift_inner_self (P : qset) (v : l2 qmem) :
    inner (oapp (oadj (Usplit P)) v) (oapp (oadj (Usplit P)) v) = inner v v.
  Proof. apply oisometry_inner, oisometry_oadj, Wsplit_unitary. Qed.

  Lemma olift_meas (P : qset) (D : Type) (M : D -> op (qsub P) (qsub P)) :
    is_meas M -> is_meas (fun z => olift P (M z)).
  Proof.
    intros [Hproj [Hsum Hbd]].
    destruct (meas_bound_tensor (qsub P) (qsub (qneg P)) D M Hsum Hbd)
      as [Hs Hb].
    split; [| split ].
    - intros z; apply (wolift_projector qvar qtype P (M z) (Hproj z)).
    - intros v.
      assert (Heq : (fun z => Cre (inner v (oapp (olift P (M z)) v)))
                    = (fun z => Cre (inner (oapp (oadj (Usplit P)) v)
                                     (oapp (tensoro (M z) oid)
                                           (oapp (oadj (Usplit P)) v)))))
        by (apply funext; intros z; rewrite olift_inner; reflexivity).
      rewrite Heq; apply Hs.
    - intros v; unfold meas_bound.
      assert (Heq : (fun z => Cre (inner v (oapp (olift P (M z)) v)))
                    = (fun z => Cre (inner (oapp (oadj (Usplit P)) v)
                                     (oapp (tensoro (M z) oid)
                                           (oapp (oadj (Usplit P)) v)))))
        by (apply funext; intros z; rewrite olift_inner; reflexivity).
      rewrite Heq.
      eapply Rle_trans; [ apply (Hb (oapp (oadj (Usplit P)) v)) |].
      apply Req_le; f_equal; apply olift_inner_self.
  Qed.

  Lemma olift_meas_total (P : qset) (D : Type)
        (M : D -> op (qsub P) (qsub P)) :
    is_total_meas M -> is_total_meas (fun z => olift P (M z)).
  Proof.
    intros [Hproj [Hsum Hbd]].
    destruct (meas_total_tensor (qsub P) (qsub (qneg P)) D M Hsum Hbd)
      as [Hs Hb].
    split; [| split ].
    - intros z; apply (wolift_projector qvar qtype P (M z) (Hproj z)).
    - intros v.
      assert (Heq : (fun z => Cre (inner v (oapp (olift P (M z)) v)))
                    = (fun z => Cre (inner (oapp (oadj (Usplit P)) v)
                                     (oapp (tensoro (M z) oid)
                                           (oapp (oadj (Usplit P)) v)))))
        by (apply funext; intros z; rewrite olift_inner; reflexivity).
      rewrite Heq; apply Hs.
    - intros v; unfold meas_bound.
      assert (Heq : (fun z => Cre (inner v (oapp (olift P (M z)) v)))
                    = (fun z => Cre (inner (oapp (oadj (Usplit P)) v)
                                     (oapp (tensoro (M z) oid)
                                           (oapp (oadj (Usplit P)) v)))))
        by (apply funext; intros z; rewrite olift_inner; reflexivity).
      rewrite Heq, (Hb (oapp (oadj (Usplit P)) v)).
      f_equal; apply olift_inner_self.
  Qed.

  Lemma meas_trace_bound (P : qset) (D : Type) (M : D -> op (qsub P) (qsub P))
        (rho : tcp qmem) :
    is_meas M ->
    summable (fun z => tcp_trace (tcp_conj (olift P (M z)) rho))
    /\ (tsum (fun z => tcp_trace (tcp_conj (olift P (M z)) rho))
        <= tcp_trace rho)%R.
  Proof.
    intros [Hproj [Hsum Hbd]].
    destruct (Wsplit_unitary qvar qtype P) as [Hiso Hsur].
    (* rewrite each term in the split picture *)
    assert (Hstep : (fun z => tcp_trace (tcp_conj (olift P (M z)) rho))
                    = (fun z => tcp_trace (tcp_conj (tensoro (M z) oid)
                                  (tcp_conj (oadj (Usplit P)) rho)))).
    { apply funext; intros z; unfold wolift.
      rewrite !tcp_conj_ocomp.
      apply tcp_trace_conj_isometry; exact Hiso. }
    (* the discarded conjugation is by an isometry, so the trace is unchanged *)
    assert (Htr : tcp_trace (tcp_conj (oadj (Usplit P)) rho) = tcp_trace rho).
    { apply tcp_trace_conj_isometry, oisometry_oadj; split; assumption. }
    destruct (tcp_trace_meas_tensor _ _ _ M
                (tcp_conj (oadj (Usplit P)) rho)
                (fun z => proj1 (Hproj z)) (fun z => proj2 (Hproj z))
                Hsum Hbd) as [Hs Hb].
    rewrite Hstep; split; [ exact Hs | rewrite <- Htr; exact Hb ].
  Qed.

  Section MeasureWf.
    Context (x : cvar) (P : qset)
            (e : expr (ctype x -> op (qsub P) (qsub P)))
            (Hmeas : forall m, is_meas (ev e m)).

    Lemma measure_term_le (m : cmem) (z : ctype x) (rho : tcp qmem) :
      (tcp_trace (tcp_conj (olift P (ev e m z)) rho) <= tcp_trace rho)%R.
    Proof.
      destruct (Hmeas m) as [Hproj _].
      destruct (wolift_projector qvar qtype P (ev e m z) (Hproj z)) as [H1 H2].
      apply tcp_trace_conj_proj_le; assumption.
    Qed.

    Lemma measure_inner_wf (r : cqs) (m' : cmem) :
      cqs_wf r ->
      tcp_summable (fun a : ctype x =>
                      tcp_conj (olift P (ev e (cupd m' x a) (m' x)))
                               (r (cupd m' x a))).
    Proof.
      intros Hr; apply tcp_summable_trace.
      apply (summable_mono _ (fun a : ctype x => tcp_trace (r (cupd m' x a)))).
      - apply (summable_inj (fun a : ctype x => cupd m' x a)
                            (fun m => tcp_trace (r m))).
        + intros a b H; apply (cupd_inj x m'); exact H.
        + apply cqs_wf_iff; exact Hr.
      - intros a; apply measure_term_le.
    Qed.

    Lemma measure_trace (r : cqs) (m' : cmem) :
      cqs_wf r ->
      tcp_trace (sem_measure x P e r m')
      = tsum (fun a : ctype x =>
                tcp_trace (tcp_conj (olift P (ev e (cupd m' x a) (m' x)))
                                    (r (cupd m' x a)))).
    Proof.
      intros Hr; unfold sem_measure.
      apply (tcp_trace_sum _ _ _ (measure_inner_wf r m' Hr)).
    Qed.

    Lemma sem_measure_wf_trace (r : cqs) :
      cqs_wf r ->
      cqs_wf (sem_measure x P e r)
      /\ (cqs_trace (sem_measure x P e r) <= cqs_trace r)%R.
    Proof.
      intros Hr.
      pose (Gm := fun (m' : cmem) (a : ctype x) =>
                    tcp_trace (tcp_conj (olift P (ev e (cupd m' x a) (m' x)))
                                        (r (cupd m' x a)))).
      pose (Hm := fun (m : cmem) (z : ctype x) =>
                    tcp_trace (tcp_conj (olift P (ev e m z)) (r m))).
      assert (HGH : (fun p : cmem * ctype x => Gm (fst p) (snd p))
                    = (fun p : cmem * ctype x =>
                         Hm (fst (sbeta x p)) (snd (sbeta x p))))
        by (apply funext; intros p; reflexivity).
      assert (HmS : forall m, summable (Hm m))
        by (intros m; apply (proj1 (meas_trace_bound P (ctype x) (ev e m) (r m)
                                      (Hmeas m)))).
      assert (HmB : forall m, (tsum (Hm m) <= tcp_trace (r m))%R)
        by (intros m; apply (proj2 (meas_trace_bound P (ctype x) (ev e m) (r m)
                                      (Hmeas m)))).
      assert (HmIt : summable (fun m => tsum (Hm m))).
      { apply (summable_mono _ (fun m => tcp_trace (r m)));
          [ apply cqs_wf_iff; exact Hr | exact HmB ]. }
      destruct (tsum_pairs_le_iter Hm HmS HmIt) as [HmPS HmPB].
      assert (HGS : summable (fun p : cmem * ctype x => Gm (fst p) (snd p))).
      { rewrite HGH.
        apply (summable_inj (sbeta x)
                 (fun q : cmem * ctype x => Hm (fst q) (snd q)));
          [ apply sbeta_inj | exact HmPS ]. }
      assert (HGpos : nonneg (fun p : cmem * ctype x => Gm (fst p) (snd p)))
        by (intros p; apply tcp_trace_nonneg).
      destruct (tsum_iter_le_pairs Gm HGpos HGS) as [HGit HGitB].
      assert (Heq : (fun m' => tcp_trace (sem_measure x P e r m'))
                    = (fun m' => tsum (Gm m')))
        by (apply funext; intros m'; apply measure_trace; exact Hr).
      split.
      - apply cqs_wf_iff; rewrite Heq; exact HGit.
      - unfold cqs_trace; rewrite Heq.
        eapply Rle_trans; [ exact HGitB |].
        rewrite HGH.
        eapply Rle_trans.
        + apply (tsum_inj_le (sbeta x)
                   (fun q : cmem * ctype x => Hm (fst q) (snd q))
                   (sbeta_inj x) HmPS).
        + eapply Rle_trans; [ exact HmPB |].
          apply tsum_mono;
            [ intros m; apply tsum_nonneg; intros z; apply tcp_trace_nonneg
            | apply cqs_wf_iff; exact Hr
            | exact HmB ].
    Qed.

  End MeasureWf.

  (* ----------------------------------------------------------------- *)
  (** *** Quantum application and initialization

      Both are trace-preserving: [apply] conjugates by an isometry, and
      [Q <-q e] discards a register and tensors in a unit vector. *)

  Lemma sem_qapply_trace_pt (P : qset) (e : expr (op (qsub P) (qsub P)))
        (r : cqs) (m : cmem) :
    oisometry (ev e m) ->
    tcp_trace (sem_qapply P e r m) = tcp_trace (r m).
  Proof.
    intros He; unfold sem_qapply.
    apply (tcp_trace_conj_wolift qvar qtype P (ev e m) (r m) He).
  Qed.

  Lemma sem_qinit_trace_pt (P : qset) (e : expr (l2 (qsub P)))
        (r : cqs) (m : cmem) :
    inner (ev e m) (ev e m) = C1 ->
    tcp_trace (sem_qinit P e r m) = tcp_trace (r m).
  Proof.
    intros Hn; unfold sem_qinit.
    destruct (Wsplit_unitary qvar qtype P) as [Hiso Hsur].
    rewrite (tcp_trace_conj_isometry _ _ _ _ Hiso).
    rewrite tcp_trace_tensor, tcp_trace_proj, Hn, tcp_ptraceL_trace.
    rewrite (tcp_trace_conj_isometry _ _ (oadj (Usplit P)) _
               (oisometry_oadj _ (conj Hiso Hsur))).
    replace (Cre C1) with 1%R by reflexivity.
    rewrite Rmult_1_l; reflexivity.
  Qed.

  (** Both therefore preserve well-formedness and the total trace. *)
  Lemma wf_trace_of_pointwise (a r : cqs) :
    (forall m, tcp_trace (a m) = tcp_trace (r m)) ->
    cqs_wf r -> cqs_wf a /\ cqs_trace a = cqs_trace r.
  Proof.
    intros Hpt Hr.
    assert (Hfun : (fun m => tcp_trace (a m)) = (fun m => tcp_trace (r m)))
      by (apply funext; exact Hpt).
    split.
    - apply cqs_wf_iff; rewrite Hfun; apply cqs_wf_iff; exact Hr.
    - unfold cqs_trace; rewrite Hfun; reflexivity.
  Qed.

  (* ================================================================= *)
  (** ** [[c]] is a cq-superoperator

      For loop-free programs. The loop clause is an infinite sum of iterates
      and needs an argument of its own -- that the iterates' escaping mass is
      bounded by the initial trace -- which belongs with rules While1 and
      JointWhile in Phase 2. *)

  (* ----------------------------------------------------------------- *)
  (** *** Loops

      [[while e do c]](rho) = sum_i down_{~e} (([[c]] o down_e)^i rho): the
      state at the top of iteration [i], filtered by the negated guard, summed
      over all iteration counts. The trace bound is therefore not one
      application of the body's bound but a telescoping estimate.

      Write [t i] for the trace at the top of iteration [i] and [a i] for the
      trace of what exits there. Splitting by the guard gives
      [t i = tr(down_e rho_i) + a i], and the body does not increase the
      trace, so [a i + t (i+1) <= t i]. Summing the first [n] of those
      telescopes to [sum_{i<n} a i + t n <= t 0]: all the exits together weigh
      no more than the state we started with. Since every duplicate-free list
      of iteration counts sits inside an initial segment, that bounds the
      unordered sum as well. *)

  (** A summable family of cq-states. The single condition is joint
      summability of the traces over (index, memory); every pointwise and
      iterated fact below follows from it by Tonelli, and it is preserved by
      [[c]] because [[c]] does not increase the total trace. *)
  Definition cqs_fam {J : Type} (F : J -> cqs) : Prop :=
    summable (fun p : J * cmem => tcp_trace (F (fst p) (snd p))).

  Lemma cqs_fam_wf {J} (F : J -> cqs) : cqs_fam F -> forall j, cqs_wf (F j).
  Proof.
    intros H j; apply tcp_summable_trace.
    apply (summable_inj (fun m : cmem => (j, m))
                        (fun p : J * cmem => tcp_trace (F (fst p) (snd p))));
      [ intros a b Hab; congruence | exact H ].
  Qed.

  Lemma cqs_fam_ptwise {J} (F : J -> cqs) :
    cqs_fam F -> forall m, tcp_summable (fun j => F j m).
  Proof.
    intros H m; apply tcp_summable_trace.
    apply (summable_inj (fun j : J => (j, m))
                        (fun p : J * cmem => tcp_trace (F (fst p) (snd p))));
      [ intros a b Hab; congruence | exact H ].
  Qed.

  Lemma cqs_fam_trace {J} (F : J -> cqs) :
    cqs_fam F -> summable (fun j => cqs_trace (F j)).
  Proof.
    intros H.
    destruct (tsum_iter_le_pairs (fun (j : J) (m : cmem) => tcp_trace (F j m))
                (fun p => tcp_trace_nonneg _ _) H) as [Hit _].
    exact Hit.
  Qed.

  Lemma cqs_fam_sum_wf {J} (F : J -> cqs) : cqs_fam F -> cqs_wf (cqs_sum F).
  Proof.
    intros H; apply tcp_summable_trace.
    assert (Heq : (fun m => tcp_trace (cqs_sum F m))
                  = (fun m : cmem => tsum (fun j => tcp_trace (F j m))))
      by (apply funext; intros m; unfold cqs_sum;
          apply (tcp_trace_sum _ _ _ (cqs_fam_ptwise F H m))).
    rewrite Heq.
    (* the same joint summability, with the two indices the other way round *)
    assert (Hsw : summable (fun q : cmem * J => tcp_trace (F (snd q) (fst q)))).
    { apply (summable_inj (fun q : cmem * J => (snd q, fst q))
                          (fun p : J * cmem => tcp_trace (F (fst p) (snd p)))).
      - intros [m1 j1] [m2 j2] Hq; cbn in Hq; congruence.
      - exact H. }
    destruct (tsum_iter_le_pairs (fun (m : cmem) (j : J) => tcp_trace (F j m))
                (fun q => tcp_trace_nonneg _ _) Hsw) as [Hit _].
    exact Hit.
  Qed.

  Lemma cqs_fam_restr {J} (e : expr bool) (F : J -> cqs) :
    cqs_fam F -> cqs_fam (fun j => restr e (F j)).
  Proof.
    intros H; unfold cqs_fam.
    apply (summable_mono _ (fun p : J * cmem => tcp_trace (F (fst p) (snd p))));
      [ exact H |].
    intros [j m]; cbn [fst snd]; unfold restr.
    destruct (ev e m);
      [ apply Rle_refl | rewrite tcp_trace_zero; apply tcp_trace_nonneg ].
  Qed.

  Lemma cqs_fam_restrn {J} (e : expr bool) (F : J -> cqs) :
    cqs_fam F -> cqs_fam (fun j => restrn e (F j)).
  Proof.
    intros H; unfold cqs_fam.
    apply (summable_mono _ (fun p : J * cmem => tcp_trace (F (fst p) (snd p))));
      [ exact H |].
    intros [j m]; cbn [fst snd]; unfold restrn.
    destruct (ev e m);
      [ rewrite tcp_trace_zero; apply tcp_trace_nonneg | apply Rle_refl ].
  Qed.

  Lemma restr_add (e : expr bool) (r s : cqs) :
    restr e (cqs_add r s) = cqs_add (restr e r) (restr e s).
  Proof.
    apply funext; intros m; unfold restr, cqs_add.
    destruct (ev e m); [ reflexivity | symmetry; apply tcp_add_zero ].
  Qed.

  Lemma restrn_add (e : expr bool) (r s : cqs) :
    restrn e (cqs_add r s) = cqs_add (restrn e r) (restrn e s).
  Proof.
    apply funext; intros m; unfold restrn, cqs_add.
    destruct (ev e m); [ symmetry; apply tcp_add_zero | reflexivity ].
  Qed.

  Lemma restr_scale (a : R) (e : expr bool) (r : cqs) :
    restr e (cqs_scale a r) = cqs_scale a (restr e r).
  Proof.
    apply funext; intros m; unfold restr, cqs_scale.
    destruct (ev e m); [ reflexivity | symmetry; apply tcp_scale_zero ].
  Qed.

  Lemma restrn_scale (a : R) (e : expr bool) (r : cqs) :
    restrn e (cqs_scale a r) = cqs_scale a (restrn e r).
  Proof.
    apply funext; intros m; unfold restrn, cqs_scale.
    destruct (ev e m); [ symmetry; apply tcp_scale_zero | reflexivity ].
  Qed.

  Lemma cqs_sum_add {J} (A B : J -> cqs) :
    cqs_fam A -> cqs_fam B ->
    cqs_add (cqs_sum A) (cqs_sum B) = cqs_sum (fun j => cqs_add (A j) (B j)).
  Proof.
    intros HA HB; apply funext; intros m; unfold cqs_add, cqs_sum.
    symmetry;
      apply (tcp_sum_add _ _ _ _ (cqs_fam_ptwise A HA m)
                                 (cqs_fam_ptwise B HB m)).
  Qed.

  Lemma cqs_sum_scale {J} (a : R) (A : J -> cqs) :
    cqs_fam A -> cqs_scale a (cqs_sum A) = cqs_sum (fun j => cqs_scale a (A j)).
  Proof.
    intros HA; apply funext; intros m; unfold cqs_scale, cqs_sum.
    apply (tcp_scale_sum _ _ _ _ (cqs_fam_ptwise A HA m)).
  Qed.

  Lemma restr_sum {J} (e : expr bool) (F : J -> cqs) :
    restr e (cqs_sum F) = cqs_sum (fun j => restr e (F j)).
  Proof.
    apply funext; intros m; unfold restr, cqs_sum.
    destruct (ev e m);
      [ reflexivity | symmetry; apply tcp_sum_zero; intros; reflexivity ].
  Qed.

  Lemma restrn_sum {J} (e : expr bool) (F : J -> cqs) :
    restrn e (cqs_sum F) = cqs_sum (fun j => restrn e (F j)).
  Proof.
    apply funext; intros m; unfold restrn, cqs_sum.
    destruct (ev e m);
      [ symmetry; apply tcp_sum_zero; intros; reflexivity | reflexivity ].
  Qed.

  Lemma cqs_trace_sum {J} (F : J -> cqs) :
    cqs_fam F -> cqs_trace (cqs_sum F) = tsum (fun j => cqs_trace (F j)).
  Proof.
    intros H; unfold cqs_trace, cqs_sum.
    assert (Heq : (fun m : cmem => tcp_trace (tcp_sum (fun j => F j m)))
                  = (fun m : cmem => tsum (fun j => tcp_trace (F j m))))
      by (apply funext; intros m;
          apply (tcp_trace_sum _ _ _ (cqs_fam_ptwise F H m))).
    rewrite Heq.
    assert (Hmj : summable (fun q : cmem * J => tcp_trace (F (snd q) (fst q)))).
    { apply (summable_inj (fun q : cmem * J => (snd q, fst q))
                          (fun p : J * cmem => tcp_trace (F (fst p) (snd p))));
        [ intros [a b] [x y] Hq; cbn in Hq; congruence | exact H ]. }
    destruct (tsum_iter_le_pairs (fun (m : cmem) (j : J) => tcp_trace (F j m))
                (fun q => tcp_trace_nonneg _ _) Hmj) as [Hit _].
    destruct (tsum_tonelli (fun (m : cmem) (j : J) => tcp_trace (F j m))
                (fun m j => tcp_trace_nonneg _ _)
                (fun m => proj1 (tcp_summable_trace _ _ _)
                            (cqs_fam_ptwise F H m))
                Hit) as [_ E1].
    destruct (tsum_tonelli (fun (j : J) (m : cmem) => tcp_trace (F j m))
                (fun j m => tcp_trace_nonneg _ _)
                (fun j => proj1 (tcp_summable_trace _ _ _) (cqs_fam_wf F H j))
                (cqs_fam_trace F H)) as [_ E2].
    rewrite <- E1, <- E2.
    apply (tsum_swap_pair
             (fun p : J * cmem => tcp_trace (F (fst p) (snd p)))), H.
  Qed.

  Section While.
    Context (e : expr bool) (F : cqs -> cqs)
            (HF : forall r, cqs_wf r ->
                   cqs_wf (F r) /\ (cqs_trace (F r) <= cqs_trace r)%R).

    Definition witer (r : cqs) (i : nat) : cqs :=
      Nat.iter i (fun s => F (restr e s)) r.

    Lemma witer_wf (r : cqs) (i : nat) : cqs_wf r -> cqs_wf (witer r i).
    Proof.
      intros Hr; induction i as [| n IH]; [ exact Hr |].
      apply HF, restr_wf, IH.
    Qed.

    Lemma witer_step (r : cqs) (i : nat) :
      cqs_wf r ->
      (cqs_trace (restrn e (witer r i)) + cqs_trace (witer r (S i))
       <= cqs_trace (witer r i))%R.
    Proof.
      intros Hr.
      assert (Hw : cqs_wf (witer r i)) by (apply witer_wf; exact Hr).
      pose proof (cqs_trace_restr_split e (witer r i) Hw) as Hsplit.
      assert (Hb : (cqs_trace (witer r (S i))
                    <= cqs_trace (restr e (witer r i)))%R)
        by (apply HF, restr_wf, Hw).
      lra.
    Qed.

    Lemma witer_telescope (r : cqs) (n : nat) :
      cqs_wf r ->
      (lsum (fun i => cqs_trace (restrn e (witer r i))) (seq 0 n)
       + cqs_trace (witer r n) <= cqs_trace r)%R.
    Proof.
      intros Hr; induction n as [| n IH]; [ cbn; lra |].
      rewrite seq_S, lsum_app; cbn [lsum].
      pose proof (witer_step r n Hr) as Hstep.
      replace (0 + n)%nat with n by apply Nat.add_0_l.
      lra.
    Qed.

    Lemma witer_summable (r : cqs) :
      cqs_wf r ->
      summable (fun i : nat => cqs_trace (restrn e (witer r i)))
      /\ (tsum (fun i : nat => cqs_trace (restrn e (witer r i)))
          <= cqs_trace r)%R.
    Proof.
      intros Hr.
      apply (nat_summable_of_seq
               (fun i : nat => cqs_trace (restrn e (witer r i)))
               (cqs_trace r) (fun i => cqs_trace_nonneg _)).
      intros n; pose proof (witer_telescope r n Hr);
        pose proof (cqs_trace_nonneg (witer r n)); lra.
    Qed.

    Lemma witer_fam (r : cqs) :
      cqs_wf r -> cqs_fam (fun i : nat => restrn e (witer r i)).
    Proof.
      intros Hr; unfold cqs_fam.
      refine (proj1 (tsum_pairs_le_iter
                       (fun (i : nat) (m : cmem) =>
                          tcp_trace (restrn e (witer r i) m)) _ _)).
      - intros i; apply tcp_summable_trace, restrn_wf, witer_wf; exact Hr.
      - apply (proj1 (witer_summable r Hr)).
    Qed.

    Lemma sem_while_sum (r : cqs) :
      sem_while e F r = cqs_sum (fun i : nat => restrn e (witer r i)).
    Proof. reflexivity. Qed.

    Lemma sem_while_wf_trace (r : cqs) :
      cqs_wf r ->
      cqs_wf (sem_while e F r)
      /\ (cqs_trace (sem_while e F r) <= cqs_trace r)%R.
    Proof.
      intros Hr.
      pose proof (witer_fam r Hr) as Hfam.
      rewrite sem_while_sum.
      split; [ apply cqs_fam_sum_wf; exact Hfam
             | rewrite (cqs_trace_sum _ Hfam);
               apply (proj2 (witer_summable r Hr)) ].
    Qed.

    (** Additivity and normality of the loop, from the same properties of its
        body. In both cases the iterates split first (an induction on the
        iteration count), and then the sum over iteration counts is exchanged
        with the other sum. *)

    Lemma witer_add
          (Hadd : forall a b, cqs_wf a -> cqs_wf b ->
                              F (cqs_add a b) = cqs_add (F a) (F b))
          (r s : cqs) (Hr : cqs_wf r) (Hs : cqs_wf s) (i : nat) :
      witer (cqs_add r s) i = cqs_add (witer r i) (witer s i).
    Proof.
      induction i as [| n IH]; [ reflexivity |].
      change (witer (cqs_add r s) (S n))
        with (F (restr e (witer (cqs_add r s) n))).
      change (witer r (S n)) with (F (restr e (witer r n))).
      change (witer s (S n)) with (F (restr e (witer s n))).
      rewrite IH, restr_add.
      apply Hadd; apply restr_wf, witer_wf; assumption.
    Qed.

    Lemma sem_while_add
          (Hadd : forall a b, cqs_wf a -> cqs_wf b ->
                              F (cqs_add a b) = cqs_add (F a) (F b))
          (r s : cqs) :
      cqs_wf r -> cqs_wf s ->
      sem_while e F (cqs_add r s)
      = cqs_add (sem_while e F r) (sem_while e F s).
    Proof.
      intros Hr Hs; rewrite !sem_while_sum.
      rewrite (cqs_sum_add (fun i : nat => restrn e (witer r i))
                           (fun i : nat => restrn e (witer s i))
                           (witer_fam r Hr) (witer_fam s Hs)).
      f_equal; apply funext; intros i.
      rewrite (witer_add Hadd r s Hr Hs i); apply restrn_add.
    Qed.

    Lemma witer_scale
          (Hscale : forall a r, (0 <= a)%R -> cqs_wf r ->
                                F (cqs_scale a r) = cqs_scale a (F r))
          (a : R) (Ha : (0 <= a)%R) (r : cqs) (Hr : cqs_wf r) (i : nat) :
      witer (cqs_scale a r) i = cqs_scale a (witer r i).
    Proof.
      induction i as [| n IH]; [ reflexivity |].
      change (witer (cqs_scale a r) (S n))
        with (F (restr e (witer (cqs_scale a r) n))).
      change (witer r (S n)) with (F (restr e (witer r n))).
      rewrite IH, restr_scale.
      apply Hscale; [ exact Ha | apply restr_wf, witer_wf; exact Hr ].
    Qed.

    Lemma sem_while_scale
          (Hscale : forall a r, (0 <= a)%R -> cqs_wf r ->
                                F (cqs_scale a r) = cqs_scale a (F r))
          (a : R) (Ha : (0 <= a)%R) (r : cqs) :
      cqs_wf r ->
      sem_while e F (cqs_scale a r) = cqs_scale a (sem_while e F r).
    Proof.
      intros Hr; rewrite !sem_while_sum.
      rewrite (cqs_sum_scale a (fun i : nat => restrn e (witer r i))
                             (witer_fam r Hr)).
      f_equal; apply funext; intros i.
      rewrite (witer_scale Hscale a Ha r Hr i); apply restrn_scale.
    Qed.

    Section WhileNormal.
      Context (Hnorm : forall (J : Type) (G : J -> cqs), cqs_fam G ->
                         F (cqs_sum G) = cqs_sum (fun j => F (G j)))
              (Hpres : forall (J : Type) (G : J -> cqs), cqs_fam G ->
                         cqs_fam (fun j => F (G j))).

      Lemma witer_sum (J : Type) (G : J -> cqs) (HG : cqs_fam G) (i : nat) :
        witer (cqs_sum G) i = cqs_sum (fun j => witer (G j) i)
        /\ cqs_fam (fun j => witer (G j) i).
      Proof.
        induction i as [| n IH]; [ split; [ reflexivity | exact HG ] |].
        destruct IH as [IHeq IHfam]; split.
        - change (witer (cqs_sum G) (S n))
            with (F (restr e (witer (cqs_sum G) n))).
          rewrite IHeq, restr_sum, (Hnorm J _ (cqs_fam_restr e _ IHfam)).
          reflexivity.
        - apply Hpres, cqs_fam_restr, IHfam.
      Qed.

      Lemma sem_while_normal (J : Type) (G : J -> cqs) :
        cqs_fam G ->
        sem_while e F (cqs_sum G) = cqs_sum (fun j => sem_while e F (G j)).
      Proof.
        intros HG.
        assert (HGwf : forall j, cqs_wf (G j)) by (apply cqs_fam_wf; exact HG).
        assert (Hsum_wf : cqs_wf (cqs_sum G)) by (apply cqs_fam_sum_wf; exact HG).
        apply funext; intros m.
        set (H := fun (i : nat) (j : J) => restrn e (witer (G j) i) m).
        assert (H1 : forall i, tcp_summable (H i)).
        { intros i; apply (cqs_fam_ptwise _
                             (cqs_fam_restrn e _ (proj2 (witer_sum J G HG i)))). }
        assert (H3 : forall j, tcp_summable (fun i => H i j))
          by (intros j; apply (cqs_fam_ptwise _ (witer_fam (G j) (HGwf j)))).
        assert (H2 : tcp_summable (fun i => tcp_sum (H i))).
        { assert (Heq : (fun i : nat => tcp_sum (H i))
                        = (fun i : nat => restrn e (witer (cqs_sum G) i) m)).
          { apply funext; intros i; unfold H.
            destruct (witer_sum J G HG i) as [Hi _].
            rewrite Hi, restrn_sum; reflexivity. }
          rewrite Heq.
          apply (cqs_fam_ptwise _ (witer_fam (cqs_sum G) Hsum_wf)). }
        assert (Hwfam : cqs_fam (fun j => sem_while e F (G j))).
        { unfold cqs_fam.
          refine (proj1 (tsum_pairs_le_iter
                           (fun (j : J) (m0 : cmem) =>
                              tcp_trace (sem_while e F (G j) m0)) _ _)).
          - intros j; apply tcp_summable_trace,
              (sem_while_wf_trace (G j) (HGwf j)).
          - apply (summable_mono _ (fun j => cqs_trace (G j)));
              [ apply cqs_fam_trace; exact HG |].
            intros j; apply (sem_while_wf_trace (G j) (HGwf j)). }
        assert (H4 : tcp_summable (fun j => tcp_sum (fun i => H i j))).
        { assert (Heq : (fun j : J => tcp_sum (fun i : nat => H i j))
                        = (fun j : J => sem_while e F (G j) m))
            by (apply funext; intros j; rewrite sem_while_sum; reflexivity).
          rewrite Heq; apply (cqs_fam_ptwise _ Hwfam). }
        transitivity (tcp_sum (fun i : nat => tcp_sum (H i))).
        { rewrite sem_while_sum.
          change (cqs_sum (fun i : nat => restrn e (witer (cqs_sum G) i)) m)
            with (tcp_sum (fun i : nat => restrn e (witer (cqs_sum G) i) m)).
          f_equal; apply funext; intros i; unfold H.
          destruct (witer_sum J G HG i) as [Hi _].
          rewrite Hi, restrn_sum; reflexivity. }
        rewrite (tcp_sum_swap H H1 H2 H3 H4).
        unfold cqs_sum; reflexivity.
      Qed.

    End WhileNormal.

  End While.

  Theorem denote_wf_trace (c : prog) :
    wt c ->
    forall r, cqs_wf r ->
      cqs_wf (denote c r) /\ (cqs_trace (denote c r) <= cqs_trace r)%R.
  Proof.
    induction c as [ | x e | x e | e c1 IH1 c2 IH2 | e c1 IH1
                   | c1 IH1 c2 IH2 | Pq e | Pq e | x Pq e ];
      intros Hwt r Hr; cbn [denote] in *.
    - (* Skip *) split; [ exact Hr | apply Rle_refl ].
    - (* Assign *) apply sem_assign_wf_trace; exact Hr.
    - (* Sample *) apply sem_sample_wf_trace; exact Hr.
    - (* Cond *)
      cbn [wt] in Hwt; destruct Hwt as [Hwt1 Hwt2].
      destruct (IH1 Hwt1 (restr e r) (restr_wf e r Hr)) as [Hw1 Hb1].
      destruct (IH2 Hwt2 (restrn e r) (restrn_wf e r Hr)) as [Hw2 Hb2].
      split.
      + apply cqs_add_wf; assumption.
      + rewrite (cqs_trace_add _ _ Hw1 Hw2).
        rewrite <- (cqs_trace_restr_split e r Hr).
        apply Rplus_le_compat; assumption.
    - (* While *)
      cbn [wt] in Hwt.
      apply (sem_while_wf_trace e (denote c1) (IH1 Hwt) r Hr).
    - (* Seq *)
      cbn [wt] in Hwt; destruct Hwt as [Hwt1 Hwt2].
      destruct (IH1 Hwt1 r Hr) as [Hw1 Hb1].
      destruct (IH2 Hwt2 _ Hw1) as [Hw2 Hb2].
      split; [ exact Hw2 | eapply Rle_trans; eassumption ].
    - (* QInit *)
      cbn [wt] in Hwt.
      destruct (wf_trace_of_pointwise (sem_qinit Pq e r) r
                  (fun m => sem_qinit_trace_pt Pq e r m (Hwt m)) Hr) as [Hw Hb].
      split; [ exact Hw | rewrite Hb; apply Rle_refl ].
    - (* QApply *)
      cbn [wt] in Hwt.
      destruct (wf_trace_of_pointwise (sem_qapply Pq e r) r
                  (fun m => sem_qapply_trace_pt Pq e r m (Hwt m)) Hr) as [Hw Hb].
      split; [ exact Hw | rewrite Hb; apply Rle_refl ].
    - (* Measure *)
      cbn [wt] in Hwt.
      apply sem_measure_wf_trace; [ exact Hwt | exact Hr ].
  Qed.

  Corollary denote_wf (c : prog) :
    wt c -> forall r, cqs_wf r -> cqs_wf (denote c r).
  Proof. intros Hwt r Hr; apply (denote_wf_trace c Hwt r Hr). Qed.

  (* ================================================================= *)
  (** ** [[c]] is additive

      A cq-superoperator is in particular additive on the positive cone. This
      is what lets a state be split -- by the value of a classical expression,
      or into its pure components -- and the pieces recombined afterwards, so
      it is a prerequisite for rules Case and If1 and for the converse of
      Lemma 36.

      Proved for loop-free programs, for the same reason as
      [denote_wf_trace]. *)



  Lemma cqs_add_assoc4 (a b c d : cqs) :
    cqs_add (cqs_add a b) (cqs_add c d)
    = cqs_add (cqs_add a c) (cqs_add b d).
  Proof.
    apply funext; intros m; unfold cqs_add.
    rewrite <- !tcp_add_assoc; f_equal.
    rewrite !tcp_add_assoc; f_equal; apply tcp_add_comm.
  Qed.

  Theorem denote_add (c : prog) :
    wt c ->
    forall r s, cqs_wf r -> cqs_wf s ->
      denote c (cqs_add r s) = cqs_add (denote c r) (denote c s).
  Proof.
    induction c as [ | y e | y e | e c1 IH1 c2 IH2 | e c1 IH1
                   | c1 IH1 c2 IH2 | Pq e | Pq e | y Pq e ];
      intros Hwt r s Hr Hs; cbn [denote] in *.
    - (* Skip *) reflexivity.
    - (* Assign *)
      apply funext; intros m'; unfold sem_assign, cqs_add.
      rewrite <- (tcp_sum_add _ _ _ _ (assign_inner_wf y e r m' Hr)
                                     (assign_inner_wf y e s m' Hs)).
      f_equal; apply funext; intros a.
      destruct (excluded_middle_informative (acond y e m' a));
        [ reflexivity | symmetry; apply tcp_add_zero ].
    - (* Sample *)
      apply funext; intros m'; unfold sem_sample, cqs_add.
      rewrite <- (tcp_sum_add _ _ _ _ (sample_inner_wf y e r m' Hr)
                                     (sample_inner_wf y e s m' Hs)).
      f_equal; apply funext; intros a; apply tcp_scale_add.
    - (* Cond *)
      cbn [wt] in Hwt; destruct Hwt as [Hwt1 Hwt2].
      rewrite restr_add, restrn_add.
      rewrite (IH1 Hwt1 _ _ (restr_wf e r Hr) (restr_wf e s Hs)).
      rewrite (IH2 Hwt2 _ _ (restrn_wf e r Hr) (restrn_wf e s Hs)).
      apply cqs_add_assoc4.
    - (* While *)
      cbn [wt] in Hwt.
      apply (sem_while_add e (denote c1) (denote_wf_trace c1 Hwt)
               (fun a b Ha Hb => IH1 Hwt a b Ha Hb) r s Hr Hs).
    - (* Seq *)
      cbn [wt] in Hwt; destruct Hwt as [Hwt1 Hwt2].
      rewrite (IH1 Hwt1 _ _ Hr Hs).
      apply (IH2 Hwt2); apply (denote_wf c1 Hwt1); assumption.
    - (* QInit *)
      apply funext; intros m; unfold sem_qinit, cqs_add.
      rewrite tcp_conj_add, tcp_ptraceL_add, tcp_tensor_add_r, tcp_conj_add;
        reflexivity.
    - (* QApply *)
      apply funext; intros m; unfold sem_qapply, cqs_add; apply tcp_conj_add.
    - (* Measure *)
      apply funext; intros m'; unfold sem_measure, cqs_add.
      cbn [wt] in Hwt.
      transitivity
        (tcp_sum (fun a : ctype y =>
           tcp_add (tcp_conj (olift Pq (ev e (cupd m' y a) (m' y)))
                             (r (cupd m' y a)))
                   (tcp_conj (olift Pq (ev e (cupd m' y a) (m' y)))
                             (s (cupd m' y a))))).
      { f_equal; apply funext; intros a; apply tcp_conj_add. }
      apply (tcp_sum_add _ _ _ _
               (measure_inner_wf y Pq e Hwt r m' Hr)
               (measure_inner_wf y Pq e Hwt s m' Hs)).
  Qed.

  (** [[c]] commutes with scaling by a nonnegative real, needed by the
      converse of Lemma 36: the witness there is a sum of *scaled*
      per-component witnesses, and scaling has to be pushed through [[c]]
      the same way addition and arbitrary sums already are. The nonnegativity
      is not used by any single clause below (every axiom used --
      [tcp_scale_sum], [tcp_conj_scale], [tcp_ptraceL_scale],
      [tcp_scale_tensor_r] -- holds for every real), but it is what keeps a
      *scaled* state inside [T^+_cq[V]] in the first place, so it is carried
      throughout for consistency with the rest of the trusted surface. *)

  Theorem denote_scale (c : prog) :
    wt c ->
    forall (a : R) (r : cqs), (0 <= a)%R -> cqs_wf r ->
      denote c (cqs_scale a r) = cqs_scale a (denote c r).
  Proof.
    induction c as [ | y e | y e | e c1 IH1 c2 IH2 | e c1 IH1
                   | c1 IH1 c2 IH2 | Pq e | Pq e | y Pq e ];
      intros Hwt a r Ha Hr; cbn [denote] in *.
    - (* Skip *) reflexivity.
    - (* Assign *)
      apply funext; intros m'; unfold sem_assign, cqs_scale.
      rewrite (tcp_scale_sum _ _ _ _ (assign_inner_wf y e r m' Hr)).
      f_equal; apply funext; intros a'.
      destruct (excluded_middle_informative (acond y e m' a'));
        [ reflexivity | symmetry; apply tcp_scale_zero ].
    - (* Sample *)
      apply funext; intros m'; unfold sem_sample, cqs_scale.
      rewrite (tcp_scale_sum _ _ _ _ (sample_inner_wf y e r m' Hr)).
      f_equal; apply funext; intros a'.
      rewrite !tcp_scale_assoc; f_equal; apply Rmult_comm.
    - (* Cond *)
      cbn [wt] in Hwt; destruct Hwt as [Hwt1 Hwt2].
      rewrite restr_scale, restrn_scale.
      rewrite (IH1 Hwt1 a _ Ha (restr_wf e r Hr)).
      rewrite (IH2 Hwt2 a _ Ha (restrn_wf e r Hr)).
      unfold cqs_add, cqs_scale; apply funext; intros m.
      symmetry; apply tcp_scale_add.
    - (* While *)
      cbn [wt] in Hwt.
      apply (sem_while_scale e (denote c1) (denote_wf_trace c1 Hwt)
               (fun a' r' Ha' Hr' => IH1 Hwt a' r' Ha' Hr') a Ha r Hr).
    - (* Seq *)
      cbn [wt] in Hwt; destruct Hwt as [Hwt1 Hwt2].
      rewrite (IH1 Hwt1 a _ Ha Hr).
      apply (IH2 Hwt2 a); [ exact Ha | apply (denote_wf c1 Hwt1); exact Hr ].
    - (* QInit *)
      apply funext; intros m; unfold sem_qinit, cqs_scale.
      rewrite tcp_conj_scale, tcp_ptraceL_scale, <- tcp_scale_tensor_r,
        tcp_conj_scale; reflexivity.
    - (* QApply *)
      apply funext; intros m; unfold sem_qapply, cqs_scale; apply tcp_conj_scale.
    - (* Measure *)
      apply funext; intros m'; unfold sem_measure, cqs_scale.
      cbn [wt] in Hwt.
      transitivity
        (tcp_sum (fun a' : ctype y =>
           tcp_scale a (tcp_conj (olift Pq (ev e (cupd m' y a') (m' y)))
                                 (r (cupd m' y a'))))).
      { f_equal; apply funext; intros a'; apply tcp_conj_scale. }
      symmetry; apply (tcp_scale_sum _ _ _ _
                          (measure_inner_wf y Pq e Hwt r m' Hr)).
  Qed.

  (* ================================================================= *)
  (** ** Normality of [[c]]

      [denote_add] says [[c]] is additive; rule Case (Lemma 48) needs the same
      for a family indexed by an arbitrary type, because the case split is
      over the values of a classical expression rather than over two branches.
      The converse of Lemma 36 needs it for the same reason.

      The clauses that have a sum of their own -- assignment, sampling,
      measurement -- are the interesting ones: there the two sums have to be
      exchanged, which is [tcp_sum_swap] and so needs all four of its
      summability side conditions. *)

  Lemma cqs_fam_denote {J} (F : J -> cqs) (c : prog) :
    wt c -> cqs_fam F -> cqs_fam (fun j => denote c (F j)).
  Proof.
    intros Hwt H; unfold cqs_fam.
    refine (proj1 (tsum_pairs_le_iter
                     (fun (j : J) (m : cmem) => tcp_trace (denote c (F j) m))
                     _ _)).
    - intros j; apply tcp_summable_trace.
      apply (denote_wf c Hwt), (cqs_fam_wf F H j).
    - apply (summable_mono _ (fun j => cqs_trace (F j)));
        [ apply cqs_fam_trace; exact H |].
      intros j; apply (proj2 (denote_wf_trace c Hwt _ (cqs_fam_wf F H j))).
  Qed.

  (** Sums of families, pointwise. *)



  Theorem denote_sum (c : prog) :
    wt c ->
    forall (J : Type) (F : J -> cqs), cqs_fam F ->
      denote c (cqs_sum F) = cqs_sum (fun j => denote c (F j)).
  Proof.
    induction c as [ | y e | y e | e c1 IH1 c2 IH2 | e c1 IH1
                   | c1 IH1 c2 IH2 | Pq e | Pq e | y Pq e ];
      intros Hwt J F HF.
    - (* Skip *) reflexivity.
    - (* Assign *)
      apply funext; intros m'.
      set (G := fun (j : J) (a : ctype y) =>
                  if excluded_middle_informative (acond y e m' a)
                  then F j (cupd m' y a) else tcp_zero).
      assert (Hin : forall a,
                 tcp_sum (fun j => G j a)
                 = (if excluded_middle_informative (acond y e m' a)
                    then cqs_sum F (cupd m' y a) else tcp_zero)).
      { intros a; unfold G, cqs_sum.
        destruct (excluded_middle_informative (acond y e m' a));
          [ reflexivity | apply tcp_sum_zero; intros; reflexivity ]. }
      assert (H1 : forall j, tcp_summable (G j))
        by (intros j; apply (assign_inner_wf y e (F j) m' (cqs_fam_wf F HF j))).
      assert (H2 : tcp_summable (fun j => tcp_sum (G j))).
      { unfold G;
          apply (cqs_fam_ptwise (fun j => denote (Assign y e) (F j))
                   (cqs_fam_denote F (Assign y e) Hwt HF) m'). }
      assert (H3 : forall a, tcp_summable (fun j => G j a)).
      { intros a; apply tcp_summable_trace.
        apply (summable_mono _ (fun j => tcp_trace (F j (cupd m' y a)))).
        - apply tcp_summable_trace, (cqs_fam_ptwise F HF).
        - intros j; unfold G;
            destruct (excluded_middle_informative (acond y e m' a));
            [ apply Rle_refl | rewrite tcp_trace_zero; apply tcp_trace_nonneg ]. }
      assert (H4 : tcp_summable (fun a => tcp_sum (fun j => G j a))).
      { assert (Heq : (fun a => tcp_sum (fun j => G j a))
                      = (fun a : ctype y =>
                           if excluded_middle_informative (acond y e m' a)
                           then cqs_sum F (cupd m' y a) else tcp_zero))
          by (apply funext; exact Hin).
        rewrite Heq.
        apply (assign_inner_wf y e (cqs_sum F) m' (cqs_fam_sum_wf F HF)). }
      cbn [denote]; unfold sem_assign at 1.
      transitivity (tcp_sum (fun a : ctype y => tcp_sum (fun j => G j a)));
        [ f_equal; apply funext; intros a; symmetry; apply Hin |].
      rewrite <- (tcp_sum_swap G H1 H2 H3 H4); reflexivity.
    - (* Sample *)
      apply funext; intros m'.
      set (G := fun (j : J) (a : ctype y) =>
                  tcp_scale (ev e (cupd m' y a) (m' y)) (F j (cupd m' y a))).
      assert (Hin : forall a,
                 tcp_sum (fun j => G j a)
                 = tcp_scale (ev e (cupd m' y a) (m' y))
                             (cqs_sum F (cupd m' y a))).
      { intros a; unfold G, cqs_sum; symmetry.
        apply (tcp_scale_sum _ _ _ _ (cqs_fam_ptwise F HF (cupd m' y a))). }
      assert (H1 : forall j, tcp_summable (G j))
        by (intros j; apply (sample_inner_wf y e (F j) m' (cqs_fam_wf F HF j))).
      assert (H2 : tcp_summable (fun j => tcp_sum (G j))).
      { unfold G;
          apply (cqs_fam_ptwise (fun j => denote (Sample y e) (F j))
                   (cqs_fam_denote F (Sample y e) Hwt HF) m'). }
      assert (H3 : forall a, tcp_summable (fun j => G j a)).
      { intros a; apply tcp_summable_trace.
        apply (summable_mono _ (fun j => tcp_trace (F j (cupd m' y a)))).
        - apply tcp_summable_trace, (cqs_fam_ptwise F HF).
        - intros j; unfold G; rewrite tcp_trace_scale.
          rewrite <- (Rmult_1_l (tcp_trace (F j (cupd m' y a)))) at 2.
          apply Rmult_le_compat_r;
            [ apply tcp_trace_nonneg | apply dfun_le1_pt ]. }
      assert (H4 : tcp_summable (fun a => tcp_sum (fun j => G j a))).
      { assert (Heq : (fun a => tcp_sum (fun j => G j a))
                      = (fun a : ctype y =>
                           tcp_scale (ev e (cupd m' y a) (m' y))
                                     (cqs_sum F (cupd m' y a))))
          by (apply funext; exact Hin).
        rewrite Heq.
        apply (sample_inner_wf y e (cqs_sum F) m' (cqs_fam_sum_wf F HF)). }
      cbn [denote]; unfold sem_sample at 1.
      transitivity (tcp_sum (fun a : ctype y => tcp_sum (fun j => G j a)));
        [ f_equal; apply funext; intros a; symmetry; apply Hin |].
      rewrite <- (tcp_sum_swap G H1 H2 H3 H4); reflexivity.
    - (* Cond *)
      cbn [wt] in Hwt; destruct Hwt as [Hwt1 Hwt2].
      cbn [denote]; rewrite restr_sum, restrn_sum.
      rewrite (IH1 Hwt1 J _ (cqs_fam_restr e F HF)).
      rewrite (IH2 Hwt2 J _ (cqs_fam_restrn e F HF)).
      apply cqs_sum_add;
        [ apply (cqs_fam_denote _ c1 Hwt1), cqs_fam_restr; exact HF
        | apply (cqs_fam_denote _ c2 Hwt2), cqs_fam_restrn; exact HF ].
    - (* While *)
      cbn [wt] in Hwt; cbn [denote].
      apply (sem_while_normal e (denote c1) (denote_wf_trace c1 Hwt)
               (fun K H HK => IH1 Hwt K H HK)
               (fun K H HK => cqs_fam_denote H c1 Hwt HK) J F HF).
    - (* Seq *)
      cbn [wt] in Hwt; destruct Hwt as [Hwt1 Hwt2].
      cbn [denote]; rewrite (IH1 Hwt1 J F HF).
      apply (IH2 Hwt2), (cqs_fam_denote F c1 Hwt1 HF).
    - (* QInit *)
      apply funext; intros m.
      assert (S0 : tcp_summable (fun j => F j m)) by apply (cqs_fam_ptwise F HF).
      assert (S1 : tcp_summable
                     (fun j => tcp_conj (oadj (Usplit Pq)) (F j m))).
      { apply (tcp_summable_conj _ _
                 (oisometry_oadj _ (Wsplit_unitary qvar qtype Pq)) S0). }
      assert (S2 : tcp_summable
                     (fun j => tcp_ptraceL
                                 (tcp_conj (oadj (Usplit Pq)) (F j m))))
        by (apply tcp_summable_ptraceL, S1).
      cbn [denote]; unfold sem_qinit at 1, cqs_sum at 1.
      (* through the discard ... *)
      transitivity
        (tcp_conj (Usplit Pq)
           (tcp_tensor (tcp_proj (ev e m))
              (tcp_sum (fun j : J =>
                 tcp_ptraceL (tcp_conj (oadj (Usplit Pq)) (F j m)))))).
      { f_equal; f_equal.
        rewrite (tcp_conj_sum _ _ _ _ _ S0); apply (tcp_ptraceL_sum _ S1). }
      (* ... then past the fresh state ... *)
      transitivity
        (tcp_conj (Usplit Pq)
           (tcp_sum (fun j : J =>
              tcp_tensor (tcp_proj (ev e m))
                (tcp_ptraceL (tcp_conj (oadj (Usplit Pq)) (F j m)))))).
      { f_equal; apply (tcp_tensor_sum_r _ _ _ _ _ S2). }
      (* ... and out of the conjugation. *)
      apply (tcp_conj_sum _ _ _ _ _ (tcp_summable_tensor_r _ _ S2)).
    - (* QApply *)
      apply funext; intros m.
      cbn [denote]; unfold sem_qapply at 1, cqs_sum at 1.
      apply (tcp_conj_sum _ _ _ _ _ (cqs_fam_ptwise F HF m)).
    - (* Measure *)
      cbn [wt] in Hwt.
      apply funext; intros m'.
      set (G := fun (j : J) (a : ctype y) =>
                  tcp_conj (olift Pq (ev e (cupd m' y a) (m' y)))
                           (F j (cupd m' y a))).
      assert (Hin : forall a,
                 tcp_sum (fun j => G j a)
                 = tcp_conj (olift Pq (ev e (cupd m' y a) (m' y)))
                            (cqs_sum F (cupd m' y a))).
      { intros a; unfold G, cqs_sum; symmetry.
        apply (tcp_conj_sum _ _ _ _ _ (cqs_fam_ptwise F HF (cupd m' y a))). }
      assert (H1 : forall j, tcp_summable (G j))
        by (intros j;
            apply (measure_inner_wf y Pq e Hwt (F j) m' (cqs_fam_wf F HF j))).
      assert (H2 : tcp_summable (fun j => tcp_sum (G j))).
      { unfold G;
          apply (cqs_fam_ptwise (fun j => denote (Measure y Pq e) (F j))
                   (cqs_fam_denote F (Measure y Pq e) Hwt HF) m'). }
      assert (H3 : forall a, tcp_summable (fun j => G j a)).
      { intros a; apply tcp_summable_trace.
        apply (summable_mono _ (fun j => tcp_trace (F j (cupd m' y a)))).
        - apply tcp_summable_trace, (cqs_fam_ptwise F HF).
        - intros j; unfold G; apply (measure_term_le y Pq e Hwt). }
      assert (H4 : tcp_summable (fun a => tcp_sum (fun j => G j a))).
      { assert (Heq : (fun a => tcp_sum (fun j => G j a))
                      = (fun a : ctype y =>
                           tcp_conj (olift Pq (ev e (cupd m' y a) (m' y)))
                                    (cqs_sum F (cupd m' y a))))
          by (apply funext; exact Hin).
        rewrite Heq.
        apply (measure_inner_wf y Pq e Hwt (cqs_sum F) m'
                 (cqs_fam_sum_wf F HF)). }
      cbn [denote]; unfold sem_measure at 1.
      transitivity (tcp_sum (fun a : ctype y => tcp_sum (fun j => G j a)));
        [ f_equal; apply funext; intros a; symmetry; apply Hin |].
      rewrite <- (tcp_sum_swap G H1 H2 H3 H4); reflexivity.
  Qed.

  Corollary denote_trace_le (c : prog) :
    wt c -> forall r, cqs_wf r -> (cqs_trace (denote c r) <= cqs_trace r)%R.
  Proof. intros Hwt r Hr; apply (denote_wf_trace c Hwt r Hr). Qed.

  (* ================================================================= *)
  (** ** Locality

      Definition 10: "we call [c] X-local iff [[c]] = E (x) id_{V\X} for some
      cq-superoperator E on X", and Lemma 11: "if [fv(c) subseteq X] then [c] is
      X-local".

      Both need an abstract notion of superoperator, which the substrate does
      not yet have -- it is needed first by rules Frame and Equal, in Phase 2,
      and the project's discipline is to add to the signature only when a proof
      demands it. Deferred to there. *)

End SemTheory.
