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
      [m' x]. *)
  Definition sem_assign (x : cvar) (e : expr (ctype x)) (r : cqs) : cqs :=
    fun m' =>
      tcp_sum (fun a : { a : ctype x | ev e (cupd m' x a) = m' x } =>
                 r (cupd m' x (proj1_sig a))).

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
    - (* the image memory: exactly one preimage, [a := m x] *)
      rewrite cqdirac_same.
      assert (Hx : ev e (cupd m0 x (m x)) = m0 x)
        by (rewrite Hback, Hm0x; reflexivity).
      rewrite (tcp_sum_singleton _ (exist _ (m x) Hx)).
      + cbn [proj1_sig]; rewrite Hback; apply cqdirac_same.
      + intros [a Ha] Hj; cbn [proj1_sig].
        apply cqdirac_other; intros Heq.
        apply Hj, sig_eq; cbn [proj1_sig].
        rewrite <- (cupd_same m0 x a), Heq; reflexivity.
    - (* any other memory: every term vanishes *)
      rewrite cqdirac_other by exact Hne.
      apply tcp_sum_zero; intros [a Ha]; cbn [proj1_sig].
      apply cqdirac_other; intros Heq.
      apply Hne; transitivity (cupd m x (m' x)).
      + rewrite <- Heq, cupd_cupd, cupd_id; reflexivity.
      + unfold m0; f_equal; rewrite <- Ha, Heq; reflexivity.
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
  (** *** Assignment

      The preimage of [m'] is indexed by the old value of [x] subject to
      [[e](m'(x := a)) = m' x], and that side condition is what makes the map
      to source memories injective: it pins [m' x] down. *)

  Section AssignWf.
    Context (x : cvar) (e : expr (ctype x)).

    Let Pre (m' : cmem) : Type := { a : ctype x | ev e (cupd m' x a) = m' x }.
    Let src (m' : cmem) (a : Pre m') : cmem := cupd m' x (proj1_sig a).

    Lemma assign_src_fib (m' : cmem) (a b : Pre m') : src m' a = src m' b -> a = b.
    Proof.
      unfold src; destruct a as [a Ha], b as [b Hb]; cbn [proj1_sig].
      intros Heq; apply sig_eq; cbn [proj1_sig].
      rewrite <- (cupd_same m' x a), Heq, cupd_same; reflexivity.
    Qed.

    Lemma assign_src_sep (m1 : cmem) (a : Pre m1) (m2 : cmem) (b : Pre m2) :
      src m1 a = src m2 b -> m1 = m2.
    Proof.
      unfold src; destruct a as [a Ha], b as [b Hb]; cbn [proj1_sig].
      intros Heq; apply funext; intros y.
      destruct (cvar_eq_dec x y) as [Hxy | Hne].
      - subst y; rewrite <- Ha, <- Hb, Heq; reflexivity.
      - rewrite <- (cupd_other m1 x y a Hne), Heq.
        apply cupd_other; exact Hne.
    Qed.

    Lemma assign_inner_wf (r : cqs) (m' : cmem) :
      cqs_wf r -> tcp_summable (fun a : Pre m' => r (src m' a)).
    Proof.
      intros Hr; apply tcp_summable_trace.
      apply (summable_inj (src m') (fun m => tcp_trace (r m))).
      - apply assign_src_fib.
      - apply cqs_wf_iff; exact Hr.
    Qed.

    Lemma assign_trace (r : cqs) (m' : cmem) :
      cqs_wf r ->
      tcp_trace (sem_assign x e r m')
      = tsum (fun a : Pre m' => tcp_trace (r (src m' a))).
    Proof.
      intros Hr; apply tcp_trace_sum, assign_inner_wf; exact Hr.
    Qed.

    Lemma sem_assign_wf_trace (r : cqs) :
      cqs_wf r ->
      cqs_wf (sem_assign x e r)
      /\ (cqs_trace (sem_assign x e r) <= cqs_trace r)%R.
    Proof.
      intros Hr.
      assert (Heq : (fun m' => tcp_trace (sem_assign x e r m'))
                    = (fun m' => tsum (fun a : Pre m' => tcp_trace (r (src m' a)))))
        by (apply funext; intros m'; apply assign_trace; exact Hr).
      destruct (tsum_partition_le Pre src assign_src_sep assign_src_fib
                  (fun m => tcp_trace (r m)) (cqs_trace_fn_nonneg r)
                  (proj1 (cqs_wf_iff r) Hr)) as [Hs Hle].
      split.
      - apply cqs_wf_iff; rewrite Heq; exact Hs.
      - unfold cqs_trace; rewrite Heq; exact Hle.
    Qed.

  End AssignWf.

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

  Theorem denote_wf_trace (c : prog) :
    wt c -> loopfree c ->
    forall r, cqs_wf r ->
      cqs_wf (denote c r) /\ (cqs_trace (denote c r) <= cqs_trace r)%R.
  Proof.
    induction c as [ | x e | x e | e c1 IH1 c2 IH2 | e c1 IH1
                   | c1 IH1 c2 IH2 | Pq e | Pq e | x Pq e ];
      intros Hwt Hlf r Hr; cbn [denote] in *.
    - (* Skip *) split; [ exact Hr | apply Rle_refl ].
    - (* Assign *) apply sem_assign_wf_trace; exact Hr.
    - (* Sample *) apply sem_sample_wf_trace; exact Hr.
    - (* Cond *)
      cbn [wt loopfree] in Hwt, Hlf.
      destruct Hwt as [Hwt1 Hwt2]; destruct Hlf as [Hlf1 Hlf2].
      destruct (IH1 Hwt1 Hlf1 (restr e r) (restr_wf e r Hr)) as [Hw1 Hb1].
      destruct (IH2 Hwt2 Hlf2 (restrn e r) (restrn_wf e r Hr)) as [Hw2 Hb2].
      split.
      + apply cqs_add_wf; assumption.
      + rewrite (cqs_trace_add _ _ Hw1 Hw2).
        rewrite <- (cqs_trace_restr_split e r Hr).
        apply Rplus_le_compat; assumption.
    - (* While: excluded by [loopfree] *)
      cbn [loopfree] in Hlf; destruct Hlf.
    - (* Seq *)
      cbn [wt loopfree] in Hwt, Hlf.
      destruct Hwt as [Hwt1 Hwt2]; destruct Hlf as [Hlf1 Hlf2].
      destruct (IH1 Hwt1 Hlf1 r Hr) as [Hw1 Hb1].
      destruct (IH2 Hwt2 Hlf2 _ Hw1) as [Hw2 Hb2].
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
    wt c -> loopfree c -> forall r, cqs_wf r -> cqs_wf (denote c r).
  Proof. intros Hwt Hlf r Hr; apply (denote_wf_trace c Hwt Hlf r Hr). Qed.

  Corollary denote_trace_le (c : prog) :
    wt c -> loopfree c ->
    forall r, cqs_wf r -> (cqs_trace (denote c r) <= cqs_trace r)%R.
  Proof. intros Hwt Hlf r Hr; apply (denote_wf_trace c Hwt Hlf r Hr). Qed.

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
