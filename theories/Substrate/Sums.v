(** * Unordered sums of nonnegative reals, and discrete (sub)distributions.

    Section 2 of the paper works with sums over arbitrary, possibly uncountable
    index sets: [D(X)] is the set of functions [X -> R>=0], and a
    subdistribution is one with [sum_{x in X} mu(x) <= 1]. Such a sum is the
    supremum of its finite partial sums, which is what we define here.

    This file is concrete, proved mathematics -- not part of the substrate
    signature. Sums of *operators* (section 2's [sum_i rho_i] over trace-class
    operators) are a different matter and belong to the substrate, because they
    need the order structure on positive operators.

    Following the project's discipline, the lemma set here is grown on demand
    by the proofs that need it rather than written speculatively. Notably,
    Fubini for unordered nonnegative sums -- needed only by rule JointSample,
    for [marginal1] / [marginal2] -- is deliberately not here yet. *)

From Stdlib Require Import List Lra.
From QRHL.Substrate Require Import Ambient.
Import ListNotations.

Local Open Scope R_scope.

Section Sums.
  Context {I : Type}.

  Definition nonneg (f : I -> R) : Prop := forall i, 0 <= f i.

  (** Partial sum over a finite list of indices. *)
  Fixpoint lsum (f : I -> R) (l : list I) : R :=
    match l with
    | []     => 0
    | i :: t => f i + lsum f t
    end.

  (** The set of finite partial sums, taken over *duplicate-free* lists: a
      finite subset of [I], presented as a list. *)
  Definition PSum (f : I -> R) (r : R) : Prop :=
    exists l, NoDup l /\ lsum f l = r.

  Definition summable (f : I -> R) : Prop := bound (PSum f).

  Lemma PSum_0 (f : I -> R) : PSum f 0.
  Proof. exists []; split; [ constructor | reflexivity ]. Qed.

  Lemma PSum_inhabited (f : I -> R) : exists r, PSum f r.
  Proof. exists 0; apply PSum_0. Qed.

  (** The unordered sum. Total by fiat: junk value [0] when [f] is not
      summable, which keeps every downstream statement free of side
      conditions on well-definedness (the real side conditions reappear, where
      they belong, as [summable] hypotheses on the lemmas). *)
  Definition tsum (f : I -> R) : R :=
    match excluded_middle_informative (summable f) with
    | left H  => proj1_sig (completeness (PSum f) H (PSum_inhabited f))
    | right _ => 0
    end.

  Lemma tsum_is_lub (f : I -> R) : summable f -> is_lub (PSum f) (tsum f).
  Proof.
    intros Hs; unfold tsum.
    destruct (excluded_middle_informative (summable f)) as [H | H].
    - exact (proj2_sig (completeness (PSum f) H (PSum_inhabited f))).
    - contradiction.
  Qed.

  Lemma tsum_not_summable (f : I -> R) : ~ summable f -> tsum f = 0.
  Proof.
    intros Hs; unfold tsum.
    destruct (excluded_middle_informative (summable f)); [ contradiction | reflexivity ].
  Qed.

  (** [tsum] is an upper bound for every finite partial sum ... *)
  Lemma tsum_ub (f : I -> R) (l : list I) :
    summable f -> NoDup l -> lsum f l <= tsum f.
  Proof.
    intros Hs Hnd.
    destruct (tsum_is_lub f Hs) as [Hub _].
    apply Hub; exists l; split; [ exact Hnd | reflexivity ].
  Qed.

  (** ... and the least such. *)
  Lemma tsum_least (f : I -> R) (c : R) :
    summable f -> (forall l, NoDup l -> lsum f l <= c) -> tsum f <= c.
  Proof.
    intros Hs Hc.
    destruct (tsum_is_lub f Hs) as [_ Hlub].
    apply Hlub; intros r [l [Hnd <-]]; apply Hc; assumption.
  Qed.

  Lemma lsum_nonneg (f : I -> R) (l : list I) : nonneg f -> 0 <= lsum f l.
  Proof.
    intros Hf; induction l as [| i t IH]; simpl; [ lra |].
    specialize (Hf i); lra.
  Qed.

  Lemma tsum_nonneg (f : I -> R) : nonneg f -> 0 <= tsum f.
  Proof.
    intros Hf.
    destruct (classic (summable f)) as [Hs | Hs].
    - change 0 with (lsum f []).
      apply tsum_ub; [ exact Hs | constructor ].
    - rewrite tsum_not_summable by exact Hs; lra.
  Qed.

  Lemma tsum_unique (f : I -> R) (s : R) :
    summable f -> is_lub (PSum f) s -> tsum f = s.
  Proof.
    intros Hs Hlub.
    apply Rle_antisym.
    - destruct (tsum_is_lub f Hs) as [_ H]; apply H; apply Hlub.
    - destruct Hlub as [_ H]; apply H; apply tsum_is_lub; exact Hs.
  Qed.

  Lemma lsum_mono (f g : I -> R) :
    (forall i, f i <= g i) -> forall l, lsum f l <= lsum g l.
  Proof.
    intros Hfg l; induction l as [| i t IH]; simpl; [ lra |].
    specialize (Hfg i); lra.
  Qed.

  (** Domination: a family below a summable one is summable. Used pervasively,
      since almost every construction in the semantics only shrinks traces. *)
  Lemma summable_mono (f g : I -> R) :
    summable g -> (forall i, f i <= g i) -> summable f.
  Proof.
    intros [M HM] Hfg; exists M; intros r [l [Hnd <-]].
    eapply Rle_trans; [ apply (lsum_mono f g Hfg) |].
    apply HM; exists l; split; [ exact Hnd | reflexivity ].
  Qed.

  (** Monotonicity. Note [summable g] is required: without it [tsum g] is junk. *)
  Lemma tsum_mono (f g : I -> R) :
    nonneg f -> summable g -> (forall i, f i <= g i) -> tsum f <= tsum g.
  Proof.
    intros Hf Hg Hfg.
    assert (Hsf : summable f) by (apply (summable_mono f g); assumption).
    apply tsum_least; [ exact Hsf | intros l Hnd ].
    eapply Rle_trans; [ apply (lsum_mono f g Hfg) | apply tsum_ub; assumption ].
  Qed.

  Lemma summable_bounded (f : I -> R) (M : R) :
    (forall l, NoDup l -> lsum f l <= M) -> summable f.
  Proof.
    intros H; exists M; intros r [l [Hnd <-]]; apply H; exact Hnd.
  Qed.

  (** ** Point masses

      Needed for the semantics of assignment, which maps [delta_m] to
      [delta_{m(x := e)}] (section 3.3). *)

  Definition indicator (i : I) : I -> R :=
    fun j => if excluded_middle_informative (j = i) then 1 else 0.

  Lemma indicator_nonneg (i : I) : nonneg (indicator i).
  Proof.
    intros j; unfold indicator.
    destruct (excluded_middle_informative (j = i)); lra.
  Qed.

  Lemma lsum_indicator_absent (i : I) (l : list I) :
    ~ In i l -> lsum (indicator i) l = 0.
  Proof.
    induction l as [| j t IH]; simpl; [ reflexivity |].
    intros Hni; unfold indicator at 1.
    destruct (excluded_middle_informative (j = i)) as [-> |].
    - exfalso; apply Hni; left; reflexivity.
    - rewrite IH by (intros H; apply Hni; right; exact H); lra.
  Qed.

  Lemma lsum_indicator_present (i : I) (l : list I) :
    NoDup l -> In i l -> lsum (indicator i) l = 1.
  Proof.
    induction l as [| j t IH]; intros Hnd Hin; [ destruct Hin |].
    inversion Hnd as [| ? ? Hnj Hndt]; subst.
    simpl; unfold indicator at 1.
    destruct (excluded_middle_informative (j = i)) as [Heq | Hneq].
    - subst j.
      rewrite lsum_indicator_absent by exact Hnj; lra.
    - destruct Hin as [Heq | Hin]; [ congruence |].
      rewrite (IH Hndt Hin); lra.
  Qed.

  Lemma lsum_indicator_le1 (i : I) (l : list I) :
    NoDup l -> lsum (indicator i) l <= 1.
  Proof.
    intros Hnd; destruct (classic (In i l)) as [Hin | Hnin].
    - rewrite (lsum_indicator_present i l Hnd Hin); lra.
    - rewrite (lsum_indicator_absent i l Hnin); lra.
  Qed.

  Lemma summable_indicator (i : I) : summable (indicator i).
  Proof.
    apply summable_bounded with (M := 1); intros l Hnd.
    apply lsum_indicator_le1; exact Hnd.
  Qed.

  Lemma tsum_indicator (i : I) : tsum (indicator i) = 1.
  Proof.
    apply tsum_unique; [ apply summable_indicator |].
    split.
    - intros r [l [Hnd <-]]; apply lsum_indicator_le1; exact Hnd.
    - intros b Hb.
      apply (Hb 1); exists [i]; split.
      + constructor; [ intros H; inversion H | constructor ].
      + simpl; unfold indicator.
        destruct (excluded_middle_informative (i = i)); [ lra | congruence ].
  Qed.

End Sums.

Arguments nonneg {I} f /.
Arguments tsum {I} f.
Arguments summable {I} f.

(* ------------------------------------------------------------------ *)
(** ** Reindexing along an injection

    A sub-family of a summable family is summable. Cheap, and the easy part of
    the rearrangement machinery that [denote_summable] and rule JointSample
    both still need. These live outside the section because they relate sums
    over *two* different index types. *)

Lemma lsum_map {I J : Type} (h : J -> I) (f : I -> R) (l : list J) :
  lsum f (map h l) = lsum (fun j => f (h j)) l.
Proof.
  induction l as [| j t IH]; simpl; [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma NoDup_map_inj {I J : Type} (h : J -> I) (l : list J) :
  (forall a b, h a = h b -> a = b) -> NoDup l -> NoDup (map h l).
Proof.
  intros Hinj; induction l as [| j t IH]; simpl; intros Hnd; [ constructor |].
  inversion Hnd as [| ? ? Hnj Hndt]; subst.
  constructor; [| apply IH; exact Hndt ].
  intros Hin; apply in_map_iff in Hin; destruct Hin as [b [Heq Hb]].
  apply Hnj; rewrite <- (Hinj b j Heq); exact Hb.
Qed.

Lemma summable_inj {I J : Type} (h : J -> I) (f : I -> R) :
  (forall a b, h a = h b -> a = b) ->
  summable f -> summable (fun j => f (h j)).
Proof.
  intros Hinj Hf; apply summable_bounded with (M := tsum f).
  intros l Hnd; rewrite <- lsum_map.
  apply tsum_ub; [ exact Hf | apply NoDup_map_inj; assumption ].
Qed.

Lemma tsum_inj_le {I J : Type} (h : J -> I) (f : I -> R) :
  (forall a b, h a = h b -> a = b) -> summable f ->
  (tsum (fun j => f (h j)) <= tsum f)%R.
Proof.
  intros Hinj Hs; apply tsum_least.
  - apply summable_inj; assumption.
  - intros l Hnd; rewrite <- lsum_map.
    apply tsum_ub; [ exact Hs | apply NoDup_map_inj; assumption ].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Rearrangement

    The piece of analysis the development has been deferring. Three separate
    obligations reduce to it:

      - [denote_summable] in [Core/Semantics.v] -- that the denotation of a
        program really is a cq-superoperator. The clauses for assignment,
        sampling and measurement sum over the preimage of a memory update, so
        the total trace of the result is a sum *of sums*.
      - the converse of Lemma 36 in [Core/Judgment.v], whose proof assembles a
        witness out of one witness per pure component. The paper's equations
        (11)-(14) are exactly this bookkeeping.
      - the marginals [marginal_1(f)], [marginal_2(f)] of rule JointSample.

    All three have the same shape: an index set [I] is covered by fibres
    [P k] via a map [phi], injectively, and one wants to bound the iterated sum
    by the sum over [I]. The argument is the standard epsilon split -- each
    inner [tsum] is approximated from below by a finite partial sum, and the
    finitely many approximations are combined into a single finite subset of
    [I], which disjointness of the fibres makes duplicate-free. *)

Lemma lsum_app {I : Type} (f : I -> R) (l1 l2 : list I) :
  lsum f (l1 ++ l2) = (lsum f l1 + lsum f l2)%R.
Proof.
  induction l1 as [| i t IH]; simpl; [ lra | rewrite IH; lra ].
Qed.

Lemma NoDup_app {A : Type} (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
Proof.
  induction l1 as [| a t IH]; simpl; intros H1 H2 Hd; [ exact H2 |].
  inversion H1 as [| ? ? Hna Hnt]; subst.
  constructor.
  - intros Hin; apply in_app_iff in Hin; destruct Hin as [Hin | Hin].
    + contradiction.
    + apply (Hd a); [ left; reflexivity | exact Hin ].
  - apply IH; [ exact Hnt | exact H2 |].
    intros x Hx; apply Hd; right; exact Hx.
Qed.

(** An unordered sum is approximated from below by its finite partial sums.
    This is just the least-upper-bound property, read contrapositively. *)
Lemma tsum_approx {I : Type} (f : I -> R) (eps : R) :
  summable f -> (0 < eps)%R ->
  exists l, NoDup l /\ (tsum f - eps <= lsum f l)%R.
Proof.
  intros Hf Heps.
  destruct (classic (exists l, NoDup l /\ (tsum f - eps <= lsum f l)%R))
    as [H | H]; [ exact H |].
  exfalso.
  assert (Hub : is_upper_bound (PSum f) (tsum f - eps)).
  { intros r [l [Hnd <-]].
    destruct (Rle_or_lt (lsum f l) (tsum f - eps)) as [Hle | Hlt]; [ exact Hle |].
    exfalso; apply H; exists l; split; [ exact Hnd | lra ]. }
  destruct (tsum_is_lub f Hf) as [_ Hlub].
  specialize (Hlub _ Hub); lra.
Qed.

(** If [x] is below [y] by any margin, it is below [y]. *)
Lemma Rle_of_le_plus_eps (x y : R) :
  (forall eps, 0 < eps -> x <= y + eps)%R -> (x <= y)%R.
Proof.
  intros H; destruct (Rle_or_lt x y) as [Hle | Hlt]; [ exact Hle |].
  specialize (H ((x - y) / 2)%R ltac:(lra)); lra.
Qed.

Section Partition.
  Context {I K : Type} (P : K -> Type) (phi : forall k, P k -> I).

  (** The fibres are disjoint ... *)
  Context (phi_sep : forall k a k' a', phi k a = phi k' a' -> k = k').
  (** ... and each is enumerated injectively. *)
  Context (phi_fib : forall k (a b : P k), phi k a = phi k b -> a = b).

  Lemma summable_fiber (f : I -> R) (k : K) :
    summable f -> summable (fun a => f (phi k a)).
  Proof.
    intros Hf; apply (summable_inj (phi k)); [ apply phi_fib | exact Hf ].
  Qed.

  (** The heart of it: finitely many fibres, approximated simultaneously. *)
  Lemma partition_finite_bound (f : I -> R) (l : list K) (eps : R) :
    nonneg f -> summable f -> NoDup l -> (0 < eps)%R ->
    exists L : list I,
      NoDup L /\
      (forall i, In i L -> exists k, In k l /\ exists a, i = phi k a) /\
      (lsum (fun k => tsum (fun a => f (phi k a))) l <= lsum f L + eps)%R.
  Proof.
    intros Hpos Hf Hnd Heps; revert eps Heps.
    induction l as [| k t IH]; intros eps Heps.
    - exists nil; repeat split; simpl; [ constructor | intros i [] | lra ].
    - inversion Hnd as [| ? ? Hnk Hndt]; subst.
      destruct (IH Hndt (eps / 2)%R ltac:(lra))
        as [Lt [HndLt [HmemLt HboundLt]]].
      destruct (tsum_approx (fun a => f (phi k a)) (eps / 2)%R
                            (summable_fiber f k Hf) ltac:(lra))
        as [Sk [HndSk HboundSk]].
      exists (map (phi k) Sk ++ Lt); repeat split.
      + apply NoDup_app.
        * apply NoDup_map_inj; [ apply phi_fib | exact HndSk ].
        * exact HndLt.
        * (* the new fibre is disjoint from the ones already collected *)
          intros i Hin1 Hin2.
          apply in_map_iff in Hin1; destruct Hin1 as [a [Heq _]].
          destruct (HmemLt i Hin2) as [k' [Hk't [a' Heq']]].
          apply Hnk; rewrite (phi_sep k a k' a'); [ exact Hk't | congruence ].
      + intros i Hin; apply in_app_iff in Hin; destruct Hin as [Hin | Hin].
        * apply in_map_iff in Hin; destruct Hin as [a [Heq _]].
          exists k; split; [ left; reflexivity | exists a; congruence ].
        * destruct (HmemLt i Hin) as [k' [Hk' Ha]].
          exists k'; split; [ right; exact Hk' | exact Ha ].
      + simpl; rewrite lsum_app, lsum_map; lra.
  Qed.

  (** Consequently the iterated sum is summable and bounded by the sum over
      the whole index set. *)
  Theorem tsum_partition_le (f : I -> R) :
    nonneg f -> summable f ->
    summable (fun k => tsum (fun a => f (phi k a))) /\
    (tsum (fun k => tsum (fun a => f (phi k a))) <= tsum f)%R.
  Proof.
    intros Hpos Hf.
    assert (Hkey : forall l, NoDup l ->
              (lsum (fun k => tsum (fun a => f (phi k a))) l <= tsum f)%R).
    { intros l Hnd; apply Rle_of_le_plus_eps; intros eps Heps.
      destruct (partition_finite_bound f l eps Hpos Hf Hnd Heps)
        as [L [HndL [_ Hb]]].
      eapply Rle_trans; [ exact Hb |].
      apply Rplus_le_compat_r, tsum_ub; assumption. }
    assert (Hs : summable (fun k => tsum (fun a => f (phi k a))))
      by (apply summable_bounded with (M := tsum f); exact Hkey).
    split; [ exact Hs |].
    apply tsum_least; [ exact Hs | exact Hkey ].
  Qed.

End Partition.


(* ------------------------------------------------------------------ *)
(** ** Tonelli for unordered sums over a product

    [tsum_partition_le] bounds an iterated sum by the sum over the whole index
    set. The reverse bound needs each finite partial sum over the product to be
    regrouped by first component, which is the list combinatorics below.

    Together they give the equality. The semantics of sampling and of
    measurement need it -- both clauses sum over a pair, the target memory and
    the sampled or measured value -- and so does the converse of Lemma 36, when
    it assembles one witness out of one per pure component. *)

Section Tonelli.
  Context {K A : Type}.

  Definition keq_dec (k k' : K) : {k = k'} + {k <> k'} :=
    excluded_middle_informative (k = k').

  Definition keq (k k' : K) : bool := if keq_dec k k' then true else false.

  Lemma keq_true (k k' : K) : keq k k' = true -> k = k'.
  Proof.
    unfold keq; destruct (keq_dec k k'); [ auto | discriminate ].
  Qed.

  Lemma keq_refl (k : K) : keq k k = true.
  Proof. unfold keq; destruct (keq_dec k k); congruence. Qed.

  Definition fibre (k : K) (l : list (K * A)) : list A :=
    map snd (filter (fun q => keq (fst q) k) l).

  Definition drop_key (k : K) (l : list (K * A)) : list (K * A) :=
    filter (fun q => negb (keq (fst q) k)) l.

  (** Peeling one key off a finite partial sum. *)
  Lemma lsum_split_key (G : K -> A -> R) (k : K) (l : list (K * A)) :
    lsum (fun q => G (fst q) (snd q)) l
    = (lsum (G k) (fibre k l)
       + lsum (fun q => G (fst q) (snd q)) (drop_key k l))%R.
  Proof.
    unfold fibre, drop_key in *.
    induction l as [| q t IH]; simpl; [ lra |].
    destruct (keq (fst q) k) eqn:E; simpl.
    - rewrite IH, (keq_true _ _ E); lra.
    - rewrite IH; lra.
  Qed.

  Lemma NoDup_filter_pairs (f : K * A -> bool) (l : list (K * A)) :
    NoDup l -> NoDup (filter f l).
  Proof.
    induction l as [| q t IH]; simpl; intros Hnd; [ constructor |].
    inversion Hnd as [| ? ? Hnq Hndt]; subst.
    destruct (f q).
    - constructor; [| apply IH; exact Hndt ].
      intros Hin; apply Hnq, (proj1 (filter_In _ _ _) Hin).
    - apply IH; exact Hndt.
  Qed.

  (** On a list whose pairs all share a first component, [snd] is injective. *)
  Lemma NoDup_map_snd_const (k : K) (l : list (K * A)) :
    NoDup l -> (forall q, In q l -> fst q = k) -> NoDup (map snd l).
  Proof.
    induction l as [| q t IH]; simpl; intros Hnd Hall; [ constructor |].
    inversion Hnd as [| ? ? Hnq Hndt]; subst.
    constructor.
    - intros Hin; apply in_map_iff in Hin; destruct Hin as [q' [Heq Hq']].
      apply Hnq.
      assert (Hk1 : fst q' = k) by exact (Hall q' (or_intror Hq')).
      assert (Hk2 : fst q = k) by exact (Hall q (or_introl eq_refl)).
      assert (Hpq : q' = q).
      { destruct q as [kq aq], q' as [kq' aq']; simpl in *.
        rewrite Hk1, Hk2; rewrite Heq; reflexivity. }
      rewrite <- Hpq; exact Hq'.
    - apply IH; [ exact Hndt | intros q' Hq'; apply Hall; right; exact Hq' ].
  Qed.

  Lemma NoDup_fibre (k : K) (l : list (K * A)) :
    NoDup l -> NoDup (fibre k l).
  Proof.
    intros Hnd; unfold fibre; apply (NoDup_map_snd_const k).
    - apply NoDup_filter_pairs; exact Hnd.
    - intros q Hin; apply filter_In in Hin; destruct Hin as [_ He].
      exact (keq_true _ _ He).
  Qed.

  (** Every finite partial sum over the product is bounded by the iterated sum,
      by induction on a duplicate-free list of keys covering it. *)
  Lemma lsum_pairs_le_keys (G : K -> A -> R) :
    (forall k, summable (G k)) ->
    forall (ks : list K) (l : list (K * A)),
      NoDup l -> (forall q, In q l -> In (fst q) ks) ->
      (lsum (fun q => G (fst q) (snd q)) l
       <= lsum (fun k => tsum (G k)) ks)%R.
  Proof.
    intros Hsum ks; induction ks as [| k t IH]; intros l Hnd Hcov.
    - destruct l as [| q l']; simpl; [ lra |].
      exfalso; exact (Hcov q (or_introl eq_refl)).
    - rewrite (lsum_split_key G k l); simpl.
      apply Rplus_le_compat.
      + apply tsum_ub; [ apply Hsum | apply NoDup_fibre; exact Hnd ].
      + apply IH.
        * apply NoDup_filter_pairs; exact Hnd.
        * intros q Hin; unfold drop_key in Hin.
          apply filter_In in Hin; destruct Hin as [Hin He].
          destruct (Hcov q Hin) as [Heq | Hin']; [| exact Hin' ].
          exfalso; rewrite Heq, keq_refl in He; discriminate He.
  Qed.

  Theorem tsum_pairs_le_iter (G : K -> A -> R) :
    (forall k, summable (G k)) ->
    summable (fun k => tsum (G k)) ->
    summable (fun q : K * A => G (fst q) (snd q)) /\
    (tsum (fun q : K * A => G (fst q) (snd q))
     <= tsum (fun k => tsum (G k)))%R.
  Proof.
    intros Hsum Hit.
    assert (Hkey : forall l, NoDup l ->
              (lsum (fun q : K * A => G (fst q) (snd q)) l
               <= tsum (fun k => tsum (G k)))%R).
    { intros l Hnd.
      eapply Rle_trans.
      - apply (lsum_pairs_le_keys G Hsum (nodup keq_dec (map fst l)) l Hnd).
        intros q Hin; apply nodup_In, in_map_iff.
        exists q; split; [ reflexivity | exact Hin ].
      - apply tsum_ub; [ exact Hit | apply NoDup_nodup ]. }
    assert (Hs : summable (fun q : K * A => G (fst q) (snd q)))
      by (apply summable_bounded with (M := tsum (fun k => tsum (G k))); exact Hkey).
    split; [ exact Hs | apply tsum_least; assumption ].
  Qed.

  (** The iterated sum is bounded by the product sum: an instance of
      [tsum_partition_le] with constant fibres. *)
  Theorem tsum_iter_le_pairs (G : K -> A -> R) :
    nonneg (fun q : K * A => G (fst q) (snd q)) ->
    summable (fun q : K * A => G (fst q) (snd q)) ->
    summable (fun k => tsum (G k)) /\
    (tsum (fun k => tsum (G k))
     <= tsum (fun q : K * A => G (fst q) (snd q)))%R.
  Proof.
    intros Hpos Hs.
    assert (Hsep : forall (k : K) (a : A) (k' : K) (a' : A),
                     (k, a) = (k', a') -> k = k') by (intros; congruence).
    assert (Hfib : forall (k : K) (a b : A), (k, a) = (k, b) -> a = b)
      by (intros; congruence).
    exact (tsum_partition_le (fun _ : K => A) (fun k a => (k, a)) Hsep Hfib
             (fun q : K * A => G (fst q) (snd q)) Hpos Hs).
  Qed.

  (** Tonelli. *)
  Theorem tsum_tonelli (G : K -> A -> R) :
    (forall k, nonneg (G k)) ->
    (forall k, summable (G k)) ->
    summable (fun k => tsum (G k)) ->
    summable (fun q : K * A => G (fst q) (snd q)) /\
    tsum (fun q : K * A => G (fst q) (snd q)) = tsum (fun k => tsum (G k)).
  Proof.
    intros Hpos Hsum Hit.
    destruct (tsum_pairs_le_iter G Hsum Hit) as [Hs Hle1].
    assert (Hpos' : nonneg (fun q : K * A => G (fst q) (snd q)))
      by (intros q; apply Hpos).
    destruct (tsum_iter_le_pairs G Hpos' Hs) as [_ Hle2].
    split; [ exact Hs | apply Rle_antisym; assumption ].
  Qed.

End Tonelli.

(* ------------------------------------------------------------------ *)
(** ** Scaling *)

Lemma lsum_add {I : Type} (f g : I -> R) (l : list I) :
  lsum (fun i => (f i + g i)%R) l = (lsum f l + lsum g l)%R.
Proof.
  induction l as [| i t IH]; simpl; [ lra | rewrite IH; lra ].
Qed.

Lemma summable_add {I : Type} (f g : I -> R) :
  summable f -> summable g -> summable (fun i => (f i + g i)%R).
Proof.
  intros [M HM] [N HN]; exists (M + N)%R; intros r [l [Hnd <-]].
  rewrite lsum_add; apply Rplus_le_compat.
  - apply HM; exists l; split; [ exact Hnd | reflexivity ].
  - apply HN; exists l; split; [ exact Hnd | reflexivity ].
Qed.

Lemma lsum_scale {I : Type} (c : R) (f : I -> R) (l : list I) :
  lsum (fun i => (c * f i)%R) l = (c * lsum f l)%R.
Proof.
  induction l as [| i t IH]; simpl; [ lra | rewrite IH; lra ].
Qed.

Lemma summable_scale {I : Type} (c : R) (f : I -> R) :
  (0 <= c)%R -> nonneg f -> summable f -> summable (fun i => (c * f i)%R).
Proof.
  intros Hc Hf Hs; apply summable_bounded with (M := (c * tsum f)%R).
  intros l Hnd; rewrite lsum_scale.
  apply Rmult_le_compat_l; [ exact Hc | apply tsum_ub; assumption ].
Qed.

Lemma tsum_scale {I : Type} (c : R) (f : I -> R) :
  (0 <= c)%R -> nonneg f -> summable f ->
  tsum (fun i => (c * f i)%R) = (c * tsum f)%R.
Proof.
  intros Hc Hf Hs.
  destruct (Rle_lt_or_eq_dec 0 c Hc) as [Hpos | Heq].
  - apply Rle_antisym.
    + apply tsum_least; [ apply summable_scale; assumption |].
      intros l Hnd; rewrite lsum_scale.
      apply Rmult_le_compat_l; [ exact Hc | apply tsum_ub; assumption ].
    + (* divide through by [c] and apply the same bound the other way *)
      apply Rmult_le_reg_l with (r := (/ c)%R); [ apply Rinv_0_lt_compat, Hpos |].
      rewrite <- Rmult_assoc, Rinv_l by lra; rewrite Rmult_1_l.
      apply tsum_least; [ exact Hs |].
      intros l Hnd.
      apply Rmult_le_reg_l with (r := c); [ exact Hpos |].
      rewrite <- Rmult_assoc, Rinv_r by lra; rewrite Rmult_1_l.
      rewrite <- lsum_scale.
      apply tsum_ub; [ apply summable_scale; assumption | exact Hnd ].
  - subst c.
    rewrite Rmult_0_l.
    assert (Hz : (fun i => (0 * f i)%R) = (fun _ : I => 0%R))
      by (apply funext; intros i; ring).
    rewrite Hz.
    apply Rle_antisym.
    + apply tsum_least.
      * apply summable_bounded with (M := 0%R); intros l _.
        induction l as [| i t IH]; simpl; lra.
      * intros l _; induction l as [| i t IH]; simpl; lra.
    + apply tsum_nonneg; intros i; apply Rle_refl.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Duplicate-free lists of booleans

    A two-element index type has only five duplicate-free lists, and that is
    what makes a sum over [bool] a binary addition. Used to show that
    separability is closed under binary sums, which rule If1 needs. *)

Lemma nodup_bool_tail (b : bool) (t : list bool) :
  NoDup (b :: t) -> t = nil \/ t = negb b :: nil.
Proof.
  intros Hnd; inversion Hnd as [| ? ? Hb Hndt]; subst.
  destruct t as [| d u]; [ left; reflexivity |].
  assert (Hd : d = negb b)
    by (destruct d, b; simpl; try reflexivity;
        exfalso; apply Hb; left; reflexivity).
  subst d.
  destruct u as [| c v]; [ right; reflexivity |].
  exfalso; inversion Hndt as [| ? ? Hnu Hndu]; subst.
  assert (Hc : c = b \/ c = negb b) by (destruct c, b; auto).
  destruct Hc as [-> | ->].
  - apply Hb; right; left; reflexivity.
  - apply Hnu; left; reflexivity.
Qed.

Lemma lsum_le_const {I : Type} (f : I -> R) (c : I) (l : list I) :
  nonneg f -> NoDup l -> (forall i, In i l -> i = c) -> (lsum f l <= f c)%R.
Proof.
  intros Hf Hnd Hall.
  destruct l as [| d t]; simpl; [ apply Hf |].
  inversion Hnd as [| ? ? Hnd1 Hnd2]; subst.
  assert (Hd : d = c) by (apply Hall; left; reflexivity); subst d.
  destruct t as [| u v]; simpl.
  - lra.
  - exfalso; apply Hnd1.
    assert (Hu : u = c) by (apply Hall; right; left; reflexivity); subst u.
    left; reflexivity.
Qed.

Lemma lsum_bool_le (f : bool -> R) (l : list bool) :
  nonneg f -> NoDup l -> (lsum f l <= f true + f false)%R.
Proof.
  intros Hf Hnd.
  pose proof (Hf true) as Ht; pose proof (Hf false) as Hff.
  destruct l as [| b t]; simpl; [ lra |].
  assert (Htail : (lsum f t <= f (negb b))%R).
  { apply lsum_le_const; [ exact Hf | inversion Hnd; assumption |].
    intros i Hi; inversion Hnd as [| ? ? Hb ?]; subst.
    destruct i, b; simpl; try reflexivity; exfalso; apply Hb; exact Hi. }
  destruct b; simpl in *; lra.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Additivity

    [tsum] is additive. The upper bound is immediate from the least-upper-bound
    property; the lower bound needs the two approximating finite subsets to be
    merged, hence monotonicity of a finite partial sum under list inclusion. *)

Definition Ieq_dec {I : Type} (x y : I) : {x = y} + {x <> y} :=
  excluded_middle_informative (x = y).

Fixpoint lremove {I : Type} (i : I) (l : list I) : list I :=
  match l with
  | nil    => nil
  | j :: t => if Ieq_dec i j then t else j :: lremove i t
  end.

Lemma lremove_In {I : Type} (i j : I) (l : list I) :
  In j (lremove i l) -> In j l.
Proof.
  induction l as [| k t IH]; simpl; [ tauto |].
  destruct (Ieq_dec i k) as [-> | Hne].
  - intros H; right; exact H.
  - simpl; intros [-> | H]; [ left; reflexivity | right; apply IH, H ].
Qed.

Lemma In_lremove {I : Type} (i j : I) (l : list I) :
  j <> i -> In j l -> In j (lremove i l).
Proof.
  intros Hne; induction l as [| k t IH]; simpl; [ tauto |].
  destruct (Ieq_dec i k) as [-> | Hik].
  - intros [-> | H]; [ congruence | exact H ].
  - simpl; intros [-> | H]; [ left; reflexivity | right; apply IH, H ].
Qed.

Lemma NoDup_lremove {I : Type} (i : I) (l : list I) :
  NoDup l -> NoDup (lremove i l).
Proof.
  induction l as [| k t IH]; simpl; intros Hnd; [ constructor |].
  inversion Hnd as [| ? ? Hnk Hndt]; subst.
  destruct (Ieq_dec i k) as [-> | Hne]; [ exact Hndt |].
  constructor; [ intros H; apply Hnk, (lremove_In _ _ _ H) | apply IH, Hndt ].
Qed.

Lemma lsum_lremove {I : Type} (f : I -> R) (i : I) (l : list I) :
  NoDup l -> In i l -> lsum f l = (f i + lsum f (lremove i l))%R.
Proof.
  induction l as [| k t IH]; simpl; intros Hnd Hin; [ tauto |].
  inversion Hnd as [| ? ? Hnk Hndt]; subst.
  destruct (Ieq_dec i k) as [-> | Hne]; [ reflexivity |].
  destruct Hin as [-> | Hin]; [ congruence |].
  simpl; rewrite (IH Hndt Hin); lra.
Qed.

Lemma lsum_le_incl {I : Type} (f : I -> R) (l1 l2 : list I) :
  nonneg f -> NoDup l1 -> NoDup l2 ->
  (forall i, In i l1 -> In i l2) ->
  (lsum f l1 <= lsum f l2)%R.
Proof.
  intros Hf; revert l2; induction l1 as [| i t IH]; intros l2 Hnd1 Hnd2 Hsub.
  - simpl; apply lsum_nonneg; exact Hf.
  - inversion Hnd1 as [| ? ? Hni Hndt]; subst.
    rewrite (lsum_lremove f i l2 Hnd2 (Hsub i (or_introl eq_refl))).
    simpl; apply Rplus_le_compat_l.
    apply IH; [ exact Hndt | apply NoDup_lremove; exact Hnd2 |].
    intros j Hj; apply In_lremove.
    + intros ->; contradiction.
    + apply Hsub; right; exact Hj.
Qed.

Lemma tsum_add {I : Type} (f g : I -> R) :
  nonneg f -> nonneg g -> summable f -> summable g ->
  tsum (fun i => (f i + g i)%R) = (tsum f + tsum g)%R.
Proof.
  intros Hf Hg Hsf Hsg.
  assert (Hs : summable (fun i => (f i + g i)%R))
    by (apply summable_add; assumption).
  apply Rle_antisym.
  - apply tsum_least; [ exact Hs | intros l Hnd ].
    rewrite lsum_add; apply Rplus_le_compat; apply tsum_ub; assumption.
  - apply Rle_of_le_plus_eps; intros eps Heps.
    destruct (tsum_approx f (eps / 2)%R Hsf ltac:(lra)) as [lf [Hndf Hbf]].
    destruct (tsum_approx g (eps / 2)%R Hsg ltac:(lra)) as [lg [Hndg Hbg]].
    pose (l := nodup Ieq_dec (lf ++ lg)).
    assert (Hndl : NoDup l) by apply NoDup_nodup.
    assert (Hfl : (lsum f lf <= lsum f l)%R).
    { apply lsum_le_incl; try assumption.
      intros i Hi; apply nodup_In, in_app_iff; left; exact Hi. }
    assert (Hgl : (lsum g lg <= lsum g l)%R).
    { apply lsum_le_incl; try assumption.
      intros i Hi; apply nodup_In, in_app_iff; right; exact Hi. }
    assert (Hle : (lsum (fun i => (f i + g i)%R) l
                   <= tsum (fun i => (f i + g i)%R))%R)
      by (apply tsum_ub; assumption).
    rewrite lsum_add in Hle; lra.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Subdistributions

    The paper's [D<=1(X)] (section 2). A [distr I] bundles the function with
    its nonnegativity, summability and the [<= 1] bound, so that these never
    have to be rediscovered at use sites. *)

Record distr (I : Type) : Type := mkDistr {
  dfun :> I -> R;
  dfun_nonneg  : nonneg dfun;
  dfun_summable : summable dfun;
  dfun_le1 : tsum dfun <= 1
}.

Arguments mkDistr {I} _ _ _ _.
Arguments dfun {I} _ _.
Arguments dfun_nonneg {I} _ _.
Arguments dfun_summable {I} _.
Arguments dfun_le1 {I} _.

(** "We call a distribution total if [sum_x mu(x) = 1]" (section 2). *)
Definition dtotal {I} (mu : distr I) : Prop := tsum mu = 1.

(** "[supp mu := {x : mu(x) > 0}]" (section 2). *)
Definition dsupp {I} (mu : distr I) : I -> Prop := fun i => mu i > 0.

(** "[delta_a] is the distribution with [delta_a(a) = 1]" (section 2). *)
Definition ddirac {I} (i : I) : distr I :=
  mkDistr (indicator i) (indicator_nonneg i) (summable_indicator i)
          (Rle_trans _ _ _ (Req_le _ _ (tsum_indicator i)) (Rle_refl 1)).

(** Each value of a subdistribution is at most 1. *)
Lemma dfun_le1_pt {I} (mu : distr I) (i : I) : (mu i <= 1)%R.
Proof.
  eapply Rle_trans; [| apply (dfun_le1 mu) ].
  replace (mu i) with (lsum (dfun mu) (i :: nil)) by (simpl; lra).
  apply tsum_ub;
    [ apply dfun_summable
    | constructor; [ intros H; inversion H | constructor ] ].
Qed.

(** A family that is a single constant at one index and zero elsewhere. *)
Lemma tsum_single_val {I : Type} (i0 : I) (c : R) :
  (0 <= c)%R ->
  summable (fun i => if excluded_middle_informative (i = i0) then c else 0%R)
  /\ tsum (fun i => if excluded_middle_informative (i = i0) then c else 0%R) = c.
Proof.
  intros Hc.
  assert (Heq : (fun i => if excluded_middle_informative (i = i0) then c else 0%R)
                = (fun i => (c * indicator i0 i)%R)).
  { apply funext; intros i; unfold indicator.
    destruct (excluded_middle_informative (i = i0)); lra. }
  rewrite Heq; split.
  - apply summable_scale;
      [ exact Hc | apply indicator_nonneg | apply summable_indicator ].
  - rewrite (tsum_scale c (indicator i0) Hc (indicator_nonneg i0)
               (summable_indicator i0)), tsum_indicator; lra.
Qed.

Lemma ddirac_total {I} (i : I) : dtotal (ddirac i).
Proof. unfold dtotal, ddirac; simpl; apply tsum_indicator. Qed.

(** Two subdistributions with the same underlying function are equal: the
    bundled proofs are irrelevant. *)
Lemma distr_ext {I} (mu nu : distr I) : (forall i, mu i = nu i) -> mu = nu.
Proof.
  intros H.
  destruct mu as [f Hf1 Hf2 Hf3], nu as [g Hg1 Hg2 Hg3]; simpl in H.
  assert (f = g) by (apply funext; exact H); subst g.
  f_equal; apply proof_irrel.
Qed.
