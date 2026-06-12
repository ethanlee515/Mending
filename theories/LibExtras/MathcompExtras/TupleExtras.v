Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals distr.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From Mending.LibExtras.MathcompExtras Require Import DistrExtras.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

Section TupleExtras.

Context {R : realType}.

(* Converts a coordinate of a concatenated tuple into its prefix coordinate. *)
Lemma cat_tuple_tnth_prefix_choice
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (t1 : (ℓ1.+1).-tuple A)
  (t2 : (ℓ2.+1).-tuple A)
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (Hi : (i < ℓ1.+1)%N) :
  tnth (cat_tuple t1 t2) i = tnth t1 (Ordinal Hi).
Proof.
rewrite (tnth_nth (tnth t1 (Ordinal Hi))).
rewrite (tnth_nth (tnth t1 (Ordinal Hi)) t1).
rewrite nth_cat size_tuple Hi.
by apply: set_nth_default; rewrite size_tuple.
Qed.

(* Reads a prefix coordinate out of a concatenated trace tuple. *)
Lemma cat_tuple_tnth_prefix
  {ℓ1 ℓ2 : nat}
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (Hi : (i < ℓ1.+1)%N) :
  tnth (cat_tuple s1 s2) i = tnth s1 (Ordinal Hi).
Proof. exact: cat_tuple_tnth_prefix_choice. Qed.

Lemma cat_tuple_suffix_bound
  {ℓ1 ℓ2 : nat}
  (i : 'I_(ℓ1.+1 + ℓ2.+1)) :
  (ℓ1.+1 <= i)%N ->
  (i - ℓ1.+1 < ℓ2.+1)%N.
Proof.
move=> Hi.
have Hord := ltn_ord i.
by rewrite ltn_subLR // addnC.
Qed.

(* Converts a coordinate after the prefix into its suffix ordinal. *)
Lemma cat_tuple_tnth_suffix_choice
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (t1 : (ℓ1.+1).-tuple A)
  (t2 : (ℓ2.+1).-tuple A)
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (Hi : (ℓ1.+1 <= i)%N) :
  tnth (cat_tuple t1 t2) i =
  tnth t2 (Ordinal (cat_tuple_suffix_bound i Hi)).
Proof.
rewrite (tnth_nth (tnth t2 (Ordinal (cat_tuple_suffix_bound i Hi)))).
rewrite nth_cat size_tuple.
rewrite ltnNge Hi.
rewrite /=.
by rewrite [RHS](tnth_nth (tnth t2 (Ordinal (cat_tuple_suffix_bound i Hi)))).
Qed.

(* Reads a suffix coordinate out of a concatenated trace tuple. *)
Lemma cat_tuple_tnth_suffix
  {ℓ1 ℓ2 : nat}
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (Hi : (ℓ1.+1 <= i)%N) :
  tnth (cat_tuple s1 s2) i =
  tnth s2 (Ordinal (cat_tuple_suffix_bound i Hi)).
Proof. exact: cat_tuple_tnth_suffix_choice. Qed.

Definition catTuplePrefix
  {ℓ1 ℓ2 : nat}
  {A : Type}
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A) :
  (ℓ1.+1).-tuple A :=
  [tuple a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _)))
    | j < ℓ1.+1].

Definition catTupleSuffixIndex
  {ℓ1 ℓ2 : nat}
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (Hi : (ℓ1.+1 <= i)%N) : 'I_(ℓ2.+1) :=
  Ordinal (cat_tuple_suffix_bound i Hi).

Lemma catTupleSuffixOrdinal_bound
  {ℓ1 ℓ2 : nat}
  (j : 'I_(ℓ2.+1)) :
  (ℓ1.+1 + j < ℓ1.+1 + ℓ2.+1)%N.
Proof.
by rewrite ltn_add2l ltn_ord.
Qed.

Definition catTupleSuffixAssignment
  {ℓ1 ℓ2 : nat}
  {A : Type}
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (Hi : (ℓ1.+1 <= i)%N)
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A) :
  forall j : 'I_(ℓ2.+1), A :=
  fun j =>
    a (Ordinal (catTupleSuffixOrdinal_bound j)).

(* Rewrites conditional-coordinate distances along pointwise-equal distributions. *)
Lemma conditional_coordinate_dist_ext
  {n : nat}
  {A : choiceType}
  (P Q : {distr (n.-tuple A) / R})
  (i : 'I_n)
  (a : forall j : 'I_n, A) :
  P =1 Q ->
  conditional_coordinate P i a =1 conditional_coordinate Q i a.
Proof.
move=> HP.
apply: dmargin_ext.
exact: dcond_ext.
Qed.

(* Characterizes when a concatenated trace has a given prefix. *)
Lemma tuple_prefix_eq_cat_prefix
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
  (Hi : (i < ℓ1.+1)%N)
  (omega1 : (ℓ1.+1).-tuple A)
  (omega2 : (ℓ2.+1).-tuple A) :
  let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
  let a0 : forall j : 'I_(ℓ1.+1), A :=
    fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
  tuple_prefix_eq i a (cat_tuple omega1 omega2) =
  tuple_prefix_eq i0 a0 omega1.
Proof.
rewrite /tuple_prefix_eq.
apply/idP/idP.
- move=> Hbool.
  have Hfull := forallP Hbool.
  apply/forallP=> j.
  have Hj : (j < ℓ1.+1 + ℓ2.+1)%N :=
    leq_trans (ltn_ord j) (leq_addr _ _).
  move: (Hfull (Ordinal Hj)).
  rewrite (cat_tuple_tnth_prefix_choice omega1 omega2 (Ordinal Hj)
    (ltn_ord j)) /=.
  have -> : @Ordinal ℓ1.+1 (nat_of_ord j) (ltn_ord j) = j
    by apply: val_inj.
  have -> :
      @Ordinal (ℓ1.+1 + ℓ2.+1) (nat_of_ord j) Hj =
      @Ordinal (ℓ1.+1 + ℓ2.+1) (nat_of_ord j)
        (leq_trans (ltn_ord j) (leq_addr _ _))
    by apply: val_inj.
  by [].
- move=> HsmallBool.
  have Hsmall := forallP HsmallBool.
  apply/forallP=> k.
  case Hki: (k < i)%N.
    have Hklt : (k < ℓ1.+1)%N := leq_ltn_trans (ltnW Hki) Hi.
    move: (Hsmall (@Ordinal ℓ1.+1 (nat_of_ord k) Hklt)).
    rewrite /= Hki.
    rewrite (cat_tuple_tnth_prefix_choice omega1 omega2 k Hklt).
    rewrite implyTb.
    have -> :
        @Ordinal (ℓ1.+1 + ℓ2.+1) (nat_of_ord k)
          (leq_trans
            (ltn_ord (@Ordinal ℓ1.+1 (nat_of_ord k) Hklt))
            (leq_addr _ _)) = k
      by apply: val_inj.
    by [].
  by [].
Qed.

(* Recovers the original prefix tuple from a concatenated tuple. *)
Lemma catTuplePrefix_cat
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (omega1 : (ℓ1.+1).-tuple A)
  (omega2 : (ℓ2.+1).-tuple A) :
  catTuplePrefix (fun j => tnth (cat_tuple omega1 omega2) j) =
  omega1.
Proof.
apply: eq_from_tnth=> j.
rewrite /catTuplePrefix tnth_mktuple.
rewrite (cat_tuple_tnth_prefix_choice omega1 omega2
  (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) (ltn_ord j)).
congr tnth.
by apply: val_inj.
Qed.

(* Reads coordinates from the extracted prefix tuple. *)
Lemma catTuplePrefix_tnth
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
  (j : 'I_(ℓ1.+1)) :
  tnth (catTuplePrefix a) j =
  a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))).
Proof.
by rewrite /catTuplePrefix tnth_mktuple.
Qed.

(* Preserves strict order when converting combined indices to suffix indices. *)
Lemma catTupleSuffixIndex_lt
  {ℓ1 ℓ2 : nat}
  (i j : 'I_(ℓ1.+1 + ℓ2.+1))
  (Hi : (ℓ1.+1 <= i)%N)
  (Hj : (ℓ1.+1 <= j)%N) :
  (j < i)%N ->
  (catTupleSuffixIndex j Hj < catTupleSuffixIndex i Hi)%N.
Proof.
move=> Hji.
rewrite /catTupleSuffixIndex /=.
exact: ltn_sub2r (leq_ltn_trans Hj Hji) Hji.
Qed.

(* Bounds earlier combined indices by the current suffix ordinal. *)
Lemma catTupleSuffixOrdinal_lt
  {ℓ1 ℓ2 : nat}
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (Hi : (ℓ1.+1 <= i)%N)
  (j : 'I_(ℓ2.+1)) :
  (j < catTupleSuffixIndex i Hi)%N ->
  (ℓ1.+1 + j < i)%N.
Proof.
move=> Hji.
move: Hji.
rewrite /catTupleSuffixIndex /=.
by rewrite (@leq_subRL ℓ1.+1 j.+1 i Hi) addnS.
Qed.

(* Characterizes suffix-prefix equality after fixing the concatenated prefix. *)
Lemma tuple_prefix_eq_cat_suffix
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
  (Hi : (ℓ1.+1 <= i)%N)
  (omega1 omega1' : (ℓ1.+1).-tuple A)
  (omega2 : (ℓ2.+1).-tuple A) :
  catTuplePrefix a = omega1 ->
  tuple_prefix_eq i a (cat_tuple omega1' omega2) =
    (omega1' == omega1) &&
    tuple_prefix_eq
      (catTupleSuffixIndex i Hi)
      (catTupleSuffixAssignment i Hi a)
      omega2.
Proof.
move=> Hprefix.
rewrite /tuple_prefix_eq.
apply/idP/idP.
- move=> HfullBool.
  have Hfull := forallP HfullBool.
  apply/andP; split.
    apply/eqP.
    apply: eq_from_tnth=> j.
    have Hj : (j < ℓ1.+1 + ℓ2.+1)%N :=
      leq_trans (ltn_ord j) (leq_addr _ _).
    have Hji : (Ordinal Hj < i)%N := leq_trans (ltn_ord j) Hi.
    move: (Hfull (Ordinal Hj)).
    rewrite Hji /=.
    rewrite (cat_tuple_tnth_prefix_choice omega1' omega2
      (Ordinal Hj) (ltn_ord j)).
    have -> : @Ordinal ℓ1.+1 (nat_of_ord j) (ltn_ord j) = j
      by apply: val_inj.
    rewrite -Hprefix catTuplePrefix_tnth.
    have -> :
        @Ordinal (ℓ1.+1 + ℓ2.+1) (nat_of_ord j)
          (leq_trans (ltn_ord j) (leq_addr _ _)) =
        @Ordinal (ℓ1.+1 + ℓ2.+1) (nat_of_ord j) Hj
      by apply: val_inj.
    by move/eqP.
  apply/forallP=> j.
  case Hji: (j < catTupleSuffixIndex i Hi)%N.
    have Hsum_i := catTupleSuffixOrdinal_lt i Hi j Hji.
    pose k : 'I_(ℓ1.+1 + ℓ2.+1) :=
      Ordinal (catTupleSuffixOrdinal_bound (ℓ1 := ℓ1) (ℓ2 := ℓ2) j).
    move: (Hfull k).
    rewrite Hsum_i /=.
    rewrite (cat_tuple_tnth_suffix_choice omega1' omega2 k
      (leq_addr _ _)).
    have -> :
        @Ordinal ℓ2.+1 (nat_of_ord k - ℓ1.+1)
          (cat_tuple_suffix_bound k (leq_addr _ _)) = j.
      apply: val_inj.
      rewrite /= /k /=.
      by rewrite addKn.
    by [].
  by [].
- move=> /andP [/eqP Homega HsuffixBool].
  have Hsuffix := forallP HsuffixBool.
  apply/forallP=> j.
  case Hji: (j < i)%N.
    case Hprefix_j: (j < ℓ1.+1)%N.
      rewrite (cat_tuple_tnth_prefix_choice omega1' omega2 j Hprefix_j).
      rewrite Homega.
      rewrite -Hprefix catTuplePrefix_tnth.
      rewrite implyTb.
      have -> :
          @Ordinal (ℓ1.+1 + ℓ2.+1) (nat_of_ord j)
            (leq_trans (ltn_ord (@Ordinal ℓ1.+1 (nat_of_ord j) Hprefix_j))
              (leq_addr _ _)) = j
        by apply: val_inj.
      by [].
    have Hjge : (ℓ1.+1 <= j)%N by rewrite leqNgt Hprefix_j.
    rewrite (cat_tuple_tnth_suffix_choice omega1' omega2 j Hjge).
    rewrite implyTb.
    move: (Hsuffix (catTupleSuffixIndex j Hjge)).
    rewrite (catTupleSuffixIndex_lt i j Hi Hjge Hji) /=.
    have -> :
        @Ordinal ℓ2.+1 (nat_of_ord j - ℓ1.+1)
          (cat_tuple_suffix_bound j Hjge) =
        catTupleSuffixIndex j Hjge
      by apply: val_inj.
    rewrite /catTupleSuffixAssignment.
    have -> :
        @Ordinal (ℓ1.+1 + ℓ2.+1)
          (ℓ1.+1 + nat_of_ord (catTupleSuffixIndex j Hjge))
          (catTupleSuffixOrdinal_bound (catTupleSuffixIndex j Hjge)) =
        j.
      apply: val_inj.
      rewrite /catTupleSuffixIndex /=.
      by rewrite subnKC.
    by [].
    by [].
Qed.

End TupleExtras.

Section RealTupleExtras.

Context {R : realType}.

(* Combines nonnegativity proofs for prefix and suffix error budgets. *)
Lemma cat_tuple_nonneg
  {ℓ1 ℓ2 : nat}
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (i : 'I_(ℓ1.+1 + ℓ2.+1)) :
  (forall i : 'I_(ℓ1.+1), 0 <= tnth s1 i) ->
  (forall i : 'I_(ℓ2.+1), 0 <= tnth s2 i) ->
  0 <= tnth (cat_tuple s1 s2) i.
Proof.
move=> Hs1 Hs2.
case Hi: (i < ℓ1.+1)%N.
  rewrite (cat_tuple_tnth_prefix s1 s2 i Hi).
  exact: Hs1.
have Hi' : (ℓ1.+1 <= i)%N by rewrite leqNgt Hi.
rewrite (cat_tuple_tnth_suffix s1 s2 i Hi').
exact: Hs2.
Qed.

Fixpoint sum_squares (lst : list R) : R :=
  match lst with
  | [::] => 0
  | head :: tail => head * head + sum_squares tail
  end.

Definition l2_norm (eps_lst : list R) := Num.sqrt (sum_squares eps_lst).

Definition tuple_sum {n : nat} (s : n.-tuple R) : R :=
  \sum_(i < n) tnth s i.

Definition tuple_sum_squares {n : nat} (s : n.-tuple R) : R :=
  \sum_(i < n) (tnth s i) ^+ 2.

Definition two_norm {n : nat} (s : n.-tuple R) : R :=
  Num.sqrt (tuple_sum_squares s).

Definition pythagorean_tv_bound {n : nat} (s : n.-tuple R) : R :=
  Num.sqrt (tuple_sum s / 2).

End RealTupleExtras.
