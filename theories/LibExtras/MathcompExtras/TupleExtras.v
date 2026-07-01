Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals distr.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

Lemma cat_tuple_singleton_cons {n : nat} {A : Type}
    (x : A) (xs : n.-tuple A) :
  cat_tuple [tuple x] xs = cons_tuple x xs.
Proof.
by apply: val_inj.
Qed.

Lemma mktuple_const_nseq {n : nat} {A : Type} (x : A) :
  [tuple x | i < n] = [tuple of nseq n x].
Proof.
apply: eq_from_tnth=> i.
by rewrite tnth_mktuple tnth_nseq.
Qed.

Lemma mktuple_const_1 {A : Type} (x : A) :
  [tuple x | i < 1] = [tuple x].
Proof.
apply: eq_from_tnth=> i.
by rewrite [i]ord1 tnth_mktuple tnth0.
Qed.

Lemma cat_tuple_singleton_const {n : nat} {A : Type} (x : A) :
  cat_tuple [tuple x] [tuple x | i < n] = [tuple x | i < n.+1].
Proof.
rewrite !mktuple_const_nseq.
by apply: val_inj.
Qed.

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
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (Hi : (ℓ1.+1 <= i)%N)
  (a : i.-tuple A) :
  (ℓ1.+1).-tuple A :=
  [tuple tnth a (Ordinal (leq_trans (ltn_ord j) Hi))
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

Definition tuple_prefix {n : nat} {A : Type}
    (i : 'I_n) (a : forall j : 'I_n, A) : i.-tuple A :=
  [tuple a (widen_ord (ltnW (ltn_ord i)) j) | j < i].

Definition tuple_prefix_eq {n : nat} {A : choiceType}
    {i : 'I_n} (a : i.-tuple A) (omega : n.-tuple A) : bool :=
  [forall j : 'I_i,
    tnth omega (widen_ord (ltnW (ltn_ord i)) j) == tnth a j].

(* Characterizes when a concatenated trace has a given prefix. *)
Lemma tuple_prefix_eq_cat_prefix
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : i.-tuple A)
  (Hi : (i < ℓ1.+1)%N)
  (omega1 : (ℓ1.+1).-tuple A)
  (omega2 : (ℓ2.+1).-tuple A) :
  let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
  tuple_prefix_eq a (cat_tuple omega1 omega2) =
  @tuple_prefix_eq _ _ i0 a omega1.
Proof.
rewrite /tuple_prefix_eq.
apply/forallP/forallP=> Hprefix j; move: (Hprefix j).
  rewrite (cat_tuple_tnth_prefix_choice omega1 omega2
    (widen_ord (ltnW (ltn_ord i)) j)
    (ltn_trans (ltn_ord j) Hi)).
  have -> :
      Ordinal (ltn_trans (ltn_ord j) Hi) =
      widen_ord (ltnW (ltn_ord (Ordinal Hi))) j
    by apply: val_inj.
  by [].
rewrite (cat_tuple_tnth_prefix_choice omega1 omega2
  (widen_ord (ltnW (ltn_ord i)) j)
  (ltn_trans (ltn_ord j) Hi)).
have -> :
    Ordinal (ltn_trans (ltn_ord j) Hi) =
    widen_ord (ltnW (ltn_ord (Ordinal Hi))) j
  by apply: val_inj.
by [].
Qed.

(* Reads coordinates from the extracted prefix tuple. *)
Lemma catTuplePrefix_tnth
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (Hi : (ℓ1.+1 <= i)%N)
  (a : i.-tuple A)
  (j : 'I_(ℓ1.+1)) :
  tnth (catTuplePrefix i Hi a) j =
  tnth a (Ordinal (leq_trans (ltn_ord j) Hi)).
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

Definition catTupleSuffixAssignment
  {ℓ1 ℓ2 : nat}
  {A : Type}
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (Hi : (ℓ1.+1 <= i)%N)
  (a : i.-tuple A) :
  (catTupleSuffixIndex i Hi).-tuple A :=
  [tuple
    let j' : 'I_(ℓ2.+1) :=
      Ordinal (ltn_trans (ltn_ord j) (ltn_ord (catTupleSuffixIndex i Hi))) in
    tnth a (Ordinal (catTupleSuffixOrdinal_lt i Hi j' (ltn_ord j)))
    | j < catTupleSuffixIndex i Hi].

(* Characterizes suffix-prefix equality after fixing the concatenated prefix. *)
Lemma tuple_prefix_eq_cat_suffix
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : i.-tuple A)
  (Hi : (ℓ1.+1 <= i)%N)
  (omega1 omega1' : (ℓ1.+1).-tuple A)
  (omega2 : (ℓ2.+1).-tuple A) :
  catTuplePrefix i Hi a = omega1 ->
  tuple_prefix_eq a (cat_tuple omega1' omega2) =
    (omega1' == omega1) &&
    @tuple_prefix_eq _ _ (catTupleSuffixIndex i Hi)
      (catTupleSuffixAssignment i Hi a)
      omega2.
Proof.
move=> Hprefix.
rewrite /tuple_prefix_eq.
apply/idP/idP=> [HfullBool|/andP [/eqP Homega HsuffixBool]].
  have Hfull := forallP HfullBool.
  apply/andP; split.
    apply/eqP.
    apply: eq_from_tnth=> j.
    have Hjle : (j <= ℓ1)%N by rewrite -ltnS.
    pose k : 'I_i := Ordinal (leq_ltn_trans Hjle Hi).
    move: (Hfull k).
    rewrite (cat_tuple_tnth_prefix_choice omega1' omega2
      (widen_ord (ltnW (ltn_ord i)) k)
      (ltn_ord j)).
    have -> : Ordinal (n := ℓ1.+1)
        (m := widen_ord (ltnW (ltn_ord i)) k) (ltn_ord j) = j
      by apply: val_inj.
    rewrite -Hprefix catTuplePrefix_tnth.
    have -> : Ordinal (leq_trans (ltn_ord j) Hi) = k
      by apply: val_inj.
    by move/eqP=> ->.
  apply/forallP=> j.
  pose j' : 'I_(ℓ2.+1) :=
    Ordinal (ltn_trans (ltn_ord j) (ltn_ord (catTupleSuffixIndex i Hi))).
  pose k : 'I_i := Ordinal (catTupleSuffixOrdinal_lt i Hi j' (ltn_ord j)).
  move: (Hfull k).
  rewrite (cat_tuple_tnth_suffix_choice omega1' omega2
    (widen_ord (ltnW (ltn_ord i)) k)
    (leq_addr _ _)).
  have -> :
      Ordinal (cat_tuple_suffix_bound
        (widen_ord (ltnW (ltn_ord i)) k) (leq_addr _ _)) = j'.
    apply: val_inj.
    rewrite /= /k /j' /catTupleSuffixOrdinal_lt /=.
    by rewrite addKn.
  rewrite /catTupleSuffixAssignment tnth_mktuple.
  have -> :
      Ordinal (catTupleSuffixOrdinal_lt i Hi j' (ltn_ord j)) = k
    by apply: val_inj.
  have -> :
      widen_ord (ltnW (ltn_ord (catTupleSuffixIndex i Hi))) j = j'
    by apply: val_inj.
  by [].
  apply/forallP=> j.
  case Hprefix_j: (widen_ord (ltnW (ltn_ord i)) j < ℓ1.+1)%N.
      rewrite (cat_tuple_tnth_prefix_choice omega1' omega2
        (widen_ord (ltnW (ltn_ord i)) j) Hprefix_j).
      rewrite Homega.
      rewrite -Hprefix catTuplePrefix_tnth.
      have -> :
          Ordinal (leq_trans (ltn_ord (Ordinal Hprefix_j)) Hi) = j
        by apply: val_inj.
      by [].
    pose k : 'I_(ℓ1.+1 + ℓ2.+1) := widen_ord (ltnW (ltn_ord i)) j.
    have Hjge : (ℓ1.+1 <= k)%N
      by rewrite leqNgt Hprefix_j.
    rewrite (cat_tuple_tnth_suffix_choice omega1' omega2 k Hjge).
    have Hsuffix := forallP HsuffixBool.
    pose ksuf : 'I_(catTupleSuffixIndex i Hi) :=
      Ordinal (catTupleSuffixIndex_lt i k Hi Hjge (ltn_ord j)).
    move: (Hsuffix ksuf).
    have -> :
        @Ordinal ℓ2.+1 (nat_of_ord k - ℓ1.+1)
          (cat_tuple_suffix_bound k Hjge) =
        catTupleSuffixIndex k Hjge
      by apply: val_inj.
    have -> :
        widen_ord (ltnW (ltn_ord (catTupleSuffixIndex i Hi))) ksuf =
        catTupleSuffixIndex k Hjge
      by apply: val_inj.
    rewrite /catTupleSuffixAssignment tnth_mktuple.
    have -> :
        Ordinal (catTupleSuffixOrdinal_lt i Hi
          (Ordinal (ltn_trans (ltn_ord ksuf)
            (ltn_ord (catTupleSuffixIndex i Hi))))
          (ltn_ord ksuf)) = j.
      apply: val_inj.
      rewrite /= /ksuf /k /catTupleSuffixIndex /=.
      by rewrite subnKC.
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
