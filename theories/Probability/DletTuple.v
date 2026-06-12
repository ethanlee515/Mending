(* Probability facts for dlets that concatenate tuple-valued traces. *)

From Stdlib Require Import Unicode.Utf8.
From extructures Require Import ord fset fmap.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals distr ssrZ realseq realsum.
From mathcomp Require Import lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From Mending.Probability.KL Require Import Core.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras RealSumExtras
  TupleExtras.

Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section DletTuple.

Context {R : realType}.

(* Pulls support of a concatenated dlet trace back to a concrete prefix and suffix. *)
Lemma dlet_dunit_cat_dinsupp_preimage
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (omega : (ℓ1.+1 + ℓ2.+1).-tuple A) :
  omega \in dinsupp
    (\dlet_(omega1 <- P0)
     \dlet_(omega2 <- K0 omega1)
       dunit (cat_tuple omega1 omega2)) ->
  exists omega1, exists omega2,
    omega = cat_tuple omega1 omega2 /\
    omega1 \in dinsupp P0 /\
    omega2 \in dinsupp (K0 omega1).
Proof.
move=> Homega.
have [omega1 Homega1 Hinner] := @dinsupp_dlet R _ _ _ _ _ Homega.
have [omega2 Homega2 Hunit] := @dinsupp_dlet R _ _ _ _ _ Hinner.
exists omega1; exists omega2.
split.
  move: Hunit.
  by rewrite dunit1E pnatr_eq0 eqb0 negbK=> /eqP.
by split.
Qed.

(* Builds support of a concatenated dlet trace from supported prefix and suffix traces. *)
Lemma dlet_dunit_cat_dinsupp_image
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (omega1 : (ℓ1.+1).-tuple A)
  (omega2 : (ℓ2.+1).-tuple A) :
  omega1 \in dinsupp P0 ->
  omega2 \in dinsupp (K0 omega1) ->
  cat_tuple omega1 omega2 \in dinsupp
    (\dlet_(omega1 <- P0)
     \dlet_(omega2 <- K0 omega1)
       dunit (cat_tuple omega1 omega2)).
Proof.
move=> Homega1 Homega2.
apply: (@dlet_dinsupp R _ _
  (fun omega1 =>
    \dlet_(omega2 <- K0 omega1) dunit (cat_tuple omega1 omega2))
  P0 omega1 (cat_tuple omega1 omega2) Homega1).
apply: (@dlet_dinsupp R _ _
  (fun omega2 => dunit (cat_tuple omega1 omega2))
  (K0 omega1) omega2 (cat_tuple omega1 omega2) Homega2).
by rewrite dunit1E eqxx oner_neq0.
Qed.

(* Shows concatenating dlet traces preserves absolute continuity componentwise. *)
Lemma dlet_dunit_cat_absolute_continuous
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 Q0 : {distr ((ℓ1.+1).-tuple A) / R})
  (KL KR : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R}) :
  absolute_continuous P0 Q0 ->
  (forall omega1,
    omega1 \in dinsupp P0 -> absolute_continuous (KL omega1) (KR omega1)) ->
  absolute_continuous
    (\dlet_(omega1 <- P0)
     \dlet_(omega2 <- KL omega1)
       dunit (cat_tuple omega1 omega2))
    (\dlet_(omega1 <- Q0)
     \dlet_(omega2 <- KR omega1)
       dunit (cat_tuple omega1 omega2)).
Proof.
move=> Hac0 HacK omega HQomega0.
apply/eqP; apply/negP=> HPomega_nz.
  have HPomega_supp :
    omega \in dinsupp
      (\dlet_(omega1 <- P0)
       \dlet_(omega2 <- KL omega1)
         dunit (cat_tuple omega1 omega2)).
  rewrite in_dinsupp.
  by apply/negP.
have [omega1 [omega2 [Homega [Homega1 Homega2]]]] :=
  dlet_dunit_cat_dinsupp_preimage P0 KL omega HPomega_supp.
have Hqomega1 : omega1 \in dinsupp Q0.
  rewrite in_dinsupp.
  apply/negP=> /eqP HQ0omega1.
  move: Homega1.
  by rewrite in_dinsupp (Hac0 omega1 HQ0omega1) eqxx.
have Hqomega2 : omega2 \in dinsupp (KR omega1).
  rewrite in_dinsupp.
  apply/negP=> /eqP HKRomega2.
  move: Homega2.
  by rewrite in_dinsupp (HacK omega1 Homega1 omega2 HKRomega2) eqxx.
have HQomega_supp :
    cat_tuple omega1 omega2 \in dinsupp
      (\dlet_(omega1 <- Q0)
       \dlet_(omega2 <- KR omega1)
         dunit (cat_tuple omega1 omega2)).
  exact: dlet_dunit_cat_dinsupp_image.
move: HQomega_supp.
by rewrite -Homega in_dinsupp HQomega0 eqxx.
Qed.


(* Computes a prefix event probability through the composed trace dlet. *)
Lemma pr_dlet_cat_prefix_lift_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (p : pred ((ℓ1.+1 + ℓ2.+1).-tuple A))
  (p0 : pred ((ℓ1.+1).-tuple A)) :
  (forall omega1, dweight (K0 omega1) = 1) ->
  (forall omega1 omega2, p (cat_tuple omega1 omega2) = p0 omega1) ->
  \P_[
    \dlet_(omega1 <- P0)
    \dlet_(omega2 <- K0 omega1)
      dunit (cat_tuple omega1 omega2)
  ] p =
  \P_[P0] p0.
Proof.
move=> Hmass Hp.
rewrite pr_dlet.
rewrite [RHS]pr_exp.
apply: expectation_ext=> omega1.
rewrite pr_dlet.
rewrite (expectation_ext (K0 omega1)
  (fun omega2 => \P_[dunit (cat_tuple omega1 omega2)] p)
  (fun _ => if p0 omega1 then 1 else 0)).
  case Hp0: (p0 omega1).
    by rewrite expectation_const // Hmass.
  by rewrite exp0.
move=> omega2.
rewrite pr_dunit Hp.
by case: (p0 omega1).
Qed.

(* Computes prefix conditional probabilities for composed trace distributions. *)
Lemma prc_dlet_cat_prefix_coordinate_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
  (Hi : (i < ℓ1.+1)%N)
  (x : A) :
  (forall omega1, dweight (K0 omega1) = 1) ->
  let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
  let a0 : forall j : 'I_(ℓ1.+1), A :=
    fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
  \P_[
    \dlet_(omega1 <- P0)
    \dlet_(omega2 <- K0 omega1)
      dunit (cat_tuple omega1 omega2),
    fun omega => tuple_prefix_eq i a omega
  ] [pred omega | tnth omega i \in pred1 x] =
  \P_[P0, fun omega1 => tuple_prefix_eq i0 a0 omega1]
    [pred omega1 | tnth omega1 i0 \in pred1 x].
Proof.
move=> Hmass /=.
rewrite /prc.
rewrite (pr_dlet_cat_prefix_lift_eq P0 K0
  (fun omega =>
    (tnth omega i \in pred1 x) && tuple_prefix_eq i a omega)
  (fun omega1 =>
    (tnth omega1 (Ordinal Hi) \in pred1 x) &&
    tuple_prefix_eq (Ordinal Hi)
      (fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))))
      omega1) Hmass).
  rewrite (pr_dlet_cat_prefix_lift_eq P0 K0
    (fun omega => tuple_prefix_eq i a omega)
    (fun omega1 => tuple_prefix_eq (Ordinal Hi)
      (fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))))
      omega1) Hmass) //.
  move=> omega1 omega2.
	  exact: tuple_prefix_eq_cat_prefix.
move=> omega1 omega2.
rewrite (cat_tuple_tnth_prefix_choice omega1 omega2 i Hi).
by rewrite (tuple_prefix_eq_cat_prefix i a Hi omega1 omega2).
Qed.


(* Reduces prefix conditional-coordinate distance to the outer trace distributions. *)
Lemma conditional_coordinate_dlet_cat_prefix_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
  (Hi : (i < ℓ1.+1)%N) :
  (forall omega1, dweight (K0 omega1) = 1) ->
  let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
  let a0 : forall j : 'I_(ℓ1.+1), A :=
    fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
  conditional_coordinate
    (\dlet_(omega1 <- P0)
     \dlet_(omega2 <- K0 omega1)
       dunit (cat_tuple omega1 omega2))
    i a
    =1 conditional_coordinate P0 i0 a0.
Proof.
move=> Hmass /= x.
rewrite !pr_pred1.
rewrite !pr_dmargin.
rewrite !pr_dcond.
exact: (prc_dlet_cat_prefix_coordinate_eq P0 K0 i a Hi x Hmass).
Qed.


(* Computes a dlet probability when the outer prefix is fixed. *)
Lemma pr_dlet_fixed_prefix_from_inner
  {T U : choiceType}
  (P0 : {distr T / R})
  (K0 : T -> {distr U / R})
  (omega1 : T)
  (p : pred U)
  (c : R) :
  (forall omega1',
    \P_[K0 omega1'] p =
      if omega1' == omega1 then c else 0) ->
  \P_[\dlet_(omega1 <- P0) K0 omega1] p =
    P0 omega1 * c.
Proof.
move=> Hinner.
rewrite pr_dlet.
rewrite (expectation_ext P0
  (fun omega1' => \P_[K0 omega1'] p)
  (fun omega1' => if omega1' == omega1 then c else 0)).
  exact: expectation_indicator_eq.
exact: Hinner.
Qed.

(* Relates a fixed-prefix concatenation event to the inner suffix event. *)
Lemma pr_dlet_cat_fixed_prefix_inner_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (omega1 omega1' : (ℓ1.+1).-tuple A)
  (p : pred ((ℓ1.+1 + ℓ2.+1).-tuple A))
  (q : pred ((ℓ2.+1).-tuple A)) :
  (forall omega1' omega2,
    p (cat_tuple omega1' omega2) = (omega1' == omega1) && q omega2) ->
  \P_[
    \dlet_(omega2 <- K0 omega1')
      dunit (cat_tuple omega1' omega2)
  ] p =
    if omega1' == omega1 then \P_[K0 omega1] q else 0.
Proof.
move=> Hp.
rewrite pr_dlet.
case Homega1' : (omega1' == omega1).
  move/eqP: Homega1'=> ->.
  rewrite [RHS]pr_exp.
  apply: expectation_ext=> omega2.
  by rewrite pr_dunit Hp eqxx.
rewrite -(exp0 (K0 omega1')).
apply: expectation_ext=> omega2.
by rewrite pr_dunit Hp Homega1'.
Qed.

(* Computes the probability of a full concatenated prefix by conditioning on its prefix part. *)
Lemma pr_dlet_cat_fixed_prefix_event_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (omega1 : (ℓ1.+1).-tuple A)
  (p : pred ((ℓ1.+1 + ℓ2.+1).-tuple A))
  (q : pred ((ℓ2.+1).-tuple A)) :
  (forall omega1' omega2,
    p (cat_tuple omega1' omega2) = (omega1' == omega1) && q omega2) ->
  \P_[
    \dlet_(omega1 <- P0)
    \dlet_(omega2 <- K0 omega1)
      dunit (cat_tuple omega1 omega2)
  ] p =
  P0 omega1 * \P_[K0 omega1] q.
Proof.
move=> Hp.
apply: pr_dlet_fixed_prefix_from_inner=> omega1'.
exact: (pr_dlet_cat_fixed_prefix_inner_eq K0 omega1 omega1' p q Hp).
Qed.

(* Computes suffix-prefix events after fixing the outer trace prefix. *)
Lemma pr_dlet_cat_suffix_prefix_event_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
  (Hi : (ℓ1.+1 <= i)%N)
  (omega1 : (ℓ1.+1).-tuple A) :
  catTuplePrefix a = omega1 ->
  0 < P0 omega1 ->
  \P_[
    \dlet_(omega1 <- P0)
    \dlet_(omega2 <- K0 omega1)
      dunit (cat_tuple omega1 omega2)
  ] (fun omega => tuple_prefix_eq i a omega) =
  P0 omega1 *
  \P_[K0 omega1]
    (fun omega2 =>
      tuple_prefix_eq
        (catTupleSuffixIndex i Hi)
        (catTupleSuffixAssignment i Hi a)
        omega2).
Proof.
move=> Hprefix _.
apply: pr_dlet_cat_fixed_prefix_event_eq=> omega1' omega2.
exact: (tuple_prefix_eq_cat_suffix i a Hi omega1 omega1' omega2 Hprefix).
Qed.

(* Computes suffix coordinate events after fixing the outer trace prefix. *)
Lemma pr_dlet_cat_suffix_coordinate_event_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
  (Hi : (ℓ1.+1 <= i)%N)
  (omega1 : (ℓ1.+1).-tuple A)
  (x : A) :
  catTuplePrefix a = omega1 ->
  0 < P0 omega1 ->
  \P_[
    \dlet_(omega1 <- P0)
    \dlet_(omega2 <- K0 omega1)
      dunit (cat_tuple omega1 omega2)
  ] (fun omega =>
    (tnth omega i \in pred1 x) && tuple_prefix_eq i a omega) =
  P0 omega1 *
  \P_[K0 omega1]
    (fun omega2 =>
      (tnth omega2 (catTupleSuffixIndex i Hi) \in pred1 x) &&
      tuple_prefix_eq
        (catTupleSuffixIndex i Hi)
        (catTupleSuffixAssignment i Hi a)
        omega2).
Proof.
move=> Hprefix _.
apply: pr_dlet_cat_fixed_prefix_event_eq=> omega1' omega2.
rewrite (cat_tuple_tnth_suffix_choice omega1' omega2 i Hi).
rewrite (tuple_prefix_eq_cat_suffix i a Hi omega1 omega1' omega2 Hprefix).
by case: (tnth omega2 (catTupleSuffixIndex i Hi) \in pred1 x);
   case: (omega1' == omega1);
   case: (tuple_prefix_eq (catTupleSuffixIndex i Hi)
     (catTupleSuffixAssignment i Hi a) omega2).
Qed.

(* Computes suffix conditional probabilities for the inner trace kernel. *)
Lemma prc_dlet_cat_suffix_coordinate_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
  (Hi : (ℓ1.+1 <= i)%N)
  (omega1 : (ℓ1.+1).-tuple A)
  (x : A) :
  catTuplePrefix a = omega1 ->
  0 < P0 omega1 ->
  \P_[
    \dlet_(omega1 <- P0)
    \dlet_(omega2 <- K0 omega1)
      dunit (cat_tuple omega1 omega2),
    fun omega => tuple_prefix_eq i a omega
  ] [pred omega | tnth omega i \in pred1 x] =
  \P_[K0 omega1,
    fun omega2 =>
      tuple_prefix_eq
        (catTupleSuffixIndex i Hi)
        (catTupleSuffixAssignment i Hi a)
        omega2
  ] [pred omega2 |
    tnth omega2 (catTupleSuffixIndex i Hi) \in pred1 x].
Proof.
move=> Hprefix Hpos.
rewrite /prc.
rewrite (pr_dlet_cat_suffix_coordinate_event_eq
  P0 K0 i a Hi omega1 x Hprefix Hpos).
rewrite (pr_dlet_cat_suffix_prefix_event_eq
  P0 K0 i a Hi omega1 Hprefix Hpos).
exact: divr_cancel_left_pos.
Qed.

(* Reduces suffix conditional-coordinate distance to the selected continuation kernels. *)
Lemma conditional_coordinate_dlet_cat_suffix_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
  (Hi : (ℓ1.+1 <= i)%N)
  (omega1 : (ℓ1.+1).-tuple A) :
  catTuplePrefix a = omega1 ->
  0 < P0 omega1 ->
  conditional_coordinate
    (\dlet_(omega1 <- P0)
     \dlet_(omega2 <- K0 omega1)
       dunit (cat_tuple omega1 omega2))
    i a
    =1 conditional_coordinate (K0 omega1)
        (catTupleSuffixIndex i Hi)
        (catTupleSuffixAssignment i Hi a).
Proof.
move=> Hprefix Hpos x.
rewrite !pr_pred1.
rewrite !pr_dmargin.
rewrite !pr_dcond.
exact: (prc_dlet_cat_suffix_coordinate_eq
  P0 K0 i a Hi omega1 x Hprefix Hpos).
Qed.


Lemma cat_tuple_tnth_ord_max_suffix
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (omega1 : (ℓ1.+1).-tuple A)
  (omega2 : (ℓ2.+1).-tuple A) :
  tnth (cat_tuple omega1 omega2) ord_max = tnth omega2 ord_max.
Proof.
have Hi : (ℓ1.+1 <= (ord_max : 'I_(ℓ1.+1 + ℓ2.+1)))%N.
  rewrite /ord_max /=.
  by rewrite -{1}(addn0 ℓ1) ltn_add2l.
rewrite (cat_tuple_tnth_suffix_choice omega1 omega2 ord_max Hi).
apply: congr1.
apply: val_inj.
rewrite /ord_max /=.
change ((ℓ1 + ℓ2.+1 - ℓ1.+1)%N = ℓ2).
by rewrite subnS addnC addnK.
Qed.

(* Pushes the final-coordinate margin of a concatenated trace through the inner dlet. *)
Lemma dmargin_dlet_cat_final
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R}) :
  dmargin (fun omega => tnth omega ord_max)
    (\dlet_(omega1 <- P0)
     \dlet_(omega2 <- K0 omega1)
       dunit (cat_tuple omega1 omega2))
  =1
  \dlet_(omega1 <- P0)
    dmargin (fun omega2 => tnth omega2 ord_max) (K0 omega1).
Proof.
move=> z.
rewrite dmargin_dlet.
apply: eq_in_dlet=> // omega1 _ z1.
rewrite dmargin_dlet.
apply: eq_in_dlet=> // omega2 _ z2.
rewrite dmargin_dunit.
by rewrite cat_tuple_tnth_ord_max_suffix.
Qed.


End DletTuple.
