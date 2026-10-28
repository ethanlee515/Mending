(* Probability facts for dlets that concatenate tuple-valued traces. *)

From Stdlib Require Import Unicode.Utf8.
From extructures Require Import ord fset fmap.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import boot order algebra.
From mathcomp Require Import reals distr ssrZ realseq realsum.
From mathcomp Require Import arithmetic_tactic.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From Mending.Probability.KL Require Import Core.
From Mending.Probability Require Import ConditionalCoordinate.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras RealSumExtras
  TupleExtras.
Set SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section DletTuple.

Context {R : realType}.

(* === Prefix Coordinates Of Concatenated Dlets === *)

Lemma pr_eq_from_fibers
  {T U : choiceType}
  (D : {distr T / R})
  (P0 : {distr U / R})
  (f : T -> U)
  (p : pred T)
  (p0 : pred U) :
  (forall x, p x = p0 (f x)) ->
  (forall y, \P_[D] [pred x | f x == y] = P0 y) ->
  \P_[D] p = \P_[P0] p0.
Proof.
move=> Hp Hfiber.
rewrite /pr.
rewrite (@partition_psum R T U f (fun x => (p x)%:R * D x));
  last exact: summable_pr.
apply/eq_psum=> y.
case Hp0y: (p0 y).
- rewrite mul1r -Hfiber /pr.
  apply/eq_psum=> x.
  rewrite Hp.
  case Hfx: (f x == y).
    rewrite /= Hfx.
    move/eqP: Hfx=> Hfx_eq.
    rewrite Hfx_eq Hp0y.
    change true%:R with (1 : R).
    by rewrite !mul1r !mulr1.
  rewrite /= Hfx.
  change false%:R with (0 : R).
  by rewrite !mul0r ?mulr0.
- change false%:R with (0 : R).
  rewrite mul0r.
  apply/psum_eq0=> x.
  rewrite Hp.
  case Hfx: (f x == y); last first.
    change false%:R with (0 : R).
    by rewrite mulr0.
  move/eqP: Hfx=> Hfx_eq.
  rewrite Hfx_eq Hp0y.
  change false%:R with (0 : R).
  by rewrite !mul0r.
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
have Hzero omega1' u :
    omega1' != omega1 -> p u -> K0 omega1' u = 0.
  move=> Homega1' Hp_u.
  have Hpr0 : \P_[K0 omega1'] p = 0.
    by rewrite Hinner (negbTE Homega1').
  have Hpoint := eq0_psum (summable_pr p (K0 omega1')) Hpr0 u.
  by move: Hpoint; rewrite Hp_u mul1r.
rewrite /pr.
transitivity (psum (fun u => (p u)%:R * (P0 omega1 * K0 omega1 u))).
  apply/eq_psum=> u.
  case Hp_u: (p u); last by rewrite !mul0r.
  rewrite !mul1r dletE.
  rewrite (psum_finseq (r := [:: omega1])).
  - by rewrite big_seq1 ger0_norm ?mulr_ge0 ?ge0_mu.
  - by [].
  move=> omega1' Hnz.
  rewrite inE.
  case Homega1' : (omega1' == omega1); first by [].
  by move: Hnz; rewrite inE
    (Hzero omega1' u (negbT Homega1') Hp_u) mulr0 eqxx.
rewrite (eq_psum
  (F2 := fun u => P0 omega1 * ((p u)%:R * K0 omega1 u))).
  rewrite psumZ; last exact: ge0_mu.
  rewrite -/(\P_[K0 omega1] p) Hinner eqxx.
  by rewrite mulrC.
by move=> u; rewrite !mulrA [(p u)%:R * P0 omega1]mulrC.
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
change (
  \P_[dmargin (fun omega2 => cat_tuple omega1' omega2) (K0 omega1')] p =
  if omega1' == omega1 then \P_[K0 omega1] q else 0).
rewrite pr_dmargin.
case Homega1' : (omega1' == omega1).
  move/eqP: Homega1'=> ->.
  apply/eq_pr=> omega2.
  change (p (cat_tuple omega1 omega2) = q omega2).
  by rewrite Hp eqxx.
rewrite -(pr_pred0 (K0 omega1')).
apply/eq_pr=> omega2.
change (p (cat_tuple omega1' omega2) = false).
by rewrite Hp Homega1'.
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
pose D :=
  \dlet_(omega1 <- P0)
  \dlet_(omega2 <- K0 omega1)
    dunit (cat_tuple omega1 omega2).
apply: (pr_eq_from_fibers D P0 catTuplePrefixFull p p0).
- move=> omega.
  rewrite -(catTuple_eta omega).
  by rewrite Hp catTuplePrefixFull_cat.
- move=> omega1.
  rewrite (pr_dlet_cat_fixed_prefix_event_eq P0 K0 omega1
    [pred omega | catTuplePrefixFull omega == omega1]
    predT).
    by rewrite Hmass mulr1.
  move=> omega1' omega2.
  by rewrite /= catTuplePrefixFull_cat andbT.
Qed.

(* Computes prefix conditional probabilities for composed trace distributions. *)
Lemma prc_dlet_cat_prefix_coordinate_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : i.-tuple A)
  (Hi : (i < ℓ1.+1)%N)
  (x : A) :
  (forall omega1, dweight (K0 omega1) = 1) ->
  let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
  \P_[
    \dlet_(omega1 <- P0)
    \dlet_(omega2 <- K0 omega1)
      dunit (cat_tuple omega1 omega2),
    fun omega => tuple_prefix_eq a omega
  ] [pred omega | tnth omega i \in pred1 x] =
  \P_[P0, fun omega1 => @tuple_prefix_eq _ _ i0 a omega1]
    [pred omega1 | tnth omega1 i0 \in pred1 x].
Proof.
move=> Hmass /=.
rewrite /prc.
rewrite (pr_dlet_cat_prefix_lift_eq P0 K0
  (fun omega =>
    (tnth omega i \in pred1 x) && tuple_prefix_eq a omega)
  (fun omega1 =>
    (tnth omega1 (Ordinal Hi) \in pred1 x) &&
    @tuple_prefix_eq _ _ (Ordinal Hi) a omega1) Hmass).
  rewrite (pr_dlet_cat_prefix_lift_eq P0 K0
    (fun omega => tuple_prefix_eq a omega)
    (fun omega1 => @tuple_prefix_eq _ _ (Ordinal Hi) a omega1) Hmass) //.
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
  (a : i.-tuple A)
  (Hi : (i < ℓ1.+1)%N) :
  (forall omega1, dweight (K0 omega1) = 1) ->
  let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
  conditional_coordinate
    (\dlet_(omega1 <- P0)
     \dlet_(omega2 <- K0 omega1)
       dunit (cat_tuple omega1 omega2))
    a
    =1 @conditional_coordinate _ _ _ P0 i0 a.
Proof.
move=> Hmass /= x.
rewrite !pr_pred1.
rewrite !pr_dmargin.
rewrite !pr_dcond.
exact: (prc_dlet_cat_prefix_coordinate_eq P0 K0 i a Hi x Hmass).
Qed.


(* === Suffix Coordinates Of Concatenated Dlets === *)

(* Collapses suffix conditionals when the fixed outer prefix has zero mass. *)
Lemma conditional_coordinate_dlet_cat_suffix_zero_prefix
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : i.-tuple A)
  (Hi : (ℓ1.+1 <= i)%N) :
  P0 (catTuplePrefix i Hi a) = 0 ->
  conditional_coordinate
    (\dlet_(omega1 <- P0)
     \dlet_(omega2 <- K0 omega1)
       dunit (cat_tuple omega1 omega2))
    a =1 dnull.
Proof.
move=> Hzero.
apply: conditional_coordinate_zero_prefix.
rewrite (pr_dlet_cat_fixed_prefix_event_eq
  P0 K0 (catTuplePrefix i Hi a)
  (fun omega => tuple_prefix_eq a omega)
  (fun omega2 =>
    @tuple_prefix_eq _ _ (catTupleSuffixIndex i Hi)
      (catTupleSuffixAssignment i Hi a)
      omega2)).
  by rewrite Hzero mul0r.
move=> omega1' omega2.
exact: (tuple_prefix_eq_cat_suffix i a Hi
  (catTuplePrefix i Hi a) omega1' omega2 erefl).
Qed.

(* Computes suffix-prefix events after fixing the outer trace prefix. *)
Lemma pr_dlet_cat_suffix_prefix_event_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : i.-tuple A)
  (Hi : (ℓ1.+1 <= i)%N)
  (omega1 : (ℓ1.+1).-tuple A) :
  catTuplePrefix i Hi a = omega1 ->
  0 < P0 omega1 ->
  \P_[
    \dlet_(omega1 <- P0)
    \dlet_(omega2 <- K0 omega1)
      dunit (cat_tuple omega1 omega2)
  ] (fun omega => tuple_prefix_eq a omega) =
  P0 omega1 *
  \P_[K0 omega1]
    (fun omega2 =>
      @tuple_prefix_eq _ _ (catTupleSuffixIndex i Hi)
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
  (a : i.-tuple A)
  (Hi : (ℓ1.+1 <= i)%N)
  (omega1 : (ℓ1.+1).-tuple A)
  (x : A) :
  catTuplePrefix i Hi a = omega1 ->
  0 < P0 omega1 ->
  \P_[
    \dlet_(omega1 <- P0)
    \dlet_(omega2 <- K0 omega1)
      dunit (cat_tuple omega1 omega2)
  ] (fun omega =>
    (tnth omega i \in pred1 x) && tuple_prefix_eq a omega) =
  P0 omega1 *
  \P_[K0 omega1]
    (fun omega2 =>
      (tnth omega2 (catTupleSuffixIndex i Hi) \in pred1 x) &&
      @tuple_prefix_eq _ _ (catTupleSuffixIndex i Hi)
        (catTupleSuffixAssignment i Hi a)
        omega2).
Proof.
move=> Hprefix _.
apply: pr_dlet_cat_fixed_prefix_event_eq=> omega1' omega2.
rewrite (cat_tuple_tnth_suffix_choice omega1' omega2 i Hi).
rewrite (tuple_prefix_eq_cat_suffix i a Hi omega1 omega1' omega2 Hprefix).
by case: (tnth omega2 (catTupleSuffixIndex i Hi) \in pred1 x);
   case: (omega1' == omega1);
   case: (@tuple_prefix_eq _ _ (catTupleSuffixIndex i Hi)
     (catTupleSuffixAssignment i Hi a) omega2).
Qed.

(* Computes suffix conditional probabilities for the inner trace kernel. *)
Lemma prc_dlet_cat_suffix_coordinate_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : i.-tuple A)
  (Hi : (ℓ1.+1 <= i)%N)
  (omega1 : (ℓ1.+1).-tuple A)
  (x : A) :
  catTuplePrefix i Hi a = omega1 ->
  0 < P0 omega1 ->
  \P_[
    \dlet_(omega1 <- P0)
    \dlet_(omega2 <- K0 omega1)
      dunit (cat_tuple omega1 omega2),
    fun omega => tuple_prefix_eq a omega
  ] [pred omega | tnth omega i \in pred1 x] =
  \P_[K0 omega1,
    fun omega2 =>
      @tuple_prefix_eq _ _ (catTupleSuffixIndex i Hi)
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
  (a : i.-tuple A)
  (Hi : (ℓ1.+1 <= i)%N)
  (omega1 : (ℓ1.+1).-tuple A) :
  catTuplePrefix i Hi a = omega1 ->
  0 < P0 omega1 ->
  conditional_coordinate
    (\dlet_(omega1 <- P0)
     \dlet_(omega2 <- K0 omega1)
       dunit (cat_tuple omega1 omega2))
    a
    =1 conditional_coordinate (K0 omega1)
        (catTupleSuffixAssignment i Hi a).
Proof.
move=> Hprefix Hpos x.
rewrite !pr_pred1.
rewrite !pr_dmargin.
rewrite !pr_dcond.
exact: (prc_dlet_cat_suffix_coordinate_eq
  P0 K0 i a Hi omega1 x Hprefix Hpos).
Qed.


(* === Final Coordinates Of Concatenated Dlets === *)

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
