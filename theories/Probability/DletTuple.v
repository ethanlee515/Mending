(* Probability facts for dlets that concatenate tuple-valued traces. *)

From Stdlib Require Import Unicode.Utf8.
From extructures Require Import ord fset fmap.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals distr ssrZ realseq realsum.
From mathcomp Require Import lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From Mending.Probability.KL Require Import Core.
From Mending.Probability Require Import ConditionalCoordinate.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras RealSumExtras
  TupleExtras.

Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section DletTuple.

Context {R : realType}.

(* === Support And Absolute Continuity For Concatenated Dlets === *)

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


(* === Prefix Coordinates Of Concatenated Dlets === *)

(* The prefix-lift probability wrapper below is the remaining direct Tonelli
   user in this file.  Keep the deprecated bind-probability theorem explicit
   until it is replaced by a named countable partition/Fubini proof. *)

Lemma pr_dmargin_cat_fixed_prefix
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (omega1 : (ℓ1.+1).-tuple A)
  (K0 : {distr ((ℓ2.+1).-tuple A) / R})
  (p : pred ((ℓ1.+1 + ℓ2.+1).-tuple A)) :
  \P_[dmargin (fun omega2 => cat_tuple omega1 omega2) K0] p =
  \P_[K0] (fun omega2 => p (cat_tuple omega1 omega2)).
Proof.
rewrite /pr.
pose f := fun omega2 : (ℓ2.+1).-tuple A => cat_tuple omega1 omega2.
pose S := fun omega : (ℓ1.+1 + ℓ2.+1).-tuple A =>
  (p omega)%:R * dmargin f K0 omega.
pose Img : pred ((ℓ1.+1 + ℓ2.+1).-tuple A) :=
  fun omega => cat_tuple omega1 (catTupleSuffix omega) == omega.
rewrite (@reindex_psum_onto R ((ℓ1.+1 + ℓ2.+1).-tuple A)
  ((ℓ2.+1).-tuple A) S Img f
  (fun omega => Some (catTupleSuffix omega))).
- apply/eq_psum=> omega2.
  rewrite /S /f.
  rewrite (dmargin_injectiveE f K0); last exact: cat_tuple_fixed_prefix_injective.
  by [].
- move=> omega HS.
  have Hmargin : dmargin f K0 omega != 0.
    move: HS.
    rewrite /S mulf_eq0 negb_or=> /andP[_ Hmargin].
    exact: Hmargin.
  have [omega2 _ Homega] := dmargin_dinsupp_preimage K0 f omega Hmargin.
  apply/eqP.
  by rewrite -Homega /f catTupleSuffix_cat.
- move=> omega Himg.
  by rewrite /= /f (eqP Himg).
- move=> omega2 _.
  by rewrite /= /f catTupleSuffix_cat.
Qed.

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
rewrite pr_dmargin_cat_fixed_prefix.
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

(* Pushes a final-coordinate marginal through a bind by partitioning fibers. *)
Lemma dlet_dmargin_final
  {n : nat}
  {A U : choiceType}
  (P : {distr ((n.+1).-tuple A) / R})
  (K : A -> {distr U / R}) :
  \dlet_(x <- dmargin (fun omega => tnth omega ord_max) P) K x
  =1
  \dlet_(omega <- P) K (tnth omega ord_max).
Proof.
move=> z.
rewrite !dletE.
pose f := fun omega : (n.+1).-tuple A => tnth omega ord_max.
pose S := fun omega : (n.+1).-tuple A => P omega * K (f omega) z.
have HSge omega : 0 <= S omega.
  by rewrite /S mulr_ge0 ?ge0_mu.
have HSsumm : summable S.
  apply: (le_summable (F2 := P)); last exact: summable_mu.
  move=> omega; apply/andP; split; first exact: HSge.
  rewrite /S -[X in _ <= X]mulr1.
  apply: ler_wpM2l; first exact: ge0_mu.
  apply: (le_trans _ (le1_mu (K (f omega)))).
  have Hsingle :
      K (f omega) z =
        \sum_(j <- [:: z]) `|K (f omega) j|.
    by rewrite big_seq1 ger0_norm ?ge0_mu.
  rewrite Hsingle.
  exact: (gerfinseq_psum (S := K (f omega)) (r := [:: z])
    _ (summable_mu (K (f omega)))).
transitivity
  (psum (fun x : A =>
    psum (fun omega : (n.+1).-tuple A =>
      (f omega == x)%:R * P omega * K x z))).
  apply/eq_psum=> x.
  rewrite dmargin_psumE.
  rewrite [psum _ * K x z]mulrC -psumZ; last exact: ge0_mu.
  apply/eq_psum=> omega.
  by rewrite mulrC.
transitivity
  (psum (fun x : A =>
    psum (fun omega : (n.+1).-tuple A => S omega * (f omega == x)%:R))).
  apply/eq_psum=> x.
  apply/eq_psum=> omega.
  rewrite /S.
  case Hfx: (f omega == x).
  - move/eqP: Hfx=> Hfx_eq.
    rewrite Hfx_eq.
    change true%:R with (1 : R).
    by rewrite !mul1r mulr1.
  - change false%:R with (0 : R).
    by rewrite !mul0r mulr0.
rewrite -(@partition_psum R ((n.+1).-tuple A) A f S HSsumm).
by [].
Qed.

Lemma psum_pair_fst_fiberR
    {T U : choiceType} (S : T * U -> R) (x : T) :
  (forall xy, 0 <= S xy) ->
  psum (fun xy : T * U => S xy * (xy.1 == x)%:R) =
  psum (fun y : U => S (x, y)).
Proof.
move=> HS.
rewrite (@reindex_psum_onto R (T * U)%type U
  (fun xy : T * U => S xy * (xy.1 == x)%:R)
  [pred xy : T * U | xy.1 == x]
  (fun y : U => (x, y))
  (fun xy : T * U => if xy.1 == x then Some xy.2 else None)).
- apply/eq_psum=> y.
  by rewrite eqxx mulr1.
- move=> xy Hxy.
  case Hxyx : (xy.1 == x); first by [].
  by move: Hxy; rewrite Hxyx mulr0 eqxx.
- case=> x' y /= Hx'.
  move: Hx'; rewrite /= => /eqP Hx'.
  change (x' = x) in Hx'.
  by rewrite Hx' eqxx.
- by move=> y _; rewrite eqxx.
Qed.

Lemma psum_pair_snd_fiberR
    {T U : choiceType} (S : T * U -> R) (y : U) :
  (forall xy, 0 <= S xy) ->
  psum (fun xy : T * U => S xy * (xy.2 == y)%:R) =
  psum (fun x : T => S (x, y)).
Proof.
move=> HS.
rewrite (@reindex_psum_onto R (T * U)%type T
  (fun xy : T * U => S xy * (xy.2 == y)%:R)
  [pred xy : T * U | xy.2 == y]
  (fun x : T => (x, y))
  (fun xy : T * U => if xy.2 == y then Some xy.1 else None)).
- apply/eq_psum=> x.
  by rewrite eqxx mulr1.
- move=> xy Hxy.
  case Hxyy : (xy.2 == y); first by [].
  by move: Hxy; rewrite Hxyy mulr0 eqxx.
- case=> x y' /= Hy'.
  move: Hy'; rewrite /= => /eqP Hy'.
  change (y' = y) in Hy'.
  by rewrite Hy' eqxx.
- by move=> x _; rewrite eqxx.
Qed.

Lemma dmargin_dlet_partition
    {T U V : choiceType}
    (P : {distr T / R})
    (K : T -> {distr U / R})
    (g : U -> V) :
  dmargin g (\dlet_(x <- P) K x) =1
  \dlet_(x <- P) dmargin g (K x).
Proof.
move=> z.
rewrite dmargin_psumE dletE.
pose S := fun xy : T * U =>
  K xy.1 xy.2 * P xy.1 * (g xy.2 == z)%:R.
have HSge xy : 0 <= S xy.
  by rewrite /S !mulr_ge0 ?ge0_mu ?ler0n.
have HSsumm : summable S.
  apply: (le_summable
    (F2 := fun xy : T * U => K xy.1 xy.2 * P xy.1)).
    move=> [x y]; apply/andP; split; first exact: HSge.
    rewrite /S -[X in _ <= X]mulr1.
    apply: ler_wpM2l.
      by rewrite mulr_ge0 ?ge0_mu.
    by case: (g y == z); rewrite ?ler01 ?ler0n.
  apply: (@summable_kernel_weighted_pair_nonneg R T U P K).
  - move=> x; exact: ge0_mu.
  - exact: summable_mu.
transitivity (psum S).
  rewrite (partition_psum (S := S) (fun xy : T * U => xy.2)) //.
  apply/eq_psum=> y.
  rewrite (psum_pair_snd_fiberR S y HSge).
  rewrite dletE.
  rewrite -psumZ; last by case: (g y == z); rewrite ?ler01 ?ler0n.
  apply/eq_psum=> x.
  change ((g y == z)%:R * (P x * K x y) = S (x, y)).
  by rewrite /S /= mulrC [P x * K x y]mulrC.
rewrite (partition_psum (S := S) (fun xy : T * U => xy.1)) //.
apply/eq_psum=> x.
rewrite (psum_pair_fst_fiberR S x HSge).
rewrite dmargin_psumE.
rewrite -psumZ; last exact: ge0_mu.
apply/eq_psum=> y.
change (S (x, y) = P x * ((g y == z)%:R * K x y)).
by rewrite /S [(g y == z)%:R * K x y]mulrC mulrA [P x * K x y]mulrC.
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
rewrite dmargin_dlet_partition.
apply: eq_in_dlet=> // omega1 _ z1.
rewrite dmargin_dlet_partition.
apply: eq_in_dlet=> // omega2 _ z2.
rewrite dmargin_dunit.
by rewrite cat_tuple_tnth_ord_max_suffix.
Qed.


End DletTuple.
