(* Conditional distributions for tuple-valued traces. *)

From Stdlib Require Import Unicode.Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals distr.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From Mending.LibExtras.MathcompExtras Require Import DistrExtras TupleExtras.
From Mending.Probability.KL Require Import Core.

Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section ConditionalCoordinate.

Context {R : realType}.

Definition conditional_coordinate {n : nat} {A : choiceType}
    (P : {distr (n.-tuple A) / R}) {i : 'I_n}
    (a : i.-tuple A) : {distr A / R} :=
  dmargin (fun omega : n.-tuple A => tnth omega i)
    (dcond P (fun omega : n.-tuple A => tuple_prefix_eq a omega)).

(* Rewrites conditional-coordinate distances along pointwise-equal distributions. *)
Lemma conditional_coordinate_dist_ext
  {n : nat}
  {A : choiceType}
  (P Q : {distr (n.-tuple A) / R})
  (i : 'I_n)
  (a : i.-tuple A) :
  P =1 Q ->
  conditional_coordinate P a =1 conditional_coordinate Q a.
Proof.
move=> HP.
apply: dmargin_ext.
exact: dcond_ext.
Qed.

(* Collapses conditional-coordinate distance when both conditioning prefixes have zero mass. *)
Lemma conditional_coordinate_zero_prefix
  {n : nat}
  {A : choiceType}
  (P : {distr (n.-tuple A) / R})
  (i : 'I_n)
  (a : i.-tuple A) :
  \P_[P] (fun omega => tuple_prefix_eq a omega) = 0 ->
  conditional_coordinate P a =1 dnull.
Proof.
move=> Hzero x.
rewrite pr_pred1 dnullE.
rewrite /conditional_coordinate pr_dmargin pr_dcond /prc Hzero.
by rewrite invr0 mulr0.
Qed.

Lemma conditional_coordinate_absolute_continuous
  {n : nat}
  {A : choiceType}
  (P Q : {distr (n.-tuple A) / R})
  (i : 'I_n)
  (a : i.-tuple A) :
  absolute_continuous P Q ->
  absolute_continuous
    (conditional_coordinate P a)
    (conditional_coordinate Q a).
Admitted.

End ConditionalCoordinate.
