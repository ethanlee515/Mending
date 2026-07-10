(* Conditional distributions for tuple-valued traces. *)

From Stdlib Require Import Unicode.Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals realsum distr.
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
rewrite /conditional_coordinate pr_dmargin_pred1_clean pr_dcond /prc Hzero.
by rewrite invr0 mulr0.
Qed.

Local Lemma pr_pred1I
  {T : choiceType}
  (P : {distr T / R})
  (p : pred T)
  (x : T) :
  \P_[P] [predI pred1 x & p] = (p x)%:R * P x.
Proof.
rewrite /pr.
rewrite (psum_finseq (r := [:: x])).
- rewrite big_seq1 !inE eqxx -topredE /=.
  case Hpx: (p x); rewrite ?mul1r ?mul0r.
    by rewrite ger0_norm ?ge0_mu.
  by rewrite normr0.
- by [].
move=> y.
rewrite !inE.
case: (y == x) => //=.
by rewrite mul0r eqxx.
Qed.

Local Lemma dcond_absolute_continuous
  {T : choiceType}
  (P Q : {distr T / R})
  (p : pred T) :
  absolute_continuous P Q ->
  absolute_continuous (dcond P p) (dcond Q p).
Proof.
move=> Hac x.
rewrite !dcondE /prc !pr_pred1I.
case Hpx: (p x); rewrite ?mul1r ?mul0r //.
case HQp0: (\P_[Q] p == 0).
  move/eqP: HQp0=> HQp0 _.
  rewrite /pr in HQp0.
  have HPp0 : \P_[P] p = 0.
    rewrite /pr.
    apply: psum_eq0=> y.
    case Hpy: (p y); rewrite ?mul0r //.
    have HQy0 : Q y = 0.
      have HQpy0 := eq0_psum (summable_pr p Q) HQp0 y.
      by move: HQpy0; rewrite Hpy mul1r.
    by rewrite (Hac y HQy0) mulr0.
  by rewrite HPp0 invr0 mulr0.
move=> HQx0.
have HQx_zero : Q x = 0.
  case HQx0b: (Q x == 0).
    exact/eqP.
  have HQp_pos : 0 < \P_[Q] p.
    by rewrite lt_def ge0_pr andbT HQp0.
  have HQx_pos : 0 < Q x.
    by rewrite lt_def ge0_mu andbT HQx0b.
  have Hprod_pos : 0 < Q x * (\P_[Q] p)^-1.
    by rewrite mulr_gt0 // invr_gt0.
  by rewrite HQx0 ltxx in Hprod_pos.
by rewrite (Hac x HQx_zero) mul0r.
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
Proof.
move=> Hac.
apply: dmargin_absolute_continuous.
exact: dcond_absolute_continuous.
Qed.

End ConditionalCoordinate.
