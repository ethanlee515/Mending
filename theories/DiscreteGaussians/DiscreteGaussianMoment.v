From Stdlib Require Import Utf8 Lia.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq choice bigop order all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp Require Import reals realsum exp sequences realseq distr.
Set Warnings "-notation-incompatible-prefix".
From mathcomp Require Import xfinmap.
Set Warnings "notation-incompatible-prefix".
From mathcomp Require Import lra.
From mathcomp.algebra_tactics Require Import ring.
Import GRing.Theory Num.Theory Order.Theory.

From Mending Require Import DiscreteGaussian.
From Mending Require Import RealSumExtras.
From Mending Require Import DistrExtras.

Local Open Scope ring_scope.

(** First-moment summability for the integer discrete Gaussian.

    The intended proof follows the same strategy as [summable_gaussian]:
    dominate the Gaussian tail by a geometric tail.  For the first moment we
    reduce to the reusable fact that [n * r^n] is summable for [0 <= r < 1]. *)

Section DiscreteGaussianMoment.

Context (R : realType).

Definition mid_step_ratio (r : R) : R :=
  (1 + r) / 2.

Definition linear_geometric_tail_scale (r : R) : R :=
  1 + (1 / (1 - r / mid_step_ratio r)) ^ 2.

Lemma mid_step_ratio_in01 (r : R) :
  0 <= r < 1 ->
  0 <= mid_step_ratio r < 1.
Proof.
move/andP=> [ge0_r lt1_r].
rewrite /mid_step_ratio.
apply/andP; split; lra.
Qed.

Lemma nat_mul_expr_le_geometric_series (x : R) n :
  0 <= x ->
  x <= 1 ->
  n%:R * x ^+ n <= series (geometric 1 x) n.+1.
Proof.
move=> ge0_x le1_x.
elim: n => [|n ih].
- rewrite mul0r.
  apply: sumr_ge0 => i _.
  rewrite mulr_ge0 ?ler01 ?exprn_ge0 //.
rewrite -natr1 mulrDl mul1r.
rewrite exprS.
rewrite seriesSr.
apply: lerD.
- apply: le_trans ih.
  rewrite ler_wpM2l ?ler0n //.
  rewrite {2}(_ : x ^+ n = x ^+ n * 1); last by rewrite mulr1.
  rewrite mulrC ler_wpM2l ?exprn_ge0 //.
rewrite /geometric /= mul1r exprS.
exact: lexx.
Qed.

Lemma nat_mul_expr_le_inverse_square (x : R) n :
  0 <= x < 1 ->
  n%:R * x ^+ n <= (1 - x)^-2.
Proof.
move=> x01.
have ge0_x : 0 <= x by case/andP: x01.
have lt1_x : x < 1 by case/andP: x01.
have [-> | nz_x] := eqVneq x 0.
- case: n => [|n].
  + rewrite expr0 ?mulr0 ?mul0r ?subr0 ?expr0 ?mulr1 ?invr_ge0 ?ler01.
    exact: exprn_ge0.
  + rewrite exprS ?mul0r ?mulr0 ?subr0 ?expr0 ?mulr1 ?invr_ge0 ?ler01.
    exact: exprn_ge0.
have gt0_x : 0 < x by rewrite lt_neqAle eq_sym nz_x ge0_x.
have le_sum :
    n%:R * x ^+ n <= series (geometric 1 x) n.+1.
  exact: (nat_mul_expr_le_geometric_series x n ge0_x (ltW lt1_x)).
apply: (le_trans le_sum).
have le_lim :
    series (geometric 1 x) n.+1 <= 1 * (1 - x)^-1.
  apply: geometric_le_lim.
  - exact: ler01.
  - exact: gt0_x.
  by rewrite ger0_norm.
apply: le_trans le_lim _.
rewrite mul1r expr2.
rewrite ler_pV2 ?mulr_gt0 ?subr_gt0 //.
- rewrite -[leRHS]mulr1 ler_pM2l ?subr_gt0 //; lra.
- by rewrite inE unitf_gt0 ?subr_gt0.
- by rewrite inE unitf_gt0 ?mulr_gt0 ?subr_gt0.
Qed.

Lemma linear_geometric_eventually_le_geometric (r : R) n :
  0 <= r < 1 ->
  n%:R * geometric 1 r n <=
    linear_geometric_tail_scale r * geometric 1 (mid_step_ratio r) n.
Proof.
move=> r01.
have ge0_r : 0 <= r by case/andP: r01.
have lt1_r : r < 1 by case/andP: r01.
pose u := mid_step_ratio r.
have u01 : 0 <= u < 1 by exact: mid_step_ratio_in01.
have gt0_u : 0 < u.
  rewrite /u /mid_step_ratio; lra.
pose q := r / u.
have q01 : 0 <= q < 1.
  apply/andP; split.
  - rewrite divr_ge0 // ltW //.
  - rewrite ltr_pdivrMr // /u /mid_step_ratio; lra.
rewrite /geometric /= !mul1r.
have rE : r = q * u by rewrite /q divfK // gt_eqF.
rewrite {1}rE exprMn mulrA.
apply: ler_wpM2r.
- apply: exprn_ge0.
  exact: (ltW gt0_u).
have le_q : n%:R * q ^+ n <= (1 - q)^-2.
  exact: (nat_mul_expr_le_inverse_square q n q01).
apply: (le_trans le_q).
rewrite /linear_geometric_tail_scale /q /u.
lra.
Qed.

Lemma linear_geometric_tail_scale_ge0 (r : R) :
  0 <= linear_geometric_tail_scale r.
Proof.
rewrite /linear_geometric_tail_scale.
rewrite addr_ge0 ?ler01 //.
exact: sqr_ge0.
Qed.

Lemma summable_nat_mul_geometric (r : R) :
  0 <= r < 1 ->
  summable (T := nat) (fun n : nat => n%:R * geometric 1 r n).
Proof.
move=> r01.
apply: (le_summable
  (F2 := fun n : nat =>
     linear_geometric_tail_scale r * geometric 1 (mid_step_ratio r) n)).
- move=> n; apply/andP; split.
  + rewrite mulr_ge0 ?ler0n //.
    apply: ge0_geo.
    by case/andP: r01.
  exact: linear_geometric_eventually_le_geometric.
apply: summableZ.
apply: summable_geo.
exact: mid_step_ratio_in01.
Qed.

Lemma summable_int_linear_geometric s :
  s > 0 ->
  summable (fun x : int => (absz x)%:R * geom_above R s (absz x)).
Proof.
move=> gt0_s.
apply: (mirror_summable R
  (fun n : nat => n%:R * geom_above R s n)).
apply: summable_nat_mul_geometric.
rewrite /geom_above /max_step_ratio /=.
apply/andP; split.
- exact: expR_ge0.
rewrite expR_lt1.
suff: (1 / s) ^ 2 > 0 by lra.
rewrite /exprz /= expr2.
have H : 1 / s > 0 by exact: divr_gt0.
exact: mulr_gt0.
Qed.

Lemma le_abs_int_gaussian_linear_geo s x :
  s > 0 ->
  `|x%:~R * gaussian R s x| <=
    (absz x)%:R * geom_above R s (absz x).
Proof.
move=> gt0_s.
rewrite normrM.
have -> : `|gaussian R s x| = gaussian R s x by rewrite ger0_norm ?ge0_gaussian.
rewrite natr_absz intr_norm.
apply: ler_pM.
- exact: normr_ge0.
- exact: ge0_gaussian.
- by [].
exact: le_gauss_geo.
Qed.

Lemma summable_int_gaussian_moment s :
  s > 0 ->
  summable (fun x : int => x%:~R * gaussian R s x).
Proof.
move=> gt0_s.
apply/summable_abs.
apply: (le_summable
  (F2 := fun x : int => (absz x)%:R * geom_above R s (absz x))).
- move=> x.
  apply/andP; split.
  + exact: normr_ge0.
  + exact: le_abs_int_gaussian_linear_geo.
exact: summable_int_linear_geometric.
Qed.

Lemma summable_centered_discrete_gaussian_moment s :
  s > 0 ->
  \E?_[centered_discrete_gaussian R s] (fun x : int => x%:~R).
Proof.
move=> gt0_s.
rewrite /has_esp.
apply: (eq_summable
  (S1 := (1 / sum (gaussian R s)) \*o
    (fun x : int => x%:~R * gaussian R s x))).
- move=> x /=.
  rewrite /centered_discrete_gaussian /gaussian_pdf.
  rewrite ifT //.
  lra.
apply: summableZ.
exact: summable_int_gaussian_moment.
Qed.

Lemma discrete_gaussian_centered_difference_has_exp center s :
  s > 0 ->
  \E?_[discrete_gaussian R center s] (fun x : int => (x - center)%:~R).
Proof.
move=> gt0_s.
rewrite /has_esp.
rewrite /discrete_gaussian.
apply: (eq_summable
  (S1 := fun x : int =>
     (x - center)%:~R * centered_discrete_gaussian R s (x - center))).
- move=> x.
  by rewrite dmargin_add_intE.
apply: (summable_shift_add_int R
  (fun y : int => y%:~R * centered_discrete_gaussian R s y) center).
exact: summable_centered_discrete_gaussian_moment.
Qed.

End DiscreteGaussianMoment.
