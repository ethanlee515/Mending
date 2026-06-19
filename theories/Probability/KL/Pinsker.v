Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra all_reals distr.
From mathcomp Require Import realseq realsum exp lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From mathcomp.algebra_tactics Require Import ring.

From Mending.LibExtras.MathcompExtras Require Import DistrExtras.
From Mending.Probability.KL Require Import Core.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

Section KL_Pinsker.

Context {R: realType}.

Lemma ln_r_ineq (r : R) :
  0 < r ->
  r * ln r - r + 1 >= (r - 1)^2 / (r + 1).
Admitted.

Lemma kl_chi2_pointwise {T : choiceType} (P Q : {distr T / R}) x :
  absolute_continuous P Q ->
  Q x * ((P x / Q x - 1)^2 / (P x / Q x + 1)) <=
    P x * ln (P x / Q x) - P x + Q x.
Proof.
move=> Hac.
case HQx0: (Q x == 0).
- have HPx0 : P x = 0 by exact: Hac x (eqP HQx0).
  by rewrite (eqP HQx0) HPx0 invr0 !mul0r subrr addr0.
- have HQx_pos : 0 < Q x by rewrite lt_def ge0_mu HQx0.
  case HPx0: (P x == 0).
  + rewrite (eqP HPx0) mul0r sub0r add0r.
    lra.
  have HPx_pos : 0 < P x by rewrite lt_def ge0_mu HPx0.
  have Hratio_pos : 0 < P x / Q x by rewrite divr_gt0.
  have Hineq := ln_r_ineq (P x / Q x) Hratio_pos.
  have Hscaled :
      Q x * ((P x / Q x - 1)^2 / (P x / Q x + 1)) <=
      Q x * (P x / Q x * ln (P x / Q x) - P x / Q x + 1).
    by apply: ler_wpM2l; first exact: ltW.
  apply: (le_trans Hscaled).
  rewrite mulrDr mulrBr.
  rewrite [Q x * (P x / Q x * _)]mulrC -mulrA.
  rewrite [Q x * (P x / Q x)]mulrC.
  rewrite -mulrA divfK ?lt0r_neq0 //.
  rewrite mulr1.
  have -> : (Q x)^-1 * ln (P x / Q x) * Q x = ln (P x / Q x).
    by rewrite [(Q x)^-1 * _]mulrC divfK ?lt0r_neq0.
  rewrite le_eqVlt.
  apply/orP; left; apply/eqP.
  ring.
Qed.

Lemma sum_muB {T : choiceType} (P Q : {distr T / R}) :
  dweight P = 1 ->
  dweight Q = 1 ->
  sum (fun x : T => P x - Q x) = 0.
Proof.
move=> HP HQ.
rewrite (eq_sum (F2 := P \+ (fun x => - Q x))); last by move=> x.
rewrite sumD.
- rewrite sumN.
  rewrite -!psum_sum; try exact: ge0_mu.
  rewrite -!pr_predT HP HQ.
  ring.
- exact: summable_mu.
- exact: summableN; exact: summable_mu.
Qed.

Lemma chi2_summand_nonneg {T : choiceType} (P Q : {distr T / R}) x :
  absolute_continuous P Q ->
  0 <= Q x * ((P x / Q x - 1)^2 / (P x / Q x + 1)).
Proof.
move=> Hac.
have Hden : 0 < P x / Q x + 1.
  case HQx0: (Q x == 0).
  - have HPx0 : P x = 0 by exact: Hac x (eqP HQx0).
    by rewrite (eqP HQx0) HPx0 invr0 !mul0r add0r ltr01.
  - have HQx_pos : 0 < Q x by rewrite lt_def ge0_mu HQx0.
    have Hratio : 0 <= P x / Q x by rewrite divr_ge0 ?ge0_mu ?ltW.
    lra.
apply: mulr_ge0; first exact: ge0_mu.
apply: divr_ge0; first exact: sqr_ge0.
exact: ltW Hden.
Qed.

Lemma chi2_summand_le_mass {T : choiceType} (P Q : {distr T / R}) x :
  absolute_continuous P Q ->
  Q x * ((P x / Q x - 1)^2 / (P x / Q x + 1)) <= P x + Q x.
Proof.
move=> Hac.
case HQx0: (Q x == 0).
- have HPx0 : P x = 0 by exact: Hac x (eqP HQx0).
  by rewrite (eqP HQx0) HPx0 invr0 !mul0r addr0 lexx.
- have HQx_pos : 0 < Q x by rewrite lt_def ge0_mu HQx0.
  have Hratio_nonneg : 0 <= P x / Q x by rewrite divr_ge0 ?ge0_mu ?ltW.
  have Hden_pos : 0 < P x / Q x + 1 by lra.
  have Hfrac : (P x / Q x - 1)^2 / (P x / Q x + 1) <=
      P x / Q x + 1.
    rewrite (@ler_pdivrMr R (P x / Q x + 1)
      (P x / Q x + 1) ((P x / Q x - 1)^2) Hden_pos).
    lra.
  have Hscaled := ler_wpM2l (ltW HQx_pos) Hfrac.
  apply: (le_trans Hscaled).
  rewrite mulrDr.
  rewrite [Q x * (P x / Q x)]mulrC divfK ?lt0r_neq0 //.
  by rewrite mulr1 lexx.
Qed.

Lemma chi2_summable {T : choiceType} (P Q : {distr T / R}) :
  absolute_continuous P Q ->
  summable (fun x : T =>
    Q x * ((P x / Q x - 1)^2 / (P x / Q x + 1))).
Proof.
move=> Hac.
apply: le_summable.
- move=> x; apply/andP; split.
  + exact: chi2_summand_nonneg.
  + exact: chi2_summand_le_mass.
- apply: (eq_summable (S1 := P \+ Q)).
    by move=> x.
  exact: summableD; exact: summable_mu.
Qed.

Lemma kl_lower_bound_chi2 {T : choiceType} (P Q : {distr T / R}) :
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  δ_KL P Q >=
    sum (fun x : T =>
      Q x * ((P x / Q x - 1)^2 / (P x / Q x + 1))).
Admitted.

Lemma chi2_sum_nonneg {T : choiceType} (P Q : {distr T / R}) :
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  0 <=
    sum (fun x : T =>
      Q x * ((P x / Q x - 1)^2 / (P x / Q x + 1))).
Proof.
move=> Hac _ _.
rewrite -psum_sum; last by move=> x; exact: chi2_summand_nonneg.
exact: ge0_psum.
Qed.

Lemma divide_by_two_le (a b : R) :
  a <= b ->
  a / 2 <= b / 2.
Proof. by lra. Qed.

Lemma divide_by_two_nonneg (a : R) :
  0 <= a ->
  0 <= a / 2.
Proof. by lra. Qed.

Lemma sqrt_monotone_nonneg (a b : R) :
  0 <= a ->
  0 <= b ->
  a <= b ->
  Num.sqrt a <= Num.sqrt b.
Proof.
move=> Ha Hb Hab.
exact: ler_wsqrtr.
Qed.

Lemma total_variation_chi2_bound {T : choiceType} (P Q : {distr T / R}) :
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  total_variation P Q <=
    Num.sqrt (
      sum (fun x : T =>
        Q x * ((P x / Q x - 1)^2 / (P x / Q x + 1))) / 2).
Admitted.

Lemma pinsker {T : choiceType} (P Q : {distr T / R}) :
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  total_variation P Q <= Num.sqrt (δ_KL P Q / 2).
Proof.
move=> Hac HP HQ.
have Hchi :
    sum (fun x : T =>
      Q x * ((P x / Q x - 1)^2 / (P x / Q x + 1))) <=
    δ_KL P Q :=
  kl_lower_bound_chi2 P Q Hac HP HQ.
have Htv :
    total_variation P Q <=
      Num.sqrt (
        sum (fun x : T =>
          Q x * ((P x / Q x - 1)^2 / (P x / Q x + 1))) / 2) :=
  total_variation_chi2_bound P Q Hac HP HQ.
have Hchi2 :
    sum (fun x : T =>
      Q x * ((P x / Q x - 1)^2 / (P x / Q x + 1))) / 2 <=
    δ_KL P Q / 2 :=
  divide_by_two_le _ _ Hchi.
have Hsum_nonneg :
    0 <=
      sum (fun x : T =>
        Q x * ((P x / Q x - 1)^2 / (P x / Q x + 1))) / 2 :=
  divide_by_two_nonneg _ (chi2_sum_nonneg P Q Hac HP HQ).
have Hkl_nonneg : 0 <= δ_KL P Q / 2 :=
  divide_by_two_nonneg _ (kl_nonnegative P Q Hac HP).
apply: (le_trans Htv).
apply: sqrt_monotone_nonneg.
- exact: Hsum_nonneg.
- exact: Hkl_nonneg.
- exact: Hchi2.
Qed.

End KL_Pinsker.
