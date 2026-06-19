Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra all_reals distr.
From mathcomp Require Import realseq realsum exp lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

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
pose F := fun x : T =>
  Q x * ((P x / Q x - 1)^2 / (P x / Q x + 1)).
have Hden x : 0 < P x / Q x + 1.
  case HQx0: (Q x == 0).
  - have HPx0 : P x = 0 by exact: Hac x (eqP HQx0).
    by rewrite (eqP HQx0) HPx0 invr0 !mul0r add0r ltr01.
  - have HQx_pos : 0 < Q x by rewrite lt_def ge0_mu HQx0.
    have Hratio : 0 <= P x / Q x by rewrite divr_ge0 ?ge0_mu ?ltW.
    lra.
have HF_nonneg x : 0 <= F x.
  rewrite /F.
  apply: mulr_ge0; first exact: ge0_mu.
  apply: divr_ge0.
  - exact: sqr_ge0.
  - exact: ltW (Hden x).
rewrite -psum_sum; last exact: HF_nonneg.
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
