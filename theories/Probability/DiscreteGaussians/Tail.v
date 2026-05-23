From Stdlib Require Import Utf8 Lia.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq choice bigop order all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp Require Import reals realsum exp sequences realseq distr.
Set Warnings "-notation-incompatible-prefix".
From mathcomp Require Import xfinmap.
Set Warnings "notation-incompatible-prefix".
From mathcomp Require Import lra.
Import GRing.Theory Num.Theory Order.Theory.

From Mending.Probability Require Import DiscreteGaussian DiscreteGaussianKL.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras.

Local Open Scope ring_scope.

Section DiscreteGaussianTail.

Context {R : realType}.

Definition discrete_gaussian_tail_event (center : int) (k : nat) : pred int :=
  [pred x | (k <= absz (x - center))%N].

Definition mirrored_geometric_tail (s : R) (k : nat) : R :=
  psum (fun x : int => (k <= absz x)%:R * geom_above s (absz x)).

Lemma gaussian_weight_ge1 (s : R) :
  s > 0 -> 1 <= sum (gaussian s).
Proof.
move=> gt0_s.
rewrite -psum_sum; last exact: ge0_gaussian.
have H := ger1_psum (S := gaussian s) 0 (summable_gaussian s gt0_s).
rewrite /gaussian /= in H.
have g0 : (0%:~R / s) ^ 2 = 0 :> R by lra.
rewrite g0 oppr0 mul0r expR0 normr1 in H.
exact: H.
Qed.

Lemma centered_discrete_gaussian_le_geom (s : R) (x : int) :
  s > 0 ->
  centered_discrete_gaussian s x <= geom_above s (absz x).
Proof.
move=> gt0_s.
rewrite centered_discrete_gaussianE // gaussian_pdfE //.
have ge1_sum : 1 <= sum (gaussian s) by exact: gaussian_weight_ge1.
have gt0_sum : 0 < sum (gaussian s) by exact: gt0_weight_gaussian.
apply: le_trans (le_gauss_geo s x gt0_s).
rewrite ler_pdivrMr //.
rewrite -[leLHS]mulr1.
apply: ler_wpM2l; first exact: ge0_gaussian.
exact: ge1_sum.
Qed.

Lemma summable_mirrored_geometric_tail (s : R) (k : nat) :
  s > 0 ->
  summable (fun x : int => (k <= absz x)%:R * geom_above s (absz x)).
Proof.
move=> gt0_s.
apply: (mirror_summable (fun n : nat => (k <= n)%:R * geom_above s n)).
apply: (le_summable (F2 := geom_above s)).
- move=> n; apply/andP; split.
  + rewrite mulr_ge0 ?ler0n //.
    rewrite /geom_above.
    apply: ge0_geo.
    rewrite /max_step_ratio; exact: expR_ge0.
  case: (k <= n)%N; first by rewrite mul1r.
  rewrite mul0r.
  rewrite /geom_above.
  apply: ge0_geo.
  rewrite /max_step_ratio; exact: expR_ge0.
rewrite /geom_above.
apply: summable_geo.
rewrite /max_step_ratio /=.
apply/andP; split; first exact: expR_ge0.
rewrite expR_lt1.
suff: (1 / s) ^ 2 > 0 by lra.
rewrite /exprz /= expr2.
have H : 1 / s > 0 by exact: divr_gt0.
exact: mulr_gt0.
Qed.

Lemma centered_discrete_gaussian_tail_bound (s : R) (k : nat) :
  s > 0 ->
  \P_[centered_discrete_gaussian s] [pred x | (k <= absz x)%N] <=
    mirrored_geometric_tail s k.
Proof.
move=> gt0_s.
rewrite /mirrored_geometric_tail /pr.
apply: le_psum; last exact: summable_mirrored_geometric_tail.
move=> x; apply/andP; split.
- by rewrite mulr_ge0 ?ler0n ?ge0_mu.
- case Htail: (k <= absz x)%N.
  + rewrite /= Htail !mul1r.
    exact: (centered_discrete_gaussian_le_geom s x gt0_s).
  by rewrite /= Htail !mul0r.
Qed.

Lemma discrete_gaussian_tail_bound (center : int) (s : R) (k : nat) :
  s > 0 ->
  \P_[discrete_gaussian center s] (discrete_gaussian_tail_event center k) <=
    mirrored_geometric_tail s k.
Proof.
move=> gt0_s.
rewrite /discrete_gaussian_tail_event.
rewrite -(pr_dmargin [pred x | (k <= absz x)%N]
  (fun x : int => x - center) (discrete_gaussian center s)).
rewrite /mirrored_geometric_tail /pr.
apply: le_psum; last exact: summable_mirrored_geometric_tail.
move=> x; apply/andP; split.
- by rewrite mulr_ge0 ?ler0n ?ge0_mu.
- rewrite (discrete_gaussian_translate center s gt0_s x).
  case Htail: (k <= absz x)%N.
  + rewrite /= Htail !mul1r.
    exact: (centered_discrete_gaussian_le_geom s x gt0_s).
  by rewrite /= Htail !mul0r.
Qed.

End DiscreteGaussianTail.
