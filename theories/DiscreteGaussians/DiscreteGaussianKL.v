From Stdlib Require Import Utf8 Lia.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice bigop order all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp Require Import reals realsum exp sequences realseq distr.
Set Warnings "-notation-incompatible-prefix".
From mathcomp Require Import xfinmap.
Set Warnings "notation-incompatible-prefix".
From mathcomp Require Import lra.
From mathcomp.algebra_tactics Require Import ring.
Import GRing.Theory Num.Theory Order.Theory.

From Mending Require Import DiscreteGaussian DiscreteGaussianMoment KL.
From Mending Require Import RealSumExtras DistrExtras.
From Mending Require Import KL.

Local Open Scope ring_scope.

(** A top-down sketch of the integer-centered KL proof. *)

Section IntegerCenteredKL.

Context (R : realType).

Definition centered_difference (center : int) : int -> R :=
  fun x => (x - center)%:~R.

Definition quadratic_gap (mu nu : int) (x : int) : R :=
  (((x - nu)%:~R) ^+ 2 - ((x - mu)%:~R) ^+ 2).

(** First layer: expose the concrete mass functions. *)

Lemma gaussian_pdfE s x :
  s > 0 ->
  gaussian_pdf R s x = gaussian R s x / sum (gaussian R s).
Proof.
move=> gt0_s.
by rewrite /gaussian_pdf ifT.
Qed.

Lemma centered_discrete_gaussianE s x :
  s > 0 ->
  centered_discrete_gaussian R s x = gaussian_pdf R s x.
Proof.
by [].
Qed.

Lemma discrete_gaussianE center s x :
  s > 0 ->
  discrete_gaussian R center s x =
    gaussian_pdf R s (x - center).
Proof.
move=> gt0_s.
by rewrite /discrete_gaussian dmargin_add_intE centered_discrete_gaussianE.
Qed.

(** Second layer: the integer-shift facts replacing Poisson summation. *)

Lemma gaussian_opp s x :
  gaussian R s (- x) = gaussian R s x.
Proof.
rewrite /gaussian.
congr expR.
rewrite rmorphN.
lra.
Qed.

Lemma gaussian_weight_shift_int center s :
  sum (fun x : int => gaussian R s (x - center)) =
  sum (gaussian R s).
Proof.
exact: (sum_shift_sub_int R (gaussian R s) center).
Qed.

Lemma discrete_gaussian_translate center s :
  s > 0 ->
  dmargin (fun x => x - center) (discrete_gaussian R center s) =1
  centered_discrete_gaussian R s.
Proof.
move=> gt0_s x.
rewrite dmargin_sub_intE discrete_gaussianE //.
have ->: x + center - center = x by ring.
by rewrite centered_discrete_gaussianE.
Qed.

(** Third layer: symmetry gives the one expectation needed by the KL proof. *)

Lemma centered_discrete_gaussian_opp s x :
  s > 0 ->
  centered_discrete_gaussian R s (- x) =
  centered_discrete_gaussian R s x.
Proof.
move=> gt0_s.
rewrite !centered_discrete_gaussianE // !gaussian_pdfE //.
by rewrite gaussian_opp.
Qed.

Lemma centered_discrete_gaussian_mean0 s :
  s > 0 ->
  \E_[centered_discrete_gaussian R s] (fun x => x%:~R) = 0.
Proof.
move=> gt0_s.
rewrite /esp.
set F := fun x : int => x%:~R * centered_discrete_gaussian R s x.
have odd_F x : F (- x) = - F x.
  rewrite /F rmorphN centered_discrete_gaussian_opp //.
  lra.
have H : sum F = - sum F.
  rewrite -sumN.
  rewrite -(sum_opp_int R F).
  by apply/eq_sum=> x.
lra.
Qed.

Lemma discrete_gaussian_centered_difference_mean0 center s :
  s > 0 ->
  \E_[discrete_gaussian R center s] (centered_difference center) = 0.
Proof.
move=> gt0_s.
rewrite -[RHS](centered_discrete_gaussian_mean0 s gt0_s).
Locate expectation_dmargin_sub_int.
rewrite -[LHS](expectation_dmargin_sub_int center
  (discrete_gaussian R center s) (fun x => x%:~R)).
apply: expectation_distr_ext.
exact: discrete_gaussian_translate.
Qed.

Lemma centered_discrete_gaussian_mass1 s :
  s > 0 ->
  dweight (centered_discrete_gaussian R s) = 1.
Proof.
move=> gt0_s.
rewrite pr_predT psum_sum; last exact: ge0_mu.
rewrite (eq_sum (F2 := fun x => (1 / sum (gaussian R s)) * gaussian R s x)).
- rewrite sumZ.
  have gt0_sum : 0 < sum (gaussian R s) by exact: gt0_weight_gaussian.
  by rewrite mul1r mulVf //; apply/eqP; lra.
move=> x.
rewrite centered_discrete_gaussianE // gaussian_pdfE //.
lra.
Qed.

Lemma discrete_gaussian_mass1 center s :
  s > 0 ->
  dweight (discrete_gaussian R center s) = 1.
Proof.
move=> gt0_s.
rewrite /discrete_gaussian dmargin_dweight.
exact: centered_discrete_gaussian_mass1.
Qed.

(** Fourth layer: pointwise logarithm algebra for equal-variance Gaussians. *)

Lemma ln_discrete_gaussian_ratio mu nu s x :
  s > 0 ->
  ln ((discrete_gaussian R mu s x) / (discrete_gaussian R nu s x)) =
    quadratic_gap mu nu x / (2 * s ^ 2).
Proof.
move=> gt0_s.
rewrite !discrete_gaussianE // !gaussian_pdfE //.
have gt0_sum : 0 < sum (gaussian R s) by exact: gt0_weight_gaussian.
have gt0_g_mu : 0 < gaussian R s (x - mu) by rewrite /gaussian; exact: expR_gt0.
have gt0_g_nu : 0 < gaussian R s (x - nu) by rewrite /gaussian; exact: expR_gt0.
have -> :
    gaussian R s (x - mu) / sum (gaussian R s) /
      (gaussian R s (x - nu) / sum (gaussian R s)) =
    gaussian R s (x - mu) / gaussian R s (x - nu).
- field.
  by apply/andP; split; apply/eqP; lra.
rewrite ln_div ?gt0_g_mu ?gt0_g_nu //.
rewrite /gaussian !expRK /quadratic_gap !rmorphB /=.
lra.
Qed.

Lemma quadratic_gap_centered mu nu x :
  quadratic_gap mu nu x =
    ((mu - nu)%:~R) ^+ 2 + 2 * (x - mu)%:~R * (mu - nu)%:~R.
Proof.
rewrite /quadratic_gap !rmorphB /=.
lra.
Qed.

(** Main theorem: the direct integer-centered KL calculation. *)

Theorem kl_discrete_gaussian_integer_centered mu nu s :
  s > 0 ->
  kl_divergence (discrete_gaussian R mu s) (discrete_gaussian R nu s) =
    ((nu - mu)%:~R) ^+ 2 / (2 * s ^ 2).
Proof.
move=> gt0_s.
rewrite /kl_divergence.
rewrite (expectation_ext (discrete_gaussian R mu s)
  (fun x => ln (discrete_gaussian R mu s x / discrete_gaussian R nu s x))
  (fun x => quadratic_gap mu nu x / (2 * s ^ 2))); last first.
- by move=> x; rewrite ln_discrete_gaussian_ratio.
rewrite (expectation_ext (discrete_gaussian R mu s)
  (fun x => quadratic_gap mu nu x / (2 * s ^ 2))
  (fun x =>
     (((mu - nu)%:~R) ^+ 2 + 2 * (x - mu)%:~R * (mu - nu)%:~R) /
       (2 * s ^ 2))); last first.
- by move=> x; rewrite quadratic_gap_centered.
rewrite (expectation_ext (discrete_gaussian R mu s)
  (fun x =>
     (((mu - nu)%:~R) ^+ 2 + 2 * (x - mu)%:~R * (mu - nu)%:~R) /
       (2 * s ^ 2))
  (fun x =>
     (1 / (2 * s ^ 2)) * ((mu - nu)%:~R) ^+ 2 +
     ((1 / (2 * s ^ 2)) * 2 * (mu - nu)%:~R) *
       centered_difference mu x)); last first.
- move=> x.
  rewrite /centered_difference.
  lra.
rewrite expectation_add; last first.
- apply: has_expZ.
  rewrite /centered_difference.
  exact: discrete_gaussian_centered_difference_has_exp.
- exact: has_expC.
rewrite expectation_const; last first.
- exact: discrete_gaussian_mass1.
rewrite expectation_scale.
rewrite discrete_gaussian_centered_difference_mean0 //.
rewrite mulr0 addr0.
have -> : (nu - mu)%:~R = - (mu - nu)%:~R :> R.
- by rewrite !rmorphB /=; lra.
lra.
Qed.

Print Assumptions kl_discrete_gaussian_integer_centered.

End IntegerCenteredKL.
