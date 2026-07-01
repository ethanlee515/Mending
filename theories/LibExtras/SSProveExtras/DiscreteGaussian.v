(* Glue code that converts Discrete Gaussian into SSProve int types *)

From Stdlib Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot all_order all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp Require Import distr.
From SSProve Require Import Axioms choice_type Package.
From Mending.Probability.DiscreteGaussians Require Import DiscreteGaussian.
Import ssrZ.
Import GRing.Theory Num.Theory Order.Theory.
Import PackageNotation.
Local Open Scope package_scope.

From Mending.LibExtras.SSProveExtras Require Import ChoiceVector.
From mathcomp Require Import reals realsum.
From Mending.Probability.KL Require Import Core.
From Mending.Probability.DiscreteGaussians Require Import DiscreteGaussianKL.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras.

Definition ssp_dg (m : 'int) (s : R) : distr R 'int :=
  dmargin (U := 'int) Z_of_int (discrete_gaussian (int_of_Z m) s).

Lemma ssp_dg_mass1 (m : 'int) (s : R) :
  0 < s ->
  dweight (ssp_dg m s) = 1.
Proof.
move=> Hs.
rewrite /ssp_dg dmargin_dweight.
exact: discrete_gaussian_mass1.
Qed.

Lemma Z_of_int_injective : injective Z_of_int.
Proof.
move=> x y Hxy.
by rewrite -(Z_of_intK x) Hxy Z_of_intK.
Qed.

Lemma dmargin_int_of_Z_ssp_dg (m : 'int) (s : R) :
  dmargin (fun z : 'int => int_of_Z z) (ssp_dg m s) =1
    discrete_gaussian (int_of_Z m) s.
Proof.
move=> x.
rewrite /ssp_dg dmargin_psumE.
rewrite (@psum_finseq R 'int
  (fun z : 'int =>
     ((fun z' : 'int => int_of_Z z') z == x)%:R *
       dmargin (U := 'int) Z_of_int
         (discrete_gaussian (int_of_Z m) s) z)
  [:: (Z_of_int x : 'int)]).
- rewrite big_seq1 Z_of_intK eqxx mul1r ger0_norm ?ge0_mu.
  exact: (@dmargin_injectiveE R int 'int Z_of_int
    (discrete_gaussian (int_of_Z m) s) Z_of_int_injective x).
- by [].
- by [].
move=> z.
case Hzx : (int_of_Z z == x); last first.
  move=> H.
  move: H.
  by rewrite inE Hzx /= mul0r eqxx.
move=> _.
rewrite inE.
apply/eqP.
move/eqP: Hzx=> Hzx.
by rewrite -Hzx int_of_ZK.
Qed.

Lemma dmargin_int_of_Z_ssp_dg_centered (m : 'int) (s : R) :
  int_of_Z m = 0 ->
  dmargin (fun z : 'int => int_of_Z z) (ssp_dg m s) =1
    centered_discrete_gaussian s.
Proof.
move=> Hm z.
rewrite dmargin_int_of_Z_ssp_dg /discrete_gaussian Hm.
by rewrite dmargin_add_intE subr0.
Qed.

Lemma ssp_dg_finite_kl (m1 m2 : 'int) (s : R) :
  0 < s ->
  finite_kl (ssp_dg m1 s) (ssp_dg m2 s).
Proof.
move=> Hs.
rewrite /ssp_dg.
apply: finite_kl_dmargin_injective.
- exact: Z_of_int_injective.
exact: finite_kl_discrete_gaussian.
Qed.

Lemma ssp_dg_absolute_continuous (m1 m2 : 'int) (s : R) :
  0 < s ->
  absolute_continuous (ssp_dg m1 s) (ssp_dg m2 s).
Proof.
move=> Hs.
exact: (finite_kl_absolute_continuous _ _ (ssp_dg_finite_kl m1 m2 s Hs)).
Qed.

Lemma kl_ssp_dg (m1 m2 : 'int) (s : R) :
  0 < s ->
  δ_KL (ssp_dg m1 s) (ssp_dg m2 s) <=
    ((int_of_Z m2 - int_of_Z m1)%:~R) ^+ 2 / (2 * s ^ 2).
Proof.
move=> Hs.
rewrite /ssp_dg.
rewrite (@kl_dmargin_injective R int 'int Z_of_int
  (discrete_gaussian (int_of_Z m1) s)
  (discrete_gaussian (int_of_Z m2) s)).
- by rewrite kl_discrete_gaussian.
- exact: Z_of_int_injective.
- exact: finite_kl_discrete_gaussian.
Qed.

Fixpoint discrete_gaussians_aux {n : nat} (s : R)
  : chVec 'int n -> distr R (chVec 'int n) :=
  match n with
  | 0 => fun _ => dunit (T := chVec 'int 0) tt
  | S i => fun ms =>
    let '(mhead, mtail) := ms in
    let dg := discrete_gaussians_aux s mtail in
    \dlet_(x <- ssp_dg mhead s)
    \dlet_(xs <- dg)
    dunit (x, xs)
  end.

Definition discrete_gaussians {n : nat} (center : chVec 'int n) (s : R) :=
  discrete_gaussians_aux s center.

Lemma discrete_gaussians_mass1 {n : nat}
    (center : chVec 'int n) (s : R) :
  0 < s ->
  dweight (discrete_gaussians center s) = 1.
Proof.
elim: n center=> [|n IH] center Hs.
- by case: center; rewrite /discrete_gaussians /= dunit_dweight.
case: center=> h tail.
rewrite /discrete_gaussians /=.
rewrite dweight_dlet_sum.
rewrite (eq_psum
  (F2 := fun x : 'int => ssp_dg h s x * 1)); last first.
  move=> x.
  congr (_ * _).
  rewrite dweight_dlet_sum.
  rewrite (eq_psum
    (F2 := fun xs : chVec 'int n => discrete_gaussians_aux s tail xs * 1));
    last by move=> xs; rewrite dunit_dweight.
  rewrite (eq_psum (F2 := discrete_gaussians_aux s tail)); last
    by move=> xs; rewrite mulr1.
  by rewrite -pr_predT IH.
rewrite (eq_psum (F2 := ssp_dg h s)); last by move=> x; rewrite mulr1.
by rewrite -pr_predT ssp_dg_mass1.
Qed.
