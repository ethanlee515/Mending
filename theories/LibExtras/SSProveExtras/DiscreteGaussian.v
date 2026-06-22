(* Glue code that converts Discrete Gaussian into SSProve int types *)

From Stdlib Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot all_order all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp Require Import distr.
From SSProve Require Import Axioms choice_type Package.
From Mending.Probability.DiscreteGaussians Require Import DiscreteGaussian.
Import ssrZ.
Import PackageNotation.
Local Open Scope package_scope.

From Mending.LibExtras.SSProveExtras Require Import ChoiceVector.
From mathcomp Require Import reals.
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

Lemma ssp_dg_absolute_continuous (m1 m2 : 'int) (s : R) :
  0 < s ->
  absolute_continuous (ssp_dg m1 s) (ssp_dg m2 s).
Admitted.

Lemma ssp_dg_finite_kl (m1 m2 : 'int) (s : R) :
  0 < s ->
  finite_kl (ssp_dg m1 s) (ssp_dg m2 s).
Admitted.

Lemma kl_ssp_dg (m1 m2 : 'int) (s : R) :
  0 < s ->
  δ_KL (ssp_dg m1 s) (ssp_dg m2 s) <=
    ((int_of_Z m2 - int_of_Z m1)%:~R) ^+ 2 / (2 * s ^ 2).
Admitted.

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
