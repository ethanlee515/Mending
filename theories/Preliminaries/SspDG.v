(* Glue code that converts Discrete Gaussian into SSProve int types *)

From Stdlib Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp Require Import distr.
From SSProve Require Import Axioms choice_type Package.
From Mending Require Import DiscreteGaussian.
Import ssrZ.
Import PackageNotation.
Local Open Scope package_scope.

From Mending Require Import ChoiceVector.
From mathcomp Require Import reals.

Definition ssp_dg (m : 'int) (s : R) : distr R 'int :=
  dmargin (U := 'int) Z_of_int (discrete_gaussian R (int_of_Z m) s).

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

