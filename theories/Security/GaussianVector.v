Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".
From extructures Require Import ord fset fmap.
From SSProve Require Import Axioms pkg_core_definition Package Prelude.
From SSProve Require Import Adv NominalPrelude choice_type.
From Mending Require Import ChoiceVector SspDG.

Import PackageNotation.
Local Open Scope package_scope.
Local Open Scope ring_scope.

(**
Parameter n_dg' : forall (n : nat), R -> distr R (chVec 'int n).
Definition add_chIntVec {n : nat} (v1 v2 : chVec 'int n) := v1.
Parameter dg' : 'int -> R -> distr R 'int.
*)

Definition sample_gaussian_vector
    (dims: nat)
    (stdev : R)
    (center : chVec 'int dims)
    : code emptym [interface] (chVec 'int dims) :=
  {code
    res <$ (chVec 'int dims; discrete_gaussians center stdev) ;;
    ret res
  }.

Fixpoint iterative_sample_gaussian_vector
    (dims: nat)
    (stdev : R)
    : chVec 'int dims -> code emptym [interface] (chVec 'int dims) :=
  match dims with
  | 0 => fun _ => {code ret tt}
  | S i => fun center =>
  let '(h, b) := center in
  {code
    xs ← iterative_sample_gaussian_vector i stdev b ;;
    x <$ ('int; ssp_dg h stdev) ;;
    ret (x, xs)
  }
  end.

Lemma iterative_sample_gaussian_vector_correct d s c :
  let prog := sample_gaussian_vector d s c in
  let prog' := iterative_sample_gaussian_vector d s c in
  ⊢ ⦃ fun '(s₀, s₁) => s₀ = s₁ ⦄  prog  ≈  prog'  ⦃ eq ⦄.
Proof. Admitted.

(* TODO two iterative samples are Pythagoean-close if their centers are *)
