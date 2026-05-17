(* Distributional and stateless RHL with Pythagorean errors. *)

Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import reals distr.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Crypt Require Import Axioms FreeProbProg Theta_dens.

From Mending.KL Require Import KL.
From Mending Require Import DistrExtras.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

Section PythagoreanDistributionJudgments.

Definition pythDist
    {n : nat} {Ω : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i)
    (P Q : {distr Ω / R}) (eps : n.-tuple R) : Prop :=
  coordinates_separate coord /\
  (forall i : 'I_n, 0 <= tnth eps i) /\
  absolute_continuous P Q /\
  dweight P = 1 /\
  dweight Q = 1 /\
  forall (i : 'I_n) (a : forall j : 'I_n, X j),
    δ_KL (conditional_coordinate coord P i a)
         (conditional_coordinate coord Q i a) <= tnth eps i.

Lemma pythDist_total_variation
    {n : nat} {Ω : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i)
    (P Q : {distr Ω / R}) (eps : n.-tuple R) :
  pythDist coord P Q eps ->
  total_variation P Q <= Num.sqrt ((\sum_(i < n) tnth eps i) / 2).
Proof.
move=> [Hsep [Heps [Hac [HP [HQ Hcond]]]]].
exact: (pythagorean_probability_preservation coord P Q eps
          Hsep Heps Hac HP HQ Hcond).
Qed.


Definition rcons_choice {n : nat}
    (X : 'I_n -> choiceType) (A : choiceType)
    (i : 'I_n.+1) : choiceType :=
  if unlift ord_max i is Some j then X j else A.

Definition rcons_coord {n : nat} {Ω : choiceType}
    {X : 'I_n -> choiceType} {A : choiceType}
    (coord : forall i : 'I_n, Ω -> X i) (final : Ω -> A)
    (i : 'I_n.+1) : Ω -> rcons_choice X A i :=
  match unlift ord_max i as u return
      Ω -> (if u is Some j then X j else A) with
  | Some j => coord j
  | None => final
  end.

Definition pythDistWithFinal
    {n : nat} {Ω A : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i) (final : Ω -> A)
    (P Q : {distr Ω / R}) (eps : n.+1.-tuple R) : Prop :=
  pythDist (rcons_coord coord final) P Q eps.

Definition rFreePr_distr {A : choiceType} (c : rFreePr A) : {distr A / R} :=
  Theta_dens.unary_ThetaDens0 A c.

Definition pythFree
    {n : nat} {Ω : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i)
    (progL progR : rFreePr Ω) (eps : n.-tuple R) : Prop :=
  pythDist coord (rFreePr_distr progL) (rFreePr_distr progR) eps.

Lemma pythFree_total_variation
    {n : nat} {Ω : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i)
    (progL progR : rFreePr Ω) (eps : n.-tuple R) :
  pythFree coord progL progR eps ->
  total_variation (rFreePr_distr progL) (rFreePr_distr progR) <=
    Num.sqrt ((\sum_(i < n) tnth eps i) / 2).
Proof.
exact: pythDist_total_variation.
Qed.

End PythagoreanDistributionJudgments.
