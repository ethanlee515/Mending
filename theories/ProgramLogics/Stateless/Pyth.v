(* Stateless rFreePr RHL with Pythagorean errors. *)

Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import reals distr.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Crypt Require Import Axioms FreeProbProg Theta_dens.

From Mending.MathcompExtras Require Import DistrExtras.
From Mending.ProgramLogics.Distribution Require Import Pyth.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

Section PythagoreanStatelessJudgments.

Definition rFreePr_distr {A : choiceType} (c : rFreePr A) : {distr A / R} :=
  Theta_dens.unary_ThetaDens0 A c.

Definition pythFreeCoord
    {n : nat} {Ω : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i)
    (progL progR : rFreePr Ω) (eps : n.-tuple R) : Prop :=
  pythDist coord (rFreePr_distr progL) (rFreePr_distr progR) eps.

Lemma pythFreeCoord_total_variation
    {n : nat} {Ω : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i)
    (progL progR : rFreePr Ω) (eps : n.-tuple R) :
  pythFreeCoord coord progL progR eps ->
  total_variation (rFreePr_distr progL) (rFreePr_distr progR) <=
    Num.sqrt ((\sum_(i < n) tnth eps i) / 2).
Proof.
exact: pythDist_total_variation.
Qed.


Definition pythFree
    {ℓ : nat}
    {inL_t inR_t out_t : choiceType}
    (progL : inL_t -> rFreePr out_t)
    (progR : inR_t -> rFreePr out_t)
    (pre : pred (inL_t * inR_t))
    (post : pred out_t)
    (s : (ℓ.+1).-tuple R) : Prop :=
  forall xL xR, pre (xL, xR) ->
  exists
  (Ω : choiceType)
  (X : 'I_ℓ -> choiceType)
  (coord : forall i : 'I_ℓ, Ω -> X i)
  (final : Ω -> out_t)
  (P Q : {distr Ω / R}),
  let outL := rFreePr_distr (progL xL) in
  let outR := rFreePr_distr (progR xR) in
  pythDistWithFinal coord final P Q s /\
  dmargin final P =1 outL /\
  dmargin final Q =1 outR /\
  (forall x, x \in dinsupp outL -> post x) /\
  (forall x, x \in dinsupp outR -> post x).

End PythagoreanStatelessJudgments.
