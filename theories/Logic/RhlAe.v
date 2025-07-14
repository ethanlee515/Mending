From Stdlib Require Import Unicode.Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import reals distr.
From mathcomp Require Import realseq realsum exp.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Crypt Require Import ChoiceAsOrd Couplings StateTransformingLaxMorph.
From SSProve.Crypt Require Import Axioms StateTransfThetaDens.

Local Open Scope ring_scope.

Definition equiv_with_additive_error
    {outL_t outR_t : ord_choiceType}
    {memL_t memR_t : choiceType}
    (progL : @FrStP memL_t outL_t) (progR : @FrStP memR_t outR_t)
    (pre : pred (memL_t * memR_t))
    (post : pred ((outL_t * memL_t) * (outR_t * memR_t)))
    (ε : R) : Prop :=
  ∀ memL memR, pre (memL, memR) →
    let out1 := thetaFstd outL_t progL memL in
    let out2 := thetaFstd outR_t progR memR in
    ∃ d, coupling d out1 out2 ∧ \P_[ d ] post >= 1 - ε.

(* I'm sure this belongs somewhere else
 * and requires a bunch of other lemma *)
Definition statistical_distance {T : choiceType} (P Q : {distr T / R}) : R :=
  sum (fun x => `| P x - Q x |).

(* There is probably a stronger version of this...? *)
Lemma up_to_bad (out_t: ord_choiceType)
  {mem_t: choiceType}
  (progL : @FrStP mem_t out_t) (progR : @FrStP mem_t out_t)
  (pre : pred (mem_t * mem_t))
  (post : pred ((out_t * mem_t) * (out_t * mem_t)))
  (ε : R) :
  equiv_with_additive_error progL progR
    (fun mems => match mems with (mL, mR) => mL == mR end)
    (fun results => match results with (resL, resR) => resL == resR end)
    ε ->
  forall s,
    let out1 := thetaFstd out_t progL s in
    let out2 := thetaFstd out_t progR s in
    statistical_distance out1 out2 < ε.
Admitted.