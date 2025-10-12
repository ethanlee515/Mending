From Stdlib Require Import Unicode.Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import reals distr.
From mathcomp Require Import realseq realsum exp.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From Mending Require Import DistrExtras.
From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Crypt Require Import ChoiceAsOrd Couplings StateTransformingLaxMorph.
From SSProve.Crypt Require Import Axioms StateTransfThetaDens.
From SSProve Require Import pkg_core_definition pkg_advantage.

Local Open Scope ring_scope.

Import pkg_heap.

Definition upToBadJudgment
  {inL_t inR_t outL_t outR_t : ord_choiceType}
  (progL : inL_t -> raw_code outL_t)
  (progR : inR_t -> raw_code outR_t)
  (pre : pred ((inL_t * heap_choiceType) * (inR_t * heap_choiceType)))
  (post : pred ((outL_t * heap_choiceType) * (outR_t * heap_choiceType)))
  (ε : R) : Prop :=
  ∀ memL memR xL xR, pre ((xL, memL), (xR, memR)) →
    let out1 := Pr_code (progL xL) memL in
    let out2 := Pr_code (progR xR) memR in
    ∃ d, coupling d out1 out2 ∧ \P_[ d ] post >= 1 - ε.

Declare Scope UtbNotations.
Local Open Scope UtbNotations.

Notation "⊨UTB ⦃ pre ⦄ progL ≈( ε ) progR ⦃ post ⦄" :=
  (upToBadJudgment progL progR pre post ε) : UtbNotations.

(* I'm sure this belongs somewhere else
 * and requires a bunch of other lemma *)

(* There is probably a stronger version of this...? *)
(**
Lemma up_to_bad (out_t: ord_choiceType)
  {mem_t: choiceType}
  (progL : @FrStP mem_t out_t) (progR : @FrStP mem_t out_t)
  (ε : R) :
  equiv_with_additive_error progL progR
    (fun mems => match mems with (mL, mR) => mL == mR end)
    (fun results => match results with (resL, resR) => resL == resR end)
    ε ->
  ∀ s,
    let out1 := thetaFstd out_t progL s in
    let out2 := thetaFstd out_t progR s in
    statistical_distance out1 out2 < ε.
Admitted.
*)
