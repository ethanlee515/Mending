From Stdlib Require Import Unicode.Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import reals distr.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Crypt Require Import ChoiceAsOrd Couplings StateTransformingLaxMorph.
From SSProve.Crypt Require Import Axioms StateTransfThetaDens.

Open Scope ring_scope.

Definition equiv_with_additive_error
    (A1 A2 : ord_choiceType)
    {S1 S2 : choiceType}
    (c1 : @FrStP S1 A1) (c2 : @FrStP S2 A2)
    (pre : pred (S1 * S2))
    (post : pred ((A1 * S1) * (A2 * S2)))
    (ε : R) : Prop :=
  ∀ s1 s2, pre (s1, s2) →
    let out1 := thetaFstd A1 c1 s1 in
    let out2 := thetaFstd A2 c2 s2 in
    ∃ d, coupling d out1 out2 ∧ \P_[ d ] post >= 1 - ε.
