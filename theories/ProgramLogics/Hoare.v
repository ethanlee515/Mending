From Stdlib Require Import Unicode.Utf8.
From extructures Require Import ord fset fmap.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals distr ssrZ realseq realsum.
From mathcomp Require Import lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Crypt Require Import ChoiceAsOrd Couplings StateTransformingLaxMorph.
From SSProve.Crypt Require Import Axioms StateTransfThetaDens.
From SSProve.Crypt Require Import choice_type SubDistr.
From SSProve Require Import pkg_core_definition pkg_advantage pkg_notation.

Declare Scope HoareNotations.
Local Open Scope HoareNotations.

Import PackageNotation.
Import pkg_heap.
Local Open Scope package_scope.
Local Open Scope ring_scope.

Definition hoareJudgment
  {in_t out_t : ord_choiceType}
  (prog : in_t -> raw_code out_t)
  (pre : pred (in_t * heap))
  (post : pred (out_t * heap)) : Prop :=
  ∀ x mem, pre (x, mem) →
    let out := Pr_code (prog x) mem in
    (forall x, x \in dinsupp out -> post x).

Notation "⊨Hoare ⦃ pre ⦄ prog ⦃ post ⦄" :=
  (hoareJudgment prog pre post) : HoareNotations.
