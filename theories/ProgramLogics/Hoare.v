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
From SSProve.Crypt.nominal Require Import Pr.
From SSProve Require Import pkg_core_definition pkg_advantage pkg_distr
  pkg_notation.

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

Lemma hoareRetRule
  {in_t out_t : ord_choiceType}
  (pre : pred (in_t * heap))
  (post : pred (out_t * heap))
  (f : in_t -> out_t) :
  (forall x mem, pre (x, mem) -> post (f x, mem)) ->
  ⊨Hoare ⦃ pre ⦄ (fun x => ret (f x)) ⦃ post ⦄.
Proof.
rewrite /hoareJudgment=> Hpost x mem Hpre out Hout.
rewrite Pr_code_ret in Hout.
have -> : out = (f x, mem) by exact: in_dunit Hout.
exact: (Hpost x mem Hpre).
Qed.

Lemma dinsupp_assertD
  {out_t : choice_type} (b : bool)
  (cont : b = true -> raw_code out_t) mem out :
  out \in dinsupp (Pr_code (@assertD out_t b cont) mem) ->
  exists Hb : b = true,
    out \in dinsupp (Pr_code (cont Hb) mem).
Proof.
destruct b.
- rewrite /assertD /=.
  move=> Hout.
  by exists erefl.
- rewrite /assertD Pr_code_fail.
  move=> Hout.
  by move/dinsuppP: Hout; rewrite dnullE.
Qed.

Lemma Pr_code_bind_assertD
  {mid_t out_t : choice_type} (b : bool)
  (cont : b = true -> raw_code mid_t)
  (k : mid_t -> raw_code out_t) mem :
  Pr_code
    (x ← @assertD mid_t b cont ;;
     k x)
    mem =1
  Pr_code
    (@assertD out_t b (fun Hb =>
      x ← cont Hb ;;
      k x))
    mem.
Proof.
move=> out.
destruct b.
- by rewrite /assertD Pr_code_bind.
rewrite /assertD Pr_code_bind Pr_code_fail dlet_null_ext Pr_code_fail.
by [].
Qed.
