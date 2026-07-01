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

Lemma hoareBindRule
  {in_t mid_t out_t : ord_choiceType}
  (pre : pred (in_t * heap))
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (prog : in_t -> raw_code mid_t)
  (cont : mid_t -> raw_code out_t) :
  ⊨Hoare ⦃ pre ⦄ prog ⦃ mid ⦄ ->
  ⊨Hoare ⦃ mid ⦄ cont ⦃ post ⦄ ->
  ⊨Hoare ⦃ pre ⦄ (fun x => y ← prog x ;; cont y) ⦃ post ⦄.
Proof.
rewrite /hoareJudgment=> Hprog Hcont x mem Hpre out Hout.
rewrite Pr_code_bind in Hout.
have [mid_out Hmid Hinner] := @dinsupp_dlet R _ _ _ _ _ Hout.
case: mid_out Hmid Hinner=> y mem' Hmid Hinner.
exact: (Hcont y mem' (Hprog x mem Hpre (y, mem') Hmid) out Hinner).
Qed.

Lemma hoareGetRule
  {in_t out_t : ord_choiceType}
  (l : Location)
  (pre : pred (in_t * heap))
  (post : pred (out_t * heap))
  (cont : in_t -> l -> raw_code out_t) :
  (forall x v mem,
    pre (x, mem) ->
    v = get_heap mem l ->
    forall out, out \in dinsupp (Pr_code (cont x v) mem) -> post out) ->
  ⊨Hoare ⦃ pre ⦄ (fun x => v ← get l ;; cont x v) ⦃ post ⦄.
Proof.
rewrite /hoareJudgment=> Hcont x mem Hpre out Hout.
rewrite Pr_code_get in Hout.
exact: (Hcont x (get_heap mem l) mem Hpre erefl out Hout).
Qed.

Lemma hoarePutRule
  {in_t out_t : ord_choiceType}
  (l : Location)
  (v : l)
  (pre : pred (in_t * heap))
  (post : pred (out_t * heap))
  (cont : in_t -> raw_code out_t) :
  (forall x mem,
    pre (x, mem) ->
    forall out,
      out \in dinsupp (Pr_code (cont x) (set_heap mem l v)) -> post out) ->
  ⊨Hoare ⦃ pre ⦄ (fun x => #put l := v ;; cont x) ⦃ post ⦄.
Proof.
rewrite /hoareJudgment=> Hcont x mem Hpre out Hout.
rewrite Pr_code_put in Hout.
exact: (Hcont x mem Hpre out Hout).
Qed.

Lemma hoareSampleRule
  {in_t out_t : ord_choiceType}
  (op : Op)
  (pre : pred (in_t * heap))
  (post : pred (out_t * heap))
  (cont : in_t -> Arit op -> raw_code out_t) :
  (forall x sample mem,
    pre (x, mem) ->
    sample \in dinsupp (projT2 op) ->
    forall out, out \in dinsupp (Pr_code (cont x sample) mem) ->
      post out) ->
  ⊨Hoare ⦃ pre ⦄ (fun x => sample ← sample op ;; cont x sample) ⦃ post ⦄.
Proof.
rewrite /hoareJudgment=> Hcont x mem Hpre out Hout.
rewrite Pr_code_sample in Hout.
have [sample Hsample Hinner] := @dinsupp_dlet R _ _ _ _ _ Hout.
exact: (Hcont x sample mem Hpre Hsample out Hinner).
Qed.
