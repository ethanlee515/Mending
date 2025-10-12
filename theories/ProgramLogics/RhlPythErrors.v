(* RHL with Pythagorean Errors *)

From Stdlib Require Import Unicode.Utf8.
From Stdlib Require Import List.
(* Require Import Stdlib.Vectors.Vector. *)
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import reals distr.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Crypt Require Import ChoiceAsOrd Couplings StateTransformingLaxMorph.
From SSProve.Crypt Require Import Axioms StateTransfThetaDens.
From SSProve Require Import FreeProbProg.
From SSProve.Crypt Require Import choice_type SubDistr.
From SSProve Require Import pkg_core_definition pkg_advantage.
From Mending Require Import KL.
From Mending Require Import RhlAe.
From Mending Require Import DistrExtras.

Import ListNotations.
Import pkg_heap.
Local Open Scope list_scope.
Local Open Scope ring_scope.

Arguments retrFree {_ _ _} _.
Arguments bindrFree {_ _ _ _} _ _.
Arguments callrFree {_ _ } _.

Fixpoint sum_squares (lst : list R) :=
  match lst with
  | [] => 0
  | head :: tail => head * head + sum_squares tail
  end.

Definition l2_norm (eps_lst : list R) := Num.sqrt (sum_squares eps_lst).

From Stdlib Require Import Lia.
From mathcomp Require Import lra.

Program Definition lift_i {ℓ : nat} {t : 'I_(ℓ.+1)} (i : 'I_t) : 'I_(ℓ.+1) :=
  widen_ord _ i.
Next Obligation.
move => ℓ t i.
have ?: (t < ℓ.+1)%N by apply ltn_ord.
lia.
Defined.

Definition pythJudgment
  {ℓ : nat}
  {outs_t : 'I_ℓ.+1 -> choiceType}
  {prod_out_t : choiceType}
  {marginal : forall (i : 'I_ℓ.+1), prod_out_t -> (outs_t i * heap_choiceType)}
  {inL_t inR_t : ord_choiceType}
  (progL : inL_t -> raw_code (outs_t ord_max))
  (progR : inR_t -> raw_code (outs_t ord_max))
  (pre : pred ((inL_t * heap_choiceType) * (inR_t * heap_choiceType)))
  (post : pred (outs_t ord_max * heap_choiceType))
  (s : (ℓ.+1).-tuple R) :=
  ∀ memL memR xL xR, pre ((xL, memL), (xR, memR)) →
  exists (P Q : {distr prod_out_t / R}),
  let outL := Pr_code (progL xL) memL in
  let outR := Pr_code (progR xR) memR in
  (* Marginals match *)
  dmargin (marginal ord_max) P =1 outL /\
  dmargin (marginal ord_max) Q =1 outR /\
  (* KL closeness *)
  (forall (t : 'I_ℓ.+1) (a : forall (i : 'I_t), outs_t (lift_i i)),
  let Pa := P in
  let Qa := Q in
  δ_KL (dmargin (marginal t) Pa) (dmargin (marginal t) Qa) < tnth s t) /\
  (* post-condition satisfied *)
  forall x, x \in dinsupp outL -> post x.

Declare Scope pyth_scope.
Local Open Scope pyth_scope.

Notation "⊨Pyth ⦃ pre ⦄ progL ≈( s ) progR ⦃ post ⦄" :=
  (pythJudgment progL progR pre post s) : pyth_scope.

(**
    @FrStP mem_t out_t → @FrStP mem_t out_t → list R → Prop :=
Inductive equiv_with_pythagorean_errors :
  ∀ (out_t : ord_choiceType) (mem_t : choiceType),
    @FrStP mem_t out_t → @FrStP mem_t out_t → list R → Prop :=
| pyth_ret_eq {out_t : ord_choiceType} (mem_t : choiceType) (v : out_t) :
    equiv_with_pythagorean_errors out_t mem_t (retrFree v) (retrFree v) []
| pyth_same_op {supp_t : choice_type} (mem_t : choiceType)
  (P : {distr supp_t / R}) :
  equiv_with_pythagorean_errors _ mem_t
    (callrFree (samplee (existT _ supp_t P)))
    (callrFree (samplee (existT _ supp_t P))) [ ]
| pyth_eps_samp {supp_t : choice_type} (mem_t : choiceType)
    (P Q : {distr supp_t / R}) (ε : R) :
  δ_KL P Q < ε →
  equiv_with_pythagorean_errors _ mem_t
    (callrFree (samplee (existT _ supp_t P)))
    (callrFree (samplee (existT _ supp_t Q))) [ ε ]
| pyth_bind_eq (mem_t: choiceType) (outA_t outB_t : ord_choiceType)
    (progA_L progA_R : @FrStP mem_t outA_t) (progB_L progB_R : outA_t → @FrStP mem_t outB_t)
    (ε_L ε_R : list R) :
  equiv_with_pythagorean_errors outA_t mem_t progA_L progA_R ε_L →
  (∀ a, equiv_with_pythagorean_errors outB_t mem_t (progB_L a) (progB_R a) ε_R) →
  equiv_with_pythagorean_errors outB_t mem_t
    (bindrFree progA_L progB_L) (bindrFree progA_R progB_R) (ε_L ++ ε_R).


Local Open Scope UtbNotations.

Theorem mw18 (out_t : ord_choiceType) (mem_t : choiceType)
  (progL progR : @FrStP mem_t out_t) (eps_lst : list R) :
  equiv_with_pythagorean_errors out_t mem_t progL progR eps_lst →
  equiv_with_additive_error progL progR
  (fun mems => match mems with (mL, mR) => mL == mR end)
  (fun results => match results with (resL, resR) => resL == resR end)
  (l2_norm eps_lst).
Admitted.
*)
