(* RHL with Pythagorean Errors *)

From Stdlib Require Import Unicode.Utf8.
From Stdlib Require Import List.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import reals distr.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Crypt Require Import ChoiceAsOrd Couplings StateTransformingLaxMorph.
From SSProve.Crypt Require Import Axioms StateTransfThetaDens.
From SSProve Require Import FreeProbProg.
From SSProve.Crypt Require Import choice_type SubDistr.
From VerifiedCKKS Require Import KL.
From VerifiedCKKS Require Import RhlAe.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope ring_scope.

Arguments retrFree {_ _ _} _.
Arguments bindrFree {_ _ _ _} _ _.
Arguments callrFree {_ _ } _.

Inductive equiv_with_pythagorean_errors :
  ∀ (out_t : ord_choiceType) (mem_t : choiceType),
    @FrStP mem_t out_t -> @FrStP mem_t out_t -> list R -> Prop :=
| pyth_ret_eq {out_t : ord_choiceType} (mem_t : choiceType) (v : out_t) :
    equiv_with_pythagorean_errors out_t mem_t (retrFree v) (retrFree v) []
| pyth_eps_samp {supp_t : choice_type} (mem_t : choiceType)
    (P Q : {distr supp_t / R}) (ε : R) :
  δ_KL P Q < ε ->
  equiv_with_pythagorean_errors _ mem_t
    (callrFree (samplee (existT _ supp_t P)))
    (callrFree (samplee (existT _ supp_t Q))) [ ε ]
| pyth_bind_eq (mem_t: choiceType) (outA_t outB_t : ord_choiceType)
    (pL pR : @FrStP mem_t outA_t) (qL qR : outA_t -> @FrStP mem_t outB_t)
    (lst1 lst2 : list R) :
  equiv_with_pythagorean_errors outA_t mem_t pL pR lst1 →
  (∀ a, equiv_with_pythagorean_errors outB_t mem_t (qL a) (qR a) lst2) →
  equiv_with_pythagorean_errors outB_t mem_t
    (bindrFree pL qL) (bindrFree pR qR) (lst1 ++ lst2).

Fixpoint sum_squares (lst : list R) :=
  match lst with
  | [] => 0
  | head :: tail => head * head + sum_squares tail
  end.

Definition l2_norm (eps_lst : list R) := Num.sqrt (sum_squares eps_lst).

Theorem mw18 (out_t : ord_choiceType) (mem_t : choiceType)
  (progL progR : @FrStP mem_t out_t) (eps_lst : list R) :
  equiv_with_pythagorean_errors out_t mem_t progL progR eps_lst →
  equiv_with_additive_error out_t out_t progL progR
  (fun mems => match mems with (mL, mR) => mL == mR end)
  (fun results => match results with (resL, resR) => resL == resR end)
  (l2_norm eps_lst).
Admitted.
