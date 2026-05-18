(* RHL with Pythagorean Errors *)

From Stdlib Require Import Unicode.Utf8.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From extructures Require Import ord fset fmap.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import reals distr ssrZ.
From mathcomp Require Import lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Crypt Require Import ChoiceAsOrd Couplings StateTransformingLaxMorph.
From SSProve.Crypt Require Import Axioms StateTransfThetaDens.
From SSProve Require Import FreeProbProg.
From SSProve.Crypt Require Import choice_type SubDistr.
From SSProve Require Import pkg_core_definition pkg_advantage pkg_notation.
From Mending.KL Require Import KL.
From Mending Require Import DistrExtras SspDG.
From Mending Require Import RhlAe RhlPythDist.
Local Open Scope AeNotations.

Import ListNotations.
Import PackageNotation.
Import pkg_heap.
Local Open Scope list_scope.
Local Open Scope package_scope.
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


Program Definition lift_i {ℓ : nat} {t : 'I_(ℓ.+1)} (i : 'I_t) : 'I_(ℓ.+1) :=
  widen_ord _ i.
Next Obligation.
move => ℓ t i.
have ?: (t < ℓ.+1)%N by apply ltn_ord.
lia.
Defined.

Definition pythJudgment
  {ℓ : nat}
  {inL_t inR_t out_t : ord_choiceType}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :=
  ∀ memL memR xL xR, pre ((xL, memL), (xR, memR)) →
  exists
  (Ω : choiceType)
  (X : 'I_ℓ -> choiceType)
  (coord : forall i : 'I_ℓ, Ω -> X i)
  (final : Ω -> out_t * heap)
  (P Q : {distr Ω / R}),
  let outL := Pr_code (progL xL) memL in
  let outR := Pr_code (progR xR) memR in
  pythDistWithFinal coord final P Q s /\
  dmargin final P =1 outL /\
  dmargin final Q =1 outR /\
  (forall x, x \in dinsupp outL -> post x) /\
  (forall x, x \in dinsupp outR -> post x).

Declare Scope pyth_scope.
Local Open Scope pyth_scope.

Notation "⊨Pyth ⦃ pre ⦄ progL ≈( s ) progR ⦃ post ⦄" :=
  (pythJudgment progL progR pre post s) : pyth_scope.

Definition tuple_sum {n : nat} (s : n.-tuple R) : R :=
  \sum_(i < n) tnth s i.

Definition tuple_sum_squares {n : nat} (s : n.-tuple R) : R :=
  \sum_(i < n) (tnth s i) ^+ 2.

Definition two_norm {n : nat} (s : n.-tuple R) : R :=
  Num.sqrt (tuple_sum_squares s).

Definition pythagorean_tv_bound {n : nat} (s : n.-tuple R) : R :=
  Num.sqrt (tuple_sum s / 2).


Definition sampleRaw {out_t : choice_type} (D : {distr out_t / R}) : raw_code out_t :=
  x <$ (existT _ out_t D) ;;
  ret x.

Lemma klSampRule
  {inL_t inR_t : ord_choiceType} {out_t : choice_type}
  (DL : inL_t -> {distr out_t / R})
  (DR : inR_t -> {distr out_t / R})
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (out_t * heap))
  (ε : R) :
  0 <= ε ->
  (forall xL xR, absolute_continuous (DL xL) (DR xR)) ->
  (forall xL, dweight (DL xL) = 1) ->
  (forall xR, dweight (DR xR) = 1) ->
  (forall memL memR xL xR, pre ((xL, memL), (xR, memR)) ->
    δ_KL (DL xL) (DR xR) <= ε) ->
  (forall memL memR xL xR y,
    pre ((xL, memL), (xR, memR)) -> y \in dinsupp (DL xL) -> post (y, memL)) ->
  (forall memL memR xL xR y,
    pre ((xL, memL), (xR, memR)) -> y \in dinsupp (DR xR) -> post (y, memR)) ->
  ⊨Pyth ⦃ pre ⦄ (fun x => sampleRaw (DL x)) ≈( [tuple ε] )
    (fun x => sampleRaw (DR x)) ⦃ post ⦄.
Admitted.

Lemma klDgRule
  (centerL centerR : chInt)
  (stdev ε : R)
  (pre : pred ((chUnit * heap) * (chUnit * heap)))
  (post : pred (chInt * heap)) :
  0 < stdev ->
  ((int_of_Z centerR - int_of_Z centerL)%:~R) ^+ 2 / (2 * stdev ^ 2) <= ε ->
  (forall memL memR,
    pre ((tt, memL), (tt, memR)) ->
    forall y, y \in dinsupp (ssp_dg centerL stdev) -> post (y, memL)) ->
  (forall memL memR,
    pre ((tt, memL), (tt, memR)) ->
    forall y, y \in dinsupp (ssp_dg centerR stdev) -> post (y, memR)) ->
  ⊨Pyth ⦃ pre ⦄ (fun _ : chUnit => sampleRaw (ssp_dg centerL stdev)) ≈( [tuple ε] )
    (fun _ : chUnit => sampleRaw (ssp_dg centerR stdev)) ⦃ post ⦄.
Admitted.

Lemma MicciancioWalterRule
  {ℓ : nat}
  {inL_t inR_t out_t : ord_choiceType}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :
  ⊨Pyth ⦃ pre ⦄ progL ≈( s ) progR ⦃ post ⦄ ->
  let delta := pythagorean_tv_bound s in
  ⊨AE ⦃ pre ⦄ progL ≈( delta ) progR ⦃
    fun outs =>
      let '((y_1, m_1'), (y_2, m_2')) := outs in
      post (y_1, m_1') && (y_1 == y_2) && (m_1' == m_2')⦄.
Proof.
move => *.
Admitted.

Lemma pythConseqRule
  {ℓ : nat}
  {inL_t inR_t out_t : ord_choiceType}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre pre' : pred ((inL_t * heap) * (inR_t * heap)))
  (post post' : pred (out_t * heap))
  (s s' : (ℓ.+1).-tuple R) :
  (forall inps, pre' inps -> pre inps) ->
  (forall outs, post outs -> post' outs) ->
  (forall i : 'I_(ℓ.+1), tnth s i <= tnth s' i) ->
  ⊨Pyth ⦃ pre ⦄ progL ≈( s ) progR ⦃ post ⦄ ->
  ⊨Pyth ⦃ pre' ⦄ progL ≈( s' ) progR ⦃ post' ⦄.
Admitted.

Lemma aePythSeqRule
  {ℓ : nat}
  {inL_t inR_t midL_t midR_t out_t : ord_choiceType}
  (progL : inL_t -> raw_code midL_t)
  (progR : inR_t -> raw_code midR_t)
  (contL : midL_t -> raw_code out_t)
  (contR : midR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (mid : pred ((midL_t * heap) * (midR_t * heap)))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :
  ⊨AE ⦃ pre ⦄ progL ≈( 0 ) progR ⦃ mid ⦄ ->
  ⊨Pyth ⦃ mid ⦄ contL ≈( s ) contR ⦃ post ⦄ ->
  ⊨Pyth ⦃ pre ⦄ seqRaw progL contL ≈( s ) seqRaw progR contR ⦃ post ⦄.
Admitted.

Lemma pythSeqRule
  {ℓ ℓ' : nat}
  {inL_t inR_t mid_t out_t : ord_choiceType}
  (progL : inL_t -> raw_code mid_t)
  (progR : inR_t -> raw_code mid_t)
  (contL : mid_t -> raw_code out_t)
  (contR : mid_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (left_post : pred (mid_t * heap))
  (mid : pred ((mid_t * heap) * (mid_t * heap)))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R)
  (s' : (ℓ'.+1).-tuple R) :
  (forall aL aR, left_post aL -> left_post aR -> mid (aL, aR)) ->
  ⊨Pyth ⦃ pre ⦄ progL ≈( s ) progR ⦃ left_post ⦄ ->
  ⊨Pyth ⦃ mid ⦄ contL ≈( s' ) contR ⦃ post ⦄ ->
  ⊨Pyth ⦃ pre ⦄ seqRaw progL contL ≈( cat_tuple s s' ) seqRaw progR contR ⦃ post ⦄.
Admitted.

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


Local Open Scope AeNotations.

Theorem mw18 (out_t : ord_choiceType) (mem_t : choiceType)
  (progL progR : @FrStP mem_t out_t) (eps_lst : list R) :
  equiv_with_pythagorean_errors out_t mem_t progL progR eps_lst →
  equiv_with_additive_error progL progR
  (fun mems => match mems with (mL, mR) => mL == mR end)
  (fun results => match results with (resL, resR) => resL == resR end)
  (l2_norm eps_lst).
Admitted.
*)
