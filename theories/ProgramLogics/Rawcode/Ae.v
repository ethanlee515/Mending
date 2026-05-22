From Stdlib Require Import Unicode.Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import reals distr.
From mathcomp Require Import realseq realsum exp lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From Mending.LibExtras.MathcompExtras Require Import DistrExtras.
From Mending.ProgramLogics.Distribution Require Import Ae.
From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Crypt Require Import ChoiceAsOrd Couplings StateTransformingLaxMorph.
From SSProve.Crypt Require Import Axioms StateTransfThetaDens.
From SSProve.Crypt.nominal Require Import Pr.
From SSProve Require Import pkg_core_definition pkg_advantage pkg_notation.

Import GRing.Theory Num.Theory Order.Theory Order.POrderTheory.

Local Open Scope ring_scope.

Import pkg_heap.
Import PackageNotation.
Local Open Scope package_scope.

Definition additiveErrorJudgment
  {inL_t inR_t outL_t outR_t : ord_choiceType}
  (progL : inL_t -> raw_code outL_t)
  (progR : inR_t -> raw_code outR_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred ((outL_t * heap) * (outR_t * heap)))
  (ε : R) : Prop :=
  0 <= ε /\
  ∀ memL memR xL xR, pre ((xL, memL), (xR, memR)) →
    let out1 := Pr_code (progL xL) memL in
    let out2 := Pr_code (progR xR) memR in
    ∃ d, coupling_with_loss d out1 out2 ∧ \P_[ d ] post >= 1 - ε.

Declare Scope AeNotations.
Local Open Scope AeNotations.

Notation "⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃ post ⦄" :=
  (additiveErrorJudgment progL progR pre post ε) : AeNotations.

Lemma additiveErrorCoupleRule
  {inL_t inR_t outL_t outR_t : ord_choiceType}
  (progL : inL_t -> raw_code outL_t)
  (progR : inR_t -> raw_code outR_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred ((outL_t * heap) * (outR_t * heap)))
  (ε : R)
  (wit : forall memL memR xL xR,
      pre ((xL, memL), (xR, memR)) ->
      {distr _ / R}) :
  0 <= ε ->
  (forall memL memR xL xR Hpre,
    let out1 := Pr_code (progL xL) memL in
    let out2 := Pr_code (progR xR) memR in
    coupling_with_loss (wit memL memR xL xR Hpre) out1 out2) ->
  (forall memL memR xL xR Hpre,
    \P_[ wit memL memR xL xR Hpre ] post >= 1 - ε) ->
  ⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃ post ⦄.
Proof.
move=> Heps Hcoupling Hpost.
split; first exact: Heps.
move=> memL memR xL xR Hpre.
exists (wit memL memR xL xR Hpre).
split.
- exact: Hcoupling.
- exact: Hpost.
Qed.

Lemma additiveErrorEpsNonneg
  {inL_t inR_t outL_t outR_t : ord_choiceType}
  (progL : inL_t -> raw_code outL_t)
  (progR : inR_t -> raw_code outR_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred ((outL_t * heap) * (outR_t * heap)))
  (ε : R) :
  ⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃ post ⦄ ->
  0 <= ε.
Proof.
by move=> [Heps _].
Qed.

Lemma additiveErrorTvdEqRule
  {inL_t inR_t out_t : ord_choiceType}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (ε : R) :
  0 <= ε ->
  (forall memL memR xL xR, pre ((xL, memL), (xR, memR)) ->
    total_variation (Pr_code (progL xL) memL)
                    (Pr_code (progR xR) memR) <= ε) ->
  ⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃ fun outs => outs.1.1 == outs.2.1 ⦄.
Admitted.

Lemma additiveErrorReflRule
  {in_t out_t : ord_choiceType}
  (prog : in_t -> raw_code out_t)
  (pre : pred ((in_t * heap) * (in_t * heap))) :
  (forall memL memR xL xR,
    pre ((xL, memL), (xR, memR)) -> xL = xR /\ memL = memR) ->
  ⊨AE ⦃ pre ⦄ prog ≈( 0 ) prog ⦃ fun outs => outs.1.1 == outs.2.1 ⦄.
Admitted.

Lemma additiveErrorConseqRule
  {inL_t inR_t outL_t outR_t : ord_choiceType}
  (progL : inL_t -> raw_code outL_t)
  (progR : inR_t -> raw_code outR_t)
  (pre pre' : pred ((inL_t * heap) * (inR_t * heap)))
  (post post' : pred ((outL_t * heap) * (outR_t * heap)))
  (ε ε' : R) :
  (forall inps, pre' inps -> pre inps) ->
  (forall outs, post outs -> post' outs) ->
  ε <= ε' ->
  ⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃ post ⦄ ->
  ⊨AE ⦃ pre' ⦄ progL ≈( ε' ) progR ⦃ post' ⦄.
Proof.
move=> Hpre Hpost Herr [Heps Hae].
split; first by lra.
move=> memL memR xL xR Hpre'.
have [d [Hd Hprob]] := Hae memL memR xL xR (Hpre _ Hpre').
exists d; split; first exact: Hd.
have Hmono : \P_[d] post <= \P_[d] post'.
  apply: subset_pr => out Hout.
  exact: Hpost.
(* Increasing the error budget lowers the required success threshold. *)
have Hthreshold : 1 - ε' <= 1 - ε by lra.
exact: (le_trans Hthreshold (le_trans Hprob Hmono)).
Qed.

Lemma additiveErrorSeqRule
  {inL_t inR_t midL_t midR_t outL_t outR_t : ord_choiceType}
  (progL : inL_t -> raw_code midL_t)
  (progR : inR_t -> raw_code midR_t)
  (contL : midL_t -> raw_code outL_t)
  (contR : midR_t -> raw_code outR_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (mid : pred ((midL_t * heap) * (midR_t * heap)))
  (post : pred ((outL_t * heap) * (outR_t * heap)))
  (ε ε' : R) :
  ⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃ mid ⦄ ->
  ⊨AE ⦃ mid ⦄ contL ≈( ε' ) contR ⦃ post ⦄ ->
  ⊨AE ⦃ pre ⦄
    (fun xL => yL ← progL xL ;; contL yL)
    ≈( ε + ε' )
    (fun xR => yR ← progR xR ;; contR yR)
  ⦃ post ⦄.
Proof.
move=> [Heps Hprog] [Heps' Hcont].
split; first by lra.
move=> memL memR xL xR Hpre.
set ML := Pr_code (progL xL) memL.
set MR := Pr_code (progR xR) memR.
set KL := fun y : midL_t * heap => Pr_code (contL y.1) y.2.
set KR := fun y : midR_t * heap => Pr_code (contR y.1) y.2.
have [d0 [Hd0 Hmidprob]] := Hprog memL memR xL xR Hpre.
have Hcont_wit :
    forall yL yR,
      mid (yL, yR) ->
      exists d1,
        coupling_with_loss d1 (KL yL) (KR yR) /\
        \P_[ d1 ] post >= 1 - ε'.
  move=> yL yR Hmid.
  case: yL Hmid => [yLv yLm] Hmid.
  case: yR Hmid => [yRv yRm] Hmid.
  have [d1 [Hd1 Hpost]] := Hcont yLm yRm yLv yRv Hmid.
  by exists d1.
have [d [Hd Hpost]] :=
  coupling_with_loss_bind ML MR KL KR mid post ε ε' d0
    Heps Heps' Hd0 Hmidprob Hcont_wit.
exists d; split; last exact: Hpost.
rewrite !Pr_code_bind.
exact: Hd.
Qed.

Lemma additiveErrorTvBound
  {inL_t inR_t out_t : ord_choiceType}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (ε : R) :
  ⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃ fun outs => outs.1.1 == outs.2.1 ⦄ ->
  forall memL memR xL xR,
    pre ((xL, memL), (xR, memR)) ->
    total_variation (dmargin fst (Pr_code (progL xL) memL))
                    (dmargin fst (Pr_code (progR xR) memR)) <= ε.
Admitted.
