From Stdlib Require Import Unicode.Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import reals distr.
From mathcomp Require Import realseq realsum exp lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From Mending.LibExtras.MathcompExtras Require Import DistrExtras.
From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Crypt Require Import ChoiceAsOrd Couplings StateTransformingLaxMorph.
From SSProve.Crypt Require Import Axioms StateTransfThetaDens.
From SSProve Require Import pkg_core_definition pkg_advantage pkg_notation.

Import GRing.Theory Num.Theory Order.Theory Order.POrderTheory.

Local Open Scope ring_scope.

Import pkg_heap.
Import PackageNotation.
Local Open Scope package_scope.

Definition complete_mass {T : choiceType} (D : {distr T / R}) : option T -> R :=
  fun x =>
    match x with
    | Some y => D y
    | None => 1 - dweight D
    end.

Lemma isdistr_complete_mass {T : choiceType} (D : {distr T / R}) :
  isdistr (complete_mass D).
Proof.
split.
- case=> [x|]; first exact: ge0_mu.
  rewrite subr_ge0 pr_predT.
  exact: le1_mu.
- move=> J uniq_J.
  pose get (x : option T) := x.
  have getK : ocancel get (@Some T) by case.
  have Hsplit :
      \sum_(j <- J) complete_mass D j =
      \sum_(x <- pmap get J) D x +
        (if None \in J then 1 - dweight D else 0).
    elim: J uniq_J => [|j J IH] /=.
      by rewrite !big_nil addr0.
    rewrite in_cons => /andP [Hnotin Huniq].
    rewrite !big_cons.
    case: j Hnotin => [y|] Hnotin /=.
      rewrite IH // big_cons addrA.
      by [].
    rewrite IH //.
    move/negbTE: Hnotin => ->.
    by rewrite addr0 addrC.
  rewrite Hsplit.
  have Hsomes_uniq : uniq (pmap get J).
    exact: (pmap_uniq getK uniq_J).
  have Hsomes_le : \sum_(x <- pmap get J) D x <= dweight D.
    rewrite pr_predT.
    apply: (le_trans _ (gerfinseq_psum Hsomes_uniq (summable_mu D))).
    apply/ler_sum=> x _.
    by rewrite ger0_norm ?ge0_mu.
  have Hmass_le1 : dweight D <= 1 by rewrite pr_predT; exact: le1_mu.
  have Hloss_ge0 : 0 <= 1 - dweight D by lra.
  case: ifP => _; lra.
Qed.

Definition complete {T : choiceType} (D : {distr T / R})
    : {distr (option T) / R} :=
  mkdistr (isdistr_complete_mass D).

Lemma completeE {T : choiceType} (D : {distr T / R}) x :
  complete D x = complete_mass D x.
Proof. by []. Qed.

Definition coupling_with_loss
  {outL_t outR_t : ord_choiceType}
  (d : {distr (outL_t * outR_t) / R})
  (outL : {distr outL_t / R})
  (outR : {distr outR_t / R}) : Prop :=
  dmargin fst d <=1 outL /\ dmargin snd d <=1 outR.

Definition lift_loss_post
  {outL_t outR_t : choiceType}
  (post : pred (outL_t * outR_t)) : pred (option outL_t * option outR_t) :=
  fun outs =>
    match outs with
    | (Some outL, Some outR) => post (outL, outR)
    | _ => false
    end.

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
Admitted.

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
