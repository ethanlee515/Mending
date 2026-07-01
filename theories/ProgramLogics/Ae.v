From Stdlib Require Import Unicode.Utf8.
From extructures Require Import ord fset fmap.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals distr.
From mathcomp Require Import realseq realsum exp lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From Mending.LibExtras.MathcompExtras Require Import DistrExtras.
From Mending.NextMessage Require Import Trace.
From Mending.Probability Require Import Ae OutputHeap.
From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Crypt Require Import ChoiceAsOrd Couplings StateTransformingLaxMorph
  choice_type fmap_extra SubDistr.
From SSProve.Crypt Require Import Axioms StateTransfThetaDens.
From SSProve.Crypt.nominal Require Import Pr.
From SSProve Require Import pkg_core_definition pkg_advantage pkg_composition
  pkg_notation.

Import GRing.Theory Num.Theory Order.Theory Order.POrderTheory.

Local Open Scope ring_scope.

Import pkg_heap.
Import PackageNotation.
Local Open Scope package_scope.

Definition additiveErrorJudgmentOpt
  {inL_t inR_t outL_t outR_t : ord_choiceType}
  (progL : inL_t -> raw_code outL_t)
  (progR : inR_t -> raw_code outR_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (option (outL_t * heap) * option (outR_t * heap)))
  (ε : R) : Prop :=
  0 <= ε /\
  ∀ memL memR xL xR, pre ((xL, memL), (xR, memR)) →
    let out1 := Pr_code (progL xL) memL in
    let out2 := Pr_code (progR xR) memR in
    ∃ d, coupling d (complete out1) (complete out2) ∧
      \P_[ d ] post >= 1 - ε.

Declare Scope AeNotations.
Local Open Scope AeNotations.

Notation "⊨AE_opt ⦃ pre ⦄ progL ≈( ε ) progR ⦃ post ⦄" :=
  (additiveErrorJudgmentOpt progL progR pre post ε) : AeNotations.

Definition additiveErrorJudgment
  {inL_t inR_t outL_t outR_t : ord_choiceType}
  (progL : inL_t -> raw_code outL_t)
  (progR : inR_t -> raw_code outR_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred ((outL_t * heap) * (outR_t * heap)))
  (ε : R) : Prop :=
  ⊨AE_opt ⦃ pre ⦄ progL ≈( ε ) progR ⦃ lift_loss_post post ⦄.

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
Admitted.

Lemma additiveErrorCoupleOptRule
  {inL_t inR_t outL_t outR_t : ord_choiceType}
  (progL : inL_t -> raw_code outL_t)
  (progR : inR_t -> raw_code outR_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (option (outL_t * heap) * option (outR_t * heap)))
  (ε : R)
  (wit : forall memL memR xL xR,
      pre ((xL, memL), (xR, memR)) ->
      {distr _ / R}) :
  0 <= ε ->
  (forall memL memR xL xR Hpre,
    let out1 := Pr_code (progL xL) memL in
    let out2 := Pr_code (progR xR) memR in
    coupling (wit memL memR xL xR Hpre)
      (complete out1) (complete out2)) ->
  (forall memL memR xL xR Hpre,
    \P_[ wit memL memR xL xR Hpre ] post >= 1 - ε) ->
  ⊨AE_opt ⦃ pre ⦄ progL ≈( ε ) progR ⦃ post ⦄.
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

Lemma additiveErrorOptEpsNonneg
  {inL_t inR_t outL_t outR_t : ord_choiceType}
  (progL : inL_t -> raw_code outL_t)
  (progR : inR_t -> raw_code outR_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (option (outL_t * heap) * option (outR_t * heap)))
  (ε : R) :
  ⊨AE_opt ⦃ pre ⦄ progL ≈( ε ) progR ⦃ post ⦄ ->
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
  ⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃
    fun outs =>
      let '((y_1, m_1'), (y_2, m_2')) := outs in
      (y_1 == y_2) && (m_1' == m_2') ⦄.
Admitted.

Definition same_output_heap_opt {out_t : choice_type}
    (outs : option (out_t * heap) * option (out_t * heap)) : bool :=
  outs.1 == outs.2.

Lemma additiveErrorOptSameOutputTvdEqRule
  {inL_t inR_t out_t : choice_type}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (ε : R) :
  0 <= ε ->
  (forall memL memR xL xR, pre ((xL, memL), (xR, memR)) ->
    total_variation
      (complete (Pr_code (progL xL) memL))
      (complete (Pr_code (progR xR) memR)) <= ε) ->
  ⊨AE_opt ⦃ pre ⦄ progL ≈( ε ) progR ⦃ same_output_heap_opt ⦄.
Proof.
move=> Heps Htv.
split; first exact: Heps.
move=> memL memR xL xR Hpre.
set out1 := Pr_code (progL xL) memL.
set out2 := Pr_code (progR xR) memR.
have [d [HdL [HdR Hprob]]] :=
  maximal_coupling_total_variation (complete out1) (complete out2) ε
    (complete_dweight out1) (complete_dweight out2) (Htv _ _ _ _ Hpre).
exists d.
split.
- split.
  + apply: distr_ext=> x.
    by rewrite /lmg dmarginE.
  + apply: distr_ext=> x.
    by rewrite /rmg dmarginE.
- rewrite (eq_pr (B := fun xy => xy.1 == xy.2)).
    exact: Hprob.
  by case=> outL outR.
Qed.

Lemma additiveErrorCompletedOutputHeapTvdEqRule
  {inL_t inR_t out_t : choice_type}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (ε : R) :
  0 <= ε ->
  (forall memL memR xL xR, pre ((xL, memL), (xR, memR)) ->
    total_variation
      (complete_output_heap (Pr_code (progL xL) memL))
      (complete_output_heap (Pr_code (progR xR) memR)) <= ε) ->
  ⊨AE_opt ⦃ pre ⦄ progL ≈( ε ) progR ⦃
    fun outs =>
    let '(outL, outR) := outs in
    outL == outR ⦄.
Proof.
move=> Heps Htv.
split; first exact: Heps.
move=> memL memR xL xR Hpre.
set out1 := Pr_code (progL xL) memL.
set out2 := Pr_code (progR xR) memR.
have Htv_complete : total_variation (complete out1) (complete out2) <= ε.
  rewrite (total_variation_complete_output_heap out1 out2).
  exact: Htv.
have [d [HdL [HdR Hprob]]] :=
  maximal_coupling_total_variation (complete out1) (complete out2) ε
    (complete_dweight out1) (complete_dweight out2) Htv_complete.
exists d.
split.
- split.
  + apply: distr_ext=> x.
    by rewrite /lmg dmarginE.
  + apply: distr_ext=> x.
    by rewrite /rmg dmarginE.
- rewrite (eq_pr (B := fun xy => xy.1 == xy.2)).
    exact: Hprob.
  by case=> outL outR.
Qed.

Lemma additiveErrorOptSameOutputTvBound
  {inL_t inR_t out_t : choice_type}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (ε : R) memL memR xL xR :
  ⊨AE_opt ⦃ pre ⦄ progL ≈( ε ) progR ⦃ same_output_heap_opt ⦄ ->
  pre ((xL, memL), (xR, memR)) ->
  total_variation
    (complete (Pr_code (progL xL) memL))
    (complete (Pr_code (progR xR) memR)) <= ε.
Proof.
move=> [_ Hae] Hpre.
set outL := Pr_code (progL xL) memL.
set outR := Pr_code (progR xR) memR.
have [d [Hd Hprob]] := Hae memL memR xL xR Hpre.
have [HdL HdR] := Hd.
have HdL' : dmargin fst d =1 complete outL.
  move=> z.
  by rewrite -HdL.
have HdR' : dmargin snd d =1 complete outR.
  move=> z.
  by rewrite -HdR.
rewrite /same_output_heap_opt in Hprob.
apply: (exact_coupling_eq_pr_total_variation d
  (complete outL) (complete outR) ε).
- exact: complete_dweight.
- exact: complete_dweight.
- exact: HdL'.
- exact: HdR'.
- exact: Hprob.
Qed.

Lemma additiveErrorOptSameOutputTriangleRule
  {in_t out_t : choice_type}
  (progL progM progR : in_t -> raw_code out_t)
  (pre : pred ((in_t * heap) * (in_t * heap)))
  (ε ε' : R) :
  (forall memL memR xL xR,
    pre ((xL, memL), (xR, memR)) -> xL = xR /\ memL = memR) ->
  ⊨AE_opt ⦃ pre ⦄ progL ≈( ε ) progM ⦃ same_output_heap_opt ⦄ ->
  ⊨AE_opt ⦃ pre ⦄ progM ≈( ε' ) progR ⦃ same_output_heap_opt ⦄ ->
  ⊨AE_opt ⦃ pre ⦄ progL ≈( ε + ε' ) progR ⦃ same_output_heap_opt ⦄.
Proof.
move=> Hsame HLM HMR.
apply: additiveErrorOptSameOutputTvdEqRule.
- have Heps := additiveErrorOptEpsNonneg _ _ _ _ _ HLM.
  have Heps' := additiveErrorOptEpsNonneg _ _ _ _ _ HMR.
  lra.
- move=> memL memR xL xR Hpre.
  have [Hx Hmem] := Hsame memL memR xL xR Hpre.
  subst xR; subst memR.
  have HtvLM :=
    additiveErrorOptSameOutputTvBound
      progL progM pre ε memL memL xL xL HLM Hpre.
  have HtvMR :=
    additiveErrorOptSameOutputTvBound
      progM progR pre ε' memL memL xL xL HMR Hpre.
  have Htri := total_variation_triangle
    (complete (Pr_code (progL xL) memL))
    (complete (Pr_code (progM xL) memL))
    (complete (Pr_code (progR xL) memL)).
  apply: (le_trans Htri).
  lra.
Qed.

Lemma additiveErrorTvdEqPostRule
  {inL_t inR_t out_t : ord_choiceType}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (out_t * heap))
  (ε : R) :
  0 <= ε ->
  (forall memL memR xL xR, pre ((xL, memL), (xR, memR)) ->
    total_variation (Pr_code (progL xL) memL)
                    (Pr_code (progR xR) memR) <= ε) ->
  (forall memL memR xL xR y,
    pre ((xL, memL), (xR, memR)) ->
    y \in dinsupp (Pr_code (progL xL) memL) ->
    post y) ->
  ⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃
    fun outs =>
      let '((y_1, m_1'), (y_2, m_2')) := outs in
      post (y_1, m_1') && (y_1 == y_2) && (m_1' == m_2') ⦄.
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
have Hmono : \P_[d] (lift_loss_post post) <=
    \P_[d] (lift_loss_post post').
  apply: subset_pr => out Hout.
  case: out Hout => [[outL|] [outR|]] //=.
  exact: Hpost.
(* Increasing the error budget lowers the required success threshold. *)
have Hthreshold : 1 - ε' <= 1 - ε by lra.
exact: (le_trans Hthreshold (le_trans Hprob Hmono)).
Qed.

Lemma additiveErrorOptConseqRule
  {inL_t inR_t outL_t outR_t : ord_choiceType}
  (progL : inL_t -> raw_code outL_t)
  (progR : inR_t -> raw_code outR_t)
  (pre pre' : pred ((inL_t * heap) * (inR_t * heap)))
  (post post' : pred (option (outL_t * heap) * option (outR_t * heap)))
  (ε ε' : R) :
  (forall inps, pre' inps -> pre inps) ->
  (forall outs, post outs -> post' outs) ->
  ε <= ε' ->
  ⊨AE_opt ⦃ pre ⦄ progL ≈( ε ) progR ⦃ post ⦄ ->
  ⊨AE_opt ⦃ pre' ⦄ progL ≈( ε' ) progR ⦃ post' ⦄.
Proof.
move=> Hpre Hpost Herr [Heps Hae].
split; first by lra.
move=> memL memR xL xR Hpre'.
have [d [Hd Hprob]] := Hae memL memR xL xR (Hpre _ Hpre').
exists d; split; first exact: Hd.
have Hmono : \P_[d] post <= \P_[d] post'.
  apply: subset_pr => out Hout.
  exact: Hpost.
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

Lemma additiveErrorCompileCallsRule
  (q : nat) (X Y I O : choice_type)
  (L L' : Locations) (M : Interface)
  (P' : raw_package) (fn : ident)
  (prog : I -> raw_code O) :
  ValidPackage L' [interface] M P' ->
  fhas M (mkopsig fn X Y) ->
  (forall x, ValidCode L M (prog x)) ->
  ⊨AE ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) ⦄
    (fun x => code_link
      (compile_calls q (X := X) (Y := Y) P' fn (prog x))
      P')
    ≈( 0 )
    (fun x => code_link (prog x) P')
  ⦃ fun outs =>
      let '((yL, memL), (yR, memR)) := outs in
      (yL == yR) && (memL == memR) ⦄.
Proof.
move=> HP' Hfn Hprog.
apply: additiveErrorTvdEqRule.
- exact: lexx.
- move=> memL memR xL xR Hpre.
  move/andP: Hpre => [/eqP -> /eqP ->].
  rewrite (@compile_calls_correct_code_link q X Y O L L' M P' fn (prog xR)
    HP' Hfn (Hprog xR)).
  rewrite /total_variation.
  rewrite (_ : sum (fun y =>
      `|Pr_code (code_link (prog xR) P') memR y -
        Pr_code (code_link (prog xR) P') memR y|) = 0).
    by rewrite mulr0 lexx.
  rewrite -(@sum0 R (O * heap)%type).
  apply/eq_sum => y.
  by rewrite subrr normr0.
Qed.

Lemma additiveErrorTvBound
  {inL_t inR_t out_t : ord_choiceType}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (ε : R) memL memR xL xR :
  ⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃ fun outs => outs.1.1 == outs.2.1 ⦄ ->
  pre ((xL, memL), (xR, memR)) ->
  total_variation (dmargin fst (Pr_code (progL xL) memL))
                  (dmargin fst (Pr_code (progR xR) memR)) <= ε.
Admitted.
