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

Lemma dmargin_comp
    {A B C : choiceType} (f : B -> C) (g : A -> B)
    (D : {distr A / R}) :
  dmargin f (dmargin g D) =1 dmargin (fun x => f (g x)) D.
Proof.
move=> z.
rewrite dmarginE __deprecated__dlet_dlet.
transitivity ((\dlet_(x <- D) dunit (f (g x))) z).
- apply: eq_in_dlet=> // x _ z'.
  by rewrite dlet_unit.
- by rewrite dmarginE.
Qed.

Lemma dmargin_some {T : choiceType} (D : {distr T / R}) :
  dweight D = 1 ->
  dmargin (@Some T) D =1 complete D.
Proof.
move=> HD [x|].
- rewrite dmarginE.
  rewrite dletE.
  rewrite (eq_psum
    (F2 := fun y : T => (y == x)%:R * D y)).
    by rewrite completeE /= pr_pred1.
  move=> y.
  rewrite dunit1E eq_sym mulrC.
  by rewrite /= eq_sym.
- rewrite dmarginE.
  rewrite dletE.
  rewrite (eq_psum (F2 := fun _ : T => 0)).
    rewrite psum0.
    by rewrite completeE /= HD subrr.
  move=> y.
  by rewrite dunit1E mulr0.
Qed.

Lemma additiveErrorTvdEqTotalRule
  {inL_t inR_t out_t : ord_choiceType}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (ε : R) :
  0 <= ε ->
  (forall memL memR xL xR, pre ((xL, memL), (xR, memR)) ->
    dweight (Pr_code (progL xL) memL) = 1) ->
  (forall memL memR xL xR, pre ((xL, memL), (xR, memR)) ->
    dweight (Pr_code (progR xR) memR) = 1) ->
  (forall memL memR xL xR, pre ((xL, memL), (xR, memR)) ->
    total_variation (Pr_code (progL xL) memL)
                    (Pr_code (progR xR) memR) <= ε) ->
  ⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃
    fun outs =>
      let '((y_1, m_1'), (y_2, m_2')) := outs in
      (y_1 == y_2) && (m_1' == m_2') ⦄.
Proof.
move=> Heps HweightL HweightR Htv.
split; first exact: Heps.
move=> memL memR xL xR Hpre.
set outL := Pr_code (progL xL) memL.
set outR := Pr_code (progR xR) memR.
have HoutL : dweight outL = 1 by exact: (HweightL memL memR xL xR Hpre).
have HoutR : dweight outR = 1 by exact: (HweightR memL memR xL xR Hpre).
have [d [HdL [HdR Hprob]]] :=
  maximal_coupling_total_variation outL outR ε
    HoutL HoutR (Htv _ _ _ _ Hpre).
pose lift (xy : (out_t * heap) * (out_t * heap)) :=
  (Some xy.1, Some xy.2).
exists (dmargin lift d).
split.
- split.
  + apply: distr_ext=> z.
    rewrite (dmargin_comp fst lift d z).
    change (dmargin (fun xy : (out_t * heap) * (out_t * heap) =>
      Some xy.1) d z = complete outL z).
    rewrite -(dmargin_comp (@Some (out_t * heap)) fst d z).
    rewrite (dmargin_ext (@Some (out_t * heap)) _ _ HdL z).
    exact: dmargin_some.
  + apply: distr_ext=> z.
    rewrite (dmargin_comp snd lift d z).
    change (dmargin (fun xy : (out_t * heap) * (out_t * heap) =>
      Some xy.2) d z = complete outR z).
    rewrite -(dmargin_comp (@Some (out_t * heap)) snd d z).
    rewrite (dmargin_ext (@Some (out_t * heap)) _ _ HdR z).
    exact: dmargin_some.
- apply: (le_trans Hprob).
  rewrite pr_dmargin.
  apply: subset_pr=> xy.
  case: xy=> [[yL memL'] [yR memR']] /= Hxy.
  rewrite /lift_loss_post /=.
  exact: Hxy.
Qed.

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

Lemma additiveErrorTvdEqPostTotalRule
  {inL_t inR_t out_t : ord_choiceType}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (out_t * heap))
  (ε : R) :
  0 <= ε ->
  (forall memL memR xL xR, pre ((xL, memL), (xR, memR)) ->
    dweight (Pr_code (progL xL) memL) = 1) ->
  (forall memL memR xL xR, pre ((xL, memL), (xR, memR)) ->
    dweight (Pr_code (progR xR) memR) = 1) ->
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
Proof.
move=> Heps HweightL HweightR Htv Hpost_supp.
split; first exact: Heps.
move=> memL memR xL xR Hpre.
set outL := Pr_code (progL xL) memL.
set outR := Pr_code (progR xR) memR.
have HoutL : dweight outL = 1 by exact: (HweightL memL memR xL xR Hpre).
have HoutR : dweight outR = 1 by exact: (HweightR memL memR xL xR Hpre).
have [d [HdL [HdR Hprob]]] :=
  maximal_coupling_total_variation outL outR ε
    HoutL HoutR (Htv _ _ _ _ Hpre).
pose lift (xy : (out_t * heap) * (out_t * heap)) :=
  (Some xy.1, Some xy.2).
pose post_lift := lift_loss_post
  (fun outs : (out_t * heap) * (out_t * heap) =>
    let '((y_1, m_1'), (y_2, m_2')) := outs in
    post (y_1, m_1') && (y_1 == y_2) && (m_1' == m_2')).
exists (dmargin lift d).
split.
- split.
  + apply: distr_ext=> z.
    rewrite (dmargin_comp fst lift d z).
    change (dmargin (fun xy : (out_t * heap) * (out_t * heap) =>
      Some xy.1) d z = complete outL z).
    rewrite -(dmargin_comp (@Some (out_t * heap)) fst d z).
    rewrite (dmargin_ext (@Some (out_t * heap)) _ _ HdL z).
    exact: dmargin_some.
  + apply: distr_ext=> z.
    rewrite (dmargin_comp snd lift d z).
    change (dmargin (fun xy : (out_t * heap) * (out_t * heap) =>
      Some xy.2) d z = complete outR z).
    rewrite -(dmargin_comp (@Some (out_t * heap)) snd d z).
    rewrite (dmargin_ext (@Some (out_t * heap)) _ _ HdR z).
    exact: dmargin_some.
- apply: (le_trans Hprob).
  pose I (xy : (out_t * heap) * (out_t * heap)) : R :=
    if xy \in dinsupp d then (xy.1 == xy.2)%:R else 0.
  rewrite pr_dmargin.
  rewrite [X in X <= _]pr_exp.
  rewrite (eq_exp (mu := d)
    (f1 := fun xy => (xy.1 == xy.2)%:R) (f2 := I)); last first.
    move=> xy Hxy.
    by rewrite /I Hxy.
  rewrite [X in _ <= X]pr_exp.
  apply: le_exp.
  + apply: bounded_has_exp.
    exists 1=> xy.
    rewrite /I.
    case: ifP=> _; last by rewrite normr0 ler01.
    rewrite ger0_norm ?ler0n ?lern1 ?leq_b1 //.
  + apply: bounded_has_exp.
    exists 1=> xy.
    rewrite ger0_norm ?ler0n ?lern1 ?leq_b1 //.
  + move=> xy.
    rewrite /I.
    case Hsupp: (xy \in dinsupp d); last first.
      by rewrite ler0n.
    case Heq: (xy.1 == xy.2); last by rewrite ler0n.
    rewrite /post_lift /lift_loss_post /=.
    case: xy Hsupp Heq=> [[yL memL'] [yR memR']] Hsupp /= Heq.
    have HyL_supp : (yL, memL') \in dinsupp outL.
      have Hfst_supp : (yL, memL') \in dinsupp (dmargin fst d).
        exact: dmargin_dinsupp_image Hsupp.
      by move: Hfst_supp; rewrite in_dinsupp HdL -in_dinsupp.
    have Hpost : post (yL, memL').
      exact: (Hpost_supp memL memR xL xR (yL, memL') Hpre HyL_supp).
    move/eqP: Heq=> Heq.
    move: Heq Hpost=> [-> ->] Hpost.
    rewrite /lift /=.
    change (1 <= ((post (yR, memR') && (yR == yR) && (memR' == memR'))%:R : R)).
    by rewrite Hpost !eqxx.
Qed.

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

Lemma additiveErrorReflTotalRule
  {in_t out_t : ord_choiceType}
  (prog : in_t -> raw_code out_t)
  (pre : pred ((in_t * heap) * (in_t * heap))) :
  (forall memL memR xL xR,
    pre ((xL, memL), (xR, memR)) -> xL = xR /\ memL = memR) ->
  (forall memL memR xL xR,
    pre ((xL, memL), (xR, memR)) ->
    dweight (Pr_code (prog xL) memL) = 1) ->
  ⊨AE ⦃ pre ⦄ prog ≈( 0 ) prog ⦃ fun outs => outs.1.1 == outs.2.1 ⦄.
Proof.
move=> Hsame Hweight.
apply: (additiveErrorConseqRule
  prog prog pre pre
  (fun outs =>
    let '((y_1, m_1'), (y_2, m_2')) := outs in
    (y_1 == y_2) && (m_1' == m_2'))
  (fun outs => outs.1.1 == outs.2.1) 0 0).
- by [].
- case=> [[yL memL] [yR memR]] /=.
  by move/andP=> [/eqP -> _]; rewrite eqxx.
- exact: lexx.
apply: (additiveErrorTvdEqTotalRule prog prog pre 0).
- exact: lexx.
- exact: Hweight.
- move=> memL memR xL xR Hpre.
  have [Hx Hmem] := Hsame memL memR xL xR Hpre.
  subst xR; subst memR.
  exact: (Hweight memL memL xL xL Hpre).
- move=> memL memR xL xR Hpre.
  have [Hx Hmem] := Hsame memL memR xL xR Hpre.
  subst xR; subst memR.
  exact: total_variation_refl_le0.
Qed.

Definition additiveErrorOptSeqKernel
  {midL_t midR_t outL_t outR_t : ord_choiceType}
  (contL : midL_t -> raw_code outL_t)
  (contR : midR_t -> raw_code outR_t)
  (mid : pred ((midL_t * heap) * (midR_t * heap)))
  (post : pred (option (outL_t * heap) * option (outR_t * heap)))
  (ε' : R)
  (Hcont : forall memL memR yL yR,
      mid ((yL, memL), (yR, memR)) ->
      exists d,
        coupling d
          (complete (Pr_code (contL yL) memL))
          (complete (Pr_code (contR yR) memR)) /\
        \P_[ d ] post >= 1 - ε')
  (xy : option (midL_t * heap) * option (midR_t * heap)) :
  {distr (option (outL_t * heap) * option (outR_t * heap)) / R} :=
  let KL ymem := Pr_code (contL ymem.1) ymem.2 in
  let KR ymem := Pr_code (contR ymem.1) ymem.2 in
  match xy with
  | (Some (yL, memL), Some (yR, memR)) =>
      match @idP (mid ((yL, memL), (yR, memR))) with
      | ReflectT Hmid =>
          proj1_sig
            (boolp.constructive_indefinite_description
              (Hcont memL memR yL yR Hmid))
      | ReflectF _ => complete_bind_fallback_coupling KL KR xy
      end
  | _ => complete_bind_fallback_coupling KL KR xy
  end.

Lemma additiveErrorOptSeqKernel_margins
  {midL_t midR_t outL_t outR_t : ord_choiceType}
  (contL : midL_t -> raw_code outL_t)
  (contR : midR_t -> raw_code outR_t)
  (mid : pred ((midL_t * heap) * (midR_t * heap)))
  (post : pred (option (outL_t * heap) * option (outR_t * heap)))
  (ε' : R)
  (Hcont : forall memL memR yL yR,
      mid ((yL, memL), (yR, memR)) ->
      exists d,
        coupling d
          (complete (Pr_code (contL yL) memL))
          (complete (Pr_code (contR yR) memR)) /\
        \P_[ d ] post >= 1 - ε')
  (xy : option (midL_t * heap) * option (midR_t * heap)) :
  let KL ymem := Pr_code (contL ymem.1) ymem.2 in
  let KR ymem := Pr_code (contR ymem.1) ymem.2 in
  coupling (additiveErrorOptSeqKernel contL contR mid post ε' Hcont xy)
    (complete_bind_kernel KL xy.1)
    (complete_bind_kernel KR xy.2).
Proof.
case: xy=> [[ymemL|] [ymemR|]] /=.
- case: ymemL=> yL memL; case: ymemR=> yR memR /=.
  rewrite /additiveErrorOptSeqKernel /=.
  destruct (@idP (mid ((yL, memL), (yR, memR)))) as [Hmid|Hmid].
  + case: (boolp.constructive_indefinite_description
      (Hcont memL memR yL yR Hmid))=> d [[HdL HdR] Hprob] /=.
    split; [exact: HdL | exact: HdR].
  + have [HdL HdR] :=
      complete_bind_fallback_coupling_margins
        (fun ymem : midL_t * heap => Pr_code (contL ymem.1) ymem.2)
        (fun ymem : midR_t * heap => Pr_code (contR ymem.1) ymem.2)
        (Some (yL, memL), Some (yR, memR)).
    split.
    * apply: distr_ext=> z.
      by rewrite /lmg.
    * apply: distr_ext=> z.
      by rewrite /rmg.
- case: ymemL=> yL memL.
  have [HdL HdR] :=
    complete_bind_fallback_coupling_margins
      (fun ymem : midL_t * heap => Pr_code (contL ymem.1) ymem.2)
      (fun ymem : midR_t * heap => Pr_code (contR ymem.1) ymem.2)
      (Some (yL, memL), None).
  split.
  - apply: distr_ext=> z.
    by rewrite /lmg.
  - apply: distr_ext=> z.
    by rewrite /rmg.
- case: ymemR=> yR memR.
  have [HdL HdR] :=
    complete_bind_fallback_coupling_margins
      (fun ymem : midL_t * heap => Pr_code (contL ymem.1) ymem.2)
      (fun ymem : midR_t * heap => Pr_code (contR ymem.1) ymem.2)
      (None, Some (yR, memR)).
  split.
  - apply: distr_ext=> z.
    by rewrite /lmg.
  - apply: distr_ext=> z.
    by rewrite /rmg.
- have [HdL HdR] :=
    complete_bind_fallback_coupling_margins
      (fun ymem : midL_t * heap => Pr_code (contL ymem.1) ymem.2)
      (fun ymem : midR_t * heap => Pr_code (contR ymem.1) ymem.2)
      (None, None).
  split.
  - apply: distr_ext=> z.
    by rewrite /lmg.
  - apply: distr_ext=> z.
    by rewrite /rmg.
Qed.

Definition additiveErrorOptSeqGood
  {midL_t midR_t : ord_choiceType}
  (mid : pred ((midL_t * heap) * (midR_t * heap)))
  (xy : option (midL_t * heap) * option (midR_t * heap)) : bool :=
  match xy with
  | (Some (yL, memL), Some (yR, memR)) =>
      mid ((yL, memL), (yR, memR))
  | _ => false
  end.

Lemma additiveErrorOptSeqKernel_event
  {midL_t midR_t outL_t outR_t : ord_choiceType}
  (contL : midL_t -> raw_code outL_t)
  (contR : midR_t -> raw_code outR_t)
  (mid : pred ((midL_t * heap) * (midR_t * heap)))
  (post : pred (option (outL_t * heap) * option (outR_t * heap)))
  (ε' : R)
  (Hcont : forall memL memR yL yR,
      mid ((yL, memL), (yR, memR)) ->
      exists d,
        coupling d
          (complete (Pr_code (contL yL) memL))
          (complete (Pr_code (contR yR) memR)) /\
        \P_[ d ] post >= 1 - ε')
  xy :
  additiveErrorOptSeqGood mid xy ->
  \P_[additiveErrorOptSeqKernel contL contR mid post ε' Hcont xy] post >=
    1 - ε'.
Proof.
case: xy=> [[ymemL|] [ymemR|]] /=.
- case: ymemL=> yL memL; case: ymemR=> yR memR /= Hgood.
  rewrite /additiveErrorOptSeqKernel /=.
  destruct (@idP (mid ((yL, memL), (yR, memR)))) as [Hmid|Hmid].
  + case: (boolp.constructive_indefinite_description
      (Hcont memL memR yL yR Hmid))=> d [[HdL HdR] Hprob] /=.
    exact: Hprob.
  + by move: Hmid; rewrite Hgood.
- by case: ymemL.
- by [].
- by [].
Qed.

Lemma coupling_bind_kernel
  {midL_t midR_t outL_t outR_t : ord_choiceType}
  (d : {distr (option (midL_t * heap) * option (midR_t * heap)) / R})
  (PL : {distr (option (midL_t * heap)) / R})
  (PR : {distr (option (midR_t * heap)) / R})
  (K : option (midL_t * heap) * option (midR_t * heap) ->
    {distr (option (outL_t * heap) * option (outR_t * heap)) / R})
  (KL : option (midL_t * heap) -> {distr (option (outL_t * heap)) / R})
  (KR : option (midR_t * heap) -> {distr (option (outR_t * heap)) / R}) :
  coupling d PL PR ->
  (forall xy, coupling (K xy) (KL xy.1) (KR xy.2)) ->
  coupling (\dlet_(xy <- d) K xy)
    (\dlet_(x <- PL) KL x)
    (\dlet_(y <- PR) KR y).
Proof.
move=> [HdL HdR] HK.
split.
- apply: distr_ext=> z.
  rewrite /lmg __deprecated__dmargin_dlet.
  transitivity ((\dlet_(xy <- d) KL xy.1) z).
  + apply: eq_in_dlet=> // xy _ z'.
    have [HKL _] := HK xy.
    by rewrite -HKL /lmg.
  + rewrite -(__deprecated__dlet_dmargin d fst KL z).
    rewrite /lmg in HdL.
    by rewrite HdL.
- apply: distr_ext=> z.
  rewrite /rmg __deprecated__dmargin_dlet.
  transitivity ((\dlet_(xy <- d) KR xy.2) z).
  + apply: eq_in_dlet=> // xy _ z'.
    have [_ HKR] := HK xy.
    by rewrite -HKR /rmg.
  + rewrite -(__deprecated__dlet_dmargin d snd KR z).
    rewrite /rmg in HdR.
    by rewrite HdR.
Qed.

Lemma additiveErrorOptSeqRule_coupling
  {inL_t inR_t midL_t midR_t outL_t outR_t : ord_choiceType}
  (progL : inL_t -> raw_code midL_t)
  (progR : inR_t -> raw_code midR_t)
  (contL : midL_t -> raw_code outL_t)
  (contR : midR_t -> raw_code outR_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (mid : pred ((midL_t * heap) * (midR_t * heap)))
  (post : pred (option (outL_t * heap) * option (outR_t * heap)))
  (ε ε' : R) memL memR xL xR :
  ⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃ mid ⦄ ->
  ⊨AE_opt ⦃ mid ⦄ contL ≈( ε' ) contR ⦃ post ⦄ ->
  pre ((xL, memL), (xR, memR)) ->
  exists d,
    coupling d
      (complete (Pr_code (yL ← progL xL ;; contL yL) memL))
      (complete (Pr_code (yR ← progR xR ;; contR yR) memR)).
Proof.
move=> [_ Hprefix] [_ Hcont] Hpre.
have [d0 [Hd0 Hmidprob]] := Hprefix memL memR xL xR Hpre.
pose KL (ymem : midL_t * heap) := Pr_code (contL ymem.1) ymem.2.
pose KR (ymem : midR_t * heap) := Pr_code (contR ymem.1) ymem.2.
pose K := additiveErrorOptSeqKernel contL contR mid post ε' Hcont.
exists (\dlet_(xy <- d0) K xy).
have Hbind := coupling_bind_kernel d0
  (complete (Pr_code (progL xL) memL))
  (complete (Pr_code (progR xR) memR))
  K (complete_bind_kernel KL) (complete_bind_kernel KR)
  Hd0 (additiveErrorOptSeqKernel_margins contL contR mid post ε' Hcont).
move: Hbind=> [HL HR].
split.
- apply: distr_ext=> z.
  rewrite HL.
  rewrite (complete_bind (Pr_code (progL xL) memL) KL z).
  rewrite /KL.
  rewrite Pr_code_bind.
  by [].
- apply: distr_ext=> z.
  rewrite HR.
  rewrite (complete_bind (Pr_code (progR xR) memR) KR z).
  rewrite /KR.
  rewrite Pr_code_bind.
  by [].
Qed.

Lemma additiveErrorOptSeqRule
  {inL_t inR_t midL_t midR_t outL_t outR_t : ord_choiceType}
  (progL : inL_t -> raw_code midL_t)
  (progR : inR_t -> raw_code midR_t)
  (contL : midL_t -> raw_code outL_t)
  (contR : midR_t -> raw_code outR_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (mid : pred ((midL_t * heap) * (midR_t * heap)))
  (post : pred (option (outL_t * heap) * option (outR_t * heap)))
  (ε ε' : R) :
  ⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃ mid ⦄ ->
  ⊨AE_opt ⦃ mid ⦄ contL ≈( ε' ) contR ⦃ post ⦄ ->
  ⊨AE_opt ⦃ pre ⦄
    (fun xL => yL ← progL xL ;; contL yL)
    ≈( ε + ε' )
    (fun xR => yR ← progR xR ;; contR yR)
	  ⦃ post ⦄.
Proof.
move=> Hprefix Hcont.
move: Hprefix=> [Heps Hprefix].
move: Hcont=> [Heps' Hcont].
split; first by lra.
move=> memL memR xL xR Hpre.
have [d0 [Hd0 Hmidprob]] := Hprefix memL memR xL xR Hpre.
pose KL (ymem : midL_t * heap) := Pr_code (contL ymem.1) ymem.2.
pose KR (ymem : midR_t * heap) := Pr_code (contR ymem.1) ymem.2.
pose K := additiveErrorOptSeqKernel contL contR mid post ε' Hcont.
exists (\dlet_(xy <- d0) K xy).
split.
- have Hbind := coupling_bind_kernel d0
    (complete (Pr_code (progL xL) memL))
    (complete (Pr_code (progR xR) memR))
    K (complete_bind_kernel KL) (complete_bind_kernel KR)
    Hd0 (additiveErrorOptSeqKernel_margins contL contR mid post ε' Hcont).
  move: Hbind=> [HL HR].
  split.
  + apply: distr_ext=> z.
    rewrite HL.
    rewrite (complete_bind (Pr_code (progL xL) memL) KL z).
    rewrite /KL.
    rewrite Pr_code_bind.
    by [].
  + apply: distr_ext=> z.
    rewrite HR.
    rewrite (complete_bind (Pr_code (progR xR) memR) KR z).
    rewrite /KR.
    rewrite Pr_code_bind.
    by [].
- have Hgoodprob :
      \P_[d0] (additiveErrorOptSeqGood mid) >= 1 - ε.
    rewrite (eq_pr (B := lift_loss_post mid)); first exact: Hmidprob.
    case=> [[ymemL|] [ymemR|]] /=.
    + by case: ymemL=> yL memL0; case: ymemR=> yR memR0.
    + by case: ymemL=> yL memL0.
    + by case: ymemR=> yR memR0.
    + by [].
  apply: (pr_dlet_lower_bound_good d0 K
    (additiveErrorOptSeqGood mid) post ε ε').
  + exact: Heps.
  + exact: Heps'.
  + exact: Hgoodprob.
  + exact: (additiveErrorOptSeqKernel_event contL contR mid post ε' Hcont).
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
exact: additiveErrorOptSeqRule.
Qed.

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
Proof.
move=> [_ Hae] Hpre.
move: (Hae memL memR xL xR Hpre)=> [d [Hd Hpost]].
set outL := Pr_code (progL xL) memL.
set outR := Pr_code (progR xR) memR.
pose strip (out : option (out_t * heap)) : option out_t := omap fst out.
pose project (xy : option (out_t * heap) * option (out_t * heap)) :=
  (strip xy.1, strip xy.2).
pose d' := dmargin project d.
have HdL : dmargin fst d =1 complete outL.
  move: Hd=> [HdL _] z.
  by rewrite -HdL.
have HdR : dmargin snd d =1 complete outR.
  move: Hd=> [_ HdR] z.
  by rewrite -HdR.
have Hd'L :
    dmargin fst d' =1 complete (dmargin fst outL).
  move=> z.
  rewrite /d'.
  rewrite (dmargin_comp fst project d z).
  rewrite -(dmargin_comp strip fst d z).
  rewrite (dmargin_ext strip _ _ HdL z).
  rewrite /strip.
  exact: dmargin_omap_complete.
have Hd'R :
    dmargin snd d' =1 complete (dmargin fst outR).
  move=> z.
  rewrite /d'.
  rewrite (dmargin_comp snd project d z).
  rewrite -(dmargin_comp strip snd d z).
  rewrite (dmargin_ext strip _ _ HdR z).
  rewrite /strip.
  exact: dmargin_omap_complete.
have Hpost' :
    \P_[d'] (fun xy => eq_op xy.1 xy.2) >= 1 - ε.
  apply: (le_trans Hpost).
  rewrite /d' pr_dmargin.
  apply: subset_pr=> xy Hxy.
  case: xy Hxy=> outL' outR' /= Hxy.
  rewrite /lift_loss_post /=.
  case: outL' Hxy=> [[yL memL']|] //= Hxy.
  case: outR' Hxy=> [[yR memR']|] //= Hxy.
have Hcomplete :
    total_variation (complete (dmargin fst outL))
                    (complete (dmargin fst outR)) <= ε.
  apply: (exact_coupling_eq_pr_total_variation
    d' (complete (dmargin fst outL)) (complete (dmargin fst outR)) ε).
  - exact: complete_dweight.
  - exact: complete_dweight.
  - exact: Hd'L.
  - exact: Hd'R.
  - exact: Hpost'.
exact: (le_trans (total_variation_complete_ge
  (dmargin fst outL) (dmargin fst outR)) Hcomplete).
Qed.
