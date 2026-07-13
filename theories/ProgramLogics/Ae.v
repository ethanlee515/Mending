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

Definition clean_coupling {A1 A2 : choiceType}
    (d : {distr (A1 * A2) / R})
    (c1 : {distr A1 / R}) (c2 : {distr A2 / R}) : Prop :=
  dmargin fst d =1 c1 /\ dmargin snd d =1 c2.

Definition additiveErrorJudgment
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
    ∃ d, clean_coupling d (complete out1) (complete out2) ∧
      \P_[ d ] post >= 1 - ε.

Declare Scope AeNotations.
Local Open Scope AeNotations.

Notation "⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃ post ⦄" :=
  (additiveErrorJudgment progL progR pre post ε) : AeNotations.

Definition additiveErrorRawJudgment
  {inL_t inR_t outL_t outR_t : ord_choiceType}
  (progL : inL_t -> raw_code outL_t)
  (progR : inR_t -> raw_code outR_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred ((outL_t * heap) * (outR_t * heap)))
  (ε : R) : Prop :=
  ⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃ lift_loss_post post ⦄.

Notation "⊨AE_raw ⦃ pre ⦄ progL ≈( ε ) progR ⦃ post ⦄" :=
  (additiveErrorRawJudgment progL progR pre post ε) : AeNotations.

Lemma additiveErrorEpsNonneg
  {inL_t inR_t outL_t outR_t : ord_choiceType}
  (progL : inL_t -> raw_code outL_t)
  (progR : inR_t -> raw_code outR_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (option (outL_t * heap) * option (outR_t * heap)))
  (ε : R) :
  ⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃ post ⦄ ->
  0 <= ε.
Proof.
by move=> [Heps _].
Qed.

Lemma dmargin_comp
    {A B C : choiceType} (f : B -> C) (g : A -> B)
    (D : {distr A / R}) :
  dmargin f (dmargin g D) =1 dmargin (fun x => f (g x)) D.
Proof.
move=> z.
rewrite dmarginE dmargin_dlet_partition.
apply: eq_in_dlet=> // x _ z'.
by rewrite dmargin_dunit.
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

Definition same_output_heap_opt {out_t : choice_type}
    (outs : option (out_t * heap) * option (out_t * heap)) : bool :=
  outs.1 == outs.2.

Lemma additiveErrorSameOutputTvdEqRule
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
  ⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃ same_output_heap_opt ⦄.
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
  + exact: HdL.
  + exact: HdR.
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
  ⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃
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
  + exact: HdL.
  + exact: HdR.
- rewrite (eq_pr (B := fun xy => xy.1 == xy.2)).
    exact: Hprob.
  by case=> outL outR.
Qed.

Lemma additiveErrorSameOutputTvBound
  {inL_t inR_t out_t : choice_type}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (ε : R) memL memR xL xR :
  ⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃ same_output_heap_opt ⦄ ->
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

Lemma additiveErrorSameOutputTriangleRule
  {in_t out_t : choice_type}
  (progL progM progR : in_t -> raw_code out_t)
  (pre : pred ((in_t * heap) * (in_t * heap)))
  (ε ε' : R) :
  (forall memL memR xL xR,
    pre ((xL, memL), (xR, memR)) -> xL = xR /\ memL = memR) ->
  ⊨AE ⦃ pre ⦄ progL ≈( ε ) progM ⦃ same_output_heap_opt ⦄ ->
  ⊨AE ⦃ pre ⦄ progM ≈( ε' ) progR ⦃ same_output_heap_opt ⦄ ->
  ⊨AE ⦃ pre ⦄ progL ≈( ε + ε' ) progR ⦃ same_output_heap_opt ⦄.
Proof.
move=> Hsame HLM HMR.
apply: additiveErrorSameOutputTvdEqRule.
- have Heps := additiveErrorEpsNonneg _ _ _ _ _ HLM.
  have Heps' := additiveErrorEpsNonneg _ _ _ _ _ HMR.
  lra.
- move=> memL memR xL xR Hpre.
  have [Hx Hmem] := Hsame memL memR xL xR Hpre.
  subst xR; subst memR.
  have HtvLM :=
    additiveErrorSameOutputTvBound
      progL progM pre ε memL memL xL xL HLM Hpre.
  have HtvMR :=
    additiveErrorSameOutputTvBound
      progM progR pre ε' memL memL xL xL HMR Hpre.
  have Htri := total_variation_triangle
    (complete (Pr_code (progL xL) memL))
    (complete (Pr_code (progM xL) memL))
    (complete (Pr_code (progR xL) memL)).
  apply: (le_trans Htri).
  lra.
Qed.

Lemma additiveErrorRawTvdEqPostTotalRule
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
  ⊨AE_raw ⦃ pre ⦄ progL ≈( ε ) progR ⦃
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
  + move=> z.
    rewrite (dmargin_comp fst lift d z).
    change (dmargin (fun xy : (out_t * heap) * (out_t * heap) =>
      Some xy.1) d z = complete outL z).
    rewrite -(dmargin_comp (@Some (out_t * heap)) fst d z).
    rewrite (dmargin_ext (@Some (out_t * heap)) _ _ HdL z).
    exact: dmargin_some.
  + move=> z.
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

Lemma additiveErrorRawConseqRule
  {inL_t inR_t outL_t outR_t : ord_choiceType}
  (progL : inL_t -> raw_code outL_t)
  (progR : inR_t -> raw_code outR_t)
  (pre pre' : pred ((inL_t * heap) * (inR_t * heap)))
  (post post' : pred ((outL_t * heap) * (outR_t * heap)))
  (ε ε' : R) :
  (forall inps, pre' inps -> pre inps) ->
  (forall outs, post outs -> post' outs) ->
  ε <= ε' ->
  ⊨AE_raw ⦃ pre ⦄ progL ≈( ε ) progR ⦃ post ⦄ ->
  ⊨AE_raw ⦃ pre' ⦄ progL ≈( ε' ) progR ⦃ post' ⦄.
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

Lemma additiveErrorConseqRule
  {inL_t inR_t outL_t outR_t : ord_choiceType}
  (progL : inL_t -> raw_code outL_t)
  (progR : inR_t -> raw_code outR_t)
  (pre pre' : pred ((inL_t * heap) * (inR_t * heap)))
  (post post' : pred (option (outL_t * heap) * option (outR_t * heap)))
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
have Hthreshold : 1 - ε' <= 1 - ε by lra.
exact: (le_trans Hthreshold (le_trans Hprob Hmono)).
Qed.

Definition additiveErrorSeqKernel
  {midL_t midR_t outL_t outR_t : ord_choiceType}
  (contL : midL_t -> raw_code outL_t)
  (contR : midR_t -> raw_code outR_t)
  (mid : pred ((midL_t * heap) * (midR_t * heap)))
  (post : pred (option (outL_t * heap) * option (outR_t * heap)))
  (ε' : R)
  (Hcont : forall memL memR yL yR,
      mid ((yL, memL), (yR, memR)) ->
      exists d,
        clean_coupling d
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

Lemma additiveErrorSeqKernel_margins
  {midL_t midR_t outL_t outR_t : ord_choiceType}
  (contL : midL_t -> raw_code outL_t)
  (contR : midR_t -> raw_code outR_t)
  (mid : pred ((midL_t * heap) * (midR_t * heap)))
  (post : pred (option (outL_t * heap) * option (outR_t * heap)))
  (ε' : R)
  (Hcont : forall memL memR yL yR,
      mid ((yL, memL), (yR, memR)) ->
      exists d,
        clean_coupling d
          (complete (Pr_code (contL yL) memL))
          (complete (Pr_code (contR yR) memR)) /\
        \P_[ d ] post >= 1 - ε')
  (xy : option (midL_t * heap) * option (midR_t * heap)) :
  let KL ymem := Pr_code (contL ymem.1) ymem.2 in
  let KR ymem := Pr_code (contR ymem.1) ymem.2 in
  clean_coupling (additiveErrorSeqKernel contL contR mid post ε' Hcont xy)
    (complete_bind_kernel KL xy.1)
    (complete_bind_kernel KR xy.2).
Proof.
case: xy=> [[ymemL|] [ymemR|]] /=.
- case: ymemL=> yL memL; case: ymemR=> yR memR /=.
  rewrite /additiveErrorSeqKernel /=.
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
    * exact: HdL.
    * exact: HdR.
- case: ymemL=> yL memL.
  have [HdL HdR] :=
    complete_bind_fallback_coupling_margins
      (fun ymem : midL_t * heap => Pr_code (contL ymem.1) ymem.2)
      (fun ymem : midR_t * heap => Pr_code (contR ymem.1) ymem.2)
      (Some (yL, memL), None).
  split.
  - exact: HdL.
  - exact: HdR.
- case: ymemR=> yR memR.
  have [HdL HdR] :=
    complete_bind_fallback_coupling_margins
      (fun ymem : midL_t * heap => Pr_code (contL ymem.1) ymem.2)
      (fun ymem : midR_t * heap => Pr_code (contR ymem.1) ymem.2)
      (None, Some (yR, memR)).
  split.
  - exact: HdL.
  - exact: HdR.
- have [HdL HdR] :=
    complete_bind_fallback_coupling_margins
      (fun ymem : midL_t * heap => Pr_code (contL ymem.1) ymem.2)
      (fun ymem : midR_t * heap => Pr_code (contR ymem.1) ymem.2)
      (None, None).
  split.
  - exact: HdL.
  - exact: HdR.
Qed.

Definition additiveErrorSeqGood
  {midL_t midR_t : ord_choiceType}
  (mid : pred ((midL_t * heap) * (midR_t * heap)))
  (xy : option (midL_t * heap) * option (midR_t * heap)) : bool :=
  match xy with
  | (Some (yL, memL), Some (yR, memR)) =>
      mid ((yL, memL), (yR, memR))
  | _ => false
  end.

Lemma additiveErrorSeqKernel_event
  {midL_t midR_t outL_t outR_t : ord_choiceType}
  (contL : midL_t -> raw_code outL_t)
  (contR : midR_t -> raw_code outR_t)
  (mid : pred ((midL_t * heap) * (midR_t * heap)))
  (post : pred (option (outL_t * heap) * option (outR_t * heap)))
  (ε' : R)
  (Hcont : forall memL memR yL yR,
      mid ((yL, memL), (yR, memR)) ->
      exists d,
        clean_coupling d
          (complete (Pr_code (contL yL) memL))
          (complete (Pr_code (contR yR) memR)) /\
        \P_[ d ] post >= 1 - ε')
  xy :
  additiveErrorSeqGood mid xy ->
  \P_[additiveErrorSeqKernel contL contR mid post ε' Hcont xy] post >=
    1 - ε'.
Proof.
case: xy=> [[ymemL|] [ymemR|]] /=.
- case: ymemL=> yL memL; case: ymemR=> yR memR /= Hgood.
  rewrite /additiveErrorSeqKernel /=.
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
  clean_coupling d PL PR ->
  (forall xy, clean_coupling (K xy) (KL xy.1) (KR xy.2)) ->
  clean_coupling (\dlet_(xy <- d) K xy)
    (\dlet_(x <- PL) KL x)
    (\dlet_(y <- PR) KR y).
Proof.
move=> [HdL HdR] HK.
split.
- move=> z.
  rewrite dmargin_dlet_partition.
  transitivity ((\dlet_(xy <- d) KL xy.1) z).
  + apply: eq_in_dlet=> // xy _ z'.
    have [HKL _] := HK xy.
    by rewrite -HKL.
  + rewrite -(dlet_dmargin_partition d fst KL z).
    by apply: eq_in_dlet=> // x _ z'; rewrite HdL.
- move=> z.
  rewrite dmargin_dlet_partition.
  transitivity ((\dlet_(xy <- d) KR xy.2) z).
  + apply: eq_in_dlet=> // xy _ z'.
    have [_ HKR] := HK xy.
    by rewrite -HKR.
  + rewrite -(dlet_dmargin_partition d snd KR z).
    by apply: eq_in_dlet=> // y _ z'; rewrite HdR.
Qed.

Lemma additiveErrorSeqRule
  {inL_t inR_t midL_t midR_t outL_t outR_t : ord_choiceType}
  (progL : inL_t -> raw_code midL_t)
  (progR : inR_t -> raw_code midR_t)
  (contL : midL_t -> raw_code outL_t)
  (contR : midR_t -> raw_code outR_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (mid : pred ((midL_t * heap) * (midR_t * heap)))
  (post : pred (option (outL_t * heap) * option (outR_t * heap)))
  (ε ε' : R) :
  ⊨AE_raw ⦃ pre ⦄ progL ≈( ε ) progR ⦃ mid ⦄ ->
  ⊨AE ⦃ mid ⦄ contL ≈( ε' ) contR ⦃ post ⦄ ->
  ⊨AE ⦃ pre ⦄
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
pose K := additiveErrorSeqKernel contL contR mid post ε' Hcont.
exists (\dlet_(xy <- d0) K xy).
split.
- have Hbind := coupling_bind_kernel d0
    (complete (Pr_code (progL xL) memL))
    (complete (Pr_code (progR xR) memR))
    K (complete_bind_kernel KL) (complete_bind_kernel KR)
    Hd0 (additiveErrorSeqKernel_margins contL contR mid post ε' Hcont).
  move: Hbind=> [HL HR].
  split.
  + move=> z.
    rewrite HL.
    rewrite (complete_bind (Pr_code (progL xL) memL) KL z).
    rewrite /KL.
    rewrite Pr_code_bind.
    by [].
  + move=> z.
    rewrite HR.
    rewrite (complete_bind (Pr_code (progR xR) memR) KR z).
    rewrite /KR.
    rewrite Pr_code_bind.
    by [].
- have Hgoodprob :
      \P_[d0] (additiveErrorSeqGood mid) >= 1 - ε.
    rewrite (eq_pr (B := lift_loss_post mid)); first exact: Hmidprob.
    case=> [[ymemL|] [ymemR|]] /=.
    + by case: ymemL=> yL memL0; case: ymemR=> yR memR0.
    + by case: ymemL=> yL memL0.
    + by case: ymemR=> yR memR0.
    + by [].
  apply: (pr_dlet_lower_bound_good d0 K
    (additiveErrorSeqGood mid) post ε ε').
  + exact: Heps.
  + exact: Heps'.
  + exact: Hgoodprob.
  + exact: (additiveErrorSeqKernel_event contL contR mid post ε' Hcont).
Qed.
