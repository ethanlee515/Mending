(* RHL with Pythagorean Errors and explicit divergence mass. *)

From Stdlib Require Import Unicode.Utf8.
From extructures Require Import ord fset fmap.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals distr ssrZ realseq realsum exp lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Crypt Require Import ChoiceAsOrd Couplings StateTransformingLaxMorph.
From SSProve.Crypt Require Import Axioms StateTransfThetaDens.
From SSProve.Crypt Require Import choice_type fmap_extra SubDistr.
From SSProve.Crypt.nominal Require Import Pr.
From SSProve Require Import pkg_core_definition pkg_advantage pkg_composition
  pkg_notation.
From Mending.NextMessage Require Import Trace.
From Mending.Probability.KL Require Import Core.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras TupleExtras.
From Mending.LibExtras.SSProveExtras Require Import DiscreteGaussian.
From Mending.Probability Require Import Ae OutputHeap PythSeq.
From Mending.Probability.KL Require Import Pyth.
From Mending.ProgramLogics Require Import Ae Hoare.
Local Open Scope AeNotations.
Local Open Scope HoareNotations.

Import PackageNotation.
Import pkg_heap.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope package_scope.
Local Open Scope ring_scope.

Definition pythJudgment
  {ℓ : nat}
  {inL_t inR_t out_t : choice_type}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :=
  (forall i : 'I_(ℓ.+1), 0 <= tnth s i) /\
  ∀ memL memR xL xR, pre ((xL, memL), (xR, memR)) →
  exists
  (P Q : {distr ((ℓ.+1).-tuple (option (nat * heap))) / R}),
  let outL := Pr_code (progL xL) memL in
  let outR := Pr_code (progR xR) memR in
  pythDist P Q s /\
  dmargin (fun omega => tnth omega ord_max) P
    =1 complete_output_heap outL /\
  dmargin (fun omega => tnth omega ord_max) Q
    =1 complete_output_heap outR /\
  (forall x, x \in dinsupp outL -> post x) /\
  (forall x, x \in dinsupp outR -> post x).

Definition pythClosedJudgment
  {ℓ : nat}
  {out_t : choice_type}
  (progL : raw_code out_t)
  (progR : raw_code out_t)
  (pre : pred (heap * heap))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :=
  pythJudgment
    (fun _ : 'unit => progL)
    (fun _ : 'unit => progR)
    (fun inps =>
      let '((_, memL), (_, memR)) := inps in
      pre (memL, memR))
    post s.

Declare Scope PythNotations.
Local Open Scope PythNotations.

Notation "⊨Pyth ⦃ pre ⦄ progL ≈( s ) progR ⦃ post ⦄" :=
  (pythJudgment progL progR pre post s)
  : PythNotations.

Notation "⊨PythC ⦃ pre ⦄ progL ≈( s ) progR ⦃ post ⦄" :=
  (pythClosedJudgment progL progR pre post s)
  : PythNotations.

Notation "⊨Pyth1 ⦃ pre ⦄ progL ≈( eps ) progR ⦃ post ⦄" :=
  (pythJudgment progL progR pre post [tuple eps])
  : PythNotations.

Definition sampleRaw {out_t : choice_type} (D : {distr out_t / R})
    : raw_code out_t :=
  x <$ (existT _ out_t D) ;;
  ret x.

Lemma sampleRawE {out_t : choice_type} (D : {distr out_t / R}) mem :
  Pr_code (sampleRaw D) mem =1 dmargin (fun y => (y, mem)) D.
Proof.
move=> y.
rewrite /sampleRaw Pr_code_sample dmarginE.
apply: eq_in_dlet; last by [].
move=> x _ z.
by rewrite Pr_code_ret.
Qed.

Lemma dmargin_comp
    {A B C : choice_type} (f : B -> C) (g : A -> B)
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

Lemma complete_ext {A : choice_type} (D E : {distr A / R}) :
  D =1 E ->
  complete D =1 complete E.
Proof.
move=> HDE [x|].
- by rewrite !completeE /= HDE.
rewrite !completeE /=.
have Hdweight : dweight D = dweight E.
  exact: (pr_ext D E predT HDE).
by rewrite Hdweight.
Qed.

Lemma dmargin_some_complete
    {A B : choice_type} (f : A -> B) (D : {distr A / R}) :
  dweight D = 1 ->
  dmargin (fun x => Some (f x)) D =1 complete (dmargin f D).
Proof.
move=> HD [y|].
- rewrite completeE /= !dmargin_psumE.
  apply/eq_psum=> x.
  by rewrite /=.
rewrite completeE /= dmargin_psumE.
have -> : psum (fun x : A => (Some (f x) == None)%:R * D x) = 0.
  apply/psum_eq0=> x.
  by rewrite mul0r.
by rewrite dmargin_dweight HD subrr.
Qed.

Lemma complete_output_heap_sampleRawE
    {out_t : choice_type} (D : {distr out_t / R}) mem :
  dweight D = 1 ->
  dmargin (fun y => Some (pack_output_heap (y, mem))) D =1
    complete_output_heap (Pr_code (sampleRaw D) mem).
Proof.
move=> HD z.
rewrite /complete_output_heap.
rewrite (dmargin_some_complete (fun y => pack_output_heap (y, mem)) D HD z).
apply: complete_ext=> packed.
rewrite (dmargin_ext (@pack_output_heap out_t)
  (Pr_code (sampleRaw D) mem)
  (dmargin (fun y => (y, mem)) D)
  (sampleRawE D mem) packed).
by rewrite (dmargin_comp (@pack_output_heap out_t)
  (fun y => (y, mem)) D packed).
Qed.

Lemma klSampRule
  {inL_t inR_t : choice_type} {out_t : choice_type}
  (DL : inL_t -> {distr out_t / R})
  (DR : inR_t -> {distr out_t / R})
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (out_t * heap))
  (ε : R) :
  0 <= ε ->
  (forall memL memR xL xR,
    pre ((xL, memL), (xR, memR)) -> memL = memR) ->
  (forall xL xR, finite_kl (DL xL) (DR xR)) ->
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
Proof.
move=> Heps Hsame Hfin HmassL HmassR Hkl HpostL HpostR.
split; first by move=> i; rewrite [i]ord1.
move=> memL memR xL xR Hpre.
have Hmem : memL = memR := Hsame memL memR xL xR Hpre.
subst memR.
pose encL := dmargin (fun y => Some (pack_output_heap (y, memL))) (DL xL).
pose encR := dmargin (fun y => Some (pack_output_heap (y, memL))) (DR xR).
pose P := dmargin (@singleton_pyth_trace (option (nat * heap))) encL.
pose Q := dmargin (@singleton_pyth_trace (option (nat * heap))) encR.
exists P, Q.
have Hfin_enc : finite_kl encL encR.
  exact: finite_kl_dmargin.
have Hkl_enc : δ_KL encL encR <= ε.
  apply: (le_trans (kl_dmargin_data_processing
    (fun y => Some (pack_output_heap (y, memL))) (DL xL) (DR xR)
    (finite_kl_absolute_continuous _ _ (Hfin xL xR)))).
  exact: (Hkl memL memL xL xR Hpre).
split.
- apply: pythDist_kl_singleton.
  + exact: Heps.
  + exact: Hfin_enc.
  + by rewrite /encL dmargin_dweight.
  + by rewrite /encR dmargin_dweight.
  + exact: Hkl_enc.
split.
- move=> z.
  rewrite [ord_max]ord1.
  rewrite /P dmargin_singleton_pyth_trace_final /encL.
  exact: (complete_output_heap_sampleRawE (DL xL) memL (HmassL xL) z).
split.
- move=> z.
  rewrite [ord_max]ord1.
  rewrite /Q dmargin_singleton_pyth_trace_final /encR.
  exact: (complete_output_heap_sampleRawE (DR xR) memL (HmassR xR) z).
split.
- move=> y Hy.
  have HyD : y \in dinsupp (dmargin (fun z => (z, memL)) (DL xL)).
    by rewrite in_dinsupp -(sampleRawE (DL xL) memL y) -in_dinsupp.
  rewrite dmarginE in HyD.
  have [x Hx Hunit] := dinsupp_dlet HyD.
  have -> : y = (x, memL) by exact: (in_dunit Hunit).
  exact: (HpostL memL memL xL xR x Hpre Hx).
- move=> y Hy.
  have HyD : y \in dinsupp (dmargin (fun z => (z, memL)) (DR xR)).
    by rewrite in_dinsupp -(sampleRawE (DR xR) memL y) -in_dinsupp.
  rewrite dmarginE in HyD.
  have [x Hx Hunit] := dinsupp_dlet HyD.
  have -> : y = (x, memL) by exact: (in_dunit Hunit).
  exact: (HpostR memL memL xL xR x Hpre Hx).
Qed.

Lemma klDgRule
  (centerL centerR : chInt)
  (stdev ε : R)
  (pre : pred ((chUnit * heap) * (chUnit * heap)))
  (post : pred (chInt * heap)) :
  0 < stdev ->
  ((int_of_Z centerR - int_of_Z centerL)%:~R) ^+ 2 / (2 * stdev ^ 2) <= ε ->
  (forall memL memR,
    pre ((tt, memL), (tt, memR)) -> memL = memR) ->
  (forall memL memR,
    pre ((tt, memL), (tt, memR)) ->
    forall y, y \in dinsupp (ssp_dg centerL stdev) -> post (y, memL)) ->
  (forall memL memR,
    pre ((tt, memL), (tt, memR)) ->
    forall y, y \in dinsupp (ssp_dg centerR stdev) -> post (y, memR)) ->
  ⊨Pyth ⦃ pre ⦄ (fun _ : chUnit => sampleRaw (ssp_dg centerL stdev)) ≈( [tuple ε] )
    (fun _ : chUnit => sampleRaw (ssp_dg centerR stdev)) ⦃ post ⦄.
Proof.
move=> Hstdev Hkl_bound Hsame HpostL HpostR.
have Hfin := ssp_dg_finite_kl centerL centerR stdev Hstdev.
apply: (klSampRule (fun _ : chUnit => ssp_dg centerL stdev)
                   (fun _ : chUnit => ssp_dg centerR stdev)
                   pre post ε).
- have Hkl := kl_ssp_dg centerL centerR stdev Hstdev.
  have Hnonneg : 0 <= δ_KL (ssp_dg centerL stdev) (ssp_dg centerR stdev) :=
    kl_nonnegative _ _ (finite_kl_absolute_continuous _ _ Hfin)
      (ssp_dg_mass1 centerL stdev Hstdev).
  lra.
- move=> memL memR [] [].
  exact: Hsame.
- move=> [] [].
  exact: Hfin.
- move=> [].
  exact: ssp_dg_mass1.
- move=> [].
  exact: ssp_dg_mass1.
- move=> memL memR [] [] Hpre.
  have Hkl := kl_ssp_dg centerL centerR stdev Hstdev.
  lra.
- move=> memL memR [] [] y Hpre Hy.
  exact: (HpostL memL memR Hpre y Hy).
- move=> memL memR [] [] y Hpre Hy.
  exact: (HpostR memL memR Hpre y Hy).
Qed.

Lemma pythReflRule
  {ℓ : nat}
  {in_t out_t : choice_type}
  (prog : in_t -> raw_code out_t)
  (pre : pred ((in_t * heap) * (in_t * heap)))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :
  (forall i : 'I_(ℓ.+1), 0 <= tnth s i) ->
  (forall memL memR xL xR,
    pre ((xL, memL), (xR, memR)) -> xL = xR /\ memL = memR) ->
  (forall mem x y,
    pre ((x, mem), (x, mem)) ->
    y \in dinsupp (Pr_code (prog x) mem) ->
    post y) ->
  ⊨Pyth ⦃ pre ⦄ prog ≈( s ) prog ⦃ post ⦄.
Proof.
move=> Hs Hpre_eq Hpost.
split; first exact: Hs.
move=> memL memR xL xR Hpre.
have [Hx Hmem] := Hpre_eq memL memR xL xR Hpre.
subst xL.
subst memL.
set out := Pr_code (prog xR) memR.
pose lift_final (z : option (nat * heap)) :
    (ℓ.+1).-tuple (option (nat * heap)) := [tuple z | i < ℓ.+1].
pose P := dmargin lift_final (complete_output_heap out).
exists P, P.
split.
  apply: pythDist_refl=> //.
  rewrite /P dmargin_dweight.
  exact: complete_dweight.
split.
  move=> z.
  rewrite /P __deprecated__dmargin_dlet.
  rewrite -(dlet_dunit_id (complete_output_heap out) z).
  apply: eq_in_dlet=> // y _ z'.
  by rewrite dmargin_dunit /lift_final tnth_mktuple.
split.
  move=> z.
  rewrite /P __deprecated__dmargin_dlet.
  rewrite -(dlet_dunit_id (complete_output_heap out) z).
  apply: eq_in_dlet=> // y _ z'.
  by rewrite dmargin_dunit /lift_final tnth_mktuple.
split.
- move=> y Hy.
  exact: (Hpost memR xR y Hpre Hy).
- move=> y Hy.
  exact: (Hpost memR xR y Hpre Hy).
Qed.

Lemma pythConseqRule
  {ℓ : nat}
  {inL_t inR_t out_t : choice_type}
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
Proof.
move=> Hpre Hpost Hs [Hs_nonneg Hpyth].
split.
- move=> i.
  exact: (le_trans (Hs_nonneg i) (Hs i)).
- move=> memL memR xL xR Hpre'.
  have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
    Hpyth memL memR xL xR (Hpre _ Hpre').
  exists P, Q.
  split.
  - move: Hdist=> [Heps [HP [HQ Hcond]]].
    split.
      move=> i.
      exact: (le_trans (Heps i) (Hs i)).
    split; first exact: HP.
    split; first exact: HQ.
    move=> i a.
    have [Hcond_fin Hcond_bound] := Hcond i a.
    split; first exact: Hcond_fin.
    exact: (le_trans Hcond_bound (Hs i)).
  split; first exact: HmarginL.
  split; first exact: HmarginR.
  split.
  - move=> y Hy.
    exact: Hpost (HpostL y Hy).
  - move=> y Hy.
    exact: Hpost (HpostR y Hy).
Qed.

Lemma MicciancioWalterRule
  {ℓ : nat}
  {inL_t inR_t out_t : choice_type}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :
  ⊨Pyth ⦃ pre ⦄ progL ≈( s ) progR ⦃ post ⦄ ->
  let delta := pythagorean_tv_bound s in
  ⊨AE_opt ⦃ pre ⦄ progL ≈( delta ) progR ⦃
    fun outs =>
    let '(outL, outR) := outs in
    outL == outR ⦄.
Proof.
move=> [Hs_nonneg Hpyth].
apply: additiveErrorCompletedOutputHeapTvdEqRule.
- rewrite /pythagorean_tv_bound.
  exact: Num.Theory.sqrtr_ge0.
- move=> memL memR xL xR Hpre.
  have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
    Hpyth memL memR xL xR Hpre.
  pose outL := Pr_code (progL xL) memL.
  pose outR := Pr_code (progR xR) memR.
  pose final (omega : (ℓ.+1).-tuple (option (nat * heap))) :=
    tnth omega ord_max.
  have Htv := pythDist_final_total_variation P Q s Hdist.
  have Htv_eq :
      total_variation (complete_output_heap outL) (complete_output_heap outR) =
      total_variation (dmargin final P) (dmargin final Q).
    rewrite /total_variation.
    congr (_ * _).
    apply/eq_sum=> y.
    by rewrite -(HmarginL y) -(HmarginR y).
  rewrite Htv_eq.
  exact: Htv.
Qed.

Lemma pythSeqRule
  {ℓ1 ℓ2 : nat}
  {inL_t inR_t mid_t out_t : choice_type}
  (progL : inL_t -> raw_code mid_t)
  (progR : inR_t -> raw_code mid_t)
  (contL : mid_t -> raw_code out_t)
  (contR : mid_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R) :
  ⊨Pyth ⦃ pre ⦄ progL ≈( s1 ) progR ⦃ mid ⦄ ->
  ⊨Pyth ⦃
    fun xs =>
      let '((xL, memL), (xR, memR)) := xs in
      (xL == xR) && (memL == memR) && mid (xL, memL)
  ⦄ contL ≈( s2 ) contR ⦃ post ⦄ ->
  ⊨Pyth ⦃ pre ⦄
    (fun xL => yL ← progL xL ;; contL yL)
    ≈( cat_tuple s1 s2 )
    (fun xR => yR ← progR xR ;; contR yR)
  ⦃ post ⦄.
Proof.
move=> [Hs1 Hpyth1] [Hs2 Hpyth2].
split.
- move=> i.
  apply: (cat_tuple_nonneg s1 s2 i).
  + exact: Hs1.
  + exact: Hs2.
- move=> memL memR xL xR Hpre.
have [P0 [Q0 [Hdist0 [HmarginL0 [HmarginR0 [HmidL HmidR]]]]]] :=
  Hpyth1 memL memR xL xR Hpre.
set ML := Pr_code (progL xL) memL.
set MR := Pr_code (progR xR) memR.
set KL := fun y : mid_t * heap => Pr_code (contL y.1) y.2.
set KR := fun y : mid_t * heap => Pr_code (contR y.1) y.2.
have Hcont :
    forall y, mid y ->
      exists (P Q : {distr ((ℓ2.+1).-tuple
          (option (nat * heap))) / R}),
        pythDist P Q s2 /\
        dmargin (fun omega => tnth omega ord_max) P
          =1 completed_output_heap (KL y) /\
        dmargin (fun omega => tnth omega ord_max) Q
          =1 completed_output_heap (KR y) /\
        (forall x, x \in dinsupp (KL y) -> post x) /\
        (forall x, x \in dinsupp (KR y) -> post x).
  move=> [y mem] Hy.
  have Hpre_cont :
      (let '((xL0, memL0), (xR0, memR0)) :=
          ((y, mem), (y, mem)) in
        (xL0 == xR0) && (memL0 == memR0) && mid (xL0, memL0)).
    by rewrite !eqxx Hy.
  have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
    Hpyth2 mem mem y y Hpre_cont.
  by exists P, Q.
have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
  completedPythDist_bind_pyth_kernel ML MR KL KR mid post s1 s2 P0 Q0
    Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hs2 Hcont.
exists P, Q.
rewrite !Pr_code_bind.
split; first exact: Hdist.
split; first exact: HmarginL.
split; first exact: HmarginR.
by split.
Qed.

Lemma pythAeSeqRule
  {ℓ : nat}
  {inL_t inR_t mid_t out_t : choice_type}
  (progL : inL_t -> raw_code mid_t)
  (progR : inR_t -> raw_code mid_t)
  (cont : mid_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :
  ⊨Pyth ⦃ pre ⦄ progL ≈( s ) progR ⦃ mid ⦄ ->
  ⊨Hoare ⦃ mid ⦄ cont ⦃ post ⦄ ->
  ⊨Pyth ⦃ pre ⦄
    (fun xL => yL ← progL xL ;; cont yL)
    ≈( cat_tuple s [tuple 0] )
    (fun xR => yR ← progR xR ;; cont yR)
  ⦃ post ⦄.
Proof.
move=> Hpyth Hhoare.
apply: (pythSeqRule progL progR cont cont pre mid post s [tuple 0]
  Hpyth).
apply: pythReflRule.
- by move=> i; rewrite [i]ord1.
- move=> memL memR xL xR Hpre.
  move/andP: Hpre=> [/andP [/eqP -> /eqP ->] _].
  by split.
- move=> mem x y Hpre Hy.
  move/andP: Hpre=> [_ Hmid].
  exact: (Hhoare x mem Hmid y Hy).
Qed.

Lemma pythHoareSeqRule
  {ℓ : nat}
  {in_t mid_t out_t : choice_type}
  (prog : in_t -> raw_code mid_t)
  (contL : mid_t -> raw_code out_t)
  (contR : mid_t -> raw_code out_t)
  (pre0 : pred (in_t * heap))
  (pre : pred ((in_t * heap) * (in_t * heap)))
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :
  (forall memL memR xL xR,
    pre ((xL, memL), (xR, memR)) ->
      xL = xR /\ memL = memR /\ pre0 (xL, memL)) ->
  ⊨Hoare ⦃ pre0 ⦄ prog ⦃ mid ⦄ ->
  ⊨Pyth ⦃
    fun xs =>
      let '((xL, memL), (xR, memR)) := xs in
      (xL == xR) && (memL == memR) && mid (xL, memL)
  ⦄ contL ≈( s ) contR ⦃ post ⦄ ->
  ⊨Pyth ⦃ pre ⦄
    (fun x => y ← prog x ;; contL y)
    ≈( cat_tuple [tuple 0] s )
    (fun x => y ← prog x ;; contR y)
  ⦃ post ⦄.
Proof.
move=> Hpre_eq Hhoare Hpyth.
apply: (pythSeqRule prog prog contL contR pre mid post [tuple 0] s _ Hpyth).
apply: pythReflRule.
- by move=> i; rewrite [i]ord1.
- move=> memL memR xL xR Hpre.
  have [Hx [Hmem _]] := Hpre_eq memL memR xL xR Hpre.
  by split.
- move=> mem x y Hpre Hy.
  have [_ [_ Hpre0]] := Hpre_eq mem mem x x Hpre.
  exact: (Hhoare x mem Hpre0 y Hy).
Qed.

Lemma pythClosedHoareSeqRule
  {ℓ : nat}
  {mid_t out_t : choice_type}
  (prog : raw_code mid_t)
  (contL : mid_t -> raw_code out_t)
  (contR : mid_t -> raw_code out_t)
  (pre0 : pred heap)
  (pre : pred (heap * heap))
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :
  (forall memL memR, pre (memL, memR) -> memL = memR /\ pre0 memL) ->
  ⊨Hoare ⦃ fun in_mem => pre0 in_mem.2 ⦄
    (fun _ : 'unit => prog) ⦃ mid ⦄ ->
  ⊨Pyth ⦃
    fun xs =>
      let '((xL, memL), (xR, memR)) := xs in
      (xL == xR) && (memL == memR) && mid (xL, memL)
  ⦄ contL ≈( s ) contR ⦃ post ⦄ ->
  ⊨PythC ⦃ pre ⦄
    (y ← prog ;; contL y)
    ≈( cat_tuple [tuple 0] s )
    (y ← prog ;; contR y)
  ⦃ post ⦄.
Proof.
move=> Hpre_eq Hhoare Hpyth.
rewrite /pythClosedJudgment.
apply: (pythHoareSeqRule
  (fun _ : 'unit => prog) contL contR
  (fun in_mem => pre0 in_mem.2)
  (fun inps =>
    let '((_, memL), (_, memR)) := inps in pre (memL, memR))
  mid post s _ Hhoare Hpyth).
move=> memL memR [] [] Hpre.
have [Hmem Hpre0] := Hpre_eq memL memR Hpre.
split; first done.
by split.
Qed.
