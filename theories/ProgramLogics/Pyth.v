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
  - move: Hdist=> [Heps [Hac [HP [HQ Hcond]]]].
    split.
      move=> i.
      exact: (le_trans (Heps i) (Hs i)).
    split; first exact: Hac.
    split; first exact: HP.
    split; first exact: HQ.
    move=> i a.
    exact: (le_trans (Hcond i a) (Hs i)).
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
