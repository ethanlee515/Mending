(* RHL with Pythagorean Errors *)

From Stdlib Require Import Unicode.Utf8.
From extructures Require Import ord fset fmap.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals distr ssrZ realseq realsum.
From mathcomp Require Import lra.
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
From Mending.LibExtras.MathcompExtras Require Import DistrExtras RealTupleExtras.
From Mending.LibExtras.SSProveExtras Require Import ChoiceVector DiscreteGaussian.
From Mending.Probability.KL Require Import Pyth.
From Mending.ProgramLogics Require Import Ae Hoare.
Local Open Scope AeNotations.
Local Open Scope HoareNotations.

Import PackageNotation.
Import pkg_heap.
Local Open Scope package_scope.
Local Open Scope ring_scope.

Definition cons_choice {n : nat}
    (A : choiceType) (X : 'I_n -> choiceType)
    (i : 'I_n.+1) : choiceType :=
  if unlift ord0 i is Some j then X j else A.

Definition pythOmega
  {ℓ : nat} {out_t : ord_choiceType}
  (X : 'I_ℓ -> choiceType) : choiceType :=
  canonical_pythOmega X (out_t * heap)%type.

Definition pythCoord
  {ℓ : nat} {out_t : ord_choiceType}
  (X : 'I_ℓ -> choiceType)
  (i : 'I_ℓ) : pythOmega (out_t := out_t) X -> X i :=
  canonical_pythCoord X (out_t * heap)%type i.

Definition pythFinal
  {ℓ : nat} {out_t : ord_choiceType}
  (X : 'I_ℓ -> choiceType) :
  pythOmega (out_t := out_t) X -> (out_t * heap)%type :=
  canonical_pythFinal X (out_t * heap)%type.

Definition pythJudgment
  {ℓ : nat}
  {inL_t inR_t out_t : ord_choiceType}
  (X : 'I_ℓ -> choiceType)
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :=
  ∀ memL memR xL xR, pre ((xL, memL), (xR, memR)) →
  exists
  (P Q : {distr (pythOmega (out_t := out_t) X) / R}),
  let outL := Pr_code (progL xL) memL in
  let outR := Pr_code (progR xR) memR in
  pythDistWithFinal (pythCoord X) (pythFinal X) P Q s /\
  dmargin (pythFinal X) P =1 outL /\
  dmargin (pythFinal X) Q =1 outR /\
  (forall x, x \in dinsupp outL -> post x) /\
  (forall x, x \in dinsupp outR -> post x).

Declare Scope PythNotations.
Local Open Scope PythNotations.

Notation "⊨Pyth( X ) ⦃ pre ⦄ progL ≈( s ) progR ⦃ post ⦄" :=
  (pythJudgment X progL progR pre post s) : PythNotations.

Notation "⊨Pyth1( X ) ⦃ pre ⦄ progL ≈( eps ) progR ⦃ post ⦄" :=
  (pythJudgment X progL progR pre post [tuple eps] ) : PythNotations.

Definition sampleRaw {out_t : choice_type} (D : {distr out_t / R}) : raw_code out_t :=
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

(*
TODO: Restate the sampling rules for the explicit-witness judgment.

These rules construct their witness space/final map. With [Ω], [X], [coord],
and [final] moved out of the existential in [pythJudgment], the conclusion must
name a fixed witness such as a lifted output/heap space rather than relying on
the old existential package.

Lemma klSampRule
  {inL_t inR_t : ord_choiceType} {out_t : choice_type}
  (DL : inL_t -> {distr out_t / R})
  (DR : inR_t -> {distr out_t / R})
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (out_t * heap))
  (ε : R) :
  0 <= ε ->
  (forall memL memR xL xR,
    pre ((xL, memL), (xR, memR)) -> memL = memR) ->
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
Proof.
move=> Heps Hsame Hac HmassL HmassR Hkl HpostL HpostR.
move=> memL memR xL xR Hpre.
have Hmem : memL = memR := Hsame memL memR xL xR Hpre.
subst memR.
exists out_t, empty_pyth_coord, (fun _ : 'I_0 => fun _ => tt),
  (fun y => (y, memL)), (DL xL), (DR xR).
split.
- apply: pythDistWithFinal_kl_final.
  + by move=> a b [].
  + exact: Heps.
  + exact: Hac.
  + exact: HmassL.
  + exact: HmassR.
  + exact: (Hkl memL memL xL xR Hpre).
split.
- move=> y.
  symmetry.
  exact: sampleRawE.
split.
- move=> y.
  symmetry.
  exact: sampleRawE.
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
apply: (klSampRule (fun _ : chUnit => ssp_dg centerL stdev)
                   (fun _ : chUnit => ssp_dg centerR stdev)
                   pre post ε).
- have Hkl := kl_ssp_dg centerL centerR stdev Hstdev.
  have Hnonneg : 0 <= δ_KL (ssp_dg centerL stdev) (ssp_dg centerR stdev) :=
    kl_nonnegative _ _ (ssp_dg_absolute_continuous centerL centerR stdev Hstdev)
      (ssp_dg_mass1 centerL stdev Hstdev).
  have Hupper : δ_KL (ssp_dg centerL stdev) (ssp_dg centerR stdev) <= ε.
    lra.
  lra.
- move=> memL memR [] [].
  exact: Hsame.
- move=> [] [].
  exact: ssp_dg_absolute_continuous.
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
*)

Lemma MicciancioWalterRule
  {ℓ : nat}
  {inL_t inR_t out_t : ord_choiceType}
  (X : 'I_ℓ -> choiceType)
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :
  ⊨Pyth(X) ⦃ pre ⦄ progL ≈( s ) progR ⦃ post ⦄ ->
  let delta := pythagorean_tv_bound s in
  ⊨AE ⦃ pre ⦄ progL ≈( delta ) progR ⦃
    fun outs =>
      let '((y_1, m_1'), (y_2, m_2')) := outs in
      post (y_1, m_1') && (y_1 == y_2) && (m_1' == m_2')⦄.
Proof.
move=> Hpyth.
apply: (additiveErrorTvdEqPostRule progL progR pre post (pythagorean_tv_bound s)).
- rewrite /pythagorean_tv_bound.
  exact: Num.Theory.sqrtr_ge0.
- move=> memL memR xL xR Hpre.
  have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
    Hpyth memL memR xL xR Hpre.
  pose outL := Pr_code (progL xL) memL.
  pose outR := Pr_code (progR xR) memR.
  have Htv := pythDistWithFinal_total_variation
    (pythCoord X) (pythFinal X) P Q s Hdist.
  have Htv_eq :
      total_variation outL outR =
      total_variation (dmargin (pythFinal X) P) (dmargin (pythFinal X) Q).
    rewrite /total_variation.
    congr (_ * _).
    apply/eq_sum=> y.
    by rewrite -(HmarginL y) -(HmarginR y).
  rewrite Htv_eq.
  exact: Htv.
- move=> memL memR xL xR y Hpre Hy.
  have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
    Hpyth memL memR xL xR Hpre.
  exact: HpostL.
Qed.

Lemma pythConseqRule
  {ℓ : nat}
  {inL_t inR_t out_t : ord_choiceType}
  (X : 'I_ℓ -> choiceType)
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre pre' : pred ((inL_t * heap) * (inR_t * heap)))
  (post post' : pred (out_t * heap))
  (s s' : (ℓ.+1).-tuple R) :
  (forall inps, pre' inps -> pre inps) ->
  (forall outs, post outs -> post' outs) ->
  (forall i : 'I_(ℓ.+1), tnth s i <= tnth s' i) ->
  ⊨Pyth(X) ⦃ pre ⦄ progL ≈( s ) progR ⦃ post ⦄ ->
  ⊨Pyth(X) ⦃ pre' ⦄ progL ≈( s' ) progR ⦃ post' ⦄.
Proof.
move=> Hpre Hpost Hs Hpyth memL memR xL xR Hpre'.
have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
  Hpyth memL memR xL xR (Hpre _ Hpre').
exists P, Q.
split.
- move: Hdist=> [Hsep [Heps [Hac [HP [HQ Hcond]]]]].
  split; first exact: Hsep.
  split.
    move=> i.
    have := Heps i.
    have := Hs i.
    lra.
  split; first exact: Hac.
  split; first exact: HP.
  split; first exact: HQ.
  move=> i a.
  have := Hcond i a.
  have := Hs i.
  lra.
split; first exact: HmarginL.
split; first exact: HmarginR.
split.
- move=> y Hy.
  exact: Hpost (HpostL y Hy).
- move=> y Hy.
  exact: Hpost (HpostR y Hy).
Qed.

Lemma aePythSeqRule
  {ℓ : nat}
  {inL_t inR_t midL_t midR_t out_t : ord_choiceType}
  (X : 'I_ℓ -> choiceType)
  (progL : inL_t -> raw_code midL_t)
  (progR : inR_t -> raw_code midR_t)
  (contL : midL_t -> raw_code out_t)
  (contR : midR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (mid : pred ((midL_t * heap) * (midR_t * heap)))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :
  ⊨AE ⦃ pre ⦄ progL ≈( 0 ) progR ⦃ mid ⦄ ->
  ⊨Pyth(X) ⦃ mid ⦄ contL ≈( s ) contR ⦃ post ⦄ ->
  ⊨Pyth(X) ⦃ pre ⦄
    (fun xL => yL ← progL xL ;; contL yL)
    ≈( s )
    (fun xR => yR ← progR xR ;; contR yR)
  ⦃ post ⦄.
Proof.
move=> [_ Hae] Hpyth memL memR xL xR Hpre.
pose ML := Pr_code (progL xL) memL.
pose MR := Pr_code (progR xR) memR.
pose KL (x : midL_t * heap) := Pr_code (contL x.1) x.2.
pose KR (x : midR_t * heap) := Pr_code (contR x.1) x.2.
have [d0 [Hd0 Hmidprob]] := Hae memL memR xL xR Hpre.
have Hmidprob1 : \P_[ d0 ] mid >= 1 by lra.
have Hcont_wit :
    forall aL aR,
      mid (aL, aR) ->
      exists
      (P Q : {distr (pythOmega (out_t := out_t) X) / R}),
        pythDistWithFinal (pythCoord X) (pythFinal X) P Q s /\
        dmargin (pythFinal X) P =1 KL aL /\
        dmargin (pythFinal X) Q =1 KR aR.
  move=> aL aR Hmid.
  case: aL Hmid => [yL memL'] Hmid.
  case: aR Hmid => [yR memR'] Hmid.
  have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
    Hpyth memL' memR' yL yR Hmid.
  exists P, Q.
  split; first exact: Hdist.
  split; [exact: HmarginL | exact: HmarginR].
have Hbind :=
  pythDistWithFinal_bind_coupling X ML MR KL KR mid d0 s
    Hd0 Hmidprob1 Hcont_wit.
case: Hbind => Pc [Qc [Hdistc [HmarginLc HmarginRc]]].
exists Pc, Qc.
rewrite !Pr_code_bind.
split; first exact: Hdistc.
split.
- move=> y.
  rewrite HmarginLc.
  apply: eq_in_dlet; last by [].
  by move=> x _ z.
split.
- move=> y.
  rewrite HmarginRc.
  apply: eq_in_dlet; last by [].
  by move=> x _ z.
split.
- move=> y Hy.
  have [a Ha Hay] := dinsupp_dlet Hy.
  case: a Ha Hay => [a mem] Ha Hay.
  have [aR Hmid'] :=
    coupling_with_loss_prob1_left_support ML MR mid d0 Hd0 Hmidprob1
      (a, mem) Ha.
  case: aR Hmid' => [aR memR'] Hmid'.
  have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
    Hpyth mem memR' a aR Hmid'.
  apply: (HpostL y).
  exact: Hay.
- move=> y Hy.
  have [a Ha Hay] := dinsupp_dlet Hy.
  case: a Ha Hay => [a mem] Ha Hay.
  have [aL Hmid'] :=
    coupling_with_loss_prob1_right_support ML MR mid d0 Hd0 Hmidprob1
      (a, mem) Ha.
  case: aL Hmid' => [aL memL'] Hmid'.
  have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
    Hpyth memL' mem aL a Hmid'.
  apply: (HpostR y).
  exact: Hay.
Qed.

Lemma pythAeSeqRule
  {ℓ : nat}
  {inL_t inR_t mid_t out_t : ord_choiceType}
  (X : 'I_ℓ -> choiceType)
  (progL : inL_t -> raw_code mid_t)
  (progR : inR_t -> raw_code mid_t)
  (cont : mid_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :
  ⊨Pyth(X) ⦃ pre ⦄ progL ≈( s ) progR ⦃ mid ⦄ ->
  ⊨Hoare ⦃ mid ⦄ cont ⦃ post ⦄ ->
  ⊨Pyth(X) ⦃ pre ⦄
    (fun xL => yL ← progL xL ;; cont yL)
    ≈( s )
    (fun xR => yR ← progR xR ;; cont yR)
  ⦃ post ⦄.
Proof.
move=> Hpyth Hhoare memL memR xL xR Hpre.
have [P [Q [Hdist [HmarginL [HmarginR [HmidL HmidR]]]]]] :=
  Hpyth memL memR xL xR Hpre.
pose K (x : mid_t * heap) := Pr_code (cont x.1) x.2.
have [P' [Q' [Hdist' [HmarginL' HmarginR']]]] :=
  pythDistWithFinal_postprocess X P Q s K Hdist.
exists P', Q'.
rewrite !Pr_code_bind.
split; first exact: Hdist'.
split.
- move=> y.
  rewrite HmarginL'.
  apply: eq_in_dlet; last exact: HmarginL.
  by move=> x _ z.
split.
- move=> y.
  rewrite HmarginR'.
  apply: eq_in_dlet; last exact: HmarginR.
  by move=> x _ z.
split.
- move=> y Hy.
  have [x Hx Hxy] := dinsupp_dlet Hy.
  case: x Hx Hxy => [x mem] Hx Hxy.
  apply: (Hhoare x mem (HmidL (x, mem) Hx) y).
  by rewrite in_dinsupp.
- move=> y Hy.
  have [x Hx Hxy] := dinsupp_dlet Hy.
  case: x Hx Hxy => [x mem] Hx Hxy.
  apply: (Hhoare x mem (HmidR (x, mem) Hx) y).
  by rewrite in_dinsupp.
Qed.

Lemma pythSeqRule
  {ℓ : nat}
  {inL_t inR_t mid_t out_t : ord_choiceType}
  (X : 'I_ℓ -> choiceType)
  (progL : inL_t -> raw_code mid_t)
  (progR : inR_t -> raw_code mid_t)
  (contL : mid_t -> raw_code out_t)
  (contR : mid_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (eps : R)
  (s : (ℓ.+1).-tuple R) :
  ⊨Pyth1(empty_pyth_coord) ⦃ pre ⦄ progL ≈( eps ) progR ⦃ mid ⦄ ->
  ⊨Pyth(X) ⦃
    fun xs =>
      let '((xL, memL), (xR, memR)) := xs in
      (xL == xR) && (memL == memR) && mid (xL, memL)
  ⦄ contL ≈( s ) contR ⦃ post ⦄ ->
  ⊨Pyth(cons_choice (mid_t * heap)%type X) ⦃ pre ⦄
    (fun xL => yL ← progL xL ;; contL yL)
    ≈( eps :: s )
    (fun xR => yR ← progR xR ;; contR yR)
  ⦃ post ⦄.
Proof.
Admitted.

(*
TODO: Restore this once [pythSeqRule] is proved and an induction-friendly
statement over [compile_calls_from_trace] is available.

Lemma pythCompileCallsRule
  (q : nat) (X Y A : choice_type)
  (L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (prog : raw_code A)
  (eps : R)
  (call_invariant : pred heap) :
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fhas M (mkopsig fn X Y) ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( [tuple eps] )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨Pyth ⦃ fun inps =>
          let '((_, memL), (_, memR)) := inps in
          (memL == memR) &&
          call_invariant memL ⦄
    (fun _ : chUnit => code_link
      (compile_calls q.+1 (X := X) (Y := Y) P' fn prog)
      P')
    ≈( nseq (q.+1) eps )
    (fun _ : chUnit => code_link
      (compile_calls q.+1 (X := X) (Y := Y) P'' fn prog)
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
Admitted.
*)
