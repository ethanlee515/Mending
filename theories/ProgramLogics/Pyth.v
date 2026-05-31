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
From SSProve.Crypt Require Import choice_type SubDistr.
From SSProve.Crypt.nominal Require Import Pr.
From SSProve Require Import pkg_core_definition pkg_advantage pkg_notation.
From Mending.Probability Require Import KL.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras RealListExtras.
From Mending.LibExtras.SSProveExtras Require Import DiscreteGaussian.
From Mending.Probability Require Import Pyth.
From Mending.ProgramLogics Require Import Ae Hoare.
Local Open Scope AeNotations.
Local Open Scope HoareNotations.

Import PackageNotation.
Import pkg_heap.
Local Open Scope package_scope.
Local Open Scope ring_scope.

Definition pythJudgment
  {inL_t inR_t out_t : ord_choiceType}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (out_t * heap))
  (s : heap -> heap -> list R) :=
  ∀ memL memR xL xR, pre ((xL, memL), (xR, memR)) →
  let outL := Pr_code (progL xL) memL in
  let outR := Pr_code (progR xR) memR in
  ∀ yL yR, yL \in dinsupp outL -> yR \in dinsupp outR ->
  exists
  (ℓ : nat)
  (Ω : choiceType)
  (X : 'I_ℓ -> choiceType)
  (coord : forall i : 'I_ℓ, Ω -> X i)
  (final : Ω -> out_t * heap)
  (P Q : {distr Ω / R}),
  pythDistWithFinal coord final P Q (s yL.2 yR.2) /\
  dmargin final P =1 outL /\
  dmargin final Q =1 outR /\
  (forall x, x \in dinsupp outL -> post x) /\
  (forall x, x \in dinsupp outR -> post x).

Declare Scope PythNotations.
Local Open Scope PythNotations.

Notation "⊨Pyth ⦃ pre ⦄ progL ≈( s ) progR ⦃ post ⦄" :=
  (pythJudgment progL progR pre post s) : PythNotations.

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
  ⊨Pyth ⦃ pre ⦄ (fun x => sampleRaw (DL x)) ≈( fun _ _ => [:: ε] )
    (fun x => sampleRaw (DR x)) ⦃ post ⦄.
Proof.
move=> Heps Hsame Hac HmassL HmassR Hkl HpostL HpostR.
move=> memL memR xL xR Hpre yL yR HyL HyR.
have Hmem : memL = memR := Hsame memL memR xL xR Hpre.
subst memR.
exists 0, out_t, empty_pyth_coord, (fun _ : 'I_0 => fun _ => tt),
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
  ⊨Pyth ⦃ pre ⦄ (fun _ : chUnit => sampleRaw (ssp_dg centerL stdev))
    ≈( fun _ _ => [:: ε] )
    (fun _ : chUnit => sampleRaw (ssp_dg centerR stdev)) ⦃ post ⦄.
Proof.
move=> Hstdev Hkl_bound Hsame HpostL HpostR.
apply: (klSampRule (fun _ : chUnit => ssp_dg centerL stdev)
                   (fun _ : chUnit => ssp_dg centerR stdev)
                   pre post ε).
- have Hkl := kl_ssp_dg centerL centerR stdev Hstdev.
  have Hnonneg : 0 <= δ_KL (ssp_dg centerL stdev) (ssp_dg centerR stdev) :=
    kl_nonnegative _ _.
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

Lemma MicciancioWalterRule
  {inL_t inR_t out_t : ord_choiceType}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (out_t * heap))
  (s : heap -> heap -> list R)
  (delta : R) :
  (forall memL memR, pythagorean_tv_bound (s memL memR) <= delta) ->
  ⊨Pyth ⦃ pre ⦄ progL ≈( s ) progR ⦃ post ⦄ ->
  ⊨AE ⦃ pre ⦄ progL ≈( delta ) progR ⦃
    fun outs =>
      let '((y_1, m_1'), (y_2, m_2')) := outs in
      post (y_1, m_1') && (y_1 == y_2) && (m_1' == m_2')⦄.
(* TODO: select output heaps and apply the list TV bound. *)
Admitted.

Definition list_lte (s s' : list R) : Prop :=
  size s = size s' /\
  forall i, nth 0 s i <= nth 0 s' i.

Lemma pythConseqRule
  {inL_t inR_t out_t : ord_choiceType}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre pre' : pred ((inL_t * heap) * (inR_t * heap)))
  (post post' : pred (out_t * heap))
  (s s' : heap -> heap -> list R) :
  (forall inps, pre' inps -> pre inps) ->
  (forall outs, post outs -> post' outs) ->
  (forall memL memR, list_lte (s memL memR) (s' memL memR)) ->
  ⊨Pyth ⦃ pre ⦄ progL ≈( s ) progR ⦃ post ⦄ ->
  ⊨Pyth ⦃ pre' ⦄ progL ≈( s' ) progR ⦃ post' ⦄.
(* TODO: transport [pythDistWithFinal] across equal-length lists. *)
Admitted.

Lemma aePythSeqRule
  {inL_t inR_t midL_t midR_t out_t : ord_choiceType}
  (progL : inL_t -> raw_code midL_t)
  (progR : inR_t -> raw_code midR_t)
  (contL : midL_t -> raw_code out_t)
  (contR : midR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (mid : pred ((midL_t * heap) * (midR_t * heap)))
  (post : pred (out_t * heap))
  (s : heap -> heap -> list R) :
  ⊨AE ⦃ pre ⦄ progL ≈( 0 ) progR ⦃ mid ⦄ ->
  ⊨Pyth ⦃ mid ⦄ contL ≈( s ) contR ⦃ post ⦄ ->
  ⊨Pyth ⦃ pre ⦄
    (fun xL => yL ← progL xL ;; contL yL)
    ≈( s )
    (fun xR => yR ← progR xR ;; contR yR)
  ⦃ post ⦄.
(* TODO: generalize [pythDistWithFinal_bind_coupling] to heap-indexed lists. *)
Admitted.

Definition natLocation := (nat * nat)%type.

Definition natLoc (loc : natLocation) : Location :=
  mkloc loc.1 loc.2.

Definition repeatEps (n : nat) (eps : list R) : list R :=
  flatten (nseq n eps).

Lemma repeatEpsS n eps :
  repeatEps n.+1 eps = repeatEps n eps ++ eps.
Proof.
by rewrite /repeatEps -addn1 nseqD flatten_cat /= cats0.
Qed.

Definition heapCtrEps (ctr_loc : natLocation) (eps : list R)
    (memL memR : heap) : list R :=
  repeatEps (get_heap memL (natLoc ctr_loc)) eps.

Lemma pythSeqRule
  {inL_t inR_t mid_t out_t : ord_choiceType}
  (progL : inL_t -> raw_code mid_t)
  (progR : inR_t -> raw_code mid_t)
  (contL : mid_t -> raw_code out_t)
  (contR : mid_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (left_post : pred (mid_t * heap))
  (mid : pred ((mid_t * heap) * (mid_t * heap)))
  (post : pred (out_t * heap))
  (ctr_loc : natLocation)
  (cont_eps : list R) :
  (forall aL aR, left_post aL -> left_post aR ->
    get_heap aL.2 (natLoc ctr_loc) = get_heap aR.2 (natLoc ctr_loc)) ->
  (forall y mem ctr, post (y, mem) ->
    post (y, set_heap mem (natLoc ctr_loc) ctr)) ->
  (forall aL aR, left_post aL -> left_post aR -> mid (aL, aR)) ->
  (forall a, left_post a ->
    exists z, z \in dinsupp (Pr_code (contL a.1) a.2)) ->
  (forall a, left_post a ->
    exists z, z \in dinsupp (Pr_code (contR a.1) a.2)) ->
  ⊨Pyth ⦃ pre ⦄ progL ≈( heapCtrEps ctr_loc cont_eps ) progR ⦃ left_post ⦄ ->
  ⊨Pyth ⦃ mid ⦄ contL ≈( fun _ _ => cont_eps ) contR ⦃ post ⦄ ->
  ⊨Pyth ⦃ pre ⦄
    (fun xL =>
      yL ← progL xL ;;
      ctr ← get (natLoc ctr_loc) ;;
      zL ← contL yL ;;
      #put (natLoc ctr_loc) := ctr.+1 ;;
      ret zL)
    ≈( heapCtrEps ctr_loc cont_eps )
    (fun xR =>
      yR ← progR xR ;;
      ctr ← get (natLoc ctr_loc) ;;
      zR ← contR yR ;;
      #put (natLoc ctr_loc) := ctr.+1 ;;
      ret zR)
  ⦃ post ⦄.
Proof.
move=> Hctr Hpost Hmid HsuppL HsuppR Hprog Hcont.
move=> memL memR xL xR Hpre /= yL yR HyL HyR.
have HyL0 := HyL.
have HyR0 := HyR.
rewrite Pr_code_bind in HyL0.
rewrite Pr_code_bind in HyR0.
have [aL HaL HoutL'] := dinsupp_dlet HyL0.
have [aR HaR HoutR'] := dinsupp_dlet HyR0.
have [ℓ [Ω [X [coord [final [P [Q Hwit]]]]]]] :=
  Hprog memL memR xL xR Hpre aL aR HaL HaR.
have [Hdist [HP [HQ [HleftL HleftR]]]] := Hwit.
have HleftaL : left_post aL := HleftL aL HaL.
have HleftaR : left_post aR := HleftR aR HaR.
have Hmid_eta :
    forall bL bR, left_post bL -> left_post bR ->
      mid ((bL.1, bL.2), (bR.1, bR.2)).
  by move=> [bLv bLm] [bRv bRm] /=; apply: Hmid.
set ctr := get_heap aL.2 (natLoc ctr_loc).
set KL := fun a : mid_t * heap =>
  Pr_code
    (z ← contL a.1 ;;
     #put (natLoc ctr_loc) := (get_heap a.2 (natLoc ctr_loc)).+1 ;;
     ret z) a.2.
set KR := fun a : mid_t * heap =>
  Pr_code
    (z ← contR a.1 ;;
     #put (natLoc ctr_loc) := (get_heap a.2 (natLoc ctr_loc)).+1 ;;
     ret z) a.2.
have Hcont_postL :
    forall bL bR, left_post bL -> left_post bR ->
    forall z, z \in dinsupp (Pr_code (contL bL.1) bL.2) -> post z.
  move=> bL bR HleftbL HleftbR zL HzL.
  have [zR HzR] := HsuppR bR HleftbR.
  have [ℓ' [Ω' [X' [coord' [final' [P' [Q' Hwit']]]]]]] :=
    Hcont bL.2 bR.2 bL.1 bR.1 (Hmid_eta bL bR HleftbL HleftbR)
      zL zR HzL HzR.
  have [Hdist' [HP' [HQ' [HpostL HpostR]]]] := Hwit'.
  exact: HpostL zL HzL.
have Hcont_postR :
    forall bL bR, left_post bL -> left_post bR ->
    forall z, z \in dinsupp (Pr_code (contR bR.1) bR.2) -> post z.
  move=> bL bR HleftbL HleftbR zR HzR.
  have [zL HzL] := HsuppL bL HleftbL.
  have [ℓ' [Ω' [X' [coord' [final' [P' [Q' Hwit']]]]]]] :=
    Hcont bL.2 bR.2 bL.1 bR.1 (Hmid_eta bL bR HleftbL HleftbR)
      zL zR HzL HzR.
  have [Hdist' [HP' [HQ' [HpostL HpostR]]]] := Hwit'.
  exact: HpostR zR HzR.
have Hcont_wit :
    forall bL bR,
      bL \in dinsupp (dmargin final P) ->
      bR \in dinsupp (dmargin final Q) ->
      exists
      (ℓ' : nat)
      (Ω' : choiceType)
      (X' : 'I_ℓ' -> choiceType)
      (coord' : forall i : 'I_ℓ', Ω' -> X' i)
      (final' : Ω' -> out_t * heap)
      (P' Q' : {distr Ω' / R}),
        pythDistWithFinal coord' final' P' Q' cont_eps /\
        dmargin final' P' =1 KL bL /\
        dmargin final' Q' =1 KR bR.
  move=> bL bR HbL HbR.
  have HbLprog : bL \in dinsupp (Pr_code (progL xL) memL).
    by rewrite in_dinsupp -HP -in_dinsupp.
  have HbRprog : bR \in dinsupp (Pr_code (progR xR) memR).
    by rewrite in_dinsupp -HQ -in_dinsupp.
  have HleftbL : left_post bL := HleftL bL HbLprog.
  have HleftbR : left_post bR := HleftR bR HbRprog.
  have Hctrb : get_heap bL.2 (natLoc ctr_loc) =
               get_heap bR.2 (natLoc ctr_loc) :=
    Hctr bL bR HleftbL HleftbR.
  have [zL HzL] := HsuppL bL HleftbL.
  have [zR HzR] := HsuppR bR HleftbR.
  have [ℓ' [Ω' [X' [coord' [final' [P' [Q' Hwit']]]]]]] :=
    Hcont bL.2 bR.2 bL.1 bR.1 (Hmid_eta bL bR HleftbL HleftbR)
      zL zR HzL HzR.
  have [Hdist' [HP' [HQ' [HpostL HpostR]]]] := Hwit'.
  have [Ω'' [X'' [coord'' [final'' [P'' [Q'' Hwit'']]]]]] :=
    pythDistWithFinal_postprocess coord' final' P' Q' cont_eps
      (fun z => dunit (z.1,
        set_heap z.2 (natLoc ctr_loc)
          (get_heap bL.2 (natLoc ctr_loc)).+1)) Hdist'.
  have [Hdist'' [HP'' HQ'']] := Hwit''.
  exists _, Ω'', X'', coord'', final'', P'', Q''.
  split; first exact: Hdist''.
  split.
  - move=> out.
    rewrite HP'' /KL Pr_code_bind.
    apply: eq_in_dlet; last exact: HP'.
    move=> z _ out'.
    by rewrite Pr_code_put Pr_code_ret.
  - move=> out.
    rewrite HQ'' /KR Pr_code_bind.
    apply: eq_in_dlet; last exact: HQ'.
    move=> z _ out'.
    rewrite Pr_code_put Pr_code_ret.
    by rewrite Hctrb.
have [ℓc [Ωc [Xc [coordc [finalc [Pc [Qc Hwitc]]]]]]] :=
  pythDistWithFinal_bind_exists coord final P Q
    (heapCtrEps ctr_loc cont_eps aL.2 aR.2) cont_eps KL KR Hdist Hcont_wit.
have [Hdistc [HPc HQc]] := Hwitc.
have HoutLctr : get_heap yL.2 (natLoc ctr_loc) = ctr.+1.
  rewrite Pr_code_get Pr_code_bind in HoutL'.
  have [z Hz HoutL''] := dinsupp_dlet HoutL'.
  rewrite Pr_code_put Pr_code_ret in HoutL''.
  have -> := in_dunit HoutL''.
  by rewrite get_set_heap_eq.
exists ℓc, Ωc, Xc, coordc, finalc, Pc, Qc.
split.
- rewrite /heapCtrEps HoutLctr /ctr repeatEpsS.
  exact: Hdistc.
split.
- move=> out.
  rewrite HPc Pr_code_bind.
  apply: eq_in_dlet; last exact: HP.
  move=> a _ out'.
  rewrite /KL Pr_code_get.
  by [].
split.
- move=> out.
  rewrite HQc Pr_code_bind.
  apply: eq_in_dlet; last exact: HQ.
  move=> a _ out'.
  rewrite /KR Pr_code_get.
  by [].
split.
- move=> out Hout.
  rewrite Pr_code_bind in Hout.
  have [a Ha Hout'] := dinsupp_dlet Hout.
  rewrite Pr_code_get Pr_code_bind in Hout'.
  have [z Hz Hout''] := dinsupp_dlet Hout'.
  case: z Hz Hout'' => [zv zm] Hz Hout''.
  rewrite Pr_code_put Pr_code_ret in Hout''.
  have -> := in_dunit Hout''.
  exact: Hpost zv zm _ (Hcont_postL a aR (HleftL a Ha) HleftaR (zv, zm) Hz).
- move=> out Hout.
  rewrite Pr_code_bind in Hout.
  have [a Ha Hout'] := dinsupp_dlet Hout.
  rewrite Pr_code_get Pr_code_bind in Hout'.
  have [z Hz Hout''] := dinsupp_dlet Hout'.
  case: z Hz Hout'' => [zv zm] Hz Hout''.
  rewrite Pr_code_put Pr_code_ret in Hout''.
  have -> := in_dunit Hout''.
  exact: Hpost zv zm _ (Hcont_postR aL a HleftaL (HleftR a Ha) (zv, zm) Hz).
Qed.

Lemma pythAeSeqRule
  {inL_t inR_t mid_t out_t : ord_choiceType}
  (progL : inL_t -> raw_code mid_t)
  (progR : inR_t -> raw_code mid_t)
  (cont : mid_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (s sout : heap -> heap -> list R) :
  (forall midMemL midMemR outMemL outMemR,
    s midMemL midMemR = sout outMemL outMemR) ->
  ⊨Pyth ⦃ pre ⦄ progL ≈( s ) progR ⦃ mid ⦄ ->
  ⊨Hoare ⦃ mid ⦄ cont ⦃ post ⦄ ->
  ⊨Pyth ⦃ pre ⦄
    (fun xL => yL ← progL xL ;; cont yL)
    ≈( sout )
    (fun xR => yR ← progR xR ;; cont yR)
  ⦃ post ⦄.
(* TODO: transport the indexed list through [pythDistWithFinal_postprocess]. *)
Admitted.
