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
From Mending.Probability.DiscreteGaussians Require Import
  DiscreteGaussian DiscreteGaussianKL.
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
rewrite [dmargin f _]dmarginE dmargin_dlet_partition.
transitivity ((\dlet_(x <- D) dunit (f (g x))) z).
- apply: eq_in_dlet=> // x _ z'.
  by rewrite dmargin_dunit.
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

Lemma sample_output_encoding_injective
    {out_t : choice_type} (mem : heap) :
  injective (fun y : out_t => Some (pack_output_heap (y, mem))).
Proof.
move=> y1 y2 Hsome.
move: Hsome=> [= Hpack].
exact: (pcan_inj pickleK Hpack).
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
  have Henc_inj := @sample_output_encoding_injective out_t memL.
  have Hfin_enc : finite_kl encL encR.
    exact: (finite_kl_dmargin_injective _ _ _ Henc_inj (Hfin xL xR)).
  have Hkl_enc : δ_KL encL encR <= ε.
    rewrite /encL /encR.
    rewrite (@kl_dmargin_injective R out_t (option (nat * heap))
      (fun y => Some (pack_output_heap (y, memL)))
      (DL xL) (DR xR) Henc_inj (Hfin xL xR)).
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

Fixpoint dg_tuple {n : nat}
    (center : n.-tuple int) (stdev : R) : {distr (n.-tuple int) / R} :=
  match n as n' return n'.-tuple int -> {distr (n'.-tuple int) / R} with
  | 0 => fun _ => dunit [tuple]
  | n'.+1 => fun center' =>
      \dlet_(x <- discrete_gaussian (thead center') stdev)
      \dlet_(xs <- dg_tuple (behead_tuple center') stdev)
        dunit (cons_tuple x xs)
  end center.

Lemma dg_tuple_cons_cat {n : nat}
    (c : int) (center : n.-tuple int) (stdev : R) :
  dg_tuple [tuple of c :: center] stdev =1
    \dlet_(x <- discrete_gaussian c stdev)
    \dlet_(xs <- dg_tuple center stdev)
      dunit (cat_tuple [tuple x] xs).
Proof.
move=> y.
rewrite /= theadE.
have Hbehead : behead_tuple [tuple of c :: center] = center.
  by apply: val_inj.
rewrite Hbehead.
apply: eq_in_dlet=> // x _ z.
apply: eq_in_dlet=> // xs _ w.
by rewrite cat_tuple_singleton_cons.
Qed.

Lemma dg_tuple_singleton_pyth_trace (c : int) (stdev : R) :
  dg_tuple [tuple c] stdev =1
    dmargin (@singleton_pyth_trace int) (discrete_gaussian c stdev).
Proof.
move=> y.
have Hcenter : [tuple c] = [tuple of c :: [tuple]] :> 1.-tuple int.
  by apply: val_inj.
rewrite Hcenter.
rewrite (dg_tuple_cons_cat c [tuple] stdev y).
rewrite dmarginE.
apply: eq_in_dlet=> // x _ z.
rewrite /= dlet_unit.
have -> : cat_tuple [tuple x] [tuple] = singleton_pyth_trace x.
  by apply: val_inj.
by [].
Qed.

Lemma dgTuplePythDist
    {n : nat} (centerL centerR : n.-tuple int)
    (stdev eps : R) :
  0 <= eps ->
  0 < stdev ->
  (forall i : 'I_n,
    ((tnth centerR i - tnth centerL i)%:~R) ^+ 2 /
      (2 * stdev ^ 2) <= eps) ->
  pythDist
    (dg_tuple centerL stdev)
    (dg_tuple centerR stdev)
    [tuple eps | i < n].
Proof.
elim: n centerL centerR=> [|n IH] centerL centerR Heps Hstdev Hcoord.
- rewrite [centerL](tuple0 centerL) [centerR](tuple0 centerR) /=.
  apply: pythDist_refl.
  + by move=> i; case: i.
  exact: dunit_dweight.
case: n IH centerL centerR Hcoord=> [IH0|n IH] centerL centerR Hcoord.
- pose cL := thead centerL.
  pose cR := thead centerR.
  have HcenterL : centerL = [tuple cL].
    apply: eq_from_tnth=> i.
    rewrite [i]ord1 /cL /thead.
    by rewrite tnth0.
  have HcenterR : centerR = [tuple cR].
    apply: eq_from_tnth=> i.
    rewrite [i]ord1 /cR /thead.
    by rewrite tnth0.
  have Hfin : finite_kl
      (discrete_gaussian cL stdev)
      (discrete_gaussian cR stdev).
    exact: (finite_kl_discrete_gaussian cL cR stdev Hstdev).
  have Hkl :
      δ_KL (discrete_gaussian cL stdev)
        (discrete_gaussian cR stdev) <= eps.
    rewrite kl_discrete_gaussian //.
    exact: (Hcoord ord0).
  rewrite (mktuple_const_1 eps).
  apply: (pythDist_ext
    (dmargin (@singleton_pyth_trace int)
      (discrete_gaussian cL stdev))
    (dg_tuple centerL stdev)
    (dmargin (@singleton_pyth_trace int)
      (discrete_gaussian cR stdev))
    (dg_tuple centerR stdev)
    [tuple eps]).
  + move=> y; symmetry.
    rewrite HcenterL.
    exact: dg_tuple_singleton_pyth_trace.
  + move=> y; symmetry.
    rewrite HcenterR.
    exact: dg_tuple_singleton_pyth_trace.
  apply: pythDist_kl_singleton.
  + exact: Heps.
  + exact: Hfin.
  + by rewrite discrete_gaussian_mass1.
  + by rewrite discrete_gaussian_mass1.
  exact: Hkl.
pose cL := thead centerL.
pose tailL := behead_tuple centerL.
pose cR := thead centerR.
pose tailR := behead_tuple centerR.
have HcenterL : centerL = [tuple of cL :: tailL].
  by rewrite (tuple_eta centerL).
have HcenterR : centerR = [tuple of cR :: tailR].
  by rewrite (tuple_eta centerR).
have HtailL i : tnth centerL (lift ord0 i) = tnth tailL i.
  by rewrite HcenterL tnthS.
have HtailR i : tnth centerR (lift ord0 i) = tnth tailR i.
  by rewrite HcenterR tnthS.
have Hfin_head : finite_kl
    (discrete_gaussian cL stdev)
    (discrete_gaussian cR stdev).
  exact: (finite_kl_discrete_gaussian cL cR stdev Hstdev).
have Hkl_head :
    δ_KL (discrete_gaussian cL stdev)
      (discrete_gaussian cR stdev) <= eps.
  rewrite kl_discrete_gaussian //.
  exact: (Hcoord ord0).
have Hhead :
    pythDist
      (dmargin (@singleton_pyth_trace int)
        (discrete_gaussian cL stdev))
      (dmargin (@singleton_pyth_trace int)
        (discrete_gaussian cR stdev))
      [tuple eps].
  apply: pythDist_kl_singleton.
  + exact: Heps.
  + exact: Hfin_head.
  + by rewrite discrete_gaussian_mass1.
  + by rewrite discrete_gaussian_mass1.
  exact: Hkl_head.
have Htail :
    pythDist
      (dg_tuple tailL stdev)
      (dg_tuple tailR stdev)
      [tuple eps | i < n.+1].
  apply: IH=> // i.
  move: (Hcoord (lift ord0 i)).
  by rewrite HtailL HtailR.
rewrite HcenterL HcenterR.
rewrite -cat_tuple_singleton_const.
apply: (pythDist_ext
  (\dlet_(omega0 <-
      dmargin (@singleton_pyth_trace int)
        (discrete_gaussian cL stdev))
   \dlet_(omega1 <- dg_tuple tailL stdev)
     dunit (cat_tuple omega0 omega1))
  (dg_tuple [tuple of cL :: tailL] stdev)
  (\dlet_(omega0 <-
      dmargin (@singleton_pyth_trace int)
        (discrete_gaussian cR stdev))
   \dlet_(omega1 <- dg_tuple tailR stdev)
     dunit (cat_tuple omega0 omega1))
  (dg_tuple [tuple of cR :: tailR] stdev)
  (cat_tuple [tuple eps] [tuple eps | i < n.+1])).
- move=> y.
  rewrite (dg_tuple_cons_cat cL tailL stdev y).
  rewrite dmarginE __deprecated__dlet_dlet.
  apply: eq_in_dlet=> // x _ z.
  by rewrite dlet_unit /singleton_pyth_trace.
- move=> y.
  rewrite (dg_tuple_cons_cat cR tailR stdev y).
  rewrite dmarginE __deprecated__dlet_dlet.
  apply: eq_in_dlet=> // x _ z.
  by rewrite dlet_unit /singleton_pyth_trace.
exact: (pythDist_dlet_cat_const _ _ _ _ _ _ Hhead Htail).
Qed.

Lemma klDgNRule
    {n : nat} {out_t : choice_type}
    (centerL centerR : n.-tuple int)
    (encode : n.-tuple int -> out_t)
    (stdev eps : R)
    (pre : pred ((chUnit * heap) * (chUnit * heap)))
    (post : pred (out_t * heap)) :
  injective encode ->
  0 <= eps ->
  0 < stdev ->
  (forall i : 'I_n,
    ((tnth centerR i - tnth centerL i)%:~R) ^+ 2 /
      (2 * stdev ^ 2) <= eps) ->
  (forall memL memR,
    pre ((tt, memL), (tt, memR)) -> memL = memR) ->
  (forall memL memR y,
    pre ((tt, memL), (tt, memR)) -> post (y, memL)) ->
  (forall memL memR y,
    pre ((tt, memL), (tt, memR)) -> post (y, memR)) ->
  ⊨Pyth1 ⦃ pre ⦄
    (fun _ : chUnit =>
      sampleRaw (dmargin encode (dg_tuple centerL stdev)))
    ≈( n%:R * eps )
    (fun _ : chUnit =>
      sampleRaw (dmargin encode (dg_tuple centerR stdev)))
  ⦃ post ⦄.
Proof.
move=> Hencode Heps Hstdev Hcoord Hsame HpostL HpostR.
have Hpyth := dgTuplePythDist
  centerL centerR stdev eps Heps Hstdev Hcoord.
have Hfin := pythDist_finite_kl _ _ _ Hpyth.
have Hkl := pythDist_kl_bound _ _ _ Hpyth.
have [_ [HmassL [HmassR _]]] := Hpyth.
apply: (klSampRule
  (fun _ : chUnit => dmargin encode (dg_tuple centerL stdev))
  (fun _ : chUnit => dmargin encode (dg_tuple centerR stdev))
  pre post (n%:R * eps)).
- apply: mulr_ge0; first exact: ler0n.
  exact: Heps.
- by move=> memL memR [] []; exact: Hsame.
- move=> [] [].
  exact: (finite_kl_dmargin_injective encode _ _ Hencode Hfin).
- move=> [].
  rewrite dmargin_dweight.
  exact: HmassL.
- move=> [].
  rewrite dmargin_dweight.
  exact: HmassR.
- move=> memL memR [] [] Hpre.
  rewrite (kl_dmargin_injective encode _ _ Hencode Hfin).
  apply: (le_trans Hkl).
  rewrite (eq_bigr (fun _ : 'I_n => eps)); last first.
    by move=> i _; rewrite tnth_mktuple.
  rewrite big_const_ord iter_addr_0 mulr_natl.
  exact: lexx.
- move=> memL memR [] [] y Hpre _.
  exact: (HpostL memL memR y Hpre).
- move=> memL memR [] [] y Hpre _.
  exact: (HpostR memL memR y Hpre).
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
  ⊨AE ⦃ pre ⦄ progL ≈( delta ) progR ⦃
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
          =1 complete_output_heap (KL y) /\
        dmargin (fun omega => tnth omega ord_max) Q
          =1 complete_output_heap (KR y) /\
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
