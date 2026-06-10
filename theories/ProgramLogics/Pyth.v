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
From Mending.Probability.KL Require Import Pyth.
From Mending.ProgramLogics Require Import Ae Hoare.
Local Open Scope AeNotations.
Local Open Scope HoareNotations.

Import PackageNotation.
Import pkg_heap.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope package_scope.
Local Open Scope ring_scope.

Definition pack_output_heap {out_t : choice_type}
    (out : out_t * heap) : (nat * heap)%type :=
  (pickle out.1, out.2).

Lemma total_variation_pack_output_heap
    {out_t : choice_type} (P Q : {distr (out_t * heap) / R}) :
  total_variation P Q =
  total_variation (dmargin (@pack_output_heap out_t) P)
                  (dmargin (@pack_output_heap out_t) Q).
Admitted.

Definition pythJudgment
  {ℓ : nat}
  {inL_t inR_t out_t : choice_type}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :=
  ∀ memL memR xL xR, pre ((xL, memL), (xR, memR)) →
  exists
  (P Q : {distr ((ℓ.+1).-tuple (nat * heap)) / R}),
  let outL := Pr_code (progL xL) memL in
  let outR := Pr_code (progR xR) memR in
  pythDist P Q s /\
  dmargin (fun omega => tnth omega ord_max) P
    =1 dmargin pack_output_heap outL /\
  dmargin (fun omega => tnth omega ord_max) Q
    =1 dmargin pack_output_heap outR /\
  (forall x, x \in dinsupp outL -> post x) /\
  (forall x, x \in dinsupp outR -> post x).

Declare Scope PythNotations.
Local Open Scope PythNotations.

Notation "⊨Pyth ⦃ pre ⦄ progL ≈( s ) progR ⦃ post ⦄" :=
  (pythJudgment progL progR pre post s) : PythNotations.

Notation "⊨Pyth1 ⦃ pre ⦄ progL ≈( eps ) progR ⦃ post ⦄" :=
  (pythJudgment progL progR pre post [tuple eps] ) : PythNotations.

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
  pose final (omega : (ℓ.+1).-tuple (nat * heap)) := tnth omega ord_max.
  have Htv := pythDist_final_total_variation
    P Q s Hdist.
  have Htv_eq :
      total_variation outL outR =
      total_variation (dmargin final P) (dmargin final Q).
    rewrite (total_variation_pack_output_heap outL outR).
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
move=> Hpre Hpost Hs Hpyth memL memR xL xR Hpre'.
have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
  Hpyth memL memR xL xR (Hpre _ Hpre').
exists P, Q.
split.
- move: Hdist=> [Heps [Hac [HP [HQ Hcond]]]].
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

Lemma aeEqPyth1Rule
  {in_t mid_t : choice_type}
  (progL progR : in_t -> raw_code mid_t)
  (pre : pred ((in_t * heap) * (in_t * heap)))
  (mid : pred (mid_t * heap)) :
  ⊨AE ⦃ pre ⦄ progL ≈( 0 ) progR ⦃
    fun outs =>
      let '((yL, memL'), (yR, memR')) := outs in
      (yL == yR) && (memL' == memR') && mid (yL, memL') ⦄ ->
  ⊨Pyth1 ⦃ pre ⦄ progL ≈( 0 ) progR ⦃ mid ⦄.
Admitted.

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
    ≈( s )
    (fun xR => yR ← progR xR ;; cont yR)
  ⦃ post ⦄.
Proof.
move=> Hpyth Hhoare memL memR xL xR Hpre.
have [P0 [Q0 [Hdist0 [HmarginL0 [HmarginR0 [HmidL HmidR]]]]]] :=
  Hpyth memL memR xL xR Hpre.
set ML := Pr_code (progL xL) memL.
set MR := Pr_code (progR xR) memR.
set K := fun y : mid_t * heap => Pr_code (cont y.1) y.2.
have HK :
    forall y, mid y -> forall x, x \in dinsupp (K y) -> post x.
  by move=> [y mem] Hy x Hx; exact: Hhoare y mem Hy x Hx.
have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
  pythDist_bind_same_kernel (@pack_output_heap mid_t) (@pack_output_heap out_t)
    ML MR K mid post s P0 Q0
    Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK.
exists P, Q.
rewrite !Pr_code_bind.
split; first exact: Hdist.
split; first exact: HmarginL.
split; first exact: HmarginR.
by split.
Qed.

Lemma pythSeq1Rule
  {ℓ : nat}
  {inL_t inR_t mid_t out_t : choice_type}
  (progL : inL_t -> raw_code mid_t)
  (progR : inR_t -> raw_code mid_t)
  (contL : mid_t -> raw_code out_t)
  (contR : mid_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (eps : R)
  (s : (ℓ.+1).-tuple R) :
  ⊨Pyth1 ⦃ pre ⦄ progL ≈( eps ) progR ⦃ mid ⦄ ->
  ⊨Pyth ⦃
    fun xs =>
      let '((xL, memL), (xR, memR)) := xs in
      (xL == xR) && (memL == memR) && mid (xL, memL)
  ⦄ contL ≈( s ) contR ⦃ post ⦄ ->
  ⊨Pyth ⦃ pre ⦄
    (fun xL => yL ← progL xL ;; contL yL)
    ≈( eps :: s )
    (fun xR => yR ← progR xR ;; contR yR)
  ⦃ post ⦄.
Admitted.

Definition pythKernelPair {ℓ : nat} : Type :=
  ({distr ((ℓ.+1).-tuple (nat * heap)) / R} *
   {distr ((ℓ.+1).-tuple (nat * heap)) / R})%type.

Definition pythKernelSpec
  {ℓ : nat}
  {out_t : choice_type}
  (KL KR : {distr (out_t * heap) / R})
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R)
  (W : pythKernelPair (ℓ := ℓ)) : Prop :=
  let '(P, Q) := W in
  pythDist P Q s /\
  dmargin (fun omega => tnth omega ord_max) P
    =1 dmargin (@pack_output_heap out_t) KL /\
  dmargin (fun omega => tnth omega ord_max) Q
    =1 dmargin (@pack_output_heap out_t) KR /\
  (forall x, x \in dinsupp KL -> post x) /\
  (forall x, x \in dinsupp KR -> post x).

Lemma pythKernelSpec_dist
  {ℓ : nat}
  {out_t : choice_type}
  (KL KR : {distr (out_t * heap) / R})
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R)
  (W : pythKernelPair (ℓ := ℓ)) :
  pythKernelSpec KL KR post s W ->
  pythDist W.1 W.2 s.
Proof. by case: W=> P Q /= [Hdist _]. Qed.

Lemma pythKernelSpec_marginL
  {ℓ : nat}
  {out_t : choice_type}
  (KL KR : {distr (out_t * heap) / R})
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R)
  (W : pythKernelPair (ℓ := ℓ)) :
  pythKernelSpec KL KR post s W ->
  dmargin (fun omega => tnth omega ord_max) W.1
    =1 dmargin (@pack_output_heap out_t) KL.
Proof. by case: W=> P Q /= [_ [Hmargin _]]. Qed.

Lemma pythKernelSpec_marginR
  {ℓ : nat}
  {out_t : choice_type}
  (KL KR : {distr (out_t * heap) / R})
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R)
  (W : pythKernelPair (ℓ := ℓ)) :
  pythKernelSpec KL KR post s W ->
  dmargin (fun omega => tnth omega ord_max) W.2
    =1 dmargin (@pack_output_heap out_t) KR.
Proof. by case: W=> P Q /= [_ [_ [Hmargin _]]]. Qed.

Lemma pythKernelSpec_postL
  {ℓ : nat}
  {out_t : choice_type}
  (KL KR : {distr (out_t * heap) / R})
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R)
  (W : pythKernelPair (ℓ := ℓ)) :
  pythKernelSpec KL KR post s W ->
  forall x, x \in dinsupp KL -> post x.
Proof. by case: W=> P Q /= [_ [_ [_ [Hpost _]]]]. Qed.

Lemma pythKernelSpec_postR
  {ℓ : nat}
  {out_t : choice_type}
  (KL KR : {distr (out_t * heap) / R})
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R)
  (W : pythKernelPair (ℓ := ℓ)) :
  pythKernelSpec KL KR post s W ->
  forall x, x \in dinsupp KR -> post x.
Proof. by case: W=> P Q /= [_ [_ [_ [_ Hpost]]]]. Qed.

Definition default_pyth_trace {n : nat} : n.-tuple (nat * heap) :=
  nseq_tuple n (0%N, empty_heap).

Definition decode_output_heap {out_t : choice_type}
    (x : nat * heap) : option (out_t * heap) :=
  match unpickle x.1 with
  | Some y => Some (y, x.2)
  | None => None
  end.

Lemma decode_output_heap_pack {out_t : choice_type} (x : out_t * heap) :
  decode_output_heap (pack_output_heap x) = Some x.
Proof. by case: x=> y mem; rewrite /decode_output_heap /pack_output_heap pickleK. Qed.

Lemma pythKernel_choice
  {ℓ : nat}
  {mid_t out_t : choice_type}
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :
  (forall y, mid y ->
    exists (P Q : {distr ((ℓ.+1).-tuple (nat * heap)) / R}),
      pythKernelSpec (KL y) (KR y) post s (P, Q)) ->
  exists (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ)),
    forall y,
      pythKernelSpec
        (KL (proj1_sig y)) (KR (proj1_sig y)) post s (K y).
Proof.
move=> Hcont.
have Hchoice :
    forall y : { y : mid_t * heap | mid y },
      exists W : pythKernelPair (ℓ := ℓ),
        pythKernelSpec
          (KL (proj1_sig y)) (KR (proj1_sig y)) post s W.
  move=> [y Hy] /=.
  have [P [Q HW]] := Hcont y Hy.
  by exists (P, Q).
have [K HK] := schoice _ _ _ Hchoice.
by exists K.
Qed.

Definition pythTraceKernelL
  {ℓ1 ℓ2 : nat}
  {mid_t : choice_type}
  (mid : pred (mid_t * heap))
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (omega : (ℓ1.+1).-tuple (nat * heap))
    : {distr ((ℓ2.+1).-tuple (nat * heap)) / R} :=
  match decode_output_heap (tnth omega ord_max) with
  | Some y =>
      match @idP (mid y) with
      | ReflectT Hy => (K (exist _ y Hy)).1
      | ReflectF _ => dunit (default_pyth_trace (n := ℓ2.+1))
      end
  | None => dunit (default_pyth_trace (n := ℓ2.+1))
  end.

Definition pythTraceKernelR
  {ℓ1 ℓ2 : nat}
  {mid_t : choice_type}
  (mid : pred (mid_t * heap))
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (omega : (ℓ1.+1).-tuple (nat * heap))
    : {distr ((ℓ2.+1).-tuple (nat * heap)) / R} :=
  match decode_output_heap (tnth omega ord_max) with
  | Some y =>
      match @idP (mid y) with
      | ReflectT Hy => (K (exist _ y Hy)).2
      | ReflectF _ => dunit (default_pyth_trace (n := ℓ2.+1))
      end
  | None => dunit (default_pyth_trace (n := ℓ2.+1))
  end.

Definition pythTraceBindL
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML : {distr (mid_t * heap) / R})
  (KL : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (P0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
    : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R} :=
  \dlet_(omega1 <- P0)
  \dlet_(omega2 <- pythTraceKernelL mid K omega1)
    dunit (cat_tuple omega1 omega2).

Definition pythTraceBindR
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (MR : {distr (mid_t * heap) / R})
  (KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
    : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R} :=
  \dlet_(omega1 <- Q0)
  \dlet_(omega2 <- pythTraceKernelR mid K omega1)
    dunit (cat_tuple omega1 omega2).

Definition pythTraceBindPair
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) : Prop :=
  P =1 pythTraceBindL ML KL mid P0 K /\
  Q =1 pythTraceBindR MR KR mid Q0 K.

Lemma pythTraceBindPair_exists
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2)) :
  exists (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}),
    pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q.
Proof.
exists (pythTraceBindL ML KL mid P0 K),
       (pythTraceBindR MR KR mid Q0 K).
by split=> omega.
Qed.

Lemma cat_tuple_nonneg
  {ℓ1 ℓ2 : nat}
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R) :
  (forall i : 'I_(ℓ1.+1), 0 <= tnth s1 i) ->
  (forall i : 'I_(ℓ2.+1), 0 <= tnth s2 i) ->
  forall i : 'I_(ℓ1.+1 + ℓ2.+1), 0 <= tnth (cat_tuple s1 s2) i.
Admitted.

Lemma pythTraceBindPair_s2_nonneg
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML : {distr (mid_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2)) :
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  forall i : 'I_(ℓ2.+1), 0 <= tnth s2 i.
Admitted.

Lemma pythTraceBindPair_absolute_continuous
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  absolute_continuous P Q.
Admitted.

Lemma pythTraceBindPair_dweightL
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  dweight P = 1.
Admitted.

Lemma pythTraceBindPair_dweightR
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  dweight Q = 1.
Admitted.

Lemma cat_tuple_tnth_prefix_choice
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (t1 : (ℓ1.+1).-tuple A)
  (t2 : (ℓ2.+1).-tuple A)
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (Hi : (i < ℓ1.+1)%N) :
  tnth (cat_tuple t1 t2) i = tnth t1 (Ordinal Hi).
Proof.
rewrite (tnth_nth (tnth t1 (Ordinal Hi))).
rewrite (tnth_nth (tnth t1 (Ordinal Hi)) t1).
rewrite nth_cat size_tuple Hi.
by apply: set_nth_default; rewrite size_tuple.
Qed.

Lemma cat_tuple_tnth_prefix
  {ℓ1 ℓ2 : nat}
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (Hi : (i < ℓ1.+1)%N) :
  tnth (cat_tuple s1 s2) i = tnth s1 (Ordinal Hi).
Proof. exact: cat_tuple_tnth_prefix_choice. Qed.

Lemma cat_tuple_suffix_bound
  {ℓ1 ℓ2 : nat}
  (i : 'I_(ℓ1.+1 + ℓ2.+1)) :
  (ℓ1.+1 <= i)%N ->
  (i - ℓ1.+1 < ℓ2.+1)%N.
Proof.
move=> Hi.
have Hord := ltn_ord i.
by rewrite ltn_subLR // addnC.
Qed.

Lemma cat_tuple_tnth_suffix_choice
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (t1 : (ℓ1.+1).-tuple A)
  (t2 : (ℓ2.+1).-tuple A)
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (Hi : (ℓ1.+1 <= i)%N) :
  tnth (cat_tuple t1 t2) i =
  tnth t2 (Ordinal (cat_tuple_suffix_bound i Hi)).
Proof.
rewrite (tnth_nth (tnth t2 (Ordinal (cat_tuple_suffix_bound i Hi)))).
rewrite nth_cat size_tuple.
rewrite ltnNge Hi.
rewrite /=.
by rewrite [RHS](tnth_nth (tnth t2 (Ordinal (cat_tuple_suffix_bound i Hi)))).
Qed.

Lemma cat_tuple_tnth_suffix
  {ℓ1 ℓ2 : nat}
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (Hi : (ℓ1.+1 <= i)%N) :
  tnth (cat_tuple s1 s2) i =
  tnth s2 (Ordinal (cat_tuple_suffix_bound i Hi)).
Proof. exact: cat_tuple_tnth_suffix_choice. Qed.

Definition pythCombinedPrefixTrace
  {ℓ1 ℓ2 : nat}
  {A : Type}
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A) :
  (ℓ1.+1).-tuple A :=
  [tuple a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _)))
    | j < ℓ1.+1].

Definition pythCombinedSuffixIndex
  {ℓ1 ℓ2 : nat}
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (Hi : (ℓ1.+1 <= i)%N) : 'I_(ℓ2.+1) :=
  Ordinal (cat_tuple_suffix_bound i Hi).

Lemma pythCombinedSuffixOrdinal_bound
  {ℓ1 ℓ2 : nat}
  (j : 'I_(ℓ2.+1)) :
  (ℓ1.+1 + j < ℓ1.+1 + ℓ2.+1)%N.
Proof.
by rewrite ltn_add2l ltn_ord.
Qed.

Definition pythCombinedSuffixAssignment
  {ℓ1 ℓ2 : nat}
  {A : Type}
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (Hi : (ℓ1.+1 <= i)%N)
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A) :
  forall j : 'I_(ℓ2.+1), A :=
  fun j =>
    a (Ordinal (pythCombinedSuffixOrdinal_bound j)).

Lemma kl_ext
  {T : choiceType}
  (P P' Q Q' : {distr T / R}) :
  P =1 P' ->
  Q =1 Q' ->
  δ_KL P Q = δ_KL P' Q'.
Proof.
move=> HP HQ.
rewrite /δ_KL.
rewrite (expectation_distr_ext P P' _ HP).
apply: expectation_ext=> x.
by rewrite -HP -HQ.
Qed.

Lemma pr_ext {T : choiceType} (P Q : {distr T / R}) (p : pred T) :
  P =1 Q ->
  \P_[P] p = \P_[Q] p.
Proof.
move=> HP.
rewrite /pr.
apply/eq_psum=> x.
by rewrite HP.
Qed.

Lemma prc_ext {T : choiceType}
    (P Q : {distr T / R}) (A p : pred T) :
  P =1 Q ->
  \P_[P, p] A = \P_[Q, p] A.
Proof.
move=> HP.
rewrite /prc.
by rewrite (pr_ext P Q [predI A & p] HP) (pr_ext P Q p HP).
Qed.

Lemma dcond_ext {T : choiceType}
    (P Q : {distr T / R}) (p : pred T) :
  P =1 Q ->
  dcond P p =1 dcond Q p.
Proof.
move=> HP x.
rewrite !dcondE.
exact: (prc_ext P Q (pred1 x) p HP).
Qed.

Lemma dmargin_ext {T U : choiceType} (f : T -> U) (P Q : {distr T / R}) :
  P =1 Q ->
  dmargin f P =1 dmargin f Q.
Proof.
move=> HPQ y.
rewrite !dmargin_psumE.
apply/eq_psum=> x.
by rewrite HPQ.
Qed.

Lemma dunit_dweight {T : choiceType} (x : T) :
  dweight (dunit x : {distr T / R}) = 1.
Admitted.

Lemma conditional_coordinate_dist_ext
  {n : nat}
  {A : choiceType}
  (P Q : {distr (n.-tuple A) / R})
  (i : 'I_n)
  (a : forall j : 'I_n, A) :
  P =1 Q ->
  conditional_coordinate P i a =1 conditional_coordinate Q i a.
Proof.
move=> HP.
apply: dmargin_ext.
exact: dcond_ext.
Qed.

Lemma tuple_prefix_eq_cat_prefix
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
  (Hi : (i < ℓ1.+1)%N)
  (omega1 : (ℓ1.+1).-tuple A)
  (omega2 : (ℓ2.+1).-tuple A) :
  let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
  let a0 : forall j : 'I_(ℓ1.+1), A :=
    fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
  tuple_prefix_eq i a (cat_tuple omega1 omega2) =
  tuple_prefix_eq i0 a0 omega1.
Admitted.

Lemma pythCombinedPrefixTrace_cat
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (omega1 : (ℓ1.+1).-tuple A)
  (omega2 : (ℓ2.+1).-tuple A) :
  pythCombinedPrefixTrace (fun j => tnth (cat_tuple omega1 omega2) j) =
  omega1.
Admitted.

Lemma tuple_prefix_eq_cat_suffix
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
  (Hi : (ℓ1.+1 <= i)%N)
  (omega1 omega1' : (ℓ1.+1).-tuple A)
  (omega2 : (ℓ2.+1).-tuple A) :
  pythCombinedPrefixTrace a = omega1 ->
  tuple_prefix_eq i a (cat_tuple omega1' omega2) =
    (omega1' == omega1) &&
    tuple_prefix_eq
      (pythCombinedSuffixIndex i Hi)
      (pythCombinedSuffixAssignment i Hi a)
      omega2.
Admitted.

Lemma pr_dlet_cat_prefix_lift_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R}) :
  (forall omega1, dweight (K0 omega1) = 1) ->
  forall
    (p : pred ((ℓ1.+1 + ℓ2.+1).-tuple A))
    (p0 : pred ((ℓ1.+1).-tuple A)),
    (forall omega1 omega2, p (cat_tuple omega1 omega2) = p0 omega1) ->
    \P_[
      \dlet_(omega1 <- P0)
      \dlet_(omega2 <- K0 omega1)
        dunit (cat_tuple omega1 omega2)
    ] p =
    \P_[P0] p0.
Admitted.

Lemma prc_dlet_cat_prefix_coordinate_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R}) :
  (forall omega1, dweight (K0 omega1) = 1) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
         (Hi : (i < ℓ1.+1)%N)
         (x : A),
    let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
    let a0 : forall j : 'I_(ℓ1.+1), A :=
      fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
    \P_[
      \dlet_(omega1 <- P0)
      \dlet_(omega2 <- K0 omega1)
        dunit (cat_tuple omega1 omega2),
      fun omega => tuple_prefix_eq i a omega
    ] [pred omega | tnth omega i \in pred1 x] =
    \P_[P0, fun omega1 => tuple_prefix_eq i0 a0 omega1]
      [pred omega1 | tnth omega1 i0 \in pred1 x].
Proof.
move=> Hmass i a Hi x /=.
rewrite /prc.
rewrite (pr_dlet_cat_prefix_lift_eq P0 K0 Hmass
  (fun omega =>
    (tnth omega i \in pred1 x) && tuple_prefix_eq i a omega)
  (fun omega1 =>
    (tnth omega1 (Ordinal Hi) \in pred1 x) &&
    tuple_prefix_eq (Ordinal Hi)
      (fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))))
      omega1)).
  rewrite (pr_dlet_cat_prefix_lift_eq P0 K0 Hmass
    (fun omega => tuple_prefix_eq i a omega)
    (fun omega1 => tuple_prefix_eq (Ordinal Hi)
      (fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))))
      omega1)) //.
  move=> omega1 omega2.
	  exact: tuple_prefix_eq_cat_prefix.
move=> omega1 omega2.
rewrite (cat_tuple_tnth_prefix_choice omega1 omega2 i Hi).
by rewrite (tuple_prefix_eq_cat_prefix i a Hi omega1 omega2).
Qed.


Lemma conditional_coordinate_dlet_cat_prefix_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R}) :
  (forall omega1, dweight (K0 omega1) = 1) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
         (Hi : (i < ℓ1.+1)%N),
    let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
    let a0 : forall j : 'I_(ℓ1.+1), A :=
      fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
    conditional_coordinate
      (\dlet_(omega1 <- P0)
       \dlet_(omega2 <- K0 omega1)
         dunit (cat_tuple omega1 omega2))
      i a
      =1 conditional_coordinate P0 i0 a0.
Proof.
move=> Hmass i a Hi /= x.
rewrite !pr_pred1.
rewrite !pr_dmargin.
rewrite !pr_dcond.
exact: (prc_dlet_cat_prefix_coordinate_eq P0 K0 Hmass i a Hi x).
Qed.

Lemma pythTraceKernelL_dweight1
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2)) :
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  forall omega : (ℓ1.+1).-tuple (nat * heap),
    dweight (pythTraceKernelL mid K omega) = 1.
Admitted.

Lemma pythTraceKernelR_dweight1
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2)) :
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  forall omega : (ℓ1.+1).-tuple (nat * heap),
    dweight (pythTraceKernelR mid K omega) = 1.
Admitted.

Lemma pythTraceBindL_conditional_coordinate_prefix_eq
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML : {distr (mid_t * heap) / R})
  (KL : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (P0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2)) :
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
         (Hi : (i < ℓ1.+1)%N),
    let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
    let a0 : forall j : 'I_(ℓ1.+1), nat * heap :=
      fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
    conditional_coordinate (pythTraceBindL ML KL mid P0 K) i a
      =1 conditional_coordinate P0 i0 a0.
Proof.
move=> HK i a Hi.
exact: (conditional_coordinate_dlet_cat_prefix_eq
  P0 (pythTraceKernelL mid K)
  (pythTraceKernelL_dweight1 mid s2 K HK) i a Hi).
Qed.

Lemma pythTraceBindR_conditional_coordinate_prefix_eq
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (MR : {distr (mid_t * heap) / R})
  (KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2)) :
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
         (Hi : (i < ℓ1.+1)%N),
    let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
    let a0 : forall j : 'I_(ℓ1.+1), nat * heap :=
      fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
    conditional_coordinate (pythTraceBindR MR KR mid Q0 K) i a
      =1 conditional_coordinate Q0 i0 a0.
Proof.
move=> HK i a Hi.
exact: (conditional_coordinate_dlet_cat_prefix_eq
  Q0 (pythTraceKernelR mid K)
  (pythTraceKernelR_dweight1 mid s2 K HK) i a Hi).
Qed.

Lemma pythTraceBindPair_conditional_coordinate_prefix_eqL
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
         (Hi : (i < ℓ1.+1)%N),
    let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
    let a0 : forall j : 'I_(ℓ1.+1), nat * heap :=
      fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
    conditional_coordinate P i a
      =1 conditional_coordinate P0 i0 a0.
Proof.
move=> [HP _] HK i a Hi /= x.
rewrite (conditional_coordinate_dist_ext P
  (pythTraceBindL ML KL mid P0 K) i a HP x).
exact: (pythTraceBindL_conditional_coordinate_prefix_eq
  ML KL mid s2 P0 K HK i a Hi x).
Qed.

Lemma pythTraceBindPair_conditional_coordinate_prefix_eqR
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
         (Hi : (i < ℓ1.+1)%N),
    let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
    let a0 : forall j : 'I_(ℓ1.+1), nat * heap :=
      fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
    conditional_coordinate Q i a
      =1 conditional_coordinate Q0 i0 a0.
Proof.
move=> [_ HQ] HK i a Hi /= x.
rewrite (conditional_coordinate_dist_ext Q
  (pythTraceBindR MR KR mid Q0 K) i a HQ x).
exact: (pythTraceBindR_conditional_coordinate_prefix_eq
  MR KR mid s2 Q0 K HK i a Hi x).
Qed.

Lemma pythTraceBindPair_conditional_coordinate_prefix_eq
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
         (Hi : (i < ℓ1.+1)%N),
    let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
    let a0 : forall j : 'I_(ℓ1.+1), nat * heap :=
      fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
    δ_KL (conditional_coordinate P i a)
         (conditional_coordinate Q i a) =
    δ_KL (conditional_coordinate P0 i0 a0)
         (conditional_coordinate Q0 i0 a0).
Proof.
move=> Hbind HK i a Hi.
apply: kl_ext.
- exact: (pythTraceBindPair_conditional_coordinate_prefix_eqL
    ML MR KL KR mid s2 P0 Q0 K P Q Hbind HK i a Hi).
- exact: (pythTraceBindPair_conditional_coordinate_prefix_eqR
    ML MR KL KR mid s2 P0 Q0 K P Q Hbind HK i a Hi).
Qed.

Lemma pythTraceBindPair_conditional_coordinate_bound_prefix_from_P0
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap),
    (i < ℓ1.+1)%N ->
    δ_KL (conditional_coordinate P i a)
         (conditional_coordinate Q i a) <=
      tnth (cat_tuple s1 s2) i.
Proof.
move=> Hbind [_ [_ [_ [_ Hcond0]]]] HK i a Hi.
pose i0 : 'I_(ℓ1.+1) := Ordinal Hi.
pose a0 : forall j : 'I_(ℓ1.+1), nat * heap :=
  fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))).
rewrite (pythTraceBindPair_conditional_coordinate_prefix_eq
  ML MR KL KR mid s2 P0 Q0 K P Q Hbind HK i a Hi).
rewrite (cat_tuple_tnth_prefix s1 s2 i Hi).
exact: (Hcond0 i0 a0).
Qed.

Lemma pythTraceBindPair_conditional_coordinate_bound_prefix
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap),
    (i < ℓ1.+1)%N ->
    δ_KL (conditional_coordinate P i a)
         (conditional_coordinate Q i a) <=
      tnth (cat_tuple s1 s2) i.
Proof.
move=> Hbind Hdist0 _ _ _ _ HK i a Hi.
exact: (pythTraceBindPair_conditional_coordinate_bound_prefix_from_P0
  ML MR KL KR mid s1 s2 P0 Q0 K P Q Hbind Hdist0
  HK i a Hi).
Qed.

Lemma divr_cancel_left_pos (a b c : R) :
  0 < a ->
  a * b / (a * c) = b / c.
Admitted.

Lemma expectation_indicator_eq
  {T : choiceType}
  (P0 : {distr T / R})
  (omega1 : T)
  (c : R) :
  \E_[P0] (fun omega1' => if omega1' == omega1 then c else 0) =
    P0 omega1 * c.
Proof.
rewrite /esp (sum_seq1 omega1).
- by rewrite eqxx mulrC.
- move=> omega1' Hnz.
  case Homega1' : (omega1' == omega1).
    by rewrite eq_sym Homega1'.
  move: Hnz.
  by rewrite Homega1' mul0r eqxx.
Qed.

Lemma pr_dlet_fixed_prefix_from_inner
  {T U : choiceType}
  (P0 : {distr T / R})
  (K0 : T -> {distr U / R})
  (omega1 : T)
  (p : pred U)
  (c : R) :
  (forall omega1',
    \P_[K0 omega1'] p =
      if omega1' == omega1 then c else 0) ->
  \P_[\dlet_(omega1 <- P0) K0 omega1] p =
    P0 omega1 * c.
Proof.
move=> Hinner.
rewrite pr_dlet.
rewrite (expectation_ext P0
  (fun omega1' => \P_[K0 omega1'] p)
  (fun omega1' => if omega1' == omega1 then c else 0)).
  exact: expectation_indicator_eq.
exact: Hinner.
Qed.

Lemma pr_dlet_cat_fixed_prefix_inner_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (omega1 omega1' : (ℓ1.+1).-tuple A)
  (p : pred ((ℓ1.+1 + ℓ2.+1).-tuple A))
  (q : pred ((ℓ2.+1).-tuple A)) :
  (forall omega1' omega2,
    p (cat_tuple omega1' omega2) = (omega1' == omega1) && q omega2) ->
  \P_[
    \dlet_(omega2 <- K0 omega1')
      dunit (cat_tuple omega1' omega2)
  ] p =
    if omega1' == omega1 then \P_[K0 omega1] q else 0.
Proof.
move=> Hp.
rewrite pr_dlet.
case Homega1' : (omega1' == omega1).
  move/eqP: Homega1'=> ->.
  rewrite [RHS]pr_exp.
  apply: expectation_ext=> omega2.
  by rewrite pr_dunit Hp eqxx.
rewrite -(exp0 (K0 omega1')).
apply: expectation_ext=> omega2.
by rewrite pr_dunit Hp Homega1'.
Qed.

Lemma pr_dlet_cat_fixed_prefix_event_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (omega1 : (ℓ1.+1).-tuple A)
  (p : pred ((ℓ1.+1 + ℓ2.+1).-tuple A))
  (q : pred ((ℓ2.+1).-tuple A)) :
  (forall omega1' omega2,
    p (cat_tuple omega1' omega2) = (omega1' == omega1) && q omega2) ->
  \P_[
    \dlet_(omega1 <- P0)
    \dlet_(omega2 <- K0 omega1)
      dunit (cat_tuple omega1 omega2)
  ] p =
  P0 omega1 * \P_[K0 omega1] q.
Proof.
move=> Hp.
apply: pr_dlet_fixed_prefix_from_inner=> omega1'.
exact: (pr_dlet_cat_fixed_prefix_inner_eq K0 omega1 omega1' p q Hp).
Qed.

Lemma pr_dlet_cat_suffix_prefix_event_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R}) :
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
         (Hi : (ℓ1.+1 <= i)%N)
         (omega1 : (ℓ1.+1).-tuple A),
    pythCombinedPrefixTrace a = omega1 ->
    0 < P0 omega1 ->
    \P_[
      \dlet_(omega1 <- P0)
      \dlet_(omega2 <- K0 omega1)
        dunit (cat_tuple omega1 omega2)
    ] (fun omega => tuple_prefix_eq i a omega) =
    P0 omega1 *
    \P_[K0 omega1]
      (fun omega2 =>
        tuple_prefix_eq
          (pythCombinedSuffixIndex i Hi)
          (pythCombinedSuffixAssignment i Hi a)
          omega2).
Proof.
move=> i a Hi omega1 Hprefix _.
apply: pr_dlet_cat_fixed_prefix_event_eq=> omega1' omega2.
exact: (tuple_prefix_eq_cat_suffix i a Hi omega1 omega1' omega2 Hprefix).
Qed.

Lemma pr_dlet_cat_suffix_coordinate_event_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R}) :
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
         (Hi : (ℓ1.+1 <= i)%N)
         (omega1 : (ℓ1.+1).-tuple A)
         (x : A),
    pythCombinedPrefixTrace a = omega1 ->
    0 < P0 omega1 ->
    \P_[
      \dlet_(omega1 <- P0)
      \dlet_(omega2 <- K0 omega1)
        dunit (cat_tuple omega1 omega2)
    ] (fun omega =>
      (tnth omega i \in pred1 x) && tuple_prefix_eq i a omega) =
    P0 omega1 *
    \P_[K0 omega1]
      (fun omega2 =>
        (tnth omega2 (pythCombinedSuffixIndex i Hi) \in pred1 x) &&
        tuple_prefix_eq
          (pythCombinedSuffixIndex i Hi)
          (pythCombinedSuffixAssignment i Hi a)
          omega2).
Proof.
move=> i a Hi omega1 x Hprefix _.
apply: pr_dlet_cat_fixed_prefix_event_eq=> omega1' omega2.
rewrite (cat_tuple_tnth_suffix_choice omega1' omega2 i Hi).
rewrite (tuple_prefix_eq_cat_suffix i a Hi omega1 omega1' omega2 Hprefix).
by case: (tnth omega2 (pythCombinedSuffixIndex i Hi) \in pred1 x);
   case: (omega1' == omega1);
   case: (tuple_prefix_eq (pythCombinedSuffixIndex i Hi)
     (pythCombinedSuffixAssignment i Hi a) omega2).
Qed.

Lemma prc_dlet_cat_suffix_coordinate_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R}) :
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
         (Hi : (ℓ1.+1 <= i)%N)
         (omega1 : (ℓ1.+1).-tuple A)
         (x : A),
    pythCombinedPrefixTrace a = omega1 ->
    0 < P0 omega1 ->
    \P_[
      \dlet_(omega1 <- P0)
      \dlet_(omega2 <- K0 omega1)
        dunit (cat_tuple omega1 omega2),
      fun omega => tuple_prefix_eq i a omega
    ] [pred omega | tnth omega i \in pred1 x] =
    \P_[K0 omega1,
      fun omega2 =>
        tuple_prefix_eq
          (pythCombinedSuffixIndex i Hi)
          (pythCombinedSuffixAssignment i Hi a)
          omega2
    ] [pred omega2 |
      tnth omega2 (pythCombinedSuffixIndex i Hi) \in pred1 x].
Proof.
move=> i a Hi omega1 x Hprefix Hpos.
rewrite /prc.
rewrite (pr_dlet_cat_suffix_coordinate_event_eq
  P0 K0 i a Hi omega1 x Hprefix Hpos).
rewrite (pr_dlet_cat_suffix_prefix_event_eq
  P0 K0 i a Hi omega1 Hprefix Hpos).
exact: divr_cancel_left_pos.
Qed.

Lemma conditional_coordinate_dlet_cat_suffix_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R}) :
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
         (Hi : (ℓ1.+1 <= i)%N)
         (omega1 : (ℓ1.+1).-tuple A),
    pythCombinedPrefixTrace a = omega1 ->
    0 < P0 omega1 ->
    conditional_coordinate
      (\dlet_(omega1 <- P0)
       \dlet_(omega2 <- K0 omega1)
         dunit (cat_tuple omega1 omega2))
      i a
      =1 conditional_coordinate (K0 omega1)
          (pythCombinedSuffixIndex i Hi)
          (pythCombinedSuffixAssignment i Hi a).
Proof.
move=> i a Hi omega1 Hprefix Hpos x.
rewrite !pr_pred1.
rewrite !pr_dmargin.
rewrite !pr_dcond.
exact: (prc_dlet_cat_suffix_coordinate_eq
  P0 K0 i a Hi omega1 x Hprefix Hpos).
Qed.

Lemma absolute_continuous_positive
  {T : choiceType}
  (P Q : {distr T / R}) :
  absolute_continuous P Q ->
  forall x, 0 < P x -> 0 < Q x.
Proof.
move=> Hac x HPx.
rewrite lt_def ge0_mu andbT.
apply/negP=> /eqP HQx0.
have HPx0 := Hac x HQx0.
by rewrite HPx0 ltxx in HPx.
Qed.

Lemma expectation_dnull
  {T : choiceType}
  (f : T -> R) :
  \E_[dnull] f = 0.
Proof.
rewrite /esp (eq_sum (F2 := fun _ : T => 0)).
  exact: sum0.
by move=> x; rewrite dnullE mulr0.
Qed.

Lemma kl_left_dnull
  {T : choiceType}
  (P Q : {distr T / R}) :
  P =1 dnull ->
  δ_KL P Q = 0.
Proof.
move=> HP.
rewrite /δ_KL.
rewrite (expectation_distr_ext P dnull _ HP).
exact: expectation_dnull.
Qed.

Lemma conditional_coordinate_zero_prefix
  {n : nat}
  {A : choiceType}
  (P : {distr (n.-tuple A) / R})
  (i : 'I_n)
  (a : forall j : 'I_n, A) :
  \P_[P] (fun omega => tuple_prefix_eq i a omega) = 0 ->
  conditional_coordinate P i a =1 dnull.
Proof.
move=> Hzero x.
rewrite pr_pred1 dnullE.
rewrite /conditional_coordinate pr_dmargin pr_dcond /prc Hzero.
by rewrite invr0 mulr0.
Qed.

Lemma pythTraceBindPair_conditional_coordinate_suffix_bound_zero_prefix
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
         (Hi : (ℓ1.+1 <= i)%N),
    P0 (pythCombinedPrefixTrace a) = 0 ->
    δ_KL (conditional_coordinate P i a)
         (conditional_coordinate Q i a) <=
      tnth s2 (pythCombinedSuffixIndex i Hi).
Proof.
move=> Hbind Hdist0 HmarginL0 _ HmidL _ HK i a Hi HP0z.
have Hs2 : 0 <= tnth s2 (pythCombinedSuffixIndex i Hi) :=
  pythTraceBindPair_s2_nonneg ML mid s1 s2 P0 Q0 K
    Hdist0 HmarginL0 HmidL HK (pythCombinedSuffixIndex i Hi).
have HPprefix0 :
    \P_[P] (fun omega => tuple_prefix_eq i a omega) = 0.
  case: Hbind=> HP _.
  rewrite (pr_ext P (pythTraceBindL ML KL mid P0 K)
    (fun omega => tuple_prefix_eq i a omega) HP).
  rewrite (pr_dlet_cat_fixed_prefix_event_eq
    P0 (pythTraceKernelL mid K) (pythCombinedPrefixTrace a)
    (fun omega => tuple_prefix_eq i a omega)
    (fun omega2 =>
      tuple_prefix_eq
        (pythCombinedSuffixIndex i Hi)
        (pythCombinedSuffixAssignment i Hi a)
        omega2)).
    by rewrite HP0z mul0r.
  move=> omega1' omega2.
  exact: (tuple_prefix_eq_cat_suffix i a Hi
    (pythCombinedPrefixTrace a) omega1' omega2 erefl).
rewrite (kl_left_dnull
  (conditional_coordinate P i a)
  (conditional_coordinate Q i a)
  (conditional_coordinate_zero_prefix P i a HPprefix0)).
exact: Hs2.
Qed.

Lemma pythTraceKernelL_valid_mid
  {ℓ1 ℓ2 : nat}
  {mid_t : choice_type}
  (mid : pred (mid_t * heap))
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (omega1 : (ℓ1.+1).-tuple (nat * heap))
  (y : { y : mid_t * heap | mid y }) :
    @decode_output_heap mid_t (tnth omega1 ord_max) = Some (proj1_sig y) ->
  pythTraceKernelL mid K omega1 = (K y).1.
Proof.
case: y=> y Hy /= Hdecode.
rewrite /pythTraceKernelL Hdecode.
destruct (@idP (mid y)) as [Hy'|Hy'].
  by rewrite (eq_irrelevance Hy' Hy).
by case: Hy'.
Qed.

Lemma pythTraceKernelR_valid_mid
  {ℓ1 ℓ2 : nat}
  {mid_t : choice_type}
  (mid : pred (mid_t * heap))
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (omega1 : (ℓ1.+1).-tuple (nat * heap))
  (y : { y : mid_t * heap | mid y }) :
    @decode_output_heap mid_t (tnth omega1 ord_max) = Some (proj1_sig y) ->
  pythTraceKernelR mid K omega1 = (K y).2.
Proof.
case: y=> y Hy /= Hdecode.
rewrite /pythTraceKernelR Hdecode.
destruct (@idP (mid y)) as [Hy'|Hy'].
  by rewrite (eq_irrelevance Hy' Hy).
by case: Hy'.
Qed.

Lemma pythTraceBindPair_conditional_coordinate_suffix_eqL_valid_mid
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
         (Hi : (ℓ1.+1 <= i)%N)
         (y : { y : mid_t * heap | mid y }),
    @decode_output_heap mid_t
      (tnth (pythCombinedPrefixTrace a) ord_max) =
      Some (proj1_sig y) ->
    0 < P0 (pythCombinedPrefixTrace a) ->
    conditional_coordinate P i a
      =1 conditional_coordinate (K y).1
          (pythCombinedSuffixIndex i Hi)
          (pythCombinedSuffixAssignment i Hi a).
Proof.
move=> [HP _] _ _ _ _ _ i a Hi y Hy Hpos x.
rewrite (conditional_coordinate_dist_ext P
  (pythTraceBindL ML KL mid P0 K) i a HP x).
pose omega1 := pythCombinedPrefixTrace a.
rewrite (conditional_coordinate_dlet_cat_suffix_eq
  P0 (pythTraceKernelL mid K) i a Hi omega1 erefl Hpos x).
rewrite (pythTraceKernelL_valid_mid mid K omega1 y Hy).
by [].
Qed.

Lemma pythTraceBindPair_conditional_coordinate_suffix_eqR_valid_mid
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
         (Hi : (ℓ1.+1 <= i)%N)
         (y : { y : mid_t * heap | mid y }),
    @decode_output_heap mid_t
      (tnth (pythCombinedPrefixTrace a) ord_max) =
      Some (proj1_sig y) ->
    0 < Q0 (pythCombinedPrefixTrace a) ->
    conditional_coordinate Q i a
      =1 conditional_coordinate (K y).2
          (pythCombinedSuffixIndex i Hi)
          (pythCombinedSuffixAssignment i Hi a).
Proof.
move=> [_ HQ] _ _ _ _ _ i a Hi y Hy Hpos x.
rewrite (conditional_coordinate_dist_ext Q
  (pythTraceBindR MR KR mid Q0 K) i a HQ x).
pose omega1 := pythCombinedPrefixTrace a.
rewrite (conditional_coordinate_dlet_cat_suffix_eq
  Q0 (pythTraceKernelR mid K) i a Hi omega1 erefl Hpos x).
rewrite (pythTraceKernelR_valid_mid mid K omega1 y Hy).
by [].
Qed.

Lemma pythTraceBindPair_conditional_coordinate_suffix_eq_valid_mid
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
         (Hi : (ℓ1.+1 <= i)%N)
         (y : { y : mid_t * heap | mid y }),
    @decode_output_heap mid_t
      (tnth (pythCombinedPrefixTrace a) ord_max) =
      Some (proj1_sig y) ->
    0 < P0 (pythCombinedPrefixTrace a) ->
    0 < Q0 (pythCombinedPrefixTrace a) ->
    δ_KL (conditional_coordinate P i a)
         (conditional_coordinate Q i a) =
    δ_KL (conditional_coordinate (K y).1
            (pythCombinedSuffixIndex i Hi)
            (pythCombinedSuffixAssignment i Hi a))
         (conditional_coordinate (K y).2
            (pythCombinedSuffixIndex i Hi)
            (pythCombinedSuffixAssignment i Hi a)).
Proof.
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR i a Hi y Hy HPpos HQpos.
apply: kl_ext.
- exact: (pythTraceBindPair_conditional_coordinate_suffix_eqL_valid_mid
  ML MR KL KR mid s1 s2 P0 Q0 K P Q
  Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR i a Hi y Hy HPpos).
- exact: (pythTraceBindPair_conditional_coordinate_suffix_eqR_valid_mid
  ML MR KL KR mid s1 s2 P0 Q0 K P Q
  Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR i a Hi y Hy HQpos).
Qed.

Lemma pythTraceBindPair_conditional_coordinate_suffix_bound_valid_mid
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
         (Hi : (ℓ1.+1 <= i)%N)
         (y : { y : mid_t * heap | mid y }),
    @decode_output_heap mid_t
      (tnth (pythCombinedPrefixTrace a) ord_max) =
      Some (proj1_sig y) ->
    δ_KL (conditional_coordinate P i a)
         (conditional_coordinate Q i a) <=
      tnth s2 (pythCombinedSuffixIndex i Hi).
Proof.
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK i a Hi y Hy.
move: Hdist0=> [Hs1 [Hac0 [HP0mass [HQ0mass Hcond0]]]].
have Hdist0 : pythDist P0 Q0 s1.
  by split; first exact: Hs1; split; first exact: Hac0;
     split; first exact: HP0mass; split; first exact: HQ0mass.
case HP0z: (P0 (pythCombinedPrefixTrace a) == 0).
  exact: (pythTraceBindPair_conditional_coordinate_suffix_bound_zero_prefix
    ML MR KL KR mid s1 s2 P0 Q0 K P Q
    Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK i a Hi
    (eqP HP0z)).
have HP0pos : 0 < P0 (pythCombinedPrefixTrace a).
  by rewrite lt_def ge0_mu HP0z.
have HQ0pos : 0 < Q0 (pythCombinedPrefixTrace a).
  exact: (absolute_continuous_positive P0 Q0 Hac0 _ HP0pos).
rewrite (pythTraceBindPair_conditional_coordinate_suffix_eq_valid_mid
  ML MR KL KR mid s1 s2 P0 Q0 K P Q
  Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR i a Hi y Hy
  HP0pos HQ0pos).
case: (HK y)=> _ [_ [_ [_ Hcond]]].
exact: (Hcond (pythCombinedSuffixIndex i Hi)
  (pythCombinedSuffixAssignment i Hi a)).
Qed.

Lemma pythTraceBindPair_conditional_coordinate_suffix_bound_decode_none
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
         (Hi : (ℓ1.+1 <= i)%N),
    @decode_output_heap mid_t
      (tnth (pythCombinedPrefixTrace a) ord_max) = None ->
    δ_KL (conditional_coordinate P i a)
         (conditional_coordinate Q i a) <=
      tnth s2 (pythCombinedSuffixIndex i Hi).
Admitted.

Lemma pythTraceBindPair_conditional_coordinate_suffix_bound_not_mid
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
         (Hi : (ℓ1.+1 <= i)%N)
         (y : mid_t * heap),
    @decode_output_heap mid_t
      (tnth (pythCombinedPrefixTrace a) ord_max) = Some y ->
    ~~ mid y ->
    δ_KL (conditional_coordinate P i a)
         (conditional_coordinate Q i a) <=
      tnth s2 (pythCombinedSuffixIndex i Hi).
Admitted.

Lemma pythTraceBindPair_conditional_coordinate_suffix_bound_from_kernel
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
         (Hi : (ℓ1.+1 <= i)%N),
    δ_KL (conditional_coordinate P i a)
         (conditional_coordinate Q i a) <=
      tnth s2 (Ordinal (cat_tuple_suffix_bound i Hi)).
Proof.
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK i a Hi.
case Hdecode:
    (@decode_output_heap mid_t
      (tnth (pythCombinedPrefixTrace a) ord_max))=> [y|].
  case Hmidy: (mid y).
  - have Hy : mid y by rewrite Hmidy.
    exact: (pythTraceBindPair_conditional_coordinate_suffix_bound_valid_mid
      ML MR KL KR mid s1 s2 P0 Q0 K P Q
      Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK
      i a Hi (exist _ y Hy) Hdecode).
  - exact: (pythTraceBindPair_conditional_coordinate_suffix_bound_not_mid
      ML MR KL KR mid s1 s2 P0 Q0 K P Q
      Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK
      i a Hi y Hdecode (negbT Hmidy)).
- exact: (pythTraceBindPair_conditional_coordinate_suffix_bound_decode_none
    ML MR KL KR mid s1 s2 P0 Q0 K P Q
    Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK i a Hi Hdecode).
Qed.


Lemma pythTraceBindPair_conditional_coordinate_bound_suffix_from_K
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap),
    (ℓ1.+1 <= i)%N ->
    δ_KL (conditional_coordinate P i a)
         (conditional_coordinate Q i a) <=
      tnth (cat_tuple s1 s2) i.
Proof.
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK i a Hi.
rewrite (cat_tuple_tnth_suffix s1 s2 i Hi).
exact: (pythTraceBindPair_conditional_coordinate_suffix_bound_from_kernel
  ML MR KL KR mid s1 s2 P0 Q0 K P Q
  Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK i a Hi).
Qed.

Lemma pythTraceBindPair_conditional_coordinate_bound_suffix
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap),
    (ℓ1.+1 <= i)%N ->
    δ_KL (conditional_coordinate P i a)
         (conditional_coordinate Q i a) <=
      tnth (cat_tuple s1 s2) i.
Proof.
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK i a Hi.
exact: (pythTraceBindPair_conditional_coordinate_bound_suffix_from_K
  ML MR KL KR mid s1 s2 P0 Q0 K P Q
  Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK i a Hi).
Qed.

Lemma pythTraceBindPair_conditional_coordinate_bound
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
         (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap),
    δ_KL (conditional_coordinate P i a)
         (conditional_coordinate Q i a) <=
      tnth (cat_tuple s1 s2) i.
Proof.
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK i a.
case: (ltnP i ℓ1.+1)=> Hi.
- exact: (pythTraceBindPair_conditional_coordinate_bound_prefix
    ML MR KL KR mid s1 s2 P0 Q0 K P Q
    Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK i a Hi).
- exact: (pythTraceBindPair_conditional_coordinate_bound_suffix
    ML MR KL KR mid s1 s2 P0 Q0 K P Q
    Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK i a Hi).
Qed.

Lemma pythTraceBindPair_pythDist
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  pythDist P Q (cat_tuple s1 s2).
Proof.
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK.
move: Hdist0=> [Hs1 [Hac0 [HP0 [HQ0 Hcond0]]]].
have Hdist0 : pythDist P0 Q0 s1.
  by split; first exact: Hs1; split; first exact: Hac0;
     split; first exact: HP0; split; first exact: HQ0.
have Hs2 : forall i : 'I_(ℓ2.+1), 0 <= tnth s2 i :=
  pythTraceBindPair_s2_nonneg ML mid s1 s2 P0 Q0 K
    Hdist0 HmarginL0 HmidL HK.
split.
- apply: cat_tuple_nonneg.
  + exact: Hs1.
  + exact: Hs2.
split.
- exact: (pythTraceBindPair_absolute_continuous
    ML MR KL KR mid s1 s2 P0 Q0 K P Q
    Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK).
split.
- exact: (pythTraceBindPair_dweightL
    ML MR KL KR mid s1 s2 P0 Q0 K P Q
    Hbind Hdist0 HmarginL0 HmidL HK).
split.
- exact: (pythTraceBindPair_dweightR
    ML MR KL KR mid s1 s2 P0 Q0 K P Q
    Hbind Hdist0 HmarginR0 HmidR HK).
- exact: (pythTraceBindPair_conditional_coordinate_bound
    ML MR KL KR mid s1 s2 P0 Q0 K P Q
    Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK).
Qed.

Lemma pythTraceBindL_final_margin
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML : {distr (mid_t * heap) / R})
  (KL : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (P0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2)) :
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y,
    dmargin (fun omega => tnth omega ord_max) (K y).1
      =1 dmargin (@pack_output_heap out_t) (KL (proj1_sig y))) ->
  dmargin (fun omega => tnth omega ord_max)
    (pythTraceBindL ML KL mid P0 K)
    =1 dmargin (@pack_output_heap out_t) (\dlet_(y <- ML) KL y).
Admitted.

Lemma pythTraceBindR_final_margin
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (MR : {distr (mid_t * heap) / R})
  (KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2)) :
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y,
    dmargin (fun omega => tnth omega ord_max) (K y).2
      =1 dmargin (@pack_output_heap out_t) (KR (proj1_sig y))) ->
  dmargin (fun omega => tnth omega ord_max)
    (pythTraceBindR MR KR mid Q0 K)
    =1 dmargin (@pack_output_heap out_t) (\dlet_(y <- MR) KR y).
Admitted.

Lemma pythTraceBindPair_final_margins
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y,
    dmargin (fun omega => tnth omega ord_max) (K y).1
      =1 dmargin (@pack_output_heap out_t) (KL (proj1_sig y))) ->
  (forall y,
    dmargin (fun omega => tnth omega ord_max) (K y).2
      =1 dmargin (@pack_output_heap out_t) (KR (proj1_sig y))) ->
  dmargin (fun omega => tnth omega ord_max) P
    =1 dmargin (@pack_output_heap out_t) (\dlet_(y <- ML) KL y) /\
  dmargin (fun omega => tnth omega ord_max) Q
    =1 dmargin (@pack_output_heap out_t) (\dlet_(y <- MR) KR y).
Proof.
move=> [HP HQ] HmarginL0 HmarginR0 HmidL HmidR HKL HKR.
split.
- move=> z.
  rewrite (dmargin_ext (fun omega => tnth omega ord_max)
    P (pythTraceBindL ML KL mid P0 K) HP z).
  exact: (pythTraceBindL_final_margin ML KL mid P0 K
    HmarginL0 HmidL HKL z).
- move=> z.
  rewrite (dmargin_ext (fun omega => tnth omega ord_max)
    Q (pythTraceBindR MR KR mid Q0 K) HQ z).
  exact: (pythTraceBindR_final_margin MR KR mid Q0 K
    HmarginR0 HmidR HKR z).
Qed.

Lemma pythTraceBindPair_post
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y : { y : mid_t * heap | mid y },
    forall x, x \in dinsupp (KL (proj1_sig y)) -> post x) ->
  (forall y : { y : mid_t * heap | mid y },
    forall x, x \in dinsupp (KR (proj1_sig y)) -> post x) ->
  (forall x, x \in dinsupp (\dlet_(y <- ML) KL y) -> post x) /\
  (forall x, x \in dinsupp (\dlet_(y <- MR) KR y) -> post x).
Proof.
move=> _ HmidL HmidR HpostL HpostR.
split.
- move=> x Hx.
  have [y Hy Hinner] := @dinsupp_dlet R _ _ KL ML x Hx.
  have Hy_mid := HmidL y Hy.
  have Hx_inner : x \in dinsupp (KL y).
    by rewrite in_dinsupp.
  exact: (HpostL (exist _ y Hy_mid) x Hx_inner).
- move=> x Hx.
  have [y Hy Hinner] := @dinsupp_dlet R _ _ KR MR x Hx.
  have Hy_mid := HmidR y Hy.
  have Hx_inner : x \in dinsupp (KR y).
    by rewrite in_dinsupp.
  exact: (HpostR (exist _ y Hy_mid) x Hx_inner).
Qed.

Lemma pythDist_bind_pyth_kernel_witness
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2)) :
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y,
    pythKernelSpec
      (KL (proj1_sig y)) (KR (proj1_sig y)) post s2 (K y)) ->
  exists (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}),
    pythDist P Q (cat_tuple s1 s2) /\
    dmargin (fun omega => tnth omega ord_max) P
      =1 dmargin (@pack_output_heap out_t) (\dlet_(y <- ML) KL y) /\
    dmargin (fun omega => tnth omega ord_max) Q
      =1 dmargin (@pack_output_heap out_t) (\dlet_(y <- MR) KR y) /\
    (forall x, x \in dinsupp (\dlet_(y <- ML) KL y) -> post x) /\
    (forall x, x \in dinsupp (\dlet_(y <- MR) KR y) -> post x).
Proof.
move=> Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK.
have [P [Q Hbind]] :=
  pythTraceBindPair_exists ML MR KL KR mid P0 Q0 K.
exists P, Q.
have Hdist :
    pythDist P Q (cat_tuple s1 s2).
  apply: (pythTraceBindPair_pythDist
    ML MR KL KR mid s1 s2 P0 Q0 K P Q Hbind
    Hdist0 HmarginL0 HmarginR0 HmidL HmidR).
  move=> y.
  exact: (pythKernelSpec_dist _ _ _ _ _ (HK y)).
have [HmarginL HmarginR] :
    dmargin (fun omega => tnth omega ord_max) P
      =1 dmargin (@pack_output_heap out_t) (\dlet_(y <- ML) KL y) /\
    dmargin (fun omega => tnth omega ord_max) Q
      =1 dmargin (@pack_output_heap out_t) (\dlet_(y <- MR) KR y).
  apply: (pythTraceBindPair_final_margins
    ML MR KL KR mid P0 Q0 K P Q Hbind
    HmarginL0 HmarginR0 HmidL HmidR).
  - move=> y.
    exact: (pythKernelSpec_marginL _ _ _ _ _ (HK y)).
  - move=> y.
    exact: (pythKernelSpec_marginR _ _ _ _ _ (HK y)).
have [HpostL HpostR] :
    (forall x, x \in dinsupp (\dlet_(y <- ML) KL y) -> post x) /\
    (forall x, x \in dinsupp (\dlet_(y <- MR) KR y) -> post x).
  apply: (pythTraceBindPair_post
    ML MR KL KR mid post P0 Q0 K P Q Hbind HmidL HmidR).
  - move=> y.
    exact: (pythKernelSpec_postL _ _ _ _ _ (HK y)).
  - move=> y.
    exact: (pythKernelSpec_postR _ _ _ _ _ (HK y)).
split; first exact: Hdist.
split; first exact: HmarginL.
split; first exact: HmarginR.
by split.
Qed.

Lemma pythDist_bind_pyth_kernel
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R}) :
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, mid y ->
    exists (P Q : {distr ((ℓ2.+1).-tuple (nat * heap)) / R}),
      pythDist P Q s2 /\
      dmargin (fun omega => tnth omega ord_max) P
        =1 dmargin (@pack_output_heap out_t) (KL y) /\
      dmargin (fun omega => tnth omega ord_max) Q
        =1 dmargin (@pack_output_heap out_t) (KR y) /\
      (forall x, x \in dinsupp (KL y) -> post x) /\
      (forall x, x \in dinsupp (KR y) -> post x)) ->
  exists (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R}),
    pythDist P Q (cat_tuple s1 s2) /\
    dmargin (fun omega => tnth omega ord_max) P
      =1 dmargin (@pack_output_heap out_t) (\dlet_(y <- ML) KL y) /\
    dmargin (fun omega => tnth omega ord_max) Q
      =1 dmargin (@pack_output_heap out_t) (\dlet_(y <- MR) KR y) /\
    (forall x, x \in dinsupp (\dlet_(y <- ML) KL y) -> post x) /\
    (forall x, x \in dinsupp (\dlet_(y <- MR) KR y) -> post x).
Proof.
move=> Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hcont.
have Hcont' :
    forall y, mid y ->
      exists (P Q : {distr ((ℓ2.+1).-tuple (nat * heap)) / R}),
        pythKernelSpec (KL y) (KR y) post s2 (P, Q).
  move=> y Hy.
  have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
    Hcont y Hy.
  by exists P, Q.
have [K HK] :=
  pythKernel_choice KL KR mid post s2 Hcont'.
exact:
  (pythDist_bind_pyth_kernel_witness ML MR KL KR mid post s1 s2 P0 Q0 K
    Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK).
Qed.

Lemma aePythSeqRule
  {ℓ : nat}
  {in_t mid_t out_t : choice_type}
  (progL progR : in_t -> raw_code mid_t)
  (contL contR : mid_t -> raw_code out_t)
  (pre : pred ((in_t * heap) * (in_t * heap)))
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :
  ⊨AE ⦃ pre ⦄ progL ≈( 0 ) progR ⦃
    fun outs =>
      let '((yL, memL'), (yR, memR')) := outs in
      (yL == yR) && (memL' == memR') && mid (yL, memL') ⦄ ->
  ⊨Pyth ⦃
    fun xs =>
      let '((xL, memL), (xR, memR)) := xs in
      (xL == xR) && (memL == memR) && mid (xL, memL)
  ⦄ contL ≈( s ) contR ⦃ post ⦄ ->
  ⊨Pyth ⦃ pre ⦄
    (fun xL => yL ← progL xL ;; contL yL)
    ≈( 0 :: s )
    (fun xR => yR ← progR xR ;; contR yR)
  ⦃ post ⦄.
Proof.
move=> Hae Hpyth.
apply: (pythSeq1Rule progL progR contL contR pre mid post 0 s).
- exact: aeEqPyth1Rule Hae.
- exact: Hpyth.
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
move=> Hpyth1 Hpyth2 memL memR xL xR Hpre.
have [P0 [Q0 [Hdist0 [HmarginL0 [HmarginR0 [HmidL HmidR]]]]]] :=
  Hpyth1 memL memR xL xR Hpre.
set ML := Pr_code (progL xL) memL.
set MR := Pr_code (progR xR) memR.
set KL := fun y : mid_t * heap => Pr_code (contL y.1) y.2.
set KR := fun y : mid_t * heap => Pr_code (contR y.1) y.2.
have Hcont :
    forall y, mid y ->
      exists (P Q : {distr ((ℓ2.+1).-tuple (nat * heap)) / R}),
        pythDist P Q s2 /\
        dmargin (fun omega => tnth omega ord_max) P
          =1 dmargin (@pack_output_heap out_t) (KL y) /\
        dmargin (fun omega => tnth omega ord_max) Q
          =1 dmargin (@pack_output_heap out_t) (KR y) /\
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
  pythDist_bind_pyth_kernel ML MR KL KR mid post s1 s2 P0 Q0
    Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hcont.
exists P, Q.
rewrite !Pr_code_bind.
split; first exact: Hdist.
split; first exact: HmarginL.
split; first exact: HmarginR.
by split.
Qed.

Lemma pythCompileCallsRule
  (q : nat) (X Y A B : choice_type)
  (L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (prog : A -> raw_code B)
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
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => code_link
      (compile_calls q.+1 (X := X) (Y := Y) P' fn (prog x))
      P')
    ≈( nseq (q.+1) eps )
    (fun x => code_link
      (compile_calls q.+1 (X := X) (Y := Y) P'' fn (prog x))
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
Admitted.
