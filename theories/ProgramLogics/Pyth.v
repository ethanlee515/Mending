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
Admitted.

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
