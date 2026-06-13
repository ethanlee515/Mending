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
From Mending.Probability Require Import Ae OutputHeap CompletedPythSeq.
From Mending.Probability.KL Require Import Pyth.
From Mending.ProgramLogics Require Import Ae Hoare Pyth.
Local Open Scope AeNotations.
Local Open Scope HoareNotations.
Local Open Scope PythNotations.

Import PackageNotation.
Import pkg_heap.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope package_scope.
Local Open Scope ring_scope.

Definition complete_output_heap {out_t : choice_type}
    (out : {distr (out_t * heap) / R}) :
    {distr (option (nat * heap)) / R} :=
  complete (dmargin (@pack_output_heap out_t) out).

Definition completedPythJudgment
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

Declare Scope CompletedPythNotations.
Local Open Scope CompletedPythNotations.

Notation "⊨CPyth ⦃ pre ⦄ progL ≈( s ) progR ⦃ post ⦄" :=
  (completedPythJudgment progL progR pre post s)
  : CompletedPythNotations.

Notation "⊨CPyth1 ⦃ pre ⦄ progL ≈( eps ) progR ⦃ post ⦄" :=
  (completedPythJudgment progL progR pre post [tuple eps])
  : CompletedPythNotations.

Lemma completedPythConseqRule
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
  ⊨CPyth ⦃ pre ⦄ progL ≈( s ) progR ⦃ post ⦄ ->
  ⊨CPyth ⦃ pre' ⦄ progL ≈( s' ) progR ⦃ post' ⦄.
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

Lemma pythCompletedRule
  {ℓ : nat}
  {inL_t inR_t out_t : choice_type}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :
  ⊨Pyth ⦃ pre ⦄ progL ≈( s ) progR ⦃ post ⦄ ->
  ⊨CPyth ⦃ pre ⦄ progL ≈( s ) progR ⦃ post ⦄.
Admitted.

Lemma total_variation_complete_output_heap_ge
  {out_t : choice_type} (P Q : {distr (out_t * heap) / R}) :
  total_variation P Q <=
  total_variation (complete_output_heap P) (complete_output_heap Q).
Proof.
rewrite (total_variation_pack_output_heap P Q).
rewrite /complete_output_heap.
set P' := dmargin _ P.
set Q' := dmargin _ Q.
rewrite /total_variation.
apply: ler_wpM2l.
  by lra.
rewrite -!psum_sum; try by move=> x; exact: normr_ge0.
set S := fun x : option (nat * heap) => `|complete P' x - complete Q' x|.
have HSnonneg : forall x, 0 <= S x by move=> x; exact: normr_ge0.
have HSsumm : summable S.
  apply/summable_abs.
  apply: summableD; first exact: summable_mu.
  by apply: summableN; exact: summable_mu.
have -> : psum (fun x : nat * heap => `|P' x - Q' x|) =
    psum (fun x : nat * heap => S (Some x)).
  apply/eq_psum=> x.
  by rewrite /S !completeE.
rewrite (psum_option_split S HSnonneg HSsumm).
by rewrite lerDl.
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
have Hae : ⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃
    fun outs =>
      let '((yL, memL'), (yR, memR')) := outs in
      (yL == yR) && (memL' == memR') ⦄.
  apply: (additiveErrorTvdEqRule progL progR pre ε)=> //.
  move=> memL memR xL xR Hpre.
  exact: (le_trans (total_variation_complete_output_heap_ge _ _)
           (Htv memL memR xL xR Hpre)).
move: Hae=> [_ Hae].
split; first exact: Heps.
move=> memL memR xL xR Hpre.
have [d [Hd Hprob]] := Hae memL memR xL xR Hpre.
exists d; split; first exact: Hd.
apply: (le_trans Hprob).
apply: subset_pr=> out Hout.
case: out Hout=> [[outL|] [outR|]] //=.
case: outL outR=> yL memL' [yR memR'] /= Hout.
apply/eqP.
move/andP: Hout=> [/eqP -> /eqP ->].
by [].
Qed.

Lemma completedMicciancioWalterRule
  {ℓ : nat}
  {inL_t inR_t out_t : choice_type}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :
  ⊨CPyth ⦃ pre ⦄ progL ≈( s ) progR ⦃ post ⦄ ->
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


Lemma completedPythDnullRule
  {ℓ : nat}
  {inL_t inR_t out_t : choice_type}
  (progL : inL_t -> raw_code out_t)
  (progR : inR_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :
  (forall i : 'I_(ℓ.+1), 0 <= tnth s i) ->
  (forall memL memR xL xR,
    pre ((xL, memL), (xR, memR)) ->
    Pr_code (progL xL) memL =1 dnull) ->
  (forall memL memR xL xR,
    pre ((xL, memL), (xR, memR)) ->
    Pr_code (progR xR) memR =1 dnull) ->
  ⊨CPyth ⦃ pre ⦄ progL ≈( s ) progR ⦃ post ⦄.
Admitted.

Lemma completedPythAeSeqRule
  {ℓ : nat}
  {inL_t inR_t mid_t out_t : choice_type}
  (progL : inL_t -> raw_code mid_t)
  (progR : inR_t -> raw_code mid_t)
  (cont : mid_t -> raw_code out_t)
  (pre : pred ((inL_t * heap) * (inR_t * heap)))
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :
  ⊨CPyth ⦃ pre ⦄ progL ≈( s ) progR ⦃ mid ⦄ ->
  ⊨Hoare ⦃ mid ⦄ cont ⦃ post ⦄ ->
  ⊨CPyth ⦃ pre ⦄
    (fun xL => yL ← progL xL ;; cont yL)
    ≈( s )
    (fun xR => yR ← progR xR ;; cont yR)
  ⦃ post ⦄.
Admitted.

Lemma completedPythSeqRule
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
  ⊨CPyth ⦃ pre ⦄ progL ≈( s1 ) progR ⦃ mid ⦄ ->
  ⊨CPyth ⦃
    fun xs =>
      let '((xL, memL), (xR, memR)) := xs in
      (xL == xR) && (memL == memR) && mid (xL, memL)
  ⦄ contL ≈( s2 ) contR ⦃ post ⦄ ->
  ⊨CPyth ⦃ pre ⦄
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

Lemma completedPythCompileCallsRule
  (q : nat) (X Y A B : choice_type)
  (L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (prog : A -> raw_code B)
  (eps : R)
  (call_invariant : pred heap) :
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fhas M (mkopsig fn X Y) ->
  ⊨CPyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( [tuple eps] )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨CPyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => code_link
      (compile_calls q.+1 (X := X) (Y := Y) P' fn (prog x))
      P')
    ≈( pythCallErrors q eps )
    (fun x => code_link
      (compile_calls q.+1 (X := X) (Y := Y) P'' fn (prog x))
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
Admitted.
