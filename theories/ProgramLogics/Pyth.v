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

Lemma pythCallErrors_size (q : nat) (eps : R) :
  size (flatten (nseq q.+1 [:: 0; eps])) == (q.*2).+2.
Proof.
by rewrite size_flatten /shape map_nseq sumn_nseq /= mul2n.
Qed.

Definition pythCallErrors (q : nat) (eps : R) : (q.*2).+2.-tuple R :=
  Tuple (pythCallErrors_size q eps).

Definition heap_eq_on (K : Locations) (mem0 mem1 : heap) : Prop :=
  forall l, fhas K l -> get_heap mem0 l = get_heap mem1 l.

Definition heap_pred_depends_only_on
  (K : Locations) (p : pred heap) : Prop :=
  forall mem0 mem1, heap_eq_on K mem0 mem1 -> p mem0 = p mem1.

Lemma heap_eq_on_set_heap_separate
  (K L : Locations) (mem : heap) (l : Location) (v : l) :
  fseparate K L ->
  fhas L l ->
  heap_eq_on K mem (set_heap mem l v).
Proof.
move=> HKL Hl k Hk.
rewrite get_set_heap_neq //.
apply/negP=> /eqP Hkl.
have Hnotin := notin_has_separate K L k Hk HKL.
have Hin := fhas_in L l Hl.
by rewrite Hkl Hin in Hnotin.
Qed.

Definition package_preserves_heap_pred_except
  (M : Interface) (P : raw_package) (skip : ident)
  (p : pred heap) : Prop :=
  forall (o : opsig) (x : src o),
    fhas M o ->
    fst o != skip ->
    ⊨Hoare ⦃ fun in_mem => p in_mem.2 ⦄
      (fun x => resolve P o x)
    ⦃ fun out_mem => p out_mem.2 ⦄.

Lemma pythCallErrors_nonneg (q : nat) (eps : R) :
  0 <= eps ->
  forall i : 'I_(q.*2).+2, 0 <= tnth (pythCallErrors q eps) i.
Admitted.

Lemma pythCallErrors0 (eps : R) :
  pythCallErrors 0 eps = cat_tuple [tuple 0] [tuple eps].
Admitted.

Lemma pythCallErrorsS (q : nat) (eps : R) :
  pythCallErrors q.+1 eps =
  cat_tuple [tuple 0] (cat_tuple [tuple eps] (pythCallErrors q eps)).
Admitted.

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
Admitted.

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

Lemma continue_from_trace_valid
  {A : choice_type} (L : Locations) (M : Interface)
  (root prog : raw_code A) (trace_prefix : trace_t) :
  ValidCode L M root ->
  continue_from_trace root trace_prefix = Some prog ->
  ValidCode L M prog.
Proof.
elim: trace_prefix root=> [|e trace_prefix IH] root Hvalid Htrace.
  rewrite continue_from_trace_nil in Htrace.
  by inversion Htrace; subst.
case: root Hvalid Htrace=> //=.
- move=> o x k Hvalid.
  case Hdec: (decode_call_entry o e)=> [y|] //= Htrace.
  have [_ Hk] := @inversion_valid_opr L M A o x k
    (valid_code_from_class L M A (opr o x k) Hvalid).
  exact: (IH (k y) (Hk y) Htrace).
- move=> l k Hvalid.
  case Hdec: (decode_get_entry l e)=> [y|] //= Htrace.
  have [_ Hk] := @inversion_valid_getr L M A l k
    (valid_code_from_class L M A (getr l k) Hvalid).
  exact: (IH (k y) (Hk y) Htrace).
- move=> l v k Hvalid.
  case: e=> //= Htrace.
  have [_ Hk] := @inversion_valid_putr L M A l v k
    (valid_code_from_class L M A (putr l v k) Hvalid).
  exact: (IH k Hk Htrace).
- move=> op k Hvalid.
  case Hdec: (decode_sample_entry op e)=> [y|] //= Htrace.
  have Hk := @inversion_valid_sampler L M A op k
    (valid_code_from_class L M A (sampler op k) Hvalid).
  exact: (IH (k y) (Hk y) Htrace).
Qed.

Lemma linkedRunUntilNextCallAuxPreservesHeapPred
  (X Y B : choice_type)
  (K L L' : Locations) (M : Interface)
  (P' : raw_package) (fn : ident)
  (prog : raw_code B) (trace : trace_t)
  (call_invariant : pred heap) :
  ValidCode L M prog ->
  ValidPackage L' [interface] M P' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Hoare ⦃ fun in_mem => call_invariant in_mem.2 ⦄
    (fun _ : 'unit => code_link
      (run_until_next_call_aux prog fn trace) P')
  ⦃ fun out_mem => call_invariant out_mem.2 ⦄.
Proof.
move=> Hvalid HP' HKL Hdep HP'_pres Hfn.
rewrite /hoareJudgment=> u mem Hinv out.
change (is_true (call_invariant mem)) in Hinv.
clear u.
move: trace mem Hinv out.
have Hvc := valid_code_from_class L M B prog Hvalid.
elim: Hvc=> [b|o x k Ho Hk IH|l k Hl Hk IH|l v k Hl Hk IH|op k Hk IH]
    trace mem Hinv out Hout /=.
- rewrite Pr_code_ret in Hout.
  have -> : out = ((inr b, pack_trace trace), mem).
    exact: (in_dunit Hout).
  exact: Hinv.
- move: out Hout.
  case: o Ho x k Hk IH=> f [S T] Ho x k Hk IH out Hout /=.
  case Hfid: (f == fn)%bool.
  + rewrite /run_until_next_call_aux Hfid /code_link /= in Hout.
    rewrite Pr_code_ret in Hout.
    have -> : out = ((inl (pickle x), pack_trace trace), mem).
      exact: (in_dunit Hout).
    exact: Hinv.
  + rewrite /run_until_next_call_aux Hfid /code_link /= in Hout.
    rewrite Pr_code_bind in Hout.
    have [mid Hmid Hinner] := @dinsupp_dlet R _ _ _ _ _ Hout.
    have Hneq : (f, (S, T)).1 != fn by rewrite /= Hfid.
    have Hpres := HP'_pres (f, (S, T)) x Ho Hneq.
    have Hmid_inv : call_invariant mid.2.
      exact: (Hpres x mem Hinv mid Hmid).
    exact: (IH mid.1 (rcons trace (call_entry (pickle mid.1)))
      mid.2 Hmid_inv out Hinner).
- rewrite Pr_code_get in Hout.
  exact: (IH (get_heap mem l) (rcons trace (get_entry (pickle (get_heap mem l))))
    mem Hinv out Hout).
- rewrite Pr_code_put in Hout.
  have Hinv' : call_invariant (set_heap mem l v).
    move: (Hdep mem (set_heap mem l v)
      (heap_eq_on_set_heap_separate K L mem l v HKL Hl)).
    by move=> <-.
  exact: (IH (rcons trace put_entry) (set_heap mem l v) Hinv' out Hout).
- rewrite Pr_code_sample in Hout.
  have [a _ Hinner] := @dinsupp_dlet R _ _ _ _ _ Hout.
  exact: (IH a (rcons trace (sample_entry (pickle a))) mem Hinv out Hinner).
Qed.

Lemma linkedRunUntilNextCallPreservesHeapPred
  (X Y B : choice_type)
  (K L L' : Locations) (M : Interface)
  (P' : raw_package) (fn : ident)
  (prog : raw_code B)
  (call_invariant : pred heap) :
  ValidCode L M prog ->
  ValidPackage L' [interface] M P' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Hoare ⦃ fun in_mem => call_invariant in_mem.2 ⦄
    (fun _ : 'unit => code_link (run_until_next_call prog fn) P')
  ⦃ fun out_mem => call_invariant out_mem.2 ⦄.
Proof.
move=> Hvalid HP' HKL Hdep HP'_pres Hfn.
rewrite /run_until_next_call.
exact: (linkedRunUntilNextCallAuxPreservesHeapPred X Y B K L L' M P'
  fn prog nil call_invariant Hvalid HP' HKL Hdep HP'_pres Hfn).
Qed.

Lemma pythCompileCallsFromTraceBaseRule
  (X Y B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root : raw_code B) (trace_prefix : trace_t)
  (eps : R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Pyth1 ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( eps )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨PythC ⦃ fun mems =>
          let '(memL, memR) := mems in
          (memL == memR) && call_invariant memL ⦄
    (code_link
      (compile_calls_from_trace 1 (X := X) (Y := Y) P' fn
        root trace_prefix)
      P')
    ≈( pythCallErrors 0 eps )
    (code_link
      (compile_calls_from_trace 1 (X := X) (Y := Y) P'' fn
        root trace_prefix)
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Admitted.

Lemma pythCompileCallsFromTraceStepRule
  (q : nat) (X Y B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root : raw_code B) (trace_prefix : trace_t)
  (eps : R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Pyth1 ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( eps )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  (forall trace_prefix',
    ⊨PythC ⦃ fun mems =>
            let '(memL, memR) := mems in
            (memL == memR) && call_invariant memL ⦄
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P' fn
          root trace_prefix')
        P')
      ≈( pythCallErrors q eps )
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P'' fn
          root trace_prefix')
        P')
    ⦃ fun out =>
      let '(y, mem) := out in
      call_invariant mem ⦄) ->
  ⊨PythC ⦃ fun mems =>
          let '(memL, memR) := mems in
          (memL == memR) && call_invariant memL ⦄
    (code_link
      (compile_calls_from_trace q.+2 (X := X) (Y := Y) P' fn
        root trace_prefix)
      P')
    ≈( pythCallErrors q.+1 eps )
    (code_link
      (compile_calls_from_trace q.+2 (X := X) (Y := Y) P'' fn
        root trace_prefix)
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Admitted.

Lemma pythCompileCallsFromTraceRule
  (q : nat) (X Y B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root : raw_code B) (trace_prefix : trace_t)
  (eps : R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Pyth1 ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( eps )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨PythC ⦃ fun mems =>
          let '(memL, memR) := mems in
          (memL == memR) && call_invariant memL ⦄
    (code_link
      (compile_calls_from_trace q.+1 (X := X) (Y := Y) P' fn
        root trace_prefix)
      P')
    ≈( pythCallErrors q eps )
    (code_link
      (compile_calls_from_trace q.+1 (X := X) (Y := Y) P'' fn
        root trace_prefix)
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
elim: q X Y B K L L' L'' M P' P'' fn root trace_prefix eps call_invariant
  => [|q IH] X Y B K L L' L'' M P' P'' fn root trace_prefix eps
     call_invariant Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Hcall.
- exact: (pythCompileCallsFromTraceBaseRule X Y B K L L' L'' M P' P''
    fn root trace_prefix eps call_invariant Hvalid HP' HP'' HKL Hdep
    HP'_pres Hfn Hcall).
- apply: (pythCompileCallsFromTraceStepRule q X Y B K L L' L'' M P' P''
    fn root trace_prefix eps call_invariant Hvalid HP' HP'' HKL Hdep
    HP'_pres Hfn Hcall).
  move=> trace_prefix'.
  exact: (IH X Y B K L L' L'' M P' P'' fn root trace_prefix' eps
    call_invariant Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Hcall).
Qed.

Lemma pythCompileCallsRule
  (q : nat) (X Y A B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (prog : A -> raw_code B)
  (eps : R)
  (call_invariant : pred heap) :
  (forall x, ValidCode L M (prog x)) ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Pyth1 ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( eps )
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
    ≈( pythCallErrors q eps )
    (fun x => code_link
      (compile_calls q.+1 (X := X) (Y := Y) P'' fn (prog x))
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Hcall.
have [Heps_nonneg _] := Hcall.
have Heps : 0 <= eps.
  exact: (Heps_nonneg ord0).
split.
- exact: (pythCallErrors_nonneg q eps Heps).
- move=> memL memR xL xR Hpre.
  move/andP: Hpre=> [/andP [/eqP -> /eqP ->] Hinv].
  have Htrace :=
    pythCompileCallsFromTraceRule q X Y B K L L' L'' M P' P'' fn
      (prog xR) nil eps call_invariant
      (Hvalid xR) HP' HP'' HKL Hdep HP'_pres Hfn Hcall.
  have [_ Hpyth] := Htrace.
  have Hpre_unit :
      (let '((_, memL0), (_, memR0)) := ((tt, memR), (tt, memR)) in
        (memL0 == memR0) && call_invariant memL0).
    by rewrite eqxx.
  have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
    Hpyth memR memR tt tt Hpre_unit.
  exists P, Q.
  rewrite -!compile_calls_from_trace_nil.
  split; first exact: Hdist.
  split; first exact: HmarginL.
  split; first exact: HmarginR.
  by split.
Qed.
