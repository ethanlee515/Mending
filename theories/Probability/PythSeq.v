(* Proof skeleton for sequential composition of completed Pythagorean traces. *)

From Stdlib Require Import Unicode.Utf8.
From extructures Require Import ord fset fmap.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals distr ssrZ realseq realsum lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Crypt Require Import ChoiceAsOrd Couplings StateTransformingLaxMorph.
From SSProve.Crypt Require Import Axioms StateTransfThetaDens.
From SSProve.Crypt Require Import choice_type fmap_extra SubDistr.
From SSProve.Crypt.nominal Require Import Pr.
From SSProve Require Import pkg_core_definition pkg_advantage pkg_composition
  pkg_notation.
From Mending.NextMessage Require Import Trace.
From Mending.Probability Require Import Ae ConditionalCoordinate DletTuple
  OutputHeap.
From Mending.Probability.KL Require Import Core Pyth.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras RealSumExtras
  TupleExtras.

Import PackageNotation.
Import pkg_heap.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope package_scope.
Local Open Scope ring_scope.

Definition completedPythKernelPair {ℓ : nat} : Type :=
  ({distr ((ℓ.+1).-tuple (option (nat * heap))) / R} *
   {distr ((ℓ.+1).-tuple (option (nat * heap))) / R})%type.

Lemma dlet_complete_some
  {T U : choiceType}
  (D : {distr T / R})
  (F : option T -> {distr (option U) / R})
  (z : U) :
  F None (Some z) = 0 ->
  (\dlet_(x <- complete D) F x) (Some z) =
  (\dlet_(x <- D) F (Some x)) (Some z).
Proof.
move=> HFnone.
rewrite !dletE.
rewrite (psum_option_some_zero
  (fun x : option T => complete D x * F x (Some z))).
  apply/eq_psum=> x.
  by rewrite completeE.
by rewrite completeE /= HFnone mulr0.
Qed.

Lemma dlet_complete_none
  {T U : choiceType}
  (D : {distr T / R})
  (F : option T -> {distr (option U) / R}) :
  (\dlet_(x <- complete D) F x) None =
  (\dlet_(x <- D) F (Some x)) None +
    (1 - dweight D) * F None None.
Proof.
rewrite !dletE.
rewrite (psum_option_split
  (fun x : option T => complete D x * F x None)).
- rewrite (eq_psum
    (F1 := fun x : T => complete D (Some x) * F (Some x) None)
    (F2 := fun x : T => D x * F (Some x) None)).
    by rewrite completeE.
  by move=> x; rewrite completeE.
- move=> x.
  by rewrite mulr_ge0 ?ge0_mu.
- apply: summable_mlet.
Qed.

Lemma dweight_dlet
  {T U : choiceType}
  (D : {distr T / R})
  (K : T -> {distr U / R}) :
  dweight (\dlet_(x <- D) K x) =
  psum (fun x => D x * dweight (K x)).
Proof.
exact: dweight_dlet_sum.
Qed.

Definition completedPythKernelSpec
  {ℓ : nat}
  {out_t : choice_type}
  (KL KR : {distr (out_t * heap) / R})
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R)
  (W : completedPythKernelPair (ℓ := ℓ)) : Prop :=
  let '(P, Q) := W in
  pythDist P Q s /\
  dmargin (fun omega => tnth omega ord_max) P
    =1 complete_output_heap KL /\
  dmargin (fun omega => tnth omega ord_max) Q
    =1 complete_output_heap KR /\
  (forall x, x \in dinsupp KL -> post x) /\
  (forall x, x \in dinsupp KR -> post x).

Lemma completedPythKernelSpec_dist
  {ℓ : nat}
  {out_t : choice_type}
  (KL KR : {distr (out_t * heap) / R})
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R)
  (W : completedPythKernelPair (ℓ := ℓ)) :
  completedPythKernelSpec KL KR post s W ->
  pythDist W.1 W.2 s.
Proof. by case: W=> P Q /= [Hdist _]. Qed.

Lemma completedPythKernelSpec_marginL
  {ℓ : nat}
  {out_t : choice_type}
  (KL KR : {distr (out_t * heap) / R})
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R)
  (W : completedPythKernelPair (ℓ := ℓ)) :
  completedPythKernelSpec KL KR post s W ->
  dmargin (fun omega => tnth omega ord_max) W.1
    =1 complete_output_heap KL.
Proof. by case: W=> P Q /= [_ [Hmargin _]]. Qed.

Lemma completedPythKernelSpec_marginR
  {ℓ : nat}
  {out_t : choice_type}
  (KL KR : {distr (out_t * heap) / R})
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R)
  (W : completedPythKernelPair (ℓ := ℓ)) :
  completedPythKernelSpec KL KR post s W ->
  dmargin (fun omega => tnth omega ord_max) W.2
    =1 complete_output_heap KR.
Proof. by case: W=> P Q /= [_ [_ [Hmargin _]]]. Qed.

Lemma completedPythKernelSpec_postL
  {ℓ : nat}
  {out_t : choice_type}
  (KL KR : {distr (out_t * heap) / R})
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R)
  (W : completedPythKernelPair (ℓ := ℓ))
  (x : out_t * heap) :
  completedPythKernelSpec KL KR post s W ->
  x \in dinsupp KL -> post x.
Proof.
by case: W=> P Q /= [_ [_ [_ [Hpost _]]]]; exact: Hpost.
Qed.

Lemma completedPythKernelSpec_postR
  {ℓ : nat}
  {out_t : choice_type}
  (KL KR : {distr (out_t * heap) / R})
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R)
  (W : completedPythKernelPair (ℓ := ℓ))
  (x : out_t * heap) :
  completedPythKernelSpec KL KR post s W ->
  x \in dinsupp KR -> post x.
Proof.
by case: W=> P Q /= [_ [_ [_ [_ Hpost]]]]; exact: Hpost.
Qed.

Definition default_completed_pyth_trace {n : nat} :
    n.-tuple (option (nat * heap)) :=
  nseq_tuple n None.

Lemma default_completed_pyth_trace_final {n : nat} :
  tnth (default_completed_pyth_trace (n := n.+1)) ord_max = None.
Proof.
rewrite (tnth_nth None) /default_completed_pyth_trace.
by rewrite nth_nseq ltn_ord.
Qed.

Definition completedSemanticBindKernel
  {mid_t out_t : choice_type}
  (K : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (x : option (nat * heap)) : {distr (option (nat * heap)) / R} :=
  match x with
  | Some packed =>
      match decode_output_heap packed with
      | Some y =>
          match @idP (mid y) with
          | ReflectT _ => complete_output_heap (K y)
          | ReflectF _ => dunit None
          end
      | None => dunit None
      end
  | None => dunit None
  end.

Lemma complete_output_heap_bind_some
  {mid_t out_t : choice_type}
  (ML : {distr (mid_t * heap) / R})
  (KL : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap)) :
  (forall y, y \in dinsupp ML -> mid y) ->
  forall packed,
  (\dlet_(x <- complete_output_heap ML)
    completedSemanticBindKernel KL mid x) (Some packed)
  = complete_output_heap (\dlet_(y <- ML) KL y) (Some packed).
Proof.
move=> Hmid packed.
rewrite /complete_output_heap.
rewrite (dlet_complete_some (dmargin (@pack_output_heap mid_t) ML)
  (completedSemanticBindKernel KL mid) packed); last first.
  by rewrite /completedSemanticBindKernel dunit1E.
rewrite completeE /=.
rewrite (dlet_dmargin_pack_output_heap ML
  (fun x => completedSemanticBindKernel KL mid (Some x)) (Some packed)).
rewrite (dmargin_dlet_pack_output_heap ML KL packed).
rewrite !dletE.
apply/eq_psum=> y.
case Hy0: (ML y == 0).
  move/eqP: Hy0=> Hy0.
  by rewrite Hy0 !mul0r.
have Hy : y \in dinsupp ML.
  by rewrite in_dinsupp Hy0.
congr (_ * _).
rewrite /completedSemanticBindKernel decode_output_heap_pack.
destruct (@idP (mid y)) as [Hymid|Hymid].
  by rewrite /complete_output_heap completeE.
by case: Hymid; exact: (Hmid y Hy).
Qed.

Lemma complete_output_heap_bind_none_mass
  {mid_t out_t : choice_type}
  (ML : {distr (mid_t * heap) / R})
  (KL : mid_t * heap -> {distr (out_t * heap) / R}) :
  (\dlet_(y <- ML) complete_output_heap (KL y)) None +
    (1 - dweight ML) =
  complete_output_heap (\dlet_(y <- ML) KL y) None.
Proof.
rewrite /complete_output_heap !completeE /=.
rewrite dmargin_dweight.
rewrite dletE.
rewrite (eq_psum
  (F2 := fun y => ML y * (1 - dweight (KL y)))).
  have Hscaled :
      psum (fun y => ML y * (1 - dweight (KL y))) =
      dweight ML - dweight (\dlet_(y <- ML) KL y).
    rewrite (eq_psum
      (F2 := fun y => ML y - ML y * dweight (KL y))).
      rewrite (@psum_sub_bounded_nonneg R _ ML
        (fun y => ML y * dweight (KL y))).
      - rewrite pr_predT dweight_dlet.
        by [].
      - move=> y.
        apply/andP; split.
        + rewrite mulr_ge0 ?ge0_mu //.
          rewrite pr_predT.
          exact: ge0_psum.
        rewrite -[leRHS]mulr1.
        apply: ler_wpM2l; first exact: ge0_mu.
        rewrite pr_predT.
        exact: le1_mu.
      - exact: summable_mu.
    move=> y.
    by rewrite mulrBr mulr1.
  rewrite Hscaled.
  lra.
  by move=> y; rewrite completeE /= dmargin_dweight.
Qed.

Lemma complete_output_heap_bind_none
  {mid_t out_t : choice_type}
  (ML : {distr (mid_t * heap) / R})
  (KL : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap)) :
  (forall y, y \in dinsupp ML -> mid y) ->
  (\dlet_(x <- complete_output_heap ML)
    completedSemanticBindKernel KL mid x) None
  = complete_output_heap (\dlet_(y <- ML) KL y) None.
Proof.
move=> Hmid.
rewrite /complete_output_heap.
rewrite dlet_complete_none.
rewrite dmargin_dweight dunit1E eqxx mulr1.
rewrite (dlet_dmargin_pack_output_heap ML
  (fun x => completedSemanticBindKernel KL mid (Some x)) None).
rewrite -(complete_output_heap_bind_none_mass ML KL).
congr (_ + _).
rewrite !dletE.
apply/eq_psum=> y.
case Hy0: (ML y == 0).
  move/eqP: Hy0=> Hy0.
  by rewrite Hy0 !mul0r.
have Hy : y \in dinsupp ML.
  by rewrite in_dinsupp Hy0.
congr (_ * _).
rewrite /completedSemanticBindKernel decode_output_heap_pack.
destruct (@idP (mid y)) as [Hymid|Hymid].
  by rewrite /complete_output_heap.
by case: Hymid; exact: (Hmid y Hy).
Qed.


Lemma complete_output_heap_bind
  {mid_t out_t : choice_type}
  (ML : {distr (mid_t * heap) / R})
  (KL : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap)) :
  (forall y, y \in dinsupp ML -> mid y) ->
  \dlet_(x <- complete_output_heap ML)
    completedSemanticBindKernel KL mid x
  =1 complete_output_heap (\dlet_(y <- ML) KL y).
Proof.
move=> Hmid [packed|].
- exact: complete_output_heap_bind_some.
- exact: complete_output_heap_bind_none.
Qed.

Lemma completedPythKernel_choice
  {ℓ : nat}
  {mid_t out_t : choice_type}
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R) :
  (forall y, mid y ->
    exists (P Q : {distr ((ℓ.+1).-tuple (option (nat * heap))) / R}),
      completedPythKernelSpec (KL y) (KR y) post s (P, Q)) ->
  exists (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ)),
    forall y,
      completedPythKernelSpec
        (KL (proj1_sig y)) (KR (proj1_sig y)) post s (K y).
Proof.
move=> Hcont.
have Hchoice :
    forall y : { y : mid_t * heap | mid y },
      exists W : completedPythKernelPair (ℓ := ℓ),
        completedPythKernelSpec
          (KL (proj1_sig y)) (KR (proj1_sig y)) post s W.
  move=> [y Hy] /=.
  have [P [Q HW]] := Hcont y Hy.
  by exists (P, Q).
have [K HK] := schoice _ _ _ Hchoice.
by exists K.
Qed.

Definition completedPythTraceKernelL
  {ℓ1 ℓ2 : nat}
  {mid_t : choice_type}
  (mid : pred (mid_t * heap))
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (omega : (ℓ1.+1).-tuple (option (nat * heap)))
    : {distr ((ℓ2.+1).-tuple (option (nat * heap))) / R} :=
  match tnth omega ord_max with
  | Some packed =>
      match decode_output_heap packed with
      | Some y =>
          match @idP (mid y) with
          | ReflectT Hy => (K (exist _ y Hy)).1
          | ReflectF _ => dunit (default_completed_pyth_trace (n := ℓ2.+1))
          end
      | None => dunit (default_completed_pyth_trace (n := ℓ2.+1))
      end
  | None => dunit (default_completed_pyth_trace (n := ℓ2.+1))
  end.

Definition completedPythTraceKernelR
  {ℓ1 ℓ2 : nat}
  {mid_t : choice_type}
  (mid : pred (mid_t * heap))
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (omega : (ℓ1.+1).-tuple (option (nat * heap)))
    : {distr ((ℓ2.+1).-tuple (option (nat * heap))) / R} :=
  match tnth omega ord_max with
  | Some packed =>
      match decode_output_heap packed with
      | Some y =>
          match @idP (mid y) with
          | ReflectT Hy => (K (exist _ y Hy)).2
          | ReflectF _ => dunit (default_completed_pyth_trace (n := ℓ2.+1))
          end
      | None => dunit (default_completed_pyth_trace (n := ℓ2.+1))
      end
  | None => dunit (default_completed_pyth_trace (n := ℓ2.+1))
  end.

Definition completedPythTraceBindL
  {ℓ1 ℓ2 : nat}
  {mid_t : choice_type}
  (mid : pred (mid_t * heap))
  (P0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
    : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (option (nat * heap))) / R} :=
  \dlet_(omega1 <- P0)
  \dlet_(omega2 <- completedPythTraceKernelL mid K omega1)
    dunit (cat_tuple omega1 omega2).

Definition completedPythTraceBindR
  {ℓ1 ℓ2 : nat}
  {mid_t : choice_type}
  (mid : pred (mid_t * heap))
  (Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
    : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (option (nat * heap))) / R} :=
  \dlet_(omega1 <- Q0)
  \dlet_(omega2 <- completedPythTraceKernelR mid K omega1)
    dunit (cat_tuple omega1 omega2).

Definition completedPythTraceBindPair
  {ℓ1 ℓ2 : nat}
  {mid_t : choice_type}
  (mid : pred (mid_t * heap))
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R}) : Prop :=
  P =1 completedPythTraceBindL mid P0 K /\
  Q =1 completedPythTraceBindR mid Q0 K.

Lemma completedPythTraceKernel_absolute_continuous
  {ℓ1 ℓ2 : nat}
  {mid_t : choice_type}
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (omega : (ℓ1.+1).-tuple (option (nat * heap))) :
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  absolute_continuous
    (completedPythTraceKernelL mid K omega)
    (completedPythTraceKernelR mid K omega).
Proof.
move=> HK.
rewrite /completedPythTraceKernelL /completedPythTraceKernelR.
case: (tnth omega ord_max)=> [packed|]; last by move=> x Hx.
case: (decode_output_heap packed)=> [y|]; last by move=> x Hx.
destruct (@idP (mid y)) as [Hy|Hnot].
  exact: (pythDist_absolute_continuous
    (K (exist _ y Hy)).1 (K (exist _ y Hy)).2 s2
    (HK (exist _ y Hy))).
by move=> x Hx.
Qed.

Lemma completedTraceBind_absolute_continuous
  {ℓ1 ℓ2 : nat}
  {mid_t : choice_type}
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R}) :
  completedPythTraceBindPair mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  absolute_continuous P Q.
Proof.
move=> [HP HQ] Hdist0 HK.
have Hac0 := pythDist_absolute_continuous P0 Q0 s1 Hdist0.
have Hac_bind :
    absolute_continuous
      (completedPythTraceBindL mid P0 K)
      (completedPythTraceBindR mid Q0 K).
  rewrite /completedPythTraceBindL /completedPythTraceBindR.
  apply: dlet_dunit_cat_absolute_continuous=> // omega1 _.
  exact: (completedPythTraceKernel_absolute_continuous mid s2 K omega1 HK).
move=> omega HQomega0.
rewrite HP.
apply: Hac_bind.
by rewrite -HQ.
Qed.

Lemma completedPythTraceKernelL_dweight1
  {ℓ1 ℓ2 : nat}
  {mid_t : choice_type}
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (omega : (ℓ1.+1).-tuple (option (nat * heap))) :
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  dweight (completedPythTraceKernelL mid K omega) = 1.
Proof.
move=> HK.
rewrite /completedPythTraceKernelL.
case: (tnth omega ord_max)=> [packed|]; last exact: dunit_dweight.
case: (decode_output_heap packed)=> [y|]; last exact: dunit_dweight.
destruct (@idP (mid y)) as [Hy|Hnot].
  by case: (HK (exist _ y Hy))=> _ [Hmass _].
exact: dunit_dweight.
Qed.

Lemma completedPythTraceKernelR_dweight1
  {ℓ1 ℓ2 : nat}
  {mid_t : choice_type}
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (omega : (ℓ1.+1).-tuple (option (nat * heap))) :
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  dweight (completedPythTraceKernelR mid K omega) = 1.
Proof.
move=> HK.
rewrite /completedPythTraceKernelR.
case: (tnth omega ord_max)=> [packed|]; last exact: dunit_dweight.
case: (decode_output_heap packed)=> [y|]; last exact: dunit_dweight.
destruct (@idP (mid y)) as [Hy|Hnot].
  by case: (HK (exist _ y Hy))=> _ [_ [Hmass _]].
exact: dunit_dweight.
Qed.

Lemma completedTraceBind_dweightL
  {ℓ1 ℓ2 : nat}
  {mid_t : choice_type}
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R}) :
  completedPythTraceBindPair mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  dweight P = 1.
Proof.
move=> [HP _] Hdist0 HK.
case: Hdist0=> _ [HP0mass _].
rewrite (pr_ext P (completedPythTraceBindL mid P0 K) predT HP).
rewrite /completedPythTraceBindL.
rewrite (pr_dlet_cat_prefix_lift_eq P0 (completedPythTraceKernelL mid K)
  predT predT
  (fun omega => completedPythTraceKernelL_dweight1 mid s2 K omega HK));
  last by move=> omega1 omega2.
exact: HP0mass.
Qed.

Lemma completedTraceBind_dweightR
  {ℓ1 ℓ2 : nat}
  {mid_t : choice_type}
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R}) :
  completedPythTraceBindPair mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  dweight Q = 1.
Proof.
move=> [_ HQ] Hdist0 HK.
case: Hdist0=> _ [_ [HQ0mass _]].
rewrite (pr_ext Q (completedPythTraceBindR mid Q0 K) predT HQ).
rewrite /completedPythTraceBindR.
rewrite (pr_dlet_cat_prefix_lift_eq Q0 (completedPythTraceKernelR mid K)
  predT predT
  (fun omega => completedPythTraceKernelR_dweight1 mid s2 K omega HK));
  last by move=> omega1 omega2.
exact: HQ0mass.
Qed.

Lemma completedTraceBind_prefix_cond
  {ℓ1 ℓ2 : nat}
  {mid_t : choice_type}
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : i.-tuple (option (nat * heap)))
  (Hi : (i < ℓ1.+1)%N) :
  completedPythTraceBindPair mid P0 Q0 K P Q ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
  δ_KL (conditional_coordinate P a)
       (conditional_coordinate Q a) =
  δ_KL (@conditional_coordinate _ _ _ P0 i0 a)
       (@conditional_coordinate _ _ _ Q0 i0 a).
Proof.
move=> [HP HQ] HK.
apply: kl_ext.
- move=> x.
  rewrite (conditional_coordinate_dist_ext P
    (completedPythTraceBindL mid P0 K) i a HP x).
  exact: (conditional_coordinate_dlet_cat_prefix_eq
    P0 (completedPythTraceKernelL mid K) i a Hi
    (fun omega => completedPythTraceKernelL_dweight1 mid s2 K omega HK) x).
- move=> x.
  rewrite (conditional_coordinate_dist_ext Q
    (completedPythTraceBindR mid Q0 K) i a HQ x).
  exact: (conditional_coordinate_dlet_cat_prefix_eq
    Q0 (completedPythTraceKernelR mid K) i a Hi
    (fun omega => completedPythTraceKernelR_dweight1 mid s2 K omega HK) x).
Qed.

Lemma completedTraceBind_prefix_bound
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : i.-tuple (option (nat * heap))) :
  completedPythTraceBindPair mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  (i < ℓ1.+1)%N ->
  δ_KL (conditional_coordinate P a)
       (conditional_coordinate Q a) <=
    tnth (cat_tuple s1 s2) i.
Proof.
move=> Hbind Hdist0 HK Hi.
have Hcond0 := pythDist_cond_bound P0 Q0 s1 Hdist0.
pose i0 : 'I_(ℓ1.+1) := Ordinal Hi.
rewrite (completedTraceBind_prefix_cond
  mid s2 P0 Q0 K P Q i a Hi Hbind HK).
rewrite (cat_tuple_tnth_prefix s1 s2 i Hi).
exact: (Hcond0 i0 a).
Qed.

Lemma completedTraceBind_suffix_bound_zero_prefix
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : i.-tuple (option (nat * heap)))
  (Hi : (ℓ1.+1 <= i)%N) :
  completedPythTraceBindPair mid P0 Q0 K P Q ->
  (forall i : 'I_(ℓ2.+1), 0 <= tnth s2 i) ->
  P0 (catTuplePrefix i Hi a) = 0 ->
  δ_KL (conditional_coordinate P a)
       (conditional_coordinate Q a) <=
    tnth s2 (catTupleSuffixIndex i Hi).
Proof.
move=> Hbind Hs2 HP0z.
have HPnull : conditional_coordinate P a =1 dnull.
  case: Hbind=> HP _ x.
  rewrite (conditional_coordinate_dist_ext P
    (completedPythTraceBindL mid P0 K) i a HP x).
  exact: (conditional_coordinate_dlet_cat_suffix_zero_prefix
    P0 (completedPythTraceKernelL mid K) i a Hi HP0z x).
rewrite (kl_left_dnull
  (conditional_coordinate P a)
  (conditional_coordinate Q a)
  HPnull).
exact: Hs2.
Qed.

Lemma completedTraceKernel_valid_midL
  {ℓ1 ℓ2 : nat}
  {mid_t : choice_type}
  (mid : pred (mid_t * heap))
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (omega1 : (ℓ1.+1).-tuple (option (nat * heap)))
  (packed : nat * heap)
  (y : { y : mid_t * heap | mid y }) :
  tnth omega1 ord_max = Some packed ->
  @decode_output_heap mid_t packed = Some (proj1_sig y) ->
  completedPythTraceKernelL mid K omega1 = (K y).1.
Proof.
case: y=> y Hy /= Homega Hdecode.
rewrite /completedPythTraceKernelL Homega Hdecode.
destruct (@idP (mid y)) as [Hy'|Hy'].
  by rewrite (eq_irrelevance Hy' Hy).
by case: Hy'.
Qed.

Lemma completedTraceKernel_valid_midR
  {ℓ1 ℓ2 : nat}
  {mid_t : choice_type}
  (mid : pred (mid_t * heap))
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (omega1 : (ℓ1.+1).-tuple (option (nat * heap)))
  (packed : nat * heap)
  (y : { y : mid_t * heap | mid y }) :
  tnth omega1 ord_max = Some packed ->
  @decode_output_heap mid_t packed = Some (proj1_sig y) ->
  completedPythTraceKernelR mid K omega1 = (K y).2.
Proof.
case: y=> y Hy /= Homega Hdecode.
rewrite /completedPythTraceKernelR Homega Hdecode.
destruct (@idP (mid y)) as [Hy'|Hy'].
  by rewrite (eq_irrelevance Hy' Hy).
by case: Hy'.
Qed.

Lemma completedTraceBind_suffix_condL_valid_mid
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : i.-tuple (option (nat * heap)))
  (Hi : (ℓ1.+1 <= i)%N)
  (packed : nat * heap)
  (y : { y : mid_t * heap | mid y }) :
  completedPythTraceBindPair mid P0 Q0 K P Q ->
  tnth (catTuplePrefix i Hi a) ord_max = Some packed ->
  @decode_output_heap mid_t packed = Some (proj1_sig y) ->
  0 < P0 (catTuplePrefix i Hi a) ->
  conditional_coordinate P a
    =1 conditional_coordinate (K y).1 (catTupleSuffixAssignment i Hi a).
Proof.
move=> [HP _] Homega Hdecode Hpos x.
rewrite (conditional_coordinate_dist_ext P
  (completedPythTraceBindL mid P0 K) i a HP x).
pose omega1 := catTuplePrefix i Hi a.
rewrite (conditional_coordinate_dlet_cat_suffix_eq
  P0 (completedPythTraceKernelL mid K) i a Hi omega1 erefl Hpos x).
rewrite (completedTraceKernel_valid_midL mid K omega1 packed y Homega Hdecode).
by [].
Qed.

Lemma completedTraceBind_suffix_condR_valid_mid
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : i.-tuple (option (nat * heap)))
  (Hi : (ℓ1.+1 <= i)%N)
  (packed : nat * heap)
  (y : { y : mid_t * heap | mid y }) :
  completedPythTraceBindPair mid P0 Q0 K P Q ->
  tnth (catTuplePrefix i Hi a) ord_max = Some packed ->
  @decode_output_heap mid_t packed = Some (proj1_sig y) ->
  0 < Q0 (catTuplePrefix i Hi a) ->
  conditional_coordinate Q a
    =1 conditional_coordinate (K y).2 (catTupleSuffixAssignment i Hi a).
Proof.
move=> [_ HQ] Homega Hdecode Hpos x.
rewrite (conditional_coordinate_dist_ext Q
  (completedPythTraceBindR mid Q0 K) i a HQ x).
pose omega1 := catTuplePrefix i Hi a.
rewrite (conditional_coordinate_dlet_cat_suffix_eq
  Q0 (completedPythTraceKernelR mid K) i a Hi omega1 erefl Hpos x).
rewrite (completedTraceKernel_valid_midR mid K omega1 packed y Homega Hdecode).
by [].
Qed.

Lemma completedTraceBind_suffix_cond_valid_mid
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : i.-tuple (option (nat * heap)))
  (Hi : (ℓ1.+1 <= i)%N)
  (packed : nat * heap)
  (y : { y : mid_t * heap | mid y }) :
  completedPythTraceBindPair mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  tnth (catTuplePrefix i Hi a) ord_max = Some packed ->
  @decode_output_heap mid_t packed = Some (proj1_sig y) ->
  0 < P0 (catTuplePrefix i Hi a) ->
  0 < Q0 (catTuplePrefix i Hi a) ->
  δ_KL (conditional_coordinate P a)
       (conditional_coordinate Q a) =
  δ_KL (conditional_coordinate (K y).1 (catTupleSuffixAssignment i Hi a))
       (conditional_coordinate (K y).2 (catTupleSuffixAssignment i Hi a)).
Proof.
move=> Hbind _ Homega Hdecode HPpos HQpos.
apply: kl_ext.
- exact: (completedTraceBind_suffix_condL_valid_mid
    ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi packed y
    Hbind Homega Hdecode HPpos).
- exact: (completedTraceBind_suffix_condR_valid_mid
    ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi packed y
    Hbind Homega Hdecode HQpos).
Qed.

Lemma completedTraceBind_suffix_bound_valid_mid
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : i.-tuple (option (nat * heap)))
  (Hi : (ℓ1.+1 <= i)%N)
  (packed : nat * heap)
  (y : { y : mid_t * heap | mid y }) :
  completedPythTraceBindPair mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  tnth (catTuplePrefix i Hi a) ord_max = Some packed ->
  @decode_output_heap mid_t packed = Some (proj1_sig y) ->
  δ_KL (conditional_coordinate P a)
       (conditional_coordinate Q a) <=
    tnth s2 (catTupleSuffixIndex i Hi).
Proof.
move=> Hbind Hdist0 HK Homega Hdecode.
have Hac0 := pythDist_absolute_continuous P0 Q0 s1 Hdist0.
move: Hdist0=> [Hs1 [HP0mass [HQ0mass Hcond0]]].
have Hdist0 : pythDist P0 Q0 s1.
  by split; first exact: Hs1; split; first exact: HP0mass;
     split; first exact: HQ0mass.
case HP0z: (P0 (catTuplePrefix i Hi a) == 0).
  have Hs2 : forall j : 'I_(ℓ2.+1), 0 <= tnth s2 j.
    by case: (HK y)=> Hs2 _.
  exact: (completedTraceBind_suffix_bound_zero_prefix
    ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi
    Hbind Hs2 (eqP HP0z)).
have HP0pos : 0 < P0 (catTuplePrefix i Hi a).
  by rewrite lt_def ge0_mu HP0z.
have HQ0pos : 0 < Q0 (catTuplePrefix i Hi a).
  exact: (absolute_continuous_positive P0 Q0 _ Hac0 HP0pos).
rewrite (completedTraceBind_suffix_cond_valid_mid
  ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi packed y
  Hbind Hdist0 Homega Hdecode HP0pos HQ0pos).
have Hcond := pythDist_cond_bound (K y).1 (K y).2 s2 (HK y).
exact: (Hcond (catTupleSuffixIndex i Hi)
  (catTupleSuffixAssignment i Hi a)).
Qed.

Lemma completedTraceBind_suffix_bound_bad_prefix
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : i.-tuple (option (nat * heap)))
  (Hi : (ℓ1.+1 <= i)%N) :
  match tnth (catTuplePrefix i Hi a) ord_max with
  | Some packed =>
      match @decode_output_heap mid_t packed with
      | Some y => ~~ mid y
      | None => true
      end
  | None => true
  end ->
  completedPythTraceBindPair mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 complete_output_heap ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 complete_output_heap MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall j : 'I_(ℓ2.+1), 0 <= tnth s2 j) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  δ_KL (conditional_coordinate P a)
       (conditional_coordinate Q a) <=
    tnth s2 (Ordinal (cat_tuple_suffix_bound i Hi)).
Proof.
move=> Hbad Hbind Hdist0 HmarginL0 _ HmidL _ Hs2 HK.
case Hfinal: (tnth (catTuplePrefix i Hi a) ord_max)=> [packed|].
- have HP0z : P0 (catTuplePrefix i Hi a) = 0.
    case HP0z: (P0 (catTuplePrefix i Hi a) == 0).
      exact/eqP.
    have Hprefix_supp : catTuplePrefix i Hi a \in dinsupp P0.
      by rewrite in_dinsupp HP0z.
    have Hfinal_supp_P0 :
        Some packed \in
          dinsupp (dmargin (fun omega => tnth omega ord_max) P0).
      rewrite -Hfinal.
      exact: (dmargin_dinsupp_image P0
        (fun omega => tnth omega ord_max) _ Hprefix_supp).
    have Hfinal_supp_ML :
        Some packed \in dinsupp (complete_output_heap ML).
      rewrite in_dinsupp -HmarginL0.
      by move: Hfinal_supp_P0; rewrite in_dinsupp.
    have Hpacked_supp :
        packed \in dinsupp (dmargin (@pack_output_heap mid_t) ML).
      move: Hfinal_supp_ML.
      by rewrite in_dinsupp /complete_output_heap completeE /= in_dinsupp.
    have [z Hz Hpack] :=
      dmargin_dinsupp_preimage ML (@pack_output_heap mid_t)
        packed Hpacked_supp.
    have Hdecode_z : @decode_output_heap mid_t packed = Some z.
      by rewrite -Hpack decode_output_heap_pack.
    move: Hbad.
    rewrite Hfinal.
    case Hdecode: (@decode_output_heap mid_t packed)=> [y|].
    + have Hyz : y = z by move: Hdecode; rewrite Hdecode_z=> -[].
      rewrite Hyz (HmidL z Hz).
      by [].
    + by rewrite Hdecode_z in Hdecode.
  rewrite (completedTraceBind_suffix_bound_zero_prefix
    ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi
    Hbind Hs2 HP0z).
  by [].
- case HP0z: (P0 (catTuplePrefix i Hi a) == 0).
    rewrite (completedTraceBind_suffix_bound_zero_prefix
      ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi
      Hbind Hs2 (eqP HP0z)).
    by [].
  have Hac0 := pythDist_absolute_continuous P0 Q0 s1 Hdist0.
  have HP0pos : 0 < P0 (catTuplePrefix i Hi a).
    by rewrite lt_def ge0_mu HP0z.
  have HQ0pos : 0 < Q0 (catTuplePrefix i Hi a).
    exact: (absolute_continuous_positive P0 Q0 _ Hac0 HP0pos).
  pose D : {distr (option (nat * heap)) / R} := conditional_coordinate
    (dunit (default_completed_pyth_trace (n := ℓ2.+1)))
    (catTupleSuffixAssignment i Hi a).
  have Hkl0 :
      δ_KL (conditional_coordinate P a)
           (conditional_coordinate Q a) = 0.
    rewrite -(kl_self D).
    apply: kl_ext.
    + case: Hbind=> HP _ x.
      rewrite (conditional_coordinate_dist_ext P
        (completedPythTraceBindL mid P0 K) i a HP x).
      pose omega1 := catTuplePrefix i Hi a.
      rewrite (conditional_coordinate_dlet_cat_suffix_eq
        P0 (completedPythTraceKernelL mid K) i a Hi omega1 erefl HP0pos x).
      by rewrite /completedPythTraceKernelL Hfinal.
    + case: Hbind=> _ HQ x.
      rewrite (conditional_coordinate_dist_ext Q
        (completedPythTraceBindR mid Q0 K) i a HQ x).
      pose omega1 := catTuplePrefix i Hi a.
      rewrite (conditional_coordinate_dlet_cat_suffix_eq
        Q0 (completedPythTraceKernelR mid K) i a Hi omega1 erefl HQ0pos x).
      by rewrite /completedPythTraceKernelR Hfinal.
  rewrite Hkl0.
  exact: Hs2.
Qed.

Lemma completedTraceBind_suffix_bound
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : i.-tuple (option (nat * heap))) :
  completedPythTraceBindPair mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 complete_output_heap ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 complete_output_heap MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall j : 'I_(ℓ2.+1), 0 <= tnth s2 j) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  (ℓ1.+1 <= i)%N ->
  δ_KL (conditional_coordinate P a)
       (conditional_coordinate Q a) <=
    tnth (cat_tuple s1 s2) i.
Proof.
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hs2 HK Hi.
rewrite (cat_tuple_tnth_suffix s1 s2 i Hi).
case Hfinal: (tnth (catTuplePrefix i Hi a) ord_max)=> [packed|].
  case Hdecode: (@decode_output_heap mid_t packed)=> [y|].
    case Hmidy: (mid y).
	    - have Hy : mid y by rewrite Hmidy.
	      exact: (completedTraceBind_suffix_bound_valid_mid
	        ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi packed
	        (exist _ y Hy) Hbind Hdist0 HK Hfinal Hdecode).
	    - have Hbad : is_true (
	        match tnth (catTuplePrefix i Hi a) ord_max with
	        | Some packed =>
	            match @decode_output_heap mid_t packed with
	            | Some y => ~~ mid y
	            | None => true
	            end
	        | None => true
	        end) by rewrite Hfinal Hdecode Hmidy.
      exact: (completedTraceBind_suffix_bound_bad_prefix
        ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi
        Hbad Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hs2 HK).
	  have Hbad : is_true (
	      match tnth (catTuplePrefix i Hi a) ord_max with
	      | Some packed =>
	          match @decode_output_heap mid_t packed with
	          | Some y => ~~ mid y
	          | None => true
	          end
	      | None => true
	      end) by rewrite Hfinal Hdecode.
	  exact: (completedTraceBind_suffix_bound_bad_prefix
	    ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi
	    Hbad Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hs2 HK).
have Hbad : is_true (
    match tnth (catTuplePrefix i Hi a) ord_max with
    | Some packed =>
        match @decode_output_heap mid_t packed with
        | Some y => ~~ mid y
        | None => true
        end
    | None => true
    end) by rewrite Hfinal.
exact: (completedTraceBind_suffix_bound_bad_prefix
  ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi
  Hbad Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hs2 HK).
Qed.

Lemma completedTraceBind_cond_bound
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : i.-tuple (option (nat * heap))) :
  completedPythTraceBindPair mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 complete_output_heap ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 complete_output_heap MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall j : 'I_(ℓ2.+1), 0 <= tnth s2 j) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  δ_KL (conditional_coordinate P a)
       (conditional_coordinate Q a) <=
    tnth (cat_tuple s1 s2) i.
Proof.
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hs2 HK.
case: (ltnP i ℓ1.+1)=> Hi.
- exact: (completedTraceBind_prefix_bound
    ML MR KL KR mid s1 s2 P0 Q0 K P Q i a
    Hbind Hdist0 HK Hi).
- exact: (completedTraceBind_suffix_bound
    ML MR KL KR mid s1 s2 P0 Q0 K P Q i a
    Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hs2 HK Hi).
Qed.

Lemma completedTraceBind_cond_finite_kl
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R}) :
  completedPythTraceBindPair mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 complete_output_heap ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 complete_output_heap MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall i : 'I_(ℓ2.+1), 0 <= tnth s2 i) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  forall (i : 'I_(ℓ1.+1 + ℓ2.+1))
      (a : i.-tuple (option (nat * heap))),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a).
Proof.
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hs2 HK i a.
case: (ltnP i ℓ1.+1)=> Hi.
- pose i0 : 'I_(ℓ1.+1) := Ordinal Hi.
  have Hfin0 := pythDist_cond_finite_kl P0 Q0 s1 Hdist0 i0 a.
  case: Hbind=> HP HQ.
  apply: (finite_kl_ext _ _ _ _ _ _ Hfin0).
  + move=> x; symmetry.
    rewrite (conditional_coordinate_dist_ext P
      (completedPythTraceBindL mid P0 K) i a HP x).
    exact: (conditional_coordinate_dlet_cat_prefix_eq
      P0 (completedPythTraceKernelL mid K) i a Hi
      (fun omega => completedPythTraceKernelL_dweight1
        mid s2 K omega HK) x).
  + move=> x; symmetry.
    rewrite (conditional_coordinate_dist_ext Q
      (completedPythTraceBindR mid Q0 K) i a HQ x).
    exact: (conditional_coordinate_dlet_cat_prefix_eq
      Q0 (completedPythTraceKernelR mid K) i a Hi
      (fun omega => completedPythTraceKernelR_dweight1
        mid s2 K omega HK) x).
have Hzero_fin :
    P0 (catTuplePrefix i Hi a) = 0 ->
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a).
  move=> HP0z.
  apply: finite_kl_left_dnull.
  case: Hbind=> HP _ x.
  rewrite (conditional_coordinate_dist_ext P
    (completedPythTraceBindL mid P0 K) i a HP x).
  exact: (conditional_coordinate_dlet_cat_suffix_zero_prefix
    P0 (completedPythTraceKernelL mid K) i a Hi HP0z x).
have Hac0 := pythDist_absolute_continuous P0 Q0 s1 Hdist0.
case Hfinal: (tnth (catTuplePrefix i Hi a) ord_max)=> [packed|].
  case Hdecode: (@decode_output_heap mid_t packed)=> [y|].
    case Hmidy: (mid y).
      have Hy : mid y by rewrite Hmidy.
      pose ysig : { y : mid_t * heap | mid y } :=
        exist (fun y : mid_t * heap => mid y) y Hy.
      case HP0z: (P0 (catTuplePrefix i Hi a) == 0).
        exact: Hzero_fin (eqP HP0z).
      have HP0pos : 0 < P0 (catTuplePrefix i Hi a).
        by rewrite lt_def ge0_mu HP0z.
      have HQ0pos : 0 < Q0 (catTuplePrefix i Hi a).
        exact: (absolute_continuous_positive P0 Q0 _ Hac0 HP0pos).
      have HfinK := pythDist_cond_finite_kl
        (K ysig).1 (K ysig).2 s2 (HK ysig)
        (catTupleSuffixIndex i Hi)
        (catTupleSuffixAssignment i Hi a).
      apply: (finite_kl_ext _ _ _ _ _ _ HfinK).
      * move=> x; symmetry.
        exact: (completedTraceBind_suffix_condL_valid_mid
          ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi
          packed ysig Hbind Hfinal Hdecode HP0pos x).
      * move=> x; symmetry.
        exact: (completedTraceBind_suffix_condR_valid_mid
          ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi
          packed ysig Hbind Hfinal Hdecode HQ0pos x).
    have Hbad : is_true (
        match tnth (catTuplePrefix i Hi a) ord_max with
        | Some packed =>
            match @decode_output_heap mid_t packed with
            | Some y => ~~ mid y
            | None => true
            end
        | None => true
        end) by rewrite Hfinal Hdecode Hmidy.
    have HP0z : P0 (catTuplePrefix i Hi a) = 0.
      case HP0z: (P0 (catTuplePrefix i Hi a) == 0).
        exact/eqP.
      have Hprefix_supp : catTuplePrefix i Hi a \in dinsupp P0.
        by rewrite in_dinsupp HP0z.
      have Hfinal_supp_P0 :
          Some packed \in
            dinsupp (dmargin (fun omega => tnth omega ord_max) P0).
        rewrite -Hfinal.
        exact: (dmargin_dinsupp_image P0
          (fun omega => tnth omega ord_max) _ Hprefix_supp).
      have Hfinal_supp_ML :
          Some packed \in dinsupp (complete_output_heap ML).
        rewrite in_dinsupp -HmarginL0.
        by move: Hfinal_supp_P0; rewrite in_dinsupp.
      have Hpacked_supp :
          packed \in dinsupp (dmargin (@pack_output_heap mid_t) ML).
        move: Hfinal_supp_ML.
        by rewrite in_dinsupp /complete_output_heap completeE /= in_dinsupp.
      have [z Hz Hpack] :=
        dmargin_dinsupp_preimage ML (@pack_output_heap mid_t)
          packed Hpacked_supp.
      have Hdecode_z : @decode_output_heap mid_t packed = Some z.
        by rewrite -Hpack decode_output_heap_pack.
      move: Hbad.
      rewrite Hfinal.
      case Hdecode': (@decode_output_heap mid_t packed)=> [y'|].
      + have Hyz : y' = z by move: Hdecode'; rewrite Hdecode_z=> -[].
        rewrite Hyz (HmidL z Hz).
        by [].
      + by rewrite Hdecode_z in Hdecode'.
    exact: Hzero_fin HP0z.
  have Hbad : is_true (
      match tnth (catTuplePrefix i Hi a) ord_max with
      | Some packed =>
          match @decode_output_heap mid_t packed with
          | Some y => ~~ mid y
          | None => true
          end
      | None => true
      end) by rewrite Hfinal Hdecode.
  have HP0z : P0 (catTuplePrefix i Hi a) = 0.
    case HP0z: (P0 (catTuplePrefix i Hi a) == 0).
      exact/eqP.
    have Hprefix_supp : catTuplePrefix i Hi a \in dinsupp P0.
      by rewrite in_dinsupp HP0z.
    have Hfinal_supp_P0 :
        Some packed \in
          dinsupp (dmargin (fun omega => tnth omega ord_max) P0).
      rewrite -Hfinal.
      exact: (dmargin_dinsupp_image P0
        (fun omega => tnth omega ord_max) _ Hprefix_supp).
    have Hfinal_supp_ML :
        Some packed \in dinsupp (complete_output_heap ML).
      rewrite in_dinsupp -HmarginL0.
      by move: Hfinal_supp_P0; rewrite in_dinsupp.
    have Hpacked_supp :
        packed \in dinsupp (dmargin (@pack_output_heap mid_t) ML).
      move: Hfinal_supp_ML.
      by rewrite in_dinsupp /complete_output_heap completeE /= in_dinsupp.
    have [z Hz Hpack] :=
      dmargin_dinsupp_preimage ML (@pack_output_heap mid_t)
        packed Hpacked_supp.
    have Hdecode_z : @decode_output_heap mid_t packed = Some z.
      by rewrite -Hpack decode_output_heap_pack.
    move: Hbad.
    rewrite Hfinal.
    case Hdecode': (@decode_output_heap mid_t packed)=> [y'|].
    + have Hyz : y' = z by move: Hdecode'; rewrite Hdecode_z=> -[].
      rewrite Hyz (HmidL z Hz).
      by [].
    + by rewrite Hdecode_z in Hdecode'.
  exact: Hzero_fin HP0z.
case HP0z: (P0 (catTuplePrefix i Hi a) == 0).
  exact: Hzero_fin (eqP HP0z).
have HP0pos : 0 < P0 (catTuplePrefix i Hi a).
  by rewrite lt_def ge0_mu HP0z.
have HQ0pos : 0 < Q0 (catTuplePrefix i Hi a).
  exact: (absolute_continuous_positive P0 Q0 _ Hac0 HP0pos).
pose D : {distr (option (nat * heap)) / R} := conditional_coordinate
  (dunit (default_completed_pyth_trace (n := ℓ2.+1)))
  (catTupleSuffixAssignment i Hi a).
apply: (finite_kl_ext _ _ _ _ _ _ (finite_kl_refl D)).
- move=> x; symmetry.
  case: Hbind=> HP _.
  rewrite (conditional_coordinate_dist_ext P
    (completedPythTraceBindL mid P0 K) i a HP x).
  pose omega1 := catTuplePrefix i Hi a.
  rewrite (conditional_coordinate_dlet_cat_suffix_eq
    P0 (completedPythTraceKernelL mid K) i a Hi omega1 erefl HP0pos x).
  by rewrite /completedPythTraceKernelL Hfinal.
- move=> x; symmetry.
  case: Hbind=> _ HQ.
  rewrite (conditional_coordinate_dist_ext Q
    (completedPythTraceBindR mid Q0 K) i a HQ x).
  pose omega1 := catTuplePrefix i Hi a.
  rewrite (conditional_coordinate_dlet_cat_suffix_eq
    Q0 (completedPythTraceKernelR mid K) i a Hi omega1 erefl HQ0pos x).
  by rewrite /completedPythTraceKernelR Hfinal.
Qed.

Lemma completedTraceBind_pythDist
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R}) :
  completedPythTraceBindPair mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 complete_output_heap ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 complete_output_heap MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall i : 'I_(ℓ2.+1), 0 <= tnth s2 i) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  pythDist P Q (cat_tuple s1 s2).
Proof.
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hs2 HK.
move: Hdist0=> [Hs1 [HP0 [HQ0 Hcond0]]].
have Hdist0 : pythDist P0 Q0 s1.
  by split; first exact: Hs1; split; first exact: HP0;
     split; first exact: HQ0.
split.
- move=> i.
  apply: (cat_tuple_nonneg s1 s2 i).
  + exact: Hs1.
  + exact: Hs2.
split.
- exact: (completedTraceBind_dweightL
    mid s1 s2 P0 Q0 K P Q Hbind Hdist0 HK).
split.
- exact: (completedTraceBind_dweightR
    mid s1 s2 P0 Q0 K P Q Hbind Hdist0 HK).
move=> i a.
split.
- exact: (completedTraceBind_cond_finite_kl
    ML MR KL KR mid s1 s2 P0 Q0 K P Q
    Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hs2 HK i a).
- exact: (completedTraceBind_cond_bound
    ML MR KL KR mid s1 s2 P0 Q0 K P Q i a
    Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hs2 HK).
Qed.

Lemma completedTraceKernel_final_marginL
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (KL : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2)) :
  (forall y,
    dmargin (fun omega => tnth omega ord_max) (K y).1
      =1 complete_output_heap (KL (proj1_sig y))) ->
  forall omega,
    dmargin (fun omega2 => tnth omega2 ord_max)
      (@completedPythTraceKernelL ℓ1 ℓ2 mid_t mid K omega)
    =1 completedSemanticBindKernel KL mid (tnth omega ord_max).
Proof.
move=> HK omega z.
rewrite /completedPythTraceKernelL /completedSemanticBindKernel.
case: (tnth omega ord_max)=> [packed|].
- case: (decode_output_heap packed)=> [y|].
  + destruct (@idP (mid y)) as [Hy|Hnot].
      exact: (HK (exist _ y Hy) z).
    by rewrite dmargin_dunit default_completed_pyth_trace_final.
  + by rewrite dmargin_dunit default_completed_pyth_trace_final.
- by rewrite dmargin_dunit default_completed_pyth_trace_final.
Qed.

Lemma completedTraceKernel_final_marginR
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2)) :
  (forall y,
    dmargin (fun omega => tnth omega ord_max) (K y).2
      =1 complete_output_heap (KR (proj1_sig y))) ->
  forall omega,
    dmargin (fun omega2 => tnth omega2 ord_max)
      (@completedPythTraceKernelR ℓ1 ℓ2 mid_t mid K omega)
    =1 completedSemanticBindKernel KR mid (tnth omega ord_max).
Proof.
move=> HK omega z.
rewrite /completedPythTraceKernelR /completedSemanticBindKernel.
case: (tnth omega ord_max)=> [packed|].
- case: (decode_output_heap packed)=> [y|].
  + destruct (@idP (mid y)) as [Hy|Hnot].
      exact: (HK (exist _ y Hy) z).
    by rewrite dmargin_dunit default_completed_pyth_trace_final.
  + by rewrite dmargin_dunit default_completed_pyth_trace_final.
- by rewrite dmargin_dunit default_completed_pyth_trace_final.
Qed.

Lemma completedTraceKernel_bind_final_marginL
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML : {distr (mid_t * heap) / R})
  (KL : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (P0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2)) :
  dmargin (fun omega => tnth omega ord_max) P0
    =1 complete_output_heap ML ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y,
    dmargin (fun omega => tnth omega ord_max) (K y).1
      =1 complete_output_heap (KL (proj1_sig y))) ->
  \dlet_(omega <- P0)
    dmargin (fun omega2 => tnth omega2 ord_max)
      (completedPythTraceKernelL mid K omega)
  =1 complete_output_heap (\dlet_(y <- ML) KL y).
Proof.
move=> Hmargin Hmid HK z.
pose final (omega : (ℓ1.+1).-tuple (option (nat * heap))) :=
  tnth omega ord_max.
rewrite -(eq_in_dlet (mu := P0)
  (f := fun omega => completedSemanticBindKernel KL mid (final omega))
  (g := fun omega => dmargin (fun omega2 => tnth omega2 ord_max)
          (completedPythTraceKernelL mid K omega))).
  rewrite -(dlet_dmargin_final P0
    (completedSemanticBindKernel KL mid) z).
  rewrite -(eq_in_dlet
    (mu := complete_output_heap ML)
    (nu := dmargin final P0)
    (f := completedSemanticBindKernel KL mid)
    (g := completedSemanticBindKernel KL mid)).
    exact: (complete_output_heap_bind ML KL mid Hmid z).
  - by [].
  - by move=> x; rewrite -Hmargin.
- move=> omega Homega z'.
  rewrite /final.
  rewrite (@completedTraceKernel_final_marginL ℓ1 ℓ2 mid_t out_t
    KL mid K HK omega z').
  by [].
- by [].
Qed.

Lemma completedTraceKernel_bind_final_marginR
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (MR : {distr (mid_t * heap) / R})
  (KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2)) :
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 complete_output_heap MR ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y,
    dmargin (fun omega => tnth omega ord_max) (K y).2
      =1 complete_output_heap (KR (proj1_sig y))) ->
  \dlet_(omega <- Q0)
    dmargin (fun omega2 => tnth omega2 ord_max)
      (completedPythTraceKernelR mid K omega)
  =1 complete_output_heap (\dlet_(y <- MR) KR y).
Proof.
move=> Hmargin Hmid HK z.
pose final (omega : (ℓ1.+1).-tuple (option (nat * heap))) :=
  tnth omega ord_max.
rewrite -(eq_in_dlet (mu := Q0)
  (f := fun omega => completedSemanticBindKernel KR mid (final omega))
  (g := fun omega => dmargin (fun omega2 => tnth omega2 ord_max)
          (completedPythTraceKernelR mid K omega))).
  rewrite -(dlet_dmargin_final Q0
    (completedSemanticBindKernel KR mid) z).
  rewrite -(eq_in_dlet
    (mu := complete_output_heap MR)
    (nu := dmargin final Q0)
    (f := completedSemanticBindKernel KR mid)
    (g := completedSemanticBindKernel KR mid)).
    exact: (complete_output_heap_bind MR KR mid Hmid z).
  - by [].
  - by move=> x; rewrite -Hmargin.
- move=> omega Homega z'.
  rewrite /final.
  rewrite (@completedTraceKernel_final_marginR ℓ1 ℓ2 mid_t out_t
    KR mid K HK omega z').
  by [].
- by [].
Qed.

Lemma completedTraceBind_final_margins
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R}) :
  completedPythTraceBindPair mid P0 Q0 K P Q ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 complete_output_heap ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 complete_output_heap MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y,
    dmargin (fun omega => tnth omega ord_max) (K y).1
      =1 complete_output_heap (KL (proj1_sig y))) ->
  (forall y,
    dmargin (fun omega => tnth omega ord_max) (K y).2
      =1 complete_output_heap (KR (proj1_sig y))) ->
  dmargin (fun omega => tnth omega ord_max) P
    =1 complete_output_heap (\dlet_(y <- ML) KL y) /\
  dmargin (fun omega => tnth omega ord_max) Q
    =1 complete_output_heap (\dlet_(y <- MR) KR y).
Proof.
move=> [HP HQ] HmarginL0 HmarginR0 HmidL HmidR HKL HKR.
split.
- move=> z.
  rewrite (dmargin_ext (fun omega => tnth omega ord_max)
    P (completedPythTraceBindL mid P0 K) HP z).
  rewrite /completedPythTraceBindL.
  rewrite (dmargin_dlet_cat_final P0
    (completedPythTraceKernelL mid K) z).
  exact: (completedTraceKernel_bind_final_marginL
    ML KL mid P0 K HmarginL0 HmidL HKL z).
- move=> z.
  rewrite (dmargin_ext (fun omega => tnth omega ord_max)
    Q (completedPythTraceBindR mid Q0 K) HQ z).
  rewrite /completedPythTraceBindR.
  rewrite (dmargin_dlet_cat_final Q0
    (completedPythTraceKernelR mid K) z).
  exact: (completedTraceKernel_bind_final_marginR
    MR KR mid Q0 K HmarginR0 HmidR HKR z).
Qed.

Lemma completedTraceBind_post
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap)) :
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y : { y : mid_t * heap | mid y },
    forall x, x \in dinsupp (KL (proj1_sig y)) -> post x) ->
  (forall y : { y : mid_t * heap | mid y },
    forall x, x \in dinsupp (KR (proj1_sig y)) -> post x) ->
  (forall x, x \in dinsupp (\dlet_(y <- ML) KL y) -> post x) /\
  (forall x, x \in dinsupp (\dlet_(y <- MR) KR y) -> post x).
Proof.
move=> HmidL HmidR HpostL HpostR.
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

Lemma completedPythDist_bind_pyth_kernel_witness
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2)) :
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 complete_output_heap ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 complete_output_heap MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall i : 'I_(ℓ2.+1), 0 <= tnth s2 i) ->
  (forall y,
    completedPythKernelSpec
      (KL (proj1_sig y)) (KR (proj1_sig y)) post s2 (K y)) ->
  exists (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R}),
    pythDist P Q (cat_tuple s1 s2) /\
    dmargin (fun omega => tnth omega ord_max) P
      =1 complete_output_heap (\dlet_(y <- ML) KL y) /\
    dmargin (fun omega => tnth omega ord_max) Q
      =1 complete_output_heap (\dlet_(y <- MR) KR y) /\
    (forall x, x \in dinsupp (\dlet_(y <- ML) KL y) -> post x) /\
    (forall x, x \in dinsupp (\dlet_(y <- MR) KR y) -> post x).
Proof.
move=> Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hs2 HK.
pose P := completedPythTraceBindL mid P0 K.
pose Q := completedPythTraceBindR mid Q0 K.
have Hbind : completedPythTraceBindPair mid P0 Q0 K P Q.
  by split=> omega.
exists P, Q.
have Hdist :
    pythDist P Q (cat_tuple s1 s2).
  apply: (completedTraceBind_pythDist
    ML MR KL KR mid s1 s2 P0 Q0 K P Q Hbind
    Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hs2).
  move=> y.
  exact: (completedPythKernelSpec_dist _ _ _ _ _ (HK y)).
have [HmarginL HmarginR] :
    dmargin (fun omega => tnth omega ord_max) P
      =1 complete_output_heap (\dlet_(y <- ML) KL y) /\
    dmargin (fun omega => tnth omega ord_max) Q
      =1 complete_output_heap (\dlet_(y <- MR) KR y).
  apply: (completedTraceBind_final_margins
    ML MR KL KR mid P0 Q0 K P Q Hbind
    HmarginL0 HmarginR0 HmidL HmidR).
  - move=> y.
    exact: (completedPythKernelSpec_marginL _ _ _ _ _ (HK y)).
  - move=> y.
    exact: (completedPythKernelSpec_marginR _ _ _ _ _ (HK y)).
have [HpostL HpostR] :
    (forall x, x \in dinsupp (\dlet_(y <- ML) KL y) -> post x) /\
    (forall x, x \in dinsupp (\dlet_(y <- MR) KR y) -> post x).
  apply: (completedTraceBind_post
    ML MR KL KR mid post HmidL HmidR).
  - move=> y.
    move=> x.
    exact: (completedPythKernelSpec_postL _ _ _ _ _ x (HK y)).
  - move=> y.
    move=> x.
    exact: (completedPythKernelSpec_postR _ _ _ _ _ x (HK y)).
split; first exact: Hdist.
split; first exact: HmarginL.
split; first exact: HmarginR.
by split.
Qed.

Lemma completedPythDist_bind_pyth_kernel
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R}) :
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 complete_output_heap ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 complete_output_heap MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall i : 'I_(ℓ2.+1), 0 <= tnth s2 i) ->
  (forall y, mid y ->
    exists (P Q : {distr ((ℓ2.+1).-tuple
        (option (nat * heap))) / R}),
      pythDist P Q s2 /\
      dmargin (fun omega => tnth omega ord_max) P
        =1 complete_output_heap (KL y) /\
      dmargin (fun omega => tnth omega ord_max) Q
        =1 complete_output_heap (KR y) /\
      (forall x, x \in dinsupp (KL y) -> post x) /\
      (forall x, x \in dinsupp (KR y) -> post x)) ->
  exists (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R}),
    pythDist P Q (cat_tuple s1 s2) /\
    dmargin (fun omega => tnth omega ord_max) P
      =1 complete_output_heap (\dlet_(y <- ML) KL y) /\
    dmargin (fun omega => tnth omega ord_max) Q
      =1 complete_output_heap (\dlet_(y <- MR) KR y) /\
    (forall x, x \in dinsupp (\dlet_(y <- ML) KL y) -> post x) /\
    (forall x, x \in dinsupp (\dlet_(y <- MR) KR y) -> post x).
Proof.
move=> Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hs2 Hcont.
have Hcont' :
    forall y, mid y ->
      exists (P Q : {distr ((ℓ2.+1).-tuple
          (option (nat * heap))) / R}),
        completedPythKernelSpec (KL y) (KR y) post s2 (P, Q).
  move=> y Hy.
  have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
    Hcont y Hy.
  by exists P, Q.
have [K HK] :=
  completedPythKernel_choice KL KR mid post s2 Hcont'.
exact:
	  (completedPythDist_bind_pyth_kernel_witness
	    ML MR KL KR mid post s1 s2 P0 Q0 K
	    Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hs2 HK).
Qed.
