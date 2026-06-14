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

Definition completed_output_heap {out_t : choice_type}
    (out : {distr (out_t * heap) / R}) :
    {distr (option (nat * heap)) / R} :=
  complete (dmargin (@pack_output_heap out_t) out).

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
pose b := true.
pose B : {distr bool / R} := dunit b.
  have Hleft :
    (\dlet_(_ <- \dlet_(x <- D) K x) B) b =
    dweight (\dlet_(x <- D) K x).
  rewrite dletC /B dunit1E eqxx.
  by rewrite mulr1.
rewrite -Hleft.
rewrite (__deprecated__dlet_dlet K (fun _ : U => B) D b).
rewrite dletE.
apply/eq_psum=> x.
congr (_ * _).
rewrite dletC /B dunit1E eqxx.
by rewrite mulr1.
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
    =1 completed_output_heap KL /\
  dmargin (fun omega => tnth omega ord_max) Q
    =1 completed_output_heap KR /\
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
    =1 completed_output_heap KL.
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
    =1 completed_output_heap KR.
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
          | ReflectT _ => completed_output_heap (K y)
          | ReflectF _ => dunit None
          end
      | None => dunit None
      end
  | None => dunit None
  end.

Lemma completed_output_heap_bind_some
  {mid_t out_t : choice_type}
  (ML : {distr (mid_t * heap) / R})
  (KL : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap)) :
  (forall y, y \in dinsupp ML -> mid y) ->
  forall packed,
  (\dlet_(x <- completed_output_heap ML)
    completedSemanticBindKernel KL mid x) (Some packed)
  = completed_output_heap (\dlet_(y <- ML) KL y) (Some packed).
Proof.
move=> Hmid packed.
rewrite /completed_output_heap.
rewrite (dlet_complete_some (dmargin (@pack_output_heap mid_t) ML)
  (completedSemanticBindKernel KL mid) packed); last first.
  by rewrite /completedSemanticBindKernel dunit1E.
rewrite completeE /=.
rewrite (dlet_dmargin ML (@pack_output_heap mid_t)
  (fun x => completedSemanticBindKernel KL mid (Some x)) (Some packed)).
rewrite (dmargin_dlet ML (@pack_output_heap out_t) KL packed).
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
  by rewrite /completed_output_heap completeE.
by case: Hymid; exact: (Hmid y Hy).
Qed.

Lemma completed_output_heap_bind_none_mass
  {mid_t out_t : choice_type}
  (ML : {distr (mid_t * heap) / R})
  (KL : mid_t * heap -> {distr (out_t * heap) / R}) :
  (\dlet_(y <- ML) completed_output_heap (KL y)) None +
    (1 - dweight ML) =
  completed_output_heap (\dlet_(y <- ML) KL y) None.
Proof.
rewrite /completed_output_heap !completeE /=.
rewrite dmargin_dweight.
rewrite dletE.
rewrite (eq_psum
  (F2 := fun y => ML y * (1 - dweight (KL y)))).
  have Hscaled :
      psum (fun y => ML y * (1 - dweight (KL y))) =
      dweight ML - dweight (\dlet_(y <- ML) KL y).
    rewrite (eq_psum
      (F2 := fun y => ML y - ML y * dweight (KL y))).
      rewrite (@psumB R _ ML
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

Lemma completed_output_heap_bind_none
  {mid_t out_t : choice_type}
  (ML : {distr (mid_t * heap) / R})
  (KL : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap)) :
  (forall y, y \in dinsupp ML -> mid y) ->
  (\dlet_(x <- completed_output_heap ML)
    completedSemanticBindKernel KL mid x) None
  = completed_output_heap (\dlet_(y <- ML) KL y) None.
Proof.
move=> Hmid.
rewrite /completed_output_heap.
rewrite dlet_complete_none.
rewrite dmargin_dweight dunit1E eqxx mulr1.
rewrite (dlet_dmargin ML (@pack_output_heap mid_t)
  (fun x => completedSemanticBindKernel KL mid (Some x)) None).
rewrite -(completed_output_heap_bind_none_mass ML KL).
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
  by rewrite /completed_output_heap.
by case: Hymid; exact: (Hmid y Hy).
Qed.


Lemma completed_output_heap_bind
  {mid_t out_t : choice_type}
  (ML : {distr (mid_t * heap) / R})
  (KL : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap)) :
  (forall y, y \in dinsupp ML -> mid y) ->
  \dlet_(x <- completed_output_heap ML)
    completedSemanticBindKernel KL mid x
  =1 completed_output_heap (\dlet_(y <- ML) KL y).
Proof.
move=> Hmid [packed|].
- exact: completed_output_heap_bind_some.
- exact: completed_output_heap_bind_none.
Qed.

Definition completedFinalUpdate
  {ℓ : nat}
  (omega : (ℓ.+1).-tuple (option (nat * heap)))
  (z : option (nat * heap)) :
    (ℓ.+1).-tuple (option (nat * heap)) :=
  [tuple if i == ord_max then z else tnth omega i | i < ℓ.+1].

Definition completedFinalBindTrace
  {ℓ : nat}
  {mid_t out_t : choice_type}
  (K : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (P : {distr ((ℓ.+1).-tuple (option (nat * heap))) / R}) :
    {distr ((ℓ.+1).-tuple (option (nat * heap))) / R} :=
  \dlet_(omega <- P)
  \dlet_(z <- completedSemanticBindKernel K mid (tnth omega ord_max))
    dunit (completedFinalUpdate omega z).

Lemma completedSemanticBindKernel_dweight1
  {mid_t out_t : choice_type}
  (K : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (z : option (nat * heap)) :
  dweight (completedSemanticBindKernel K mid z) = 1.
Proof.
rewrite /completedSemanticBindKernel.
case: z=> [packed|]; last exact: dunit_dweight.
case: (decode_output_heap packed)=> [y|]; last exact: dunit_dweight.
destruct (@idP (mid y)) as [Hy|Hnot].
  exact: complete_dweight.
exact: dunit_dweight.
Qed.

Lemma completedFinalBindTrace_absolute_continuous
  {ℓ : nat}
  {mid_t out_t : choice_type}
  (K : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (P0 Q0 : {distr ((ℓ.+1).-tuple (option (nat * heap))) / R}) :
  absolute_continuous P0 Q0 ->
  absolute_continuous
    (completedFinalBindTrace K mid P0)
    (completedFinalBindTrace K mid Q0).
Proof.
move=> Hac omega' HQomega'0.
apply/eqP; apply/negP=> HPomega'_nz.
have HPomega'_supp :
    omega' \in dinsupp (completedFinalBindTrace K mid P0).
  by rewrite in_dinsupp; apply/negP.
rewrite /completedFinalBindTrace in HPomega'_supp.
have [omega Homega Hinner] :=
  @dinsupp_dlet R _ _ _ _ _ HPomega'_supp.
have [z Hz Hunit] := @dinsupp_dlet R _ _ _ _ _ Hinner.
have Homega' :
    omega' = completedFinalUpdate omega z.
  move: Hunit.
  by rewrite dunit1E pnatr_eq0 eqb0 negbK=> /eqP.
have HQomega : omega \in dinsupp Q0.
  rewrite in_dinsupp.
  apply/negP=> /eqP HQomega0.
  move: Homega.
  by rewrite in_dinsupp (Hac omega HQomega0) eqxx.
have HQomega'_supp :
    omega' \in dinsupp (completedFinalBindTrace K mid Q0).
  rewrite /completedFinalBindTrace Homega'.
  apply: (@dlet_dinsupp R _ _
    (fun omega0 =>
      \dlet_(z0 <- completedSemanticBindKernel K mid
          (tnth omega0 ord_max))
        dunit (completedFinalUpdate omega0 z0))
    Q0 omega (completedFinalUpdate omega z) HQomega).
  apply: (@dlet_dinsupp R _ _
    (fun z0 => dunit (completedFinalUpdate omega z0))
    (completedSemanticBindKernel K mid (tnth omega ord_max))
    z (completedFinalUpdate omega z) Hz).
  by rewrite dunit1E eqxx oner_neq0.
move: HQomega'_supp.
by rewrite in_dinsupp HQomega'0 eqxx.
Qed.

Lemma completedFinalBindTrace_dweight1
  {ℓ : nat}
  {mid_t out_t : choice_type}
  (K : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (P0 : {distr ((ℓ.+1).-tuple (option (nat * heap))) / R}) :
  dweight P0 = 1 ->
  dweight (completedFinalBindTrace K mid P0) = 1.
Proof.
move=> HP0.
rewrite /completedFinalBindTrace dweight_dlet.
  rewrite (eq_psum
    (F2 := fun omega : (ℓ.+1).-tuple (option (nat * heap)) => P0 omega)).
  by rewrite -pr_predT.
move=> omega.
rewrite dweight_dlet.
rewrite (eq_psum
  (F2 := fun z => completedSemanticBindKernel K mid
    (tnth omega ord_max) z)).
  by rewrite -pr_predT completedSemanticBindKernel_dweight1 mulr1.
move=> z.
by rewrite dunit_dweight mulr1.
Qed.


Lemma completedFinalBindTrace_cond_nonfinal_eq
  {ℓ : nat}
  {mid_t out_t : choice_type}
  (K : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (P0 Q0 : {distr ((ℓ.+1).-tuple (option (nat * heap))) / R})
  (i : 'I_(ℓ.+1))
  (a : forall j : 'I_(ℓ.+1), option (nat * heap)) :
  (i < @ord_max ℓ)%N ->
  conditional_coordinate (completedFinalBindTrace K mid P0) i a
    =1 conditional_coordinate P0 i a /\
  conditional_coordinate (completedFinalBindTrace K mid Q0) i a
    =1 conditional_coordinate Q0 i a.
Proof.
Admitted.

Lemma completedFinalBindTrace_cond_final_eq
  {ℓ : nat}
  {mid_t out_t : choice_type}
  (K : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (P0 : {distr ((ℓ.+1).-tuple (option (nat * heap))) / R})
  (a : forall j : 'I_(ℓ.+1), option (nat * heap)) :
  conditional_coordinate
    (completedFinalBindTrace K mid P0) (@ord_max ℓ) a
  =1
  \dlet_(z <- conditional_coordinate P0 (@ord_max ℓ) a)
    completedSemanticBindKernel K mid z.
Proof.
Admitted.

Lemma completedFinalBindTrace_cond_final_bound
  {ℓ : nat}
  {mid_t out_t : choice_type}
  (K : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s : (ℓ.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ.+1).-tuple (option (nat * heap))) / R})
  (a : forall j : 'I_(ℓ.+1), option (nat * heap)) :
  pythDist P0 Q0 s ->
  δ_KL
    (conditional_coordinate
      (completedFinalBindTrace K mid P0) (@ord_max ℓ) a)
    (conditional_coordinate
      (completedFinalBindTrace K mid Q0) (@ord_max ℓ) a)
  <= tnth s (@ord_max ℓ).
Proof.
move=> Hdist.
case: Hdist=> _ [_ [_ [_ Hcond]]].
rewrite (kl_ext
  (conditional_coordinate
    (completedFinalBindTrace K mid P0) (@ord_max ℓ) a)
  (\dlet_(z <- conditional_coordinate P0 (@ord_max ℓ) a)
    completedSemanticBindKernel K mid z)
  (conditional_coordinate
    (completedFinalBindTrace K mid Q0) (@ord_max ℓ) a)
  (\dlet_(z <- conditional_coordinate Q0 (@ord_max ℓ) a)
    completedSemanticBindKernel K mid z)).
  apply: (le_trans
    (kl_dlet_data_processing
      (conditional_coordinate P0 (@ord_max ℓ) a)
      (conditional_coordinate Q0 (@ord_max ℓ) a)
      (completedSemanticBindKernel K mid)
      (completedSemanticBindKernel_dweight1 K mid))).
  exact: Hcond.
- exact: completedFinalBindTrace_cond_final_eq.
- exact: completedFinalBindTrace_cond_final_eq.
Qed.


Lemma completedFinalBindTrace_cond_bound
  {ℓ : nat}
  {mid_t out_t : choice_type}
  (K : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s : (ℓ.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ.+1).-tuple (option (nat * heap))) / R})
  (i : 'I_(ℓ.+1))
  (a : forall j : 'I_(ℓ.+1), option (nat * heap)) :
  pythDist P0 Q0 s ->
  δ_KL
    (conditional_coordinate
      (completedFinalBindTrace K mid P0) i a)
    (conditional_coordinate
      (completedFinalBindTrace K mid Q0) i a)
  <= tnth s i.
Proof.
move=> Hdist.
case Himax: (i == @ord_max ℓ).
  have -> : i = @ord_max ℓ by apply/eqP.
  exact: (completedFinalBindTrace_cond_final_bound K mid s P0 Q0 a Hdist).
	have Hi : (i < @ord_max ℓ)%N.
	  rewrite /ord_max /=.
	  have Hi_le : (i <= ℓ)%N by rewrite -ltnS.
	  move: Hi_le; rewrite leq_eqVlt; move/orP=> [/eqP Hi_eq|Hi_lt];
	    last exact: Hi_lt.
	  have Hi_ord : i = @ord_max ℓ by apply: val_inj; rewrite /= Hi_eq.
	  by rewrite Hi_ord eqxx in Himax.
have [HP HQ] := completedFinalBindTrace_cond_nonfinal_eq
  K mid P0 Q0 i a Hi.
case: Hdist=> _ [_ [_ [_ Hcond]]].
rewrite (kl_ext
  (conditional_coordinate (completedFinalBindTrace K mid P0) i a)
  (conditional_coordinate P0 i a)
  (conditional_coordinate (completedFinalBindTrace K mid Q0) i a)
  (conditional_coordinate Q0 i a) HP HQ).
exact: Hcond.
Qed.

Lemma completedFinalBindTrace_pythDist
  {ℓ : nat}
  {mid_t out_t : choice_type}
  (K : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s : (ℓ.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ.+1).-tuple (option (nat * heap))) / R}) :
  pythDist P0 Q0 s ->
  pythDist
    (completedFinalBindTrace K mid P0)
    (completedFinalBindTrace K mid Q0)
    s.
Proof.
move=> Hdist.
case: Hdist=> Hs [Hac [HP [HQ Hcond]]].
split; first exact: Hs.
split.
  exact: (completedFinalBindTrace_absolute_continuous K mid P0 Q0 Hac).
split.
  exact: (completedFinalBindTrace_dweight1 K mid P0 HP).
split.
  exact: (completedFinalBindTrace_dweight1 K mid Q0 HQ).
move=> i a.
exact: (completedFinalBindTrace_cond_bound K mid s P0 Q0 i a
  (conj Hs (conj Hac (conj HP (conj HQ Hcond))))).
Qed.


Lemma completedPythDist_bind_common_final_kernel
  {ℓ : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (K : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ.+1).-tuple (option (nat * heap))) / R}) :
  pythDist P0 Q0 s ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 completed_output_heap ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 completed_output_heap MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, mid y -> forall x, x \in dinsupp (K y) -> post x) ->
  exists (P Q : {distr ((ℓ.+1).-tuple (option (nat * heap))) / R}),
    pythDist P Q s /\
    dmargin (fun omega => tnth omega ord_max) P
      =1 completed_output_heap (\dlet_(y <- ML) K y) /\
    dmargin (fun omega => tnth omega ord_max) Q
      =1 completed_output_heap (\dlet_(y <- MR) K y) /\
    (forall x, x \in dinsupp (\dlet_(y <- ML) K y) -> post x) /\
    (forall x, x \in dinsupp (\dlet_(y <- MR) K y) -> post x).
Proof.
move=> Hdist HmarginL HmarginR HmidL HmidR Hpost.
pose P := completedFinalBindTrace K mid P0.
pose Q := completedFinalBindTrace K mid Q0.
exists P, Q.
have Hdist_bind : pythDist P Q s.
  exact: (completedFinalBindTrace_pythDist K mid s P0 Q0 Hdist).
have Hmargin_bindL :
    dmargin (fun omega => tnth omega ord_max) P
      =1 completed_output_heap (\dlet_(y <- ML) K y).
  move=> z.
  pose final (omega : (ℓ.+1).-tuple (option (nat * heap))) :=
    tnth omega ord_max.
  rewrite /P /completedFinalBindTrace.
  rewrite dmargin_dlet.
  have Hfinal_bind :
      (\dlet_(omega <- P0)
        dmargin final
          (\dlet_(z0 <- completedSemanticBindKernel K mid (tnth omega ord_max))
            dunit (completedFinalUpdate omega z0)))
      =1
      (\dlet_(omega <- P0)
        (completedSemanticBindKernel K mid (final omega))).
    apply: eq_in_dlet=> // omega _ z'.
    rewrite /final dmargin_dlet.
    rewrite -(dlet_dunit_id
      (completedSemanticBindKernel K mid (tnth omega ord_max)) z').
    apply: eq_in_dlet=> // z0 _ z1.
    rewrite dmargin_dunit /final.
    by rewrite tnth_mktuple eqxx.
  rewrite (Hfinal_bind z).
  rewrite -(dlet_dmargin P0 final (completedSemanticBindKernel K mid) z).
  rewrite -(eq_in_dlet
    (mu := completed_output_heap ML)
    (nu := dmargin final P0)
    (f := completedSemanticBindKernel K mid)
    (g := completedSemanticBindKernel K mid)).
    exact: (completed_output_heap_bind ML K mid HmidL z).
  - by [].
  - by move=> x; rewrite -HmarginL.
have Hmargin_bindR :
    dmargin (fun omega => tnth omega ord_max) Q
      =1 completed_output_heap (\dlet_(y <- MR) K y).
  move=> z.
  pose final (omega : (ℓ.+1).-tuple (option (nat * heap))) :=
    tnth omega ord_max.
  rewrite /Q /completedFinalBindTrace.
  rewrite dmargin_dlet.
  have Hfinal_bind :
      (\dlet_(omega <- Q0)
        dmargin final
          (\dlet_(z0 <- completedSemanticBindKernel K mid (tnth omega ord_max))
            dunit (completedFinalUpdate omega z0)))
      =1
      (\dlet_(omega <- Q0)
        (completedSemanticBindKernel K mid (final omega))).
    apply: eq_in_dlet=> // omega _ z'.
    rewrite /final dmargin_dlet.
    rewrite -(dlet_dunit_id
      (completedSemanticBindKernel K mid (tnth omega ord_max)) z').
    apply: eq_in_dlet=> // z0 _ z1.
    rewrite dmargin_dunit /final.
    by rewrite tnth_mktuple eqxx.
  rewrite (Hfinal_bind z).
  rewrite -(dlet_dmargin Q0 final (completedSemanticBindKernel K mid) z).
  rewrite -(eq_in_dlet
    (mu := completed_output_heap MR)
    (nu := dmargin final Q0)
    (f := completedSemanticBindKernel K mid)
    (g := completedSemanticBindKernel K mid)).
    exact: (completed_output_heap_bind MR K mid HmidR z).
  - by [].
  - by move=> x; rewrite -HmarginR.
have HpostL : forall x, x \in dinsupp (\dlet_(y <- ML) K y) -> post x.
  move=> x Hx.
  have [y Hy Hinner] := @dinsupp_dlet R _ _ K ML x Hx.
  have Hy_mid := HmidL y Hy.
  have Hx_inner : x \in dinsupp (K y).
    by rewrite in_dinsupp.
  exact: (Hpost y Hy_mid x Hx_inner).
have HpostR : forall x, x \in dinsupp (\dlet_(y <- MR) K y) -> post x.
  move=> x Hx.
  have [y Hy Hinner] := @dinsupp_dlet R _ _ K MR x Hx.
  have Hy_mid := HmidR y Hy.
  have Hx_inner : x \in dinsupp (K y).
    by rewrite in_dinsupp.
  exact: (Hpost y Hy_mid x Hx_inner).
split; first exact: Hdist_bind.
split; first exact: Hmargin_bindL.
split; first exact: Hmargin_bindR.
by split.
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
  {mid_t out_t : choice_type}
  (ML : {distr (mid_t * heap) / R})
  (KL : mid_t * heap -> {distr (out_t * heap) / R})
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
  {mid_t out_t : choice_type}
  (MR : {distr (mid_t * heap) / R})
  (KR : mid_t * heap -> {distr (out_t * heap) / R})
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
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R}) : Prop :=
  P =1 completedPythTraceBindL ML KL mid P0 K /\
  Q =1 completedPythTraceBindR MR KR mid Q0 K.

Lemma completedTraceBind_exists
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2)) :
  exists (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R}),
    completedPythTraceBindPair ML MR KL KR mid P0 Q0 K P Q.
Proof.
exists (completedPythTraceBindL ML KL mid P0 K),
       (completedPythTraceBindR MR KR mid Q0 K).
by split=> omega.
Qed.

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
  by case: (HK (exist _ y Hy))=> _ [Hac _].
by move=> x Hx.
Qed.

Lemma completedTraceBind_absolute_continuous
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
  completedPythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  absolute_continuous P Q.
Proof.
move=> [HP HQ] Hdist0 HK.
case: Hdist0=> _ [Hac0 _].
have Hac_bind :
    absolute_continuous
      (completedPythTraceBindL ML KL mid P0 K)
      (completedPythTraceBindR MR KR mid Q0 K).
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
  {mid_t out_t : choice_type}
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
  by case: (HK (exist _ y Hy))=> _ [_ [Hmass _]].
exact: dunit_dweight.
Qed.

Lemma completedPythTraceKernelR_dweight1
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
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
  by case: (HK (exist _ y Hy))=> _ [_ [_ [Hmass _]]].
exact: dunit_dweight.
Qed.

Lemma completedTraceBind_dweightL
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
  completedPythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  dweight P = 1.
Proof.
move=> [HP _] Hdist0 HK.
case: Hdist0=> _ [_ [HP0mass _]].
rewrite (pr_ext P (completedPythTraceBindL ML KL mid P0 K) predT HP).
rewrite /completedPythTraceBindL.
rewrite (pr_dlet_cat_prefix_lift_eq P0 (completedPythTraceKernelL mid K)
  predT predT
  (fun omega => @completedPythTraceKernelL_dweight1
    ℓ1 ℓ2 mid_t out_t mid s2 K omega HK));
  last by move=> omega1 omega2.
exact: HP0mass.
Qed.

Lemma completedTraceBind_dweightR
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
  completedPythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  dweight Q = 1.
Proof.
move=> [_ HQ] Hdist0 HK.
case: Hdist0=> _ [_ [_ [HQ0mass _]]].
rewrite (pr_ext Q (completedPythTraceBindR MR KR mid Q0 K) predT HQ).
rewrite /completedPythTraceBindR.
rewrite (pr_dlet_cat_prefix_lift_eq Q0 (completedPythTraceKernelR mid K)
  predT predT
  (fun omega => @completedPythTraceKernelR_dweight1
    ℓ1 ℓ2 mid_t out_t mid s2 K omega HK));
  last by move=> omega1 omega2.
exact: HQ0mass.
Qed.

Lemma completedTraceBind_conditional_coordinate_prefix_eqL
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML : {distr (mid_t * heap) / R})
  (KL : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (P0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), option (nat * heap))
  (Hi : (i < ℓ1.+1)%N) :
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
  let a0 : forall j : 'I_(ℓ1.+1), option (nat * heap) :=
    fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
  conditional_coordinate (completedPythTraceBindL ML KL mid P0 K) i a
    =1 conditional_coordinate P0 i0 a0.
Proof.
move=> HK.
exact: (conditional_coordinate_dlet_cat_prefix_eq
  P0 (completedPythTraceKernelL mid K) i a Hi
  (fun omega => completedPythTraceKernelL_dweight1 mid s2 K omega HK)).
Qed.

Lemma completedTraceBind_conditional_coordinate_prefix_eqR
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (MR : {distr (mid_t * heap) / R})
  (KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), option (nat * heap))
  (Hi : (i < ℓ1.+1)%N) :
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
  let a0 : forall j : 'I_(ℓ1.+1), option (nat * heap) :=
    fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
  conditional_coordinate (completedPythTraceBindR MR KR mid Q0 K) i a
    =1 conditional_coordinate Q0 i0 a0.
Proof.
move=> HK.
exact: (conditional_coordinate_dlet_cat_prefix_eq
  Q0 (completedPythTraceKernelR mid K) i a Hi
  (fun omega => completedPythTraceKernelR_dweight1 mid s2 K omega HK)).
Qed.

Lemma completedTraceBind_prefix_condL
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), option (nat * heap))
  (Hi : (i < ℓ1.+1)%N) :
  completedPythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
  let a0 : forall j : 'I_(ℓ1.+1), option (nat * heap) :=
    fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
  conditional_coordinate P i a
    =1 conditional_coordinate P0 i0 a0.
Proof.
move=> [HP _] HK /= x.
rewrite (conditional_coordinate_dist_ext P
  (completedPythTraceBindL ML KL mid P0 K) i a HP x).
exact: (completedTraceBind_conditional_coordinate_prefix_eqL
  ML KL mid s2 P0 K i a Hi HK x).
Qed.

Lemma completedTraceBind_prefix_condR
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), option (nat * heap))
  (Hi : (i < ℓ1.+1)%N) :
  completedPythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
  let a0 : forall j : 'I_(ℓ1.+1), option (nat * heap) :=
    fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
  conditional_coordinate Q i a
    =1 conditional_coordinate Q0 i0 a0.
Proof.
move=> [_ HQ] HK /= x.
rewrite (conditional_coordinate_dist_ext Q
  (completedPythTraceBindR MR KR mid Q0 K) i a HQ x).
exact: (completedTraceBind_conditional_coordinate_prefix_eqR
  MR KR mid s2 Q0 K i a Hi HK x).
Qed.

Lemma completedTraceBind_prefix_cond
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), option (nat * heap))
  (Hi : (i < ℓ1.+1)%N) :
  completedPythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
  let a0 : forall j : 'I_(ℓ1.+1), option (nat * heap) :=
    fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
  δ_KL (conditional_coordinate P i a)
       (conditional_coordinate Q i a) =
  δ_KL (conditional_coordinate P0 i0 a0)
       (conditional_coordinate Q0 i0 a0).
Proof.
move=> Hbind HK.
apply: kl_ext.
- exact: (completedTraceBind_prefix_condL
    ML MR KL KR mid s2 P0 Q0 K P Q i a Hi Hbind HK).
- exact: (completedTraceBind_prefix_condR
    ML MR KL KR mid s2 P0 Q0 K P Q i a Hi Hbind HK).
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
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), option (nat * heap)) :
  completedPythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  (i < ℓ1.+1)%N ->
  δ_KL (conditional_coordinate P i a)
       (conditional_coordinate Q i a) <=
    tnth (cat_tuple s1 s2) i.
Proof.
move=> Hbind [_ [_ [_ [_ Hcond0]]]] HK Hi.
pose i0 : 'I_(ℓ1.+1) := Ordinal Hi.
pose a0 : forall j : 'I_(ℓ1.+1), option (nat * heap) :=
  fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))).
rewrite (completedTraceBind_prefix_cond
  ML MR KL KR mid s2 P0 Q0 K P Q i a Hi Hbind HK).
rewrite (cat_tuple_tnth_prefix s1 s2 i Hi).
exact: (Hcond0 i0 a0).
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
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), option (nat * heap))
  (Hi : (ℓ1.+1 <= i)%N) :
  completedPythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  (forall i : 'I_(ℓ2.+1), 0 <= tnth s2 i) ->
  P0 (catTuplePrefix a) = 0 ->
  δ_KL (conditional_coordinate P i a)
       (conditional_coordinate Q i a) <=
    tnth s2 (catTupleSuffixIndex i Hi).
Proof.
move=> Hbind Hs2 HP0z.
have HPnull : conditional_coordinate P i a =1 dnull.
  case: Hbind=> HP _ x.
  rewrite (conditional_coordinate_dist_ext P
    (completedPythTraceBindL ML KL mid P0 K) i a HP x).
  exact: (conditional_coordinate_dlet_cat_suffix_zero_prefix
    P0 (completedPythTraceKernelL mid K) i a Hi HP0z x).
rewrite (kl_left_dnull
  (conditional_coordinate P i a)
  (conditional_coordinate Q i a)
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
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), option (nat * heap))
  (Hi : (ℓ1.+1 <= i)%N)
  (packed : nat * heap)
  (y : { y : mid_t * heap | mid y }) :
  completedPythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  tnth (catTuplePrefix a) ord_max = Some packed ->
  @decode_output_heap mid_t packed = Some (proj1_sig y) ->
  0 < P0 (catTuplePrefix a) ->
  conditional_coordinate P i a
    =1 conditional_coordinate (K y).1
        (catTupleSuffixIndex i Hi)
        (catTupleSuffixAssignment i Hi a).
Proof.
move=> [HP _] Homega Hdecode Hpos x.
rewrite (conditional_coordinate_dist_ext P
  (completedPythTraceBindL ML KL mid P0 K) i a HP x).
pose omega1 := catTuplePrefix a.
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
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), option (nat * heap))
  (Hi : (ℓ1.+1 <= i)%N)
  (packed : nat * heap)
  (y : { y : mid_t * heap | mid y }) :
  completedPythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  tnth (catTuplePrefix a) ord_max = Some packed ->
  @decode_output_heap mid_t packed = Some (proj1_sig y) ->
  0 < Q0 (catTuplePrefix a) ->
  conditional_coordinate Q i a
    =1 conditional_coordinate (K y).2
        (catTupleSuffixIndex i Hi)
        (catTupleSuffixAssignment i Hi a).
Proof.
move=> [_ HQ] Homega Hdecode Hpos x.
rewrite (conditional_coordinate_dist_ext Q
  (completedPythTraceBindR MR KR mid Q0 K) i a HQ x).
pose omega1 := catTuplePrefix a.
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
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), option (nat * heap))
  (Hi : (ℓ1.+1 <= i)%N)
  (packed : nat * heap)
  (y : { y : mid_t * heap | mid y }) :
  completedPythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  tnth (catTuplePrefix a) ord_max = Some packed ->
  @decode_output_heap mid_t packed = Some (proj1_sig y) ->
  0 < P0 (catTuplePrefix a) ->
  0 < Q0 (catTuplePrefix a) ->
  δ_KL (conditional_coordinate P i a)
       (conditional_coordinate Q i a) =
  δ_KL (conditional_coordinate (K y).1
          (catTupleSuffixIndex i Hi)
          (catTupleSuffixAssignment i Hi a))
       (conditional_coordinate (K y).2
          (catTupleSuffixIndex i Hi)
          (catTupleSuffixAssignment i Hi a)).
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
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), option (nat * heap))
  (Hi : (ℓ1.+1 <= i)%N)
  (packed : nat * heap)
  (y : { y : mid_t * heap | mid y }) :
  completedPythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  tnth (catTuplePrefix a) ord_max = Some packed ->
  @decode_output_heap mid_t packed = Some (proj1_sig y) ->
  δ_KL (conditional_coordinate P i a)
       (conditional_coordinate Q i a) <=
    tnth s2 (catTupleSuffixIndex i Hi).
Proof.
move=> Hbind Hdist0 HK Homega Hdecode.
move: Hdist0=> [Hs1 [Hac0 [HP0mass [HQ0mass Hcond0]]]].
have Hdist0 : pythDist P0 Q0 s1.
  by split; first exact: Hs1; split; first exact: Hac0;
     split; first exact: HP0mass; split; first exact: HQ0mass.
case HP0z: (P0 (catTuplePrefix a) == 0).
  have Hs2 : forall j : 'I_(ℓ2.+1), 0 <= tnth s2 j.
    by case: (HK y)=> Hs2 _.
  exact: (completedTraceBind_suffix_bound_zero_prefix
    ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi
    Hbind Hs2 (eqP HP0z)).
have HP0pos : 0 < P0 (catTuplePrefix a).
  by rewrite lt_def ge0_mu HP0z.
have HQ0pos : 0 < Q0 (catTuplePrefix a).
  exact: (absolute_continuous_positive P0 Q0 _ Hac0 HP0pos).
rewrite (completedTraceBind_suffix_cond_valid_mid
  ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi packed y
  Hbind Hdist0 Homega Hdecode HP0pos HQ0pos).
case: (HK y)=> _ [_ [_ [_ Hcond]]].
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
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), option (nat * heap))
  (Hi : (ℓ1.+1 <= i)%N) :
  match tnth (catTuplePrefix a) ord_max with
  | Some packed =>
      match @decode_output_heap mid_t packed with
      | Some y => ~~ mid y
      | None => true
      end
  | None => true
  end ->
  completedPythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 completed_output_heap ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 completed_output_heap MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall j : 'I_(ℓ2.+1), 0 <= tnth s2 j) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  δ_KL (conditional_coordinate P i a)
       (conditional_coordinate Q i a) <=
    tnth s2 (Ordinal (cat_tuple_suffix_bound i Hi)).
Proof.
move=> Hbad Hbind Hdist0 HmarginL0 _ HmidL _ Hs2 HK.
case Hfinal: (tnth (catTuplePrefix a) ord_max)=> [packed|].
- have HP0z : P0 (catTuplePrefix a) = 0.
    case HP0z: (P0 (catTuplePrefix a) == 0).
      exact/eqP.
    have Hprefix_supp : catTuplePrefix a \in dinsupp P0.
      by rewrite in_dinsupp HP0z.
    have Hfinal_supp_P0 :
        Some packed \in
          dinsupp (dmargin (fun omega => tnth omega ord_max) P0).
      rewrite -Hfinal.
      exact: (dmargin_dinsupp_image P0
        (fun omega => tnth omega ord_max) _ Hprefix_supp).
    have Hfinal_supp_ML :
        Some packed \in dinsupp (completed_output_heap ML).
      rewrite in_dinsupp -HmarginL0.
      by move: Hfinal_supp_P0; rewrite in_dinsupp.
    have Hpacked_supp :
        packed \in dinsupp (dmargin (@pack_output_heap mid_t) ML).
      move: Hfinal_supp_ML.
      by rewrite in_dinsupp /completed_output_heap completeE /= in_dinsupp.
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
- case HP0z: (P0 (catTuplePrefix a) == 0).
    rewrite (completedTraceBind_suffix_bound_zero_prefix
      ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi
      Hbind Hs2 (eqP HP0z)).
    by [].
  move: Hdist0=> [_ [Hac0 _]].
  have HP0pos : 0 < P0 (catTuplePrefix a).
    by rewrite lt_def ge0_mu HP0z.
  have HQ0pos : 0 < Q0 (catTuplePrefix a).
    exact: (absolute_continuous_positive P0 Q0 _ Hac0 HP0pos).
  pose D : {distr (option (nat * heap)) / R} := conditional_coordinate
    (dunit (default_completed_pyth_trace (n := ℓ2.+1)))
    (catTupleSuffixIndex i Hi)
    (catTupleSuffixAssignment i Hi a).
  have Hkl0 :
      δ_KL (conditional_coordinate P i a)
           (conditional_coordinate Q i a) = 0.
    rewrite -(kl_self D).
    apply: kl_ext.
    + case: Hbind=> HP _ x.
      rewrite (conditional_coordinate_dist_ext P
        (completedPythTraceBindL ML KL mid P0 K) i a HP x).
      pose omega1 := catTuplePrefix a.
      rewrite (conditional_coordinate_dlet_cat_suffix_eq
        P0 (completedPythTraceKernelL mid K) i a Hi omega1 erefl HP0pos x).
      by rewrite /completedPythTraceKernelL Hfinal.
    + case: Hbind=> _ HQ x.
      rewrite (conditional_coordinate_dist_ext Q
        (completedPythTraceBindR MR KR mid Q0 K) i a HQ x).
      pose omega1 := catTuplePrefix a.
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
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), option (nat * heap)) :
  completedPythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 completed_output_heap ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 completed_output_heap MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall j : 'I_(ℓ2.+1), 0 <= tnth s2 j) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  (ℓ1.+1 <= i)%N ->
  δ_KL (conditional_coordinate P i a)
       (conditional_coordinate Q i a) <=
    tnth (cat_tuple s1 s2) i.
Proof.
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hs2 HK Hi.
rewrite (cat_tuple_tnth_suffix s1 s2 i Hi).
case Hfinal: (tnth (catTuplePrefix a) ord_max)=> [packed|].
  case Hdecode: (@decode_output_heap mid_t packed)=> [y|].
    case Hmidy: (mid y).
	    - have Hy : mid y by rewrite Hmidy.
	      exact: (completedTraceBind_suffix_bound_valid_mid
	        ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi packed
	        (exist _ y Hy) Hbind Hdist0 HK Hfinal Hdecode).
	    - have Hbad : is_true (
	        match tnth (catTuplePrefix a) ord_max with
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
	      match tnth (catTuplePrefix a) ord_max with
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
    match tnth (catTuplePrefix a) ord_max with
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
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), option (nat * heap)) :
  completedPythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 completed_output_heap ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 completed_output_heap MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall j : 'I_(ℓ2.+1), 0 <= tnth s2 j) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  δ_KL (conditional_coordinate P i a)
       (conditional_coordinate Q i a) <=
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
  completedPythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 completed_output_heap ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 completed_output_heap MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall i : 'I_(ℓ2.+1), 0 <= tnth s2 i) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  pythDist P Q (cat_tuple s1 s2).
Proof.
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hs2 HK.
move: Hdist0=> [Hs1 [Hac0 [HP0 [HQ0 Hcond0]]]].
have Hdist0 : pythDist P0 Q0 s1.
  by split; first exact: Hs1; split; first exact: Hac0;
     split; first exact: HP0; split; first exact: HQ0.
split.
- move=> i.
  apply: (cat_tuple_nonneg s1 s2 i).
  + exact: Hs1.
  + exact: Hs2.
split.
- exact: (completedTraceBind_absolute_continuous
    ML MR KL KR mid s1 s2 P0 Q0 K P Q Hbind Hdist0 HK).
split.
- exact: (completedTraceBind_dweightL
    ML MR KL KR mid s1 s2 P0 Q0 K P Q Hbind Hdist0 HK).
split.
- exact: (completedTraceBind_dweightR
    ML MR KL KR mid s1 s2 P0 Q0 K P Q Hbind Hdist0 HK).
- move=> i a.
  exact: (completedTraceBind_cond_bound
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
      =1 completed_output_heap (KL (proj1_sig y))) ->
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
      =1 completed_output_heap (KR (proj1_sig y))) ->
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
    =1 completed_output_heap ML ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y,
    dmargin (fun omega => tnth omega ord_max) (K y).1
      =1 completed_output_heap (KL (proj1_sig y))) ->
  \dlet_(omega <- P0)
    dmargin (fun omega2 => tnth omega2 ord_max)
      (completedPythTraceKernelL mid K omega)
  =1 completed_output_heap (\dlet_(y <- ML) KL y).
Proof.
move=> Hmargin Hmid HK z.
pose final (omega : (ℓ1.+1).-tuple (option (nat * heap))) :=
  tnth omega ord_max.
rewrite -(eq_in_dlet (mu := P0)
  (f := fun omega => completedSemanticBindKernel KL mid (final omega))
  (g := fun omega => dmargin (fun omega2 => tnth omega2 ord_max)
          (completedPythTraceKernelL mid K omega))).
  rewrite -(dlet_dmargin P0 final
    (completedSemanticBindKernel KL mid) z).
  rewrite -(eq_in_dlet
    (mu := completed_output_heap ML)
    (nu := dmargin final P0)
    (f := completedSemanticBindKernel KL mid)
    (g := completedSemanticBindKernel KL mid)).
    exact: (completed_output_heap_bind ML KL mid Hmid z).
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
    =1 completed_output_heap MR ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y,
    dmargin (fun omega => tnth omega ord_max) (K y).2
      =1 completed_output_heap (KR (proj1_sig y))) ->
  \dlet_(omega <- Q0)
    dmargin (fun omega2 => tnth omega2 ord_max)
      (completedPythTraceKernelR mid K omega)
  =1 completed_output_heap (\dlet_(y <- MR) KR y).
Proof.
move=> Hmargin Hmid HK z.
pose final (omega : (ℓ1.+1).-tuple (option (nat * heap))) :=
  tnth omega ord_max.
rewrite -(eq_in_dlet (mu := Q0)
  (f := fun omega => completedSemanticBindKernel KR mid (final omega))
  (g := fun omega => dmargin (fun omega2 => tnth omega2 ord_max)
          (completedPythTraceKernelR mid K omega))).
  rewrite -(dlet_dmargin Q0 final
    (completedSemanticBindKernel KR mid) z).
  rewrite -(eq_in_dlet
    (mu := completed_output_heap MR)
    (nu := dmargin final Q0)
    (f := completedSemanticBindKernel KR mid)
    (g := completedSemanticBindKernel KR mid)).
    exact: (completed_output_heap_bind MR KR mid Hmid z).
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
  completedPythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 completed_output_heap ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 completed_output_heap MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y,
    dmargin (fun omega => tnth omega ord_max) (K y).1
      =1 completed_output_heap (KL (proj1_sig y))) ->
  (forall y,
    dmargin (fun omega => tnth omega ord_max) (K y).2
      =1 completed_output_heap (KR (proj1_sig y))) ->
  dmargin (fun omega => tnth omega ord_max) P
    =1 completed_output_heap (\dlet_(y <- ML) KL y) /\
  dmargin (fun omega => tnth omega ord_max) Q
    =1 completed_output_heap (\dlet_(y <- MR) KR y).
Proof.
move=> [HP HQ] HmarginL0 HmarginR0 HmidL HmidR HKL HKR.
split.
- move=> z.
  rewrite (dmargin_ext (fun omega => tnth omega ord_max)
    P (completedPythTraceBindL ML KL mid P0 K) HP z).
  rewrite /completedPythTraceBindL.
  rewrite (dmargin_dlet_cat_final P0
    (completedPythTraceKernelL mid K) z).
  exact: (completedTraceKernel_bind_final_marginL
    ML KL mid P0 K HmarginL0 HmidL HKL z).
- move=> z.
  rewrite (dmargin_ext (fun omega => tnth omega ord_max)
    Q (completedPythTraceBindR MR KR mid Q0 K) HQ z).
  rewrite /completedPythTraceBindR.
  rewrite (dmargin_dlet_cat_final Q0
    (completedPythTraceKernelR mid K) z).
  exact: (completedTraceKernel_bind_final_marginR
    MR KR mid Q0 K HmarginR0 HmidR HKR z).
Qed.

Lemma completedTraceBind_post
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (option (nat * heap))) / R})
  (K : { y : mid_t * heap | mid y } ->
      completedPythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R}) :
  completedPythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
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
    =1 completed_output_heap ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 completed_output_heap MR ->
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
      =1 completed_output_heap (\dlet_(y <- ML) KL y) /\
    dmargin (fun omega => tnth omega ord_max) Q
      =1 completed_output_heap (\dlet_(y <- MR) KR y) /\
    (forall x, x \in dinsupp (\dlet_(y <- ML) KL y) -> post x) /\
    (forall x, x \in dinsupp (\dlet_(y <- MR) KR y) -> post x).
Proof.
move=> Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hs2 HK.
have [P [Q Hbind]] :=
  completedTraceBind_exists ML MR KL KR mid P0 Q0 K.
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
      =1 completed_output_heap (\dlet_(y <- ML) KL y) /\
    dmargin (fun omega => tnth omega ord_max) Q
      =1 completed_output_heap (\dlet_(y <- MR) KR y).
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
    ML MR KL KR mid post P0 Q0 K P Q Hbind HmidL HmidR).
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
    =1 completed_output_heap ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 completed_output_heap MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall i : 'I_(ℓ2.+1), 0 <= tnth s2 i) ->
  (forall y, mid y ->
    exists (P Q : {distr ((ℓ2.+1).-tuple
        (option (nat * heap))) / R}),
      pythDist P Q s2 /\
      dmargin (fun omega => tnth omega ord_max) P
        =1 completed_output_heap (KL y) /\
      dmargin (fun omega => tnth omega ord_max) Q
        =1 completed_output_heap (KR y) /\
      (forall x, x \in dinsupp (KL y) -> post x) /\
      (forall x, x \in dinsupp (KR y) -> post x)) ->
  exists (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple
      (option (nat * heap))) / R}),
    pythDist P Q (cat_tuple s1 s2) /\
    dmargin (fun omega => tnth omega ord_max) P
      =1 completed_output_heap (\dlet_(y <- ML) KL y) /\
    dmargin (fun omega => tnth omega ord_max) Q
      =1 completed_output_heap (\dlet_(y <- MR) KR y) /\
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
