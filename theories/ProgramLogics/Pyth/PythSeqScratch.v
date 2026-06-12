(* Scratch proof machinery for sequential Pythagorean composition. *)

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
From Mending.LibExtras.MathcompExtras Require Import DistrExtras RealSumExtras
  TupleExtras.
From Mending.Probability.KL Require Import Pyth.
From Mending.ProgramLogics Require Import Ae Hoare.
From Mending.ProgramLogics.Pyth Require Import Core.

Local Open Scope AeNotations.
Local Open Scope HoareNotations.
Local Open Scope PythNotations.

Import PackageNotation.
Import pkg_heap.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope package_scope.
Local Open Scope ring_scope.

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

(* Extracts the Pythagorean distance component from a kernel specification. *)
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

(* Extracts the left final-margin component from a kernel specification. *)
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

(* Extracts the right final-margin component from a kernel specification. *)
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

(* Extracts the left postcondition guarantee from a kernel specification. *)
Lemma pythKernelSpec_postL
  {ℓ : nat}
  {out_t : choice_type}
  (KL KR : {distr (out_t * heap) / R})
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R)
  (W : pythKernelPair (ℓ := ℓ))
  (x : out_t * heap) :
  pythKernelSpec KL KR post s W ->
  x \in dinsupp KL -> post x.
Proof.
by case: W=> P Q /= [_ [_ [_ [Hpost _]]]]; exact: Hpost.
Qed.

(* Extracts the right postcondition guarantee from a kernel specification. *)
Lemma pythKernelSpec_postR
  {ℓ : nat}
  {out_t : choice_type}
  (KL KR : {distr (out_t * heap) / R})
  (post : pred (out_t * heap))
  (s : (ℓ.+1).-tuple R)
  (W : pythKernelPair (ℓ := ℓ))
  (x : out_t * heap) :
  pythKernelSpec KL KR post s W ->
  x \in dinsupp KR -> post x.
Proof.
by case: W=> P Q /= [_ [_ [_ [_ Hpost]]]]; exact: Hpost.
Qed.

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

(* Chooses one certified continuation trace kernel for every valid midpoint. *)
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

(* Packages the left and right composed trace distributions as a witness pair. *)
Lemma traceBind_exists
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

(* Pulls support of a concatenated dlet trace back to a concrete prefix and suffix. *)
Lemma dlet_dunit_cat_dinsupp_preimage
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (omega : (ℓ1.+1 + ℓ2.+1).-tuple A) :
  omega \in dinsupp
    (\dlet_(omega1 <- P0)
     \dlet_(omega2 <- K0 omega1)
       dunit (cat_tuple omega1 omega2)) ->
  exists omega1, exists omega2,
    omega = cat_tuple omega1 omega2 /\
    omega1 \in dinsupp P0 /\
    omega2 \in dinsupp (K0 omega1).
Proof.
move=> Homega.
have [omega1 Homega1 Hinner] := @dinsupp_dlet R _ _ _ _ _ Homega.
have [omega2 Homega2 Hunit] := @dinsupp_dlet R _ _ _ _ _ Hinner.
exists omega1; exists omega2.
split.
  move: Hunit.
  by rewrite dunit1E pnatr_eq0 eqb0 negbK=> /eqP.
by split.
Qed.

(* Builds support of a concatenated dlet trace from supported prefix and suffix traces. *)
Lemma dlet_dunit_cat_dinsupp_image
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (omega1 : (ℓ1.+1).-tuple A)
  (omega2 : (ℓ2.+1).-tuple A) :
  omega1 \in dinsupp P0 ->
  omega2 \in dinsupp (K0 omega1) ->
  cat_tuple omega1 omega2 \in dinsupp
    (\dlet_(omega1 <- P0)
     \dlet_(omega2 <- K0 omega1)
       dunit (cat_tuple omega1 omega2)).
Proof.
move=> Homega1 Homega2.
apply: (@dlet_dinsupp R _ _
  (fun omega1 =>
    \dlet_(omega2 <- K0 omega1) dunit (cat_tuple omega1 omega2))
  P0 omega1 (cat_tuple omega1 omega2) Homega1).
apply: (@dlet_dinsupp R _ _
  (fun omega2 => dunit (cat_tuple omega1 omega2))
  (K0 omega1) omega2 (cat_tuple omega1 omega2) Homega2).
by rewrite dunit1E eqxx oner_neq0.
Qed.

(* Shows concatenating dlet traces preserves absolute continuity componentwise. *)
Lemma dlet_dunit_cat_absolute_continuous
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 Q0 : {distr ((ℓ1.+1).-tuple A) / R})
  (KL KR : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R}) :
  absolute_continuous P0 Q0 ->
  (forall omega1,
    omega1 \in dinsupp P0 -> absolute_continuous (KL omega1) (KR omega1)) ->
  absolute_continuous
    (\dlet_(omega1 <- P0)
     \dlet_(omega2 <- KL omega1)
       dunit (cat_tuple omega1 omega2))
    (\dlet_(omega1 <- Q0)
     \dlet_(omega2 <- KR omega1)
       dunit (cat_tuple omega1 omega2)).
Proof.
move=> Hac0 HacK omega HQomega0.
apply/eqP; apply/negP=> HPomega_nz.
  have HPomega_supp :
    omega \in dinsupp
      (\dlet_(omega1 <- P0)
       \dlet_(omega2 <- KL omega1)
         dunit (cat_tuple omega1 omega2)).
  rewrite in_dinsupp.
  by apply/negP.
have [omega1 [omega2 [Homega [Homega1 Homega2]]]] :=
  dlet_dunit_cat_dinsupp_preimage P0 KL omega HPomega_supp.
have Hqomega1 : omega1 \in dinsupp Q0.
  rewrite in_dinsupp.
  apply/negP=> /eqP HQ0omega1.
  move: Homega1.
  by rewrite in_dinsupp (Hac0 omega1 HQ0omega1) eqxx.
have Hqomega2 : omega2 \in dinsupp (KR omega1).
  rewrite in_dinsupp.
  apply/negP=> /eqP HKRomega2.
  move: Homega2.
  by rewrite in_dinsupp (HacK omega1 Homega1 omega2 HKRomega2) eqxx.
have HQomega_supp :
    cat_tuple omega1 omega2 \in dinsupp
      (\dlet_(omega1 <- Q0)
       \dlet_(omega2 <- KR omega1)
         dunit (cat_tuple omega1 omega2)).
  exact: dlet_dunit_cat_dinsupp_image.
move: HQomega_supp.
by rewrite -Homega in_dinsupp HQomega0 eqxx.
Qed.

(* Extracts nonnegativity of the continuation budget from each chosen kernel. *)
Lemma traceBind_s2_nonneg
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML : {distr (mid_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (i : 'I_(ℓ2.+1)) :
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  0 <= tnth s2 i.
Proof.
move=> Hdist0 HmarginL0 HmidL HK.
case: Hdist0=> _ [_ [HP0mass _]].
have [omega Homega] := dweight1_dinsupp P0 HP0mass.
have Hfinal_supp_P0 :
    tnth omega ord_max \in
      dinsupp (dmargin (fun omega => tnth omega ord_max) P0).
  exact: (dmargin_dinsupp_image P0
    (fun omega => tnth omega ord_max) omega Homega).
have Hfinal_supp_ML :
    tnth omega ord_max \in
      dinsupp (dmargin (@pack_output_heap mid_t) ML).
  rewrite in_dinsupp -HmarginL0.
  by move: Hfinal_supp_P0; rewrite in_dinsupp.
have [y Hy _] :=
  dmargin_dinsupp_preimage ML (@pack_output_heap mid_t)
    (tnth omega ord_max) Hfinal_supp_ML.
have Hmidy : mid y := HmidL y Hy.
case: (HK (exist _ y Hmidy))=> Hs2 _.
exact: Hs2.
Qed.

(* Transfers absolute continuity from decoded midpoints to the chosen trace kernels. *)
Lemma pythTraceKernel_absolute_continuous
  {ℓ1 ℓ2 : nat}
  {mid_t : choice_type}
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (omega : (ℓ1.+1).-tuple (nat * heap)) :
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  absolute_continuous
    (pythTraceKernelL mid K omega)
    (pythTraceKernelR mid K omega).
Proof.
move=> HK.
rewrite /pythTraceKernelL /pythTraceKernelR.
case Hdecode: (decode_output_heap (tnth omega ord_max))=> [y|].
  destruct (@idP (mid y)) as [Hy|Hnot].
    by case: (HK (exist _ y Hy))=> _ [Hac _].
  by move=> x Hx.
by move=> x Hx.
Qed.

(* Shows the composed left trace distribution is absolutely continuous w.r.t. the right one. *)
Lemma traceBind_absolute_continuous
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
Proof.
move=> [HP HQ] Hdist0 _ _ _ _ HK.
case: Hdist0=> _ [Hac0 _].
have Hac_bind :
    absolute_continuous
      (pythTraceBindL ML KL mid P0 K)
      (pythTraceBindR MR KR mid Q0 K).
  rewrite /pythTraceBindL /pythTraceBindR.
  apply: dlet_dunit_cat_absolute_continuous=> // omega1 _.
  exact: (pythTraceKernel_absolute_continuous mid s2 K omega1 HK).
move=> omega HQomega0.
rewrite HP.
apply: Hac_bind.
by rewrite -HQ.
Qed.

(* Computes a prefix event probability through the composed trace dlet. *)
Lemma pr_dlet_cat_prefix_lift_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (p : pred ((ℓ1.+1 + ℓ2.+1).-tuple A))
  (p0 : pred ((ℓ1.+1).-tuple A)) :
  (forall omega1, dweight (K0 omega1) = 1) ->
  (forall omega1 omega2, p (cat_tuple omega1 omega2) = p0 omega1) ->
  \P_[
    \dlet_(omega1 <- P0)
    \dlet_(omega2 <- K0 omega1)
      dunit (cat_tuple omega1 omega2)
  ] p =
  \P_[P0] p0.
Proof.
move=> Hmass Hp.
rewrite pr_dlet.
rewrite [RHS]pr_exp.
apply: expectation_ext=> omega1.
rewrite pr_dlet.
rewrite (expectation_ext (K0 omega1)
  (fun omega2 => \P_[dunit (cat_tuple omega1 omega2)] p)
  (fun _ => if p0 omega1 then 1 else 0)).
  case Hp0: (p0 omega1).
    by rewrite expectation_const // Hmass.
  by rewrite exp0.
move=> omega2.
rewrite pr_dunit Hp.
by case: (p0 omega1).
Qed.

(* Computes prefix conditional probabilities for composed trace distributions. *)
Lemma prc_dlet_cat_prefix_coordinate_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
  (Hi : (i < ℓ1.+1)%N)
  (x : A) :
  (forall omega1, dweight (K0 omega1) = 1) ->
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
move=> Hmass /=.
rewrite /prc.
rewrite (pr_dlet_cat_prefix_lift_eq P0 K0
  (fun omega =>
    (tnth omega i \in pred1 x) && tuple_prefix_eq i a omega)
  (fun omega1 =>
    (tnth omega1 (Ordinal Hi) \in pred1 x) &&
    tuple_prefix_eq (Ordinal Hi)
      (fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))))
      omega1) Hmass).
  rewrite (pr_dlet_cat_prefix_lift_eq P0 K0
    (fun omega => tuple_prefix_eq i a omega)
    (fun omega1 => tuple_prefix_eq (Ordinal Hi)
      (fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))))
      omega1) Hmass) //.
  move=> omega1 omega2.
	  exact: tuple_prefix_eq_cat_prefix.
move=> omega1 omega2.
rewrite (cat_tuple_tnth_prefix_choice omega1 omega2 i Hi).
by rewrite (tuple_prefix_eq_cat_prefix i a Hi omega1 omega2).
Qed.


(* Reduces prefix conditional-coordinate distance to the outer trace distributions. *)
Lemma conditional_coordinate_dlet_cat_prefix_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
  (Hi : (i < ℓ1.+1)%N) :
  (forall omega1, dweight (K0 omega1) = 1) ->
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
move=> Hmass /= x.
rewrite !pr_pred1.
rewrite !pr_dmargin.
rewrite !pr_dcond.
exact: (prc_dlet_cat_prefix_coordinate_eq P0 K0 i a Hi x Hmass).
Qed.

(* Shows the selected left continuation kernel has total weight one. *)
Lemma pythTraceKernelL_dweight1
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (omega : (ℓ1.+1).-tuple (nat * heap)) :
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  dweight (pythTraceKernelL mid K omega) = 1.
Proof.
move=> HK.
rewrite /pythTraceKernelL.
case Hdecode: (decode_output_heap (tnth omega ord_max))=> [y|].
  destruct (@idP (mid y)) as [Hy|Hnot].
    by case: (HK (exist _ y Hy))=> _ [_ [Hmass _]].
  exact: dunit_dweight.
exact: dunit_dweight.
Qed.

(* Shows the selected right continuation kernel has total weight one. *)
Lemma pythTraceKernelR_dweight1
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (omega : (ℓ1.+1).-tuple (nat * heap)) :
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  dweight (pythTraceKernelR mid K omega) = 1.
Proof.
move=> HK.
rewrite /pythTraceKernelR.
case Hdecode: (decode_output_heap (tnth omega ord_max))=> [y|].
  destruct (@idP (mid y)) as [Hy|Hnot].
    by case: (HK (exist _ y Hy))=> _ [_ [_ [Hmass _]]].
  exact: dunit_dweight.
exact: dunit_dweight.
Qed.

(* Shows the composed left trace distribution has total weight one. *)
Lemma traceBind_dweightL
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
Proof.
move=> [HP _] Hdist0 _ _ HK.
case: Hdist0=> _ [_ [HP0mass _]].
rewrite (pr_ext P (pythTraceBindL ML KL mid P0 K) predT HP).
rewrite /pythTraceBindL.
rewrite (pr_dlet_cat_prefix_lift_eq P0 (pythTraceKernelL mid K)
  predT predT
  (fun omega => @pythTraceKernelL_dweight1
    ℓ1 ℓ2 mid_t out_t mid s2 K omega HK));
  last by move=> omega1 omega2.
exact: HP0mass.
Qed.

(* Shows the composed right trace distribution has total weight one. *)
Lemma traceBind_dweightR
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
Proof.
move=> [_ HQ] Hdist0 _ _ HK.
case: Hdist0=> _ [_ [_ [HQ0mass _]]].
rewrite (pr_ext Q (pythTraceBindR MR KR mid Q0 K) predT HQ).
rewrite /pythTraceBindR.
rewrite (pr_dlet_cat_prefix_lift_eq Q0 (pythTraceKernelR mid K)
  predT predT
  (fun omega => @pythTraceKernelR_dweight1
    ℓ1 ℓ2 mid_t out_t mid s2 K omega HK));
  last by move=> omega1 omega2.
exact: HQ0mass.
Qed.

(* Identifies left composed prefix conditionals with the original left trace conditionals. *)
Lemma pythTraceBindL_conditional_coordinate_prefix_eq
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML : {distr (mid_t * heap) / R})
  (KL : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (P0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
  (Hi : (i < ℓ1.+1)%N) :
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
  let a0 : forall j : 'I_(ℓ1.+1), nat * heap :=
    fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
  conditional_coordinate (pythTraceBindL ML KL mid P0 K) i a
    =1 conditional_coordinate P0 i0 a0.
Proof.
move=> HK.
exact: (conditional_coordinate_dlet_cat_prefix_eq
  P0 (pythTraceKernelL mid K) i a Hi
  (fun omega => pythTraceKernelL_dweight1 mid s2 K omega HK)).
Qed.

(* Identifies right composed prefix conditionals with the original right trace conditionals. *)
Lemma pythTraceBindR_conditional_coordinate_prefix_eq
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (MR : {distr (mid_t * heap) / R})
  (KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
  (Hi : (i < ℓ1.+1)%N) :
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
  let a0 : forall j : 'I_(ℓ1.+1), nat * heap :=
    fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
  conditional_coordinate (pythTraceBindR MR KR mid Q0 K) i a
    =1 conditional_coordinate Q0 i0 a0.
Proof.
move=> HK.
exact: (conditional_coordinate_dlet_cat_prefix_eq
  Q0 (pythTraceKernelR mid K) i a Hi
  (fun omega => pythTraceKernelR_dweight1 mid s2 K omega HK)).
Qed.

(* Rewrites the left composed prefix conditional using the original left witness. *)
Lemma traceBind_prefix_condL
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
  (Hi : (i < ℓ1.+1)%N) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
  let a0 : forall j : 'I_(ℓ1.+1), nat * heap :=
    fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
  conditional_coordinate P i a
    =1 conditional_coordinate P0 i0 a0.
Proof.
move=> [HP _] HK /= x.
rewrite (conditional_coordinate_dist_ext P
  (pythTraceBindL ML KL mid P0 K) i a HP x).
exact: (pythTraceBindL_conditional_coordinate_prefix_eq
  ML KL mid s2 P0 K i a Hi HK x).
Qed.

(* Rewrites the right composed prefix conditional using the original right witness. *)
Lemma traceBind_prefix_condR
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
  (Hi : (i < ℓ1.+1)%N) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
  let a0 : forall j : 'I_(ℓ1.+1), nat * heap :=
    fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
  conditional_coordinate Q i a
    =1 conditional_coordinate Q0 i0 a0.
Proof.
move=> [_ HQ] HK /= x.
rewrite (conditional_coordinate_dist_ext Q
  (pythTraceBindR MR KR mid Q0 K) i a HQ x).
exact: (pythTraceBindR_conditional_coordinate_prefix_eq
  MR KR mid s2 Q0 K i a Hi HK x).
Qed.

(* Rewrites prefix conditional-coordinate distance for the composed witness pair. *)
Lemma traceBind_prefix_cond
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
  (Hi : (i < ℓ1.+1)%N) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  let i0 : 'I_(ℓ1.+1) := Ordinal Hi in
  let a0 : forall j : 'I_(ℓ1.+1), nat * heap :=
    fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))) in
  δ_KL (conditional_coordinate P i a)
       (conditional_coordinate Q i a) =
  δ_KL (conditional_coordinate P0 i0 a0)
       (conditional_coordinate Q0 i0 a0).
Proof.
move=> Hbind HK.
apply: kl_ext.
- exact: (traceBind_prefix_condL
    ML MR KL KR mid s2 P0 Q0 K P Q i a Hi Hbind HK).
- exact: (traceBind_prefix_condR
    ML MR KL KR mid s2 P0 Q0 K P Q i a Hi Hbind HK).
Qed.

(* Bounds a composed prefix coordinate using the original Pythagorean prefix witness. *)
Lemma traceBind_prefix_bound_from_P0
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  (i < ℓ1.+1)%N ->
  δ_KL (conditional_coordinate P i a)
       (conditional_coordinate Q i a) <=
    tnth (cat_tuple s1 s2) i.
Proof.
move=> Hbind [_ [_ [_ [_ Hcond0]]]] HK Hi.
pose i0 : 'I_(ℓ1.+1) := Ordinal Hi.
pose a0 : forall j : 'I_(ℓ1.+1), nat * heap :=
  fun j => a (Ordinal (leq_trans (ltn_ord j) (leq_addr _ _))).
rewrite (traceBind_prefix_cond
  ML MR KL KR mid s2 P0 Q0 K P Q i a Hi Hbind HK).
rewrite (cat_tuple_tnth_prefix s1 s2 i Hi).
exact: (Hcond0 i0 a0).
Qed.

(* Proves the Pythagorean coordinate bound for every prefix coordinate. *)
Lemma traceBind_prefix_bound
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  (i < ℓ1.+1)%N ->
  δ_KL (conditional_coordinate P i a)
       (conditional_coordinate Q i a) <=
    tnth (cat_tuple s1 s2) i.
Proof.
move=> Hbind Hdist0 _ _ _ _ HK Hi.
exact: (traceBind_prefix_bound_from_P0
  ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hbind Hdist0
  HK Hi).
Qed.

(* Computes a dlet probability when the outer prefix is fixed. *)
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

(* Relates a fixed-prefix concatenation event to the inner suffix event. *)
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

(* Computes the probability of a full concatenated prefix by conditioning on its prefix part. *)
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

(* Computes suffix-prefix events after fixing the outer trace prefix. *)
Lemma pr_dlet_cat_suffix_prefix_event_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
  (Hi : (ℓ1.+1 <= i)%N)
  (omega1 : (ℓ1.+1).-tuple A) :
  catTuplePrefix a = omega1 ->
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
        (catTupleSuffixIndex i Hi)
        (catTupleSuffixAssignment i Hi a)
        omega2).
Proof.
move=> Hprefix _.
apply: pr_dlet_cat_fixed_prefix_event_eq=> omega1' omega2.
exact: (tuple_prefix_eq_cat_suffix i a Hi omega1 omega1' omega2 Hprefix).
Qed.

(* Computes suffix coordinate events after fixing the outer trace prefix. *)
Lemma pr_dlet_cat_suffix_coordinate_event_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
  (Hi : (ℓ1.+1 <= i)%N)
  (omega1 : (ℓ1.+1).-tuple A)
  (x : A) :
  catTuplePrefix a = omega1 ->
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
      (tnth omega2 (catTupleSuffixIndex i Hi) \in pred1 x) &&
      tuple_prefix_eq
        (catTupleSuffixIndex i Hi)
        (catTupleSuffixAssignment i Hi a)
        omega2).
Proof.
move=> Hprefix _.
apply: pr_dlet_cat_fixed_prefix_event_eq=> omega1' omega2.
rewrite (cat_tuple_tnth_suffix_choice omega1' omega2 i Hi).
rewrite (tuple_prefix_eq_cat_suffix i a Hi omega1 omega1' omega2 Hprefix).
by case: (tnth omega2 (catTupleSuffixIndex i Hi) \in pred1 x);
   case: (omega1' == omega1);
   case: (tuple_prefix_eq (catTupleSuffixIndex i Hi)
     (catTupleSuffixAssignment i Hi a) omega2).
Qed.

(* Computes suffix conditional probabilities for the inner trace kernel. *)
Lemma prc_dlet_cat_suffix_coordinate_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
  (Hi : (ℓ1.+1 <= i)%N)
  (omega1 : (ℓ1.+1).-tuple A)
  (x : A) :
  catTuplePrefix a = omega1 ->
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
        (catTupleSuffixIndex i Hi)
        (catTupleSuffixAssignment i Hi a)
        omega2
  ] [pred omega2 |
    tnth omega2 (catTupleSuffixIndex i Hi) \in pred1 x].
Proof.
move=> Hprefix Hpos.
rewrite /prc.
rewrite (pr_dlet_cat_suffix_coordinate_event_eq
  P0 K0 i a Hi omega1 x Hprefix Hpos).
rewrite (pr_dlet_cat_suffix_prefix_event_eq
  P0 K0 i a Hi omega1 Hprefix Hpos).
exact: divr_cancel_left_pos.
Qed.

(* Reduces suffix conditional-coordinate distance to the selected continuation kernels. *)
Lemma conditional_coordinate_dlet_cat_suffix_eq
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), A)
  (Hi : (ℓ1.+1 <= i)%N)
  (omega1 : (ℓ1.+1).-tuple A) :
  catTuplePrefix a = omega1 ->
  0 < P0 omega1 ->
  conditional_coordinate
    (\dlet_(omega1 <- P0)
     \dlet_(omega2 <- K0 omega1)
       dunit (cat_tuple omega1 omega2))
    i a
    =1 conditional_coordinate (K0 omega1)
        (catTupleSuffixIndex i Hi)
        (catTupleSuffixAssignment i Hi a).
Proof.
move=> Hprefix Hpos x.
rewrite !pr_pred1.
rewrite !pr_dmargin.
rewrite !pr_dcond.
exact: (prc_dlet_cat_suffix_coordinate_eq
  P0 K0 i a Hi omega1 x Hprefix Hpos).
Qed.

(* Collapses conditional-coordinate distance when both conditioning prefixes have zero mass. *)
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

(* Bounds a suffix coordinate when the composed prefix has zero left mass. *)
Lemma traceBind_suffix_bound_zero_prefix
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
  (Hi : (ℓ1.+1 <= i)%N) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  P0 (catTuplePrefix a) = 0 ->
  δ_KL (conditional_coordinate P i a)
       (conditional_coordinate Q i a) <=
    tnth s2 (catTupleSuffixIndex i Hi).
Proof.
move=> Hbind Hdist0 HmarginL0 _ HmidL _ HK HP0z.
have Hs2 : 0 <= tnth s2 (catTupleSuffixIndex i Hi) :=
  traceBind_s2_nonneg ML mid s1 s2 P0 Q0 K
    (catTupleSuffixIndex i Hi) Hdist0 HmarginL0 HmidL HK.
have HPprefix0 :
    \P_[P] (fun omega => tuple_prefix_eq i a omega) = 0.
  case: Hbind=> HP _.
  rewrite (pr_ext P (pythTraceBindL ML KL mid P0 K)
    (fun omega => tuple_prefix_eq i a omega) HP).
  rewrite (pr_dlet_cat_fixed_prefix_event_eq
    P0 (pythTraceKernelL mid K) (catTuplePrefix a)
    (fun omega => tuple_prefix_eq i a omega)
    (fun omega2 =>
      tuple_prefix_eq
        (catTupleSuffixIndex i Hi)
        (catTupleSuffixAssignment i Hi a)
        omega2)).
    by rewrite HP0z mul0r.
  move=> omega1' omega2.
  exact: (tuple_prefix_eq_cat_suffix i a Hi
    (catTuplePrefix a) omega1' omega2 erefl).
rewrite (kl_left_dnull
  (conditional_coordinate P i a)
  (conditional_coordinate Q i a)
  (conditional_coordinate_zero_prefix P i a HPprefix0)).
exact: Hs2.
Qed.

(* Selects the left continuation kernel when the decoded final prefix state satisfies mid. *)
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

(* Selects the right continuation kernel when the decoded final prefix state satisfies mid. *)
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

(* Rewrites left suffix conditionals to the chosen kernel at a valid midpoint. *)
Lemma traceBind_suffix_condL_valid_mid
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
  (Hi : (ℓ1.+1 <= i)%N)
  (y : { y : mid_t * heap | mid y }) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  @decode_output_heap mid_t
    (tnth (catTuplePrefix a) ord_max) =
    Some (proj1_sig y) ->
  0 < P0 (catTuplePrefix a) ->
  conditional_coordinate P i a
    =1 conditional_coordinate (K y).1
        (catTupleSuffixIndex i Hi)
        (catTupleSuffixAssignment i Hi a).
Proof.
move=> [HP _] _ _ _ _ _ Hy Hpos x.
rewrite (conditional_coordinate_dist_ext P
  (pythTraceBindL ML KL mid P0 K) i a HP x).
pose omega1 := catTuplePrefix a.
rewrite (conditional_coordinate_dlet_cat_suffix_eq
  P0 (pythTraceKernelL mid K) i a Hi omega1 erefl Hpos x).
rewrite (pythTraceKernelL_valid_mid mid K omega1 y Hy).
by [].
Qed.

(* Rewrites right suffix conditionals to the chosen kernel at a valid midpoint. *)
Lemma traceBind_suffix_condR_valid_mid
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
  (Hi : (ℓ1.+1 <= i)%N)
  (y : { y : mid_t * heap | mid y }) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  @decode_output_heap mid_t
    (tnth (catTuplePrefix a) ord_max) =
    Some (proj1_sig y) ->
  0 < Q0 (catTuplePrefix a) ->
  conditional_coordinate Q i a
    =1 conditional_coordinate (K y).2
        (catTupleSuffixIndex i Hi)
        (catTupleSuffixAssignment i Hi a).
Proof.
move=> [_ HQ] _ _ _ _ _ Hy Hpos x.
rewrite (conditional_coordinate_dist_ext Q
  (pythTraceBindR MR KR mid Q0 K) i a HQ x).
pose omega1 := catTuplePrefix a.
rewrite (conditional_coordinate_dlet_cat_suffix_eq
  Q0 (pythTraceKernelR mid K) i a Hi omega1 erefl Hpos x).
rewrite (pythTraceKernelR_valid_mid mid K omega1 y Hy).
by [].
Qed.

(* Reduces suffix conditional-coordinate distance to the kernel distance at a valid midpoint. *)
Lemma traceBind_suffix_cond_valid_mid
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
  (Hi : (ℓ1.+1 <= i)%N)
  (y : { y : mid_t * heap | mid y }) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  @decode_output_heap mid_t
    (tnth (catTuplePrefix a) ord_max) =
    Some (proj1_sig y) ->
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
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hy HPpos HQpos.
apply: kl_ext.
- exact: (traceBind_suffix_condL_valid_mid
  ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi y
  Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hy HPpos).
- exact: (traceBind_suffix_condR_valid_mid
  ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi y
  Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hy HQpos).
Qed.

(* Bounds a suffix coordinate using the selected kernel's Pythagorean condition. *)
Lemma traceBind_suffix_bound_valid_mid
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
  (Hi : (ℓ1.+1 <= i)%N)
  (y : { y : mid_t * heap | mid y }) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  @decode_output_heap mid_t
    (tnth (catTuplePrefix a) ord_max) =
    Some (proj1_sig y) ->
  δ_KL (conditional_coordinate P i a)
       (conditional_coordinate Q i a) <=
    tnth s2 (catTupleSuffixIndex i Hi).
Proof.
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK Hy.
move: Hdist0=> [Hs1 [Hac0 [HP0mass [HQ0mass Hcond0]]]].
have Hdist0 : pythDist P0 Q0 s1.
  by split; first exact: Hs1; split; first exact: Hac0;
     split; first exact: HP0mass; split; first exact: HQ0mass.
case HP0z: (P0 (catTuplePrefix a) == 0).
  exact: (traceBind_suffix_bound_zero_prefix
    ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi
    Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK
    (eqP HP0z)).
have HP0pos : 0 < P0 (catTuplePrefix a).
  by rewrite lt_def ge0_mu HP0z.
have HQ0pos : 0 < Q0 (catTuplePrefix a).
  exact: (absolute_continuous_positive P0 Q0 _ Hac0 HP0pos).
rewrite (traceBind_suffix_cond_valid_mid
  ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi y
  Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR Hy
  HP0pos HQ0pos).
case: (HK y)=> _ [_ [_ [_ Hcond]]].
exact: (Hcond (catTupleSuffixIndex i Hi)
  (catTupleSuffixAssignment i Hi a)).
Qed.

(* Handles suffix coordinates when the prefix final state does not decode. *)
Lemma traceBind_suffix_bound_decode_none
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
  (Hi : (ℓ1.+1 <= i)%N) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  @decode_output_heap mid_t
    (tnth (catTuplePrefix a) ord_max) = None ->
  δ_KL (conditional_coordinate P i a)
       (conditional_coordinate Q i a) <=
    tnth s2 (catTupleSuffixIndex i Hi).
Proof.
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK Hdecode_none.
have HP0z : P0 (catTuplePrefix a) = 0.
  case HP0z: (P0 (catTuplePrefix a) == 0).
    exact/eqP.
  have Hprefix_supp :
      catTuplePrefix a \in dinsupp P0.
    by rewrite in_dinsupp HP0z.
  have Hfinal_supp_P0 :
      tnth (catTuplePrefix a) ord_max \in
        dinsupp (dmargin (fun omega => tnth omega ord_max) P0).
    exact: (dmargin_dinsupp_image P0
      (fun omega => tnth omega ord_max) _ Hprefix_supp).
  have Hfinal_supp_ML :
      tnth (catTuplePrefix a) ord_max \in
        dinsupp (dmargin (@pack_output_heap mid_t) ML).
    rewrite in_dinsupp -HmarginL0.
    by move: Hfinal_supp_P0; rewrite in_dinsupp.
  have [z Hz Hpack] :=
    dmargin_dinsupp_preimage ML (@pack_output_heap mid_t)
      (tnth (catTuplePrefix a) ord_max) Hfinal_supp_ML.
  move: Hdecode_none.
  by rewrite -Hpack decode_output_heap_pack.
exact: (traceBind_suffix_bound_zero_prefix
  ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi
  Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK HP0z).
Qed.

(* Handles suffix coordinates when the decoded prefix final state violates mid. *)
Lemma traceBind_suffix_bound_not_mid
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
  (Hi : (ℓ1.+1 <= i)%N)
  (y : mid_t * heap) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  @decode_output_heap mid_t
    (tnth (catTuplePrefix a) ord_max) = Some y ->
  ~~ mid y ->
  δ_KL (conditional_coordinate P i a)
       (conditional_coordinate Q i a) <=
    tnth s2 (catTupleSuffixIndex i Hi).
Proof.
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK Hdecode Hnot_mid.
have HP0z : P0 (catTuplePrefix a) = 0.
  case HP0z: (P0 (catTuplePrefix a) == 0).
    exact/eqP.
  have Hprefix_supp :
      catTuplePrefix a \in dinsupp P0.
    by rewrite in_dinsupp HP0z.
  have Hfinal_supp_P0 :
      tnth (catTuplePrefix a) ord_max \in
        dinsupp (dmargin (fun omega => tnth omega ord_max) P0).
    exact: (dmargin_dinsupp_image P0
      (fun omega => tnth omega ord_max) _ Hprefix_supp).
  have Hfinal_supp_ML :
      tnth (catTuplePrefix a) ord_max \in
        dinsupp (dmargin (@pack_output_heap mid_t) ML).
    rewrite in_dinsupp -HmarginL0.
    by move: Hfinal_supp_P0; rewrite in_dinsupp.
  have [z Hz Hpack] :=
    dmargin_dinsupp_preimage ML (@pack_output_heap mid_t)
      (tnth (catTuplePrefix a) ord_max) Hfinal_supp_ML.
  have Hdecode_z :
      @decode_output_heap mid_t
        (tnth (catTuplePrefix a) ord_max) = Some z.
    by rewrite -Hpack decode_output_heap_pack.
  have Hyz : y = z by move: Hdecode; rewrite Hdecode_z=> -[].
  move: Hnot_mid.
  rewrite Hyz.
  by rewrite (HmidL z Hz).
exact: (traceBind_suffix_bound_zero_prefix
  ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi
  Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK HP0z).
Qed.

(* Dispatches all suffix cases by decoding the prefix final state. *)
Lemma traceBind_suffix_bound_from_kernel
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap)
  (Hi : (ℓ1.+1 <= i)%N) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  δ_KL (conditional_coordinate P i a)
       (conditional_coordinate Q i a) <=
    tnth s2 (Ordinal (cat_tuple_suffix_bound i Hi)).
Proof.
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK.
case Hdecode:
    (@decode_output_heap mid_t
      (tnth (catTuplePrefix a) ord_max))=> [y|].
  case Hmidy: (mid y).
  - have Hy : mid y by rewrite Hmidy.
    exact: (traceBind_suffix_bound_valid_mid
      ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi (exist _ y Hy)
      Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK Hdecode).
  - exact: (traceBind_suffix_bound_not_mid
      ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi y
      Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK
      Hdecode (negbT Hmidy)).
- exact: (traceBind_suffix_bound_decode_none
    ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi
    Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK Hdecode).
Qed.


(* Lifts the suffix bound from chosen kernels to extensionally equal trace witnesses. *)
Lemma traceBind_suffix_bound_from_K
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  (ℓ1.+1 <= i)%N ->
  δ_KL (conditional_coordinate P i a)
       (conditional_coordinate Q i a) <=
    tnth (cat_tuple s1 s2) i.
Proof.
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK Hi.
rewrite (cat_tuple_tnth_suffix s1 s2 i Hi).
exact: (traceBind_suffix_bound_from_kernel
  ML MR KL KR mid s1 s2 P0 Q0 K P Q i a Hi
  Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK).
Qed.

(* Proves the Pythagorean coordinate bound for every suffix coordinate. *)
Lemma traceBind_suffix_bound
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  (ℓ1.+1 <= i)%N ->
  δ_KL (conditional_coordinate P i a)
       (conditional_coordinate Q i a) <=
    tnth (cat_tuple s1 s2) i.
Proof.
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK Hi.
exact: (traceBind_suffix_bound_from_K
  ML MR KL KR mid s1 s2 P0 Q0 K P Q i a
  Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK Hi).
Qed.

(* Combines prefix and suffix coordinate bounds for the composed trace witness. *)
Lemma traceBind_cond_bound
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (ML MR : {distr (mid_t * heap) / R})
  (KL KR : mid_t * heap -> {distr (out_t * heap) / R})
  (mid : pred (mid_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R)
  (P0 Q0 : {distr ((ℓ1.+1).-tuple (nat * heap)) / R})
  (K : { y : mid_t * heap | mid y } -> pythKernelPair (ℓ := ℓ2))
  (P Q : {distr ((ℓ1.+1 + ℓ2.+1).-tuple (nat * heap)) / R})
  (i : 'I_(ℓ1.+1 + ℓ2.+1))
  (a : forall j : 'I_(ℓ1.+1 + ℓ2.+1), nat * heap) :
  pythTraceBindPair ML MR KL KR mid P0 Q0 K P Q ->
  pythDist P0 Q0 s1 ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin (@pack_output_heap mid_t) ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin (@pack_output_heap mid_t) MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, pythDist (K y).1 (K y).2 s2) ->
  δ_KL (conditional_coordinate P i a)
       (conditional_coordinate Q i a) <=
    tnth (cat_tuple s1 s2) i.
Proof.
move=> Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK.
case: (ltnP i ℓ1.+1)=> Hi.
- exact: (traceBind_prefix_bound
    ML MR KL KR mid s1 s2 P0 Q0 K P Q i a
    Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK Hi).
- exact: (traceBind_suffix_bound
    ML MR KL KR mid s1 s2 P0 Q0 K P Q i a
    Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK Hi).
Qed.

(* Assembles the full Pythagorean distance proof for the composed trace witness. *)
Lemma traceBind_pythDist
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
  fun i => traceBind_s2_nonneg ML mid s1 s2 P0 Q0 K i
    Hdist0 HmarginL0 HmidL HK.
split.
- move=> i.
  apply: (cat_tuple_nonneg s1 s2 i).
  + exact: Hs1.
  + exact: Hs2.
split.
- exact: (traceBind_absolute_continuous
    ML MR KL KR mid s1 s2 P0 Q0 K P Q
    Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK).
split.
- exact: (traceBind_dweightL
    ML MR KL KR mid s1 s2 P0 Q0 K P Q
    Hbind Hdist0 HmarginL0 HmidL HK).
split.
- exact: (traceBind_dweightR
    ML MR KL KR mid s1 s2 P0 Q0 K P Q
    Hbind Hdist0 HmarginR0 HmidR HK).
- move=> i a.
  exact: (traceBind_cond_bound
    ML MR KL KR mid s1 s2 P0 Q0 K P Q i a
    Hbind Hdist0 HmarginL0 HmarginR0 HmidL HmidR HK).
Qed.

Lemma cat_tuple_tnth_ord_max_suffix
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (omega1 : (ℓ1.+1).-tuple A)
  (omega2 : (ℓ2.+1).-tuple A) :
  tnth (cat_tuple omega1 omega2) ord_max = tnth omega2 ord_max.
Proof.
have Hi : (ℓ1.+1 <= (ord_max : 'I_(ℓ1.+1 + ℓ2.+1)))%N.
  rewrite /ord_max /=.
  by rewrite -{1}(addn0 ℓ1) ltn_add2l.
rewrite (cat_tuple_tnth_suffix_choice omega1 omega2 ord_max Hi).
apply: congr1.
apply: val_inj.
rewrite /ord_max /=.
change ((ℓ1 + ℓ2.+1 - ℓ1.+1)%N = ℓ2).
by rewrite subnS addnC addnK.
Qed.

(* Pushes the final-coordinate margin of a concatenated trace through the inner dlet. *)
Lemma dmargin_dlet_cat_final
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 : {distr ((ℓ1.+1).-tuple A) / R})
  (K0 : (ℓ1.+1).-tuple A -> {distr ((ℓ2.+1).-tuple A) / R}) :
  dmargin (fun omega => tnth omega ord_max)
    (\dlet_(omega1 <- P0)
     \dlet_(omega2 <- K0 omega1)
       dunit (cat_tuple omega1 omega2))
  =1
  \dlet_(omega1 <- P0)
    dmargin (fun omega2 => tnth omega2 ord_max) (K0 omega1).
Proof.
move=> z.
rewrite dmargin_dlet.
apply: eq_in_dlet=> // omega1 _ z1.
rewrite dmargin_dlet.
apply: eq_in_dlet=> // omega2 _ z2.
rewrite dmargin_dunit.
by rewrite cat_tuple_tnth_ord_max_suffix.
Qed.

(* Computes the left continuation kernel's final margin after decoding valid midpoints. *)
Lemma pythTraceKernelL_bind_final_margin
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
  \dlet_(omega <- P0)
    dmargin (fun omega2 => tnth omega2 ord_max)
      (pythTraceKernelL mid K omega)
  =1 dmargin (@pack_output_heap out_t) (\dlet_(y <- ML) KL y).
Proof.
move=> Hmargin Hmid HK z.
pose final (omega : (ℓ1.+1).-tuple (nat * heap)) := tnth omega ord_max.
pose H (x : nat * heap) : {distr (nat * heap) / R} :=
  match @decode_output_heap mid_t x with
  | Some y =>
      match @idP (mid y) with
      | ReflectT Hy => dmargin (fun omega2 => tnth omega2 ord_max) (K (exist _ y Hy)).1
      | ReflectF _ => dmargin (fun omega2 => tnth omega2 ord_max)
          (dunit (default_pyth_trace (n := ℓ2.+1)))
      end
  | None => dmargin (fun omega2 => tnth omega2 ord_max)
      (dunit (default_pyth_trace (n := ℓ2.+1)))
  end.
rewrite -(eq_in_dlet (mu := P0)
  (f := fun omega : (ℓ1.+1).-tuple (nat * heap) => H (final omega))
  (g := fun omega => dmargin (fun omega2 => tnth omega2 ord_max)
          (pythTraceKernelL mid K omega))).
  rewrite -(dlet_dmargin P0 final H z).
  rewrite -(eq_in_dlet (mu := dmargin (@pack_output_heap mid_t) ML)
    (nu := dmargin final P0) (f := H) (g := H)).
    rewrite (dlet_dmargin ML (@pack_output_heap mid_t) H z).
    rewrite dmargin_dlet.
    apply: eq_in_dlet=> // y Hy z'.
    rewrite /H decode_output_heap_pack.
    destruct (@idP (mid y)) as [Hymid|Hymid].
      by rewrite (HK (exist _ y Hymid)).
    by case: Hymid; exact: (Hmid y Hy).
  - by [].
  - by move=> x; rewrite -Hmargin.
- move=> omega Homega z'.
  rewrite /H /pythTraceKernelL /final.
  case: (decode_output_heap (tnth omega ord_max))=> [y|] //.
  by destruct (@idP (mid y)).
- by [].
Qed.

(* Computes the right continuation kernel's final margin after decoding valid midpoints. *)
Lemma pythTraceKernelR_bind_final_margin
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
  \dlet_(omega <- Q0)
    dmargin (fun omega2 => tnth omega2 ord_max)
      (pythTraceKernelR mid K omega)
  =1 dmargin (@pack_output_heap out_t) (\dlet_(y <- MR) KR y).
Proof.
move=> Hmargin Hmid HK z.
pose final (omega : (ℓ1.+1).-tuple (nat * heap)) := tnth omega ord_max.
pose H (x : nat * heap) : {distr (nat * heap) / R} :=
  match @decode_output_heap mid_t x with
  | Some y =>
      match @idP (mid y) with
      | ReflectT Hy => dmargin (fun omega2 => tnth omega2 ord_max) (K (exist _ y Hy)).2
      | ReflectF _ => dmargin (fun omega2 => tnth omega2 ord_max)
          (dunit (default_pyth_trace (n := ℓ2.+1)))
      end
  | None => dmargin (fun omega2 => tnth omega2 ord_max)
      (dunit (default_pyth_trace (n := ℓ2.+1)))
  end.
rewrite -(eq_in_dlet (mu := Q0)
  (f := fun omega : (ℓ1.+1).-tuple (nat * heap) => H (final omega))
  (g := fun omega => dmargin (fun omega2 => tnth omega2 ord_max)
          (pythTraceKernelR mid K omega))).
  rewrite -(dlet_dmargin Q0 final H z).
  rewrite -(eq_in_dlet (mu := dmargin (@pack_output_heap mid_t) MR)
    (nu := dmargin final Q0) (f := H) (g := H)).
    rewrite (dlet_dmargin MR (@pack_output_heap mid_t) H z).
    rewrite dmargin_dlet.
    apply: eq_in_dlet=> // y Hy z'.
    rewrite /H decode_output_heap_pack.
    destruct (@idP (mid y)) as [Hymid|Hymid].
      by rewrite (HK (exist _ y Hymid)).
    by case: Hymid; exact: (Hmid y Hy).
  - by [].
  - by move=> x; rewrite -Hmargin.
- move=> omega Homega z'.
  rewrite /H /pythTraceKernelR /final.
  case: (decode_output_heap (tnth omega ord_max))=> [y|] //.
  by destruct (@idP (mid y)).
- by [].
Qed.

(* Identifies the final margin of the composed left trace with the semantic left bind. *)
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
Proof.
move=> Hmargin Hmid HK z.
rewrite /pythTraceBindL.
rewrite (dmargin_dlet_cat_final P0 (pythTraceKernelL mid K) z).
exact: (pythTraceKernelL_bind_final_margin ML KL mid P0 K
  Hmargin Hmid HK z).
Qed.

(* Identifies the final margin of the composed right trace with the semantic right bind. *)
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
Proof.
move=> Hmargin Hmid HK z.
rewrite /pythTraceBindR.
rewrite (dmargin_dlet_cat_final Q0 (pythTraceKernelR mid K) z).
exact: (pythTraceKernelR_bind_final_margin MR KR mid Q0 K
  Hmargin Hmid HK z).
Qed.

(* Proves both final-margin obligations for the composed trace witness. *)
Lemma traceBind_final_margins
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

(* Propagates the postcondition through the semantic continuation binds. *)
Lemma traceBind_post
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

(* Builds a composed trace witness from an existing prefix witness and chosen kernels. *)
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
  traceBind_exists ML MR KL KR mid P0 Q0 K.
exists P, Q.
have Hdist :
    pythDist P Q (cat_tuple s1 s2).
  apply: (traceBind_pythDist
    ML MR KL KR mid s1 s2 P0 Q0 K P Q Hbind
    Hdist0 HmarginL0 HmarginR0 HmidL HmidR).
  move=> y.
  exact: (pythKernelSpec_dist _ _ _ _ _ (HK y)).
have [HmarginL HmarginR] :
    dmargin (fun omega => tnth omega ord_max) P
      =1 dmargin (@pack_output_heap out_t) (\dlet_(y <- ML) KL y) /\
    dmargin (fun omega => tnth omega ord_max) Q
      =1 dmargin (@pack_output_heap out_t) (\dlet_(y <- MR) KR y).
  apply: (traceBind_final_margins
    ML MR KL KR mid P0 Q0 K P Q Hbind
    HmarginL0 HmarginR0 HmidL HmidR).
  - move=> y.
    exact: (pythKernelSpec_marginL _ _ _ _ _ (HK y)).
  - move=> y.
    exact: (pythKernelSpec_marginR _ _ _ _ _ (HK y)).
have [HpostL HpostR] :
    (forall x, x \in dinsupp (\dlet_(y <- ML) KL y) -> post x) /\
    (forall x, x \in dinsupp (\dlet_(y <- MR) KR y) -> post x).
  apply: (traceBind_post
    ML MR KL KR mid post P0 Q0 K P Q Hbind HmidL HmidR).
  - move=> y.
    move=> x.
    exact: (pythKernelSpec_postL _ _ _ _ _ x (HK y)).
  - move=> y.
    move=> x.
    exact: (pythKernelSpec_postR _ _ _ _ _ x (HK y)).
split; first exact: Hdist.
split; first exact: HmarginL.
split; first exact: HmarginR.
by split.
Qed.

(* Chooses the continuation kernels and exposes the composed Pythagorean bind witness. *)
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
