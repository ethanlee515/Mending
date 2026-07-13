(* Probability-side encoding of outputs paired with heaps. *)

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

From Mending.LibExtras.MathcompExtras Require Import DistrExtras RealSumExtras.
From Mending.Probability Require Import Ae.

Import PackageNotation.
Import pkg_heap.
Import GRing.Theory Num.Theory Order.Theory.

Section OutputHeap.

Context {R : realType}.

Definition pack_output_heap {out_t : choice_type}
    (out : out_t * heap) : (nat * heap)%type :=
  (pickle out.1, out.2).

Definition decode_output_heap {out_t : choice_type}
    (x : nat * heap) : option (out_t * heap) :=
  match unpickle x.1 with
  | Some y => Some (y, x.2)
  | None => None
  end.

Lemma decode_output_heap_pack {out_t : choice_type} (x : out_t * heap) :
  decode_output_heap (pack_output_heap x) = Some x.
Proof. by case: x=> y mem; rewrite /decode_output_heap /pack_output_heap pickleK. Qed.

Definition canonical_decode_output_heap {out_t : choice_type}
    (x : nat * heap) : option (out_t * heap) :=
  match decode_output_heap x with
  | Some y => if pack_output_heap y == x then Some y else None
  | None => None
  end.

Lemma canonical_decode_output_heap_pack {out_t : choice_type}
    (x : out_t * heap) :
  canonical_decode_output_heap (pack_output_heap x) = Some x.
Proof.
by rewrite /canonical_decode_output_heap decode_output_heap_pack eqxx.
Qed.

Lemma canonical_decode_output_heapK {out_t : choice_type}
    (x : nat * heap) (y : out_t * heap) :
  canonical_decode_output_heap x = Some y -> pack_output_heap y = x.
Proof.
rewrite /canonical_decode_output_heap.
case: (decode_output_heap x)=> [z|] //=.
case Hpack: (pack_output_heap z == x)=> //=.
case=> <-.
exact/eqP.
Qed.

Lemma pack_output_heap_inj {out_t : choice_type} :
  injective (@pack_output_heap out_t).
Proof.
case=> x mem [y mem'] /=.
rewrite /pack_output_heap /=.
case=> Hpickle Hmem.
have -> : x = y by exact: (pcan_inj pickleK Hpickle).
by rewrite Hmem.
Qed.

Lemma dmargin_pack_output_heapE
    {out_t : choice_type} (P : {distr (out_t * heap) / R})
    (x : nat * heap) :
  dmargin (@pack_output_heap out_t) P x =
    match canonical_decode_output_heap x with
    | Some y => P y
    | None => 0
    end.
Proof.
rewrite dmargin_psumE.
case Hdecode: (canonical_decode_output_heap x)=> [y|].
- rewrite (psum_finseq (r := [:: y])).
  + rewrite big_seq1.
    have -> : pack_output_heap y == x.
      by apply/eqP; exact: canonical_decode_output_heapK Hdecode.
    by rewrite mul1r ger0_norm ?ge0_mu.
  + by [].
  move=> z.
  rewrite !inE.
  case Hpack: (pack_output_heap z == x); last by rewrite mul0r eqxx.
  move/eqP: Hpack=> Hpack _.
  have Hz : z = y.
    have Hy : pack_output_heap y = x :=
      canonical_decode_output_heapK x y Hdecode.
    apply: pack_output_heap_inj.
    by rewrite Hpack -Hy.
  by rewrite Hz eqxx.
- apply/psum_eq0=> z.
  case Hpack: (pack_output_heap z == x); last by rewrite mul0r.
  move/eqP: Hpack=> Hpack.
  move: Hdecode.
  by rewrite -Hpack canonical_decode_output_heap_pack.
Qed.

Lemma dlet_dmargin_pack_output_heap
    {out_t : choice_type} {U : choiceType}
    (P : {distr (out_t * heap) / R})
    (K : (nat * heap)%type -> {distr U / R}) z :
  (\dlet_(packed <- dmargin (@pack_output_heap out_t) P) K packed) z =
  (\dlet_(x <- P) K (pack_output_heap x)) z.
Proof.
rewrite !dletE.
pose Img : pred (nat * heap)%type :=
  fun packed => @canonical_decode_output_heap out_t packed != None.
rewrite (@reindex_psum_onto R (nat * heap)%type (out_t * heap)%type
  (fun packed => dmargin (@pack_output_heap out_t) P packed * K packed z)
  Img (@pack_output_heap out_t) (@canonical_decode_output_heap out_t)).
- apply/eq_psum=> x.
  by rewrite dmargin_pack_output_heapE canonical_decode_output_heap_pack.
- move=> packed Hnz.
  case Hdecode: (@canonical_decode_output_heap out_t packed)=> [x|].
    change ((@canonical_decode_output_heap out_t packed != None) = true).
    by rewrite Hdecode.
  have Hmargin0 : dmargin (@pack_output_heap out_t) P packed = 0.
    by rewrite dmargin_pack_output_heapE Hdecode.
  have Hzero :
      dmargin (@pack_output_heap out_t) P packed * K packed z = 0.
    by rewrite Hmargin0 mul0r.
  by rewrite Hzero eqxx in Hnz.
- move=> packed Himg.
  case Hdecode: (@canonical_decode_output_heap out_t packed)=> [x|].
  + by rewrite /= (canonical_decode_output_heapK packed x Hdecode).
  + move: Himg.
    change ((@canonical_decode_output_heap out_t packed != None) = true ->
      None = Some packed).
    by rewrite Hdecode.
- move=> x Himg.
  exact: canonical_decode_output_heap_pack.
Qed.

Lemma dmargin_dlet_pack_output_heap
    {T : choiceType} {out_t : choice_type}
    (P : {distr T / R})
    (K : T -> {distr (out_t * heap) / R}) packed :
  dmargin (@pack_output_heap out_t) (\dlet_(x <- P) K x) packed =
  (\dlet_(x <- P) dmargin (@pack_output_heap out_t) (K x)) packed.
Proof.
rewrite dmargin_pack_output_heapE.
case Hdecode: (@canonical_decode_output_heap out_t packed)=> [y|].
- rewrite !dletE.
  apply/eq_psum=> x.
  by rewrite dmargin_pack_output_heapE Hdecode.
- rewrite dletE.
  rewrite (eq_psum (F2 := fun _ : T => 0)).
    by rewrite psum0.
  move=> x.
  by rewrite dmargin_pack_output_heapE Hdecode mulr0.
Qed.

Lemma total_variation_pack_output_heap
    {out_t : choice_type} (P Q : {distr (out_t * heap) / R}) :
  total_variation P Q =
  total_variation (dmargin (@pack_output_heap out_t) P)
                  (dmargin (@pack_output_heap out_t) Q).
Proof.
rewrite /total_variation.
congr (_ * _).
rewrite -!psum_sum; try by move=> x; exact: normr_ge0.
pose S := fun x =>
    `|dmargin (@pack_output_heap out_t) P x -
      dmargin (@pack_output_heap out_t) Q x|.
pose Img : pred (nat * heap)%type :=
  [pred x | @canonical_decode_output_heap out_t x != None].
rewrite (@reindex_psum_onto R (nat * heap)%type (out_t * heap)%type
  S Img (@pack_output_heap out_t) (@canonical_decode_output_heap out_t)).
- apply/eq_psum=> x.
  by rewrite /S !dmargin_pack_output_heapE canonical_decode_output_heap_pack.
- move=> x Hx.
  rewrite /Img inE.
  case Hdecode: (@canonical_decode_output_heap out_t x)=> [y|] //=.
  move: Hx.
  by rewrite /S !dmargin_pack_output_heapE Hdecode subrr normr0 eqxx.
- move=> x.
  rewrite inE.
  case Hdecode: (canonical_decode_output_heap x)=> [y|] //= _.
  by rewrite (canonical_decode_output_heapK x y Hdecode).
- move=> x _.
  by rewrite canonical_decode_output_heap_pack.
Qed.

Definition complete_output_heap {out_t : choice_type}
    (out : {distr (out_t * heap) / R}) :
    {distr (option (nat * heap)) / R} :=
  complete (dmargin (@pack_output_heap out_t) out).

Lemma total_variation_complete_output_heap
  {out_t : choice_type} (P Q : {distr (out_t * heap) / R}) :
  total_variation (complete P) (complete Q) =
  total_variation (complete_output_heap P) (complete_output_heap Q).
Proof.
rewrite /complete_output_heap /total_variation.
set P' := dmargin _ P.
set Q' := dmargin _ Q.
congr (_ * _).
rewrite -!psum_sum; try by move=> x; exact: normr_ge0.
pose S := fun x : option (out_t * heap) =>
    `|complete P x - complete Q x|.
pose S' := fun x : option (nat * heap) =>
    `|complete P' x - complete Q' x|.
have HSnonneg : forall x, 0 <= S x by move=> x; exact: normr_ge0.
have HSsumm : summable S.
  apply/summable_abs.
  apply: summableD; first exact: summable_mu.
  by apply: summableN; exact: summable_mu.
have HS'nonneg : forall x, 0 <= S' x by move=> x; exact: normr_ge0.
have HS'summ : summable S'.
  apply/summable_abs.
  apply: summableD; first exact: summable_mu.
  by apply: summableN; exact: summable_mu.
rewrite (psum_option_split S HSnonneg HSsumm).
rewrite (psum_option_split S' HS'nonneg HS'summ).
have -> : psum (fun x : out_t * heap => S (Some x)) =
    psum (fun x : out_t * heap => `|P x - Q x|).
  apply/eq_psum=> x.
  by rewrite /S !completeE.
have -> : psum (fun x : nat * heap => S' (Some x)) =
    psum (fun x : nat * heap => `|P' x - Q' x|).
  apply/eq_psum=> x.
  by rewrite /S' !completeE.
have Hpack :
    psum (fun x : out_t * heap => `|P x - Q x|) =
    psum (fun x : nat * heap => `|P' x - Q' x|).
  move: (total_variation_pack_output_heap P Q).
  rewrite /total_variation /P' /Q'.
  rewrite -!psum_sum; try by move=> x; exact: normr_ge0.
  move=> H.
  lra.
rewrite Hpack.
congr (_ + _).
by rewrite /S /S' !completeE /= /P' /Q' !dmargin_dweight.
Qed.

End OutputHeap.
