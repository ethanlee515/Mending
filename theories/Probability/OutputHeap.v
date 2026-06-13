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

Lemma total_variation_pack_output_heap
    {out_t : choice_type} (P Q : {distr (out_t * heap) / R}) :
  total_variation P Q =
  total_variation (dmargin (@pack_output_heap out_t) P)
                  (dmargin (@pack_output_heap out_t) Q).
Admitted.

Definition complete_output_heap {out_t : choice_type}
    (out : {distr (out_t * heap) / R}) :
    {distr (option (nat * heap)) / R} :=
  complete (dmargin (@pack_output_heap out_t) out).

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

End OutputHeap.
