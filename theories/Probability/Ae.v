(* Distribution facts for additive-error couplings. *)

Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals distr.
From mathcomp Require Import realseq realsum exp lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From Mending.LibExtras.MathcompExtras Require Import DistrExtras.

Import GRing.Theory Num.Theory Order.Theory Order.POrderTheory.

Local Open Scope ring_scope.

Section AdditiveErrorCouplings.

Context {R : realType}.

Definition complete_mass {T : choiceType} (D : {distr T / R}) : option T -> R :=
  fun x =>
    match x with
    | Some y => D y
    | None => 1 - dweight D
    end.

Lemma isdistr_complete_mass {T : choiceType} (D : {distr T / R}) :
  isdistr (complete_mass D).
Proof.
split.
- case=> [x|]; first exact: ge0_mu.
  rewrite subr_ge0 pr_predT.
  exact: le1_mu.
- move=> J uniq_J.
  pose get (x : option T) := x.
  have getK : ocancel get (@Some T) by case.
  have Hsplit :
      \sum_(j <- J) complete_mass D j =
      \sum_(x <- pmap get J) D x +
        (if None \in J then 1 - dweight D else 0).
    elim: J uniq_J => [|j J IH] /=.
      by rewrite !big_nil addr0.
    rewrite in_cons => /andP [Hnotin Huniq].
    rewrite !big_cons.
    case: j Hnotin => [y|] Hnotin /=.
      rewrite IH // big_cons addrA.
      by [].
    rewrite IH //.
    move/negbTE: Hnotin => ->.
    by rewrite addr0 addrC.
  rewrite Hsplit.
  have Hsomes_uniq : uniq (pmap get J).
    exact: (pmap_uniq getK uniq_J).
  have Hsomes_le : \sum_(x <- pmap get J) D x <= dweight D.
    rewrite pr_predT.
    apply: (le_trans _ (gerfinseq_psum Hsomes_uniq (summable_mu D))).
    apply/ler_sum=> x _.
    by rewrite ger0_norm ?ge0_mu.
  have Hmass_le1 : dweight D <= 1 by rewrite pr_predT; exact: le1_mu.
  have Hloss_ge0 : 0 <= 1 - dweight D by lra.
  case: ifP => _; lra.
Qed.

Definition complete {T : choiceType} (D : {distr T / R})
    : {distr (option T) / R} :=
  mkdistr (isdistr_complete_mass D).

Lemma completeE {T : choiceType} (D : {distr T / R}) x :
  complete D x = complete_mass D x.
Proof. by []. Qed.

Definition coupling_with_loss
  {outL_t outR_t : choiceType}
  (d : {distr (outL_t * outR_t) / R})
  (outL : {distr outL_t / R})
  (outR : {distr outR_t / R}) : Prop :=
  dmargin fst d <=1 outL /\ dmargin snd d <=1 outR.

Definition lift_loss_post
  {outL_t outR_t : choiceType}
  (post : pred (outL_t * outR_t)) : pred (option outL_t * option outR_t) :=
  fun outs =>
    match outs with
    | (Some outL, Some outR) => post (outL, outR)
    | _ => false
    end.

Lemma coupling_with_loss_total_variation_dmargin_match
  {outL_t outR_t A : choiceType}
  (fL : outL_t -> A) (fR : outR_t -> A)
  (d : {distr (outL_t * outR_t) / R})
  (outL : {distr outL_t / R})
  (outR : {distr outR_t / R})
  (ε : R) :
  coupling_with_loss d outL outR ->
  \P_[ d ] (fun xy => fL xy.1 == fR xy.2) >= 1 - ε ->
  total_variation (dmargin fL outL) (dmargin fR outR) <= ε.
Admitted.

Lemma coupling_with_loss_bind
  {midL_t midR_t outL_t outR_t : choiceType}
  (ML : {distr midL_t / R})
  (MR : {distr midR_t / R})
  (KL : midL_t -> {distr outL_t / R})
  (KR : midR_t -> {distr outR_t / R})
  (mid : pred (midL_t * midR_t))
  (post : pred (outL_t * outR_t))
  (ε ε' : R)
  (d0 : {distr (midL_t * midR_t) / R}) :
  0 <= ε ->
  0 <= ε' ->
  coupling_with_loss d0 ML MR ->
  \P_[ d0 ] mid >= 1 - ε ->
  (forall xL xR,
    mid (xL, xR) ->
    exists d1,
      coupling_with_loss d1 (KL xL) (KR xR) /\
      \P_[ d1 ] post >= 1 - ε') ->
  exists d,
    coupling_with_loss d
      (\dlet_(xL <- ML) KL xL)
      (\dlet_(xR <- MR) KR xR) /\
    \P_[ d ] post >= 1 - (ε + ε').
Admitted.

End AdditiveErrorCouplings.
