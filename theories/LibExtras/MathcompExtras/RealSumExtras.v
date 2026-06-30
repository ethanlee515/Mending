From Stdlib Require Import Utf8 Lia.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq choice fintype bigop order all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".
Set Warnings "-notation-incompatible-prefix".
From mathcomp Require Import xfinmap reals realsum.
From mathcomp Require Import lra.
Set Warnings "notation-incompatible-prefix".
From mathcomp.algebra_tactics Require Import ring.
Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

(** Small reusable facts around MathComp's experimental [sum]/[summable]. *)

Section RealSumExtras.

Context {R : realType}.

Lemma psum_option_some_zero
  {T : choiceType} (S : option T -> R) :
  S None = 0 ->
  psum S = psum (fun x => S (Some x)).
Proof.
move=> HSnone.
rewrite (@reindex_psum_onto R (option T) T S
  [pred x : option T | x != None] (@Some T) (fun x => x)).
- by [].
- move=> x Hx.
  case: x Hx=> [x|] //=.
  by rewrite HSnone eqxx.
- by case=> [x|] //=; rewrite eqxx.
- by move=> x _.
Qed.

Lemma psum_option_split
  {T : choiceType} (S : option T -> R) :
  (forall x, 0 <= S x) ->
  summable S ->
  psum S = psum (fun x => S (Some x)) + S None.
Proof.
move=> HSge HSsumm.
pose is_some (x : option T) := if x is Some _ then true else false.
rewrite (@psumID R (option T) S is_some HSsumm).
congr (_ + _).
- rewrite (psum_option_some_zero
    (fun x : option T => (is_some x)%:R * S x)).
    apply/eq_psum=> x.
    by rewrite /is_some mul1r.
  by rewrite /is_some mul0r.
- rewrite (psum_finseq (r := [:: None])).
  + by rewrite big_seq1 /is_some mul1r ger0_norm.
  + by [].
  + move=> x.
    rewrite !inE.
    case: x=> [x|] //=.
    by rewrite mul0r eqxx.
Qed.

Lemma summable_shift_add_int (F : int -> R) center :
  summable F ->
  summable (fun x => F (x - center)).
Proof.
move=> smF.
rewrite summable_seqP in smF.
case: smF => M ge0_M leM.
apply/summable_seqP.
exists M => // J uniq_J.
have uniq_shift : uniq [seq x - center | x <- J].
  rewrite map_inj_in_uniq //.
  move=> x y _ _ eq_xy.
  rewrite -(subrK center x) eq_xy subrK.
  by [].
move: (leM [seq x - center | x <- J] uniq_shift).
by rewrite big_map.
Qed.

Lemma sum_shift_add_int (F : int -> R) center :
  sum (fun x => F (x + center)) = sum F.
Proof.
rewrite /sum.
congr (_ - _).
- have -> :
    psum (fpos (fun x => F (x + center))) =
    psum (fun x => fpos F (x + center)).
    by apply/eq_psum=> x; rewrite /fpos.
  rewrite -(reindex_psum (S := fpos F) (P := predT)
    (h := fun x => x + center)).
  + by [].
  + by move=> x _.
  exists (fun x => x - center) => x _; ring.
- have -> :
    psum (fneg (fun x => F (x + center))) =
    psum (fun x => fneg F (x + center)).
    by apply/eq_psum=> x; rewrite /fneg.
  rewrite -(reindex_psum (S := fneg F) (P := predT)
    (h := fun x => x + center)).
  + by [].
  + by move=> x _.
  exists (fun x => x - center) => x _; ring.
Qed.

Lemma sum_shift_sub_int (F : int -> R) center :
  sum (fun x => F (x - center)) = sum F.
Proof.
rewrite -(sum_shift_add_int F (- center)).
apply/eq_sum=> x.
by congr F.
Qed.

Lemma sum_opp_int (F : int -> R) :
  sum (fun x => F (- x)) = sum F.
Proof.
rewrite /sum.
congr (_ - _).
- have -> :
    psum (fpos (fun x => F (- x))) =
    psum (fun x => fpos F (- x)).
    by apply/eq_psum=> x; rewrite /fpos.
  rewrite -(reindex_psum (S := fpos F) (P := predT)
    (h := fun x => - x)).
  + by [].
  + by move=> x _.
  exists (fun x => - x) => x _; ring.
- have -> :
    psum (fneg (fun x => F (- x))) =
    psum (fun x => fneg F (- x)).
    by apply/eq_psum=> x; rewrite /fneg.
  rewrite -(reindex_psum (S := fneg F) (P := predT)
    (h := fun x => - x)).
  + by [].
  + by move=> x _.
  exists (fun x => - x) => x _; ring.
Qed.

Lemma divr_cancel_left_pos (a b c : R) :
  0 < a ->
  a * b / (a * c) = b / c.
Proof.
move=> Ha.
rewrite -[a * b / (a * c)]mulf_div.
by rewrite divff ?mul1r // lt0r_neq0.
Qed.

Lemma minr_lel (x y : R) :
  Num.min x y <= x.
Proof.
rewrite minr_absE.
have Hnorm : y - x <= `|x - y|.
  rewrite -opprB -normrN.
  exact: ler_norm.
lra.
Qed.

Lemma minr_ler (x y : R) :
  Num.min x y <= y.
Proof.
rewrite minr_absE.
have Hnorm : x - y <= `|x - y| := ler_norm _.
lra.
Qed.

Lemma minr_ge0 (x y : R) :
  0 <= x ->
  0 <= y ->
  0 <= Num.min x y.
Proof.
move=> Hx Hy.
rewrite minr_absE.
have Hnorm : `|x - y| <= x + y.
  apply: (le_trans (ler_normB x y)).
  by rewrite !ger0_norm.
lra.
Qed.

Lemma summable_minl_nonneg
    {T : choiceType} (F G : T -> R) :
  (forall x, 0 <= F x) ->
  (forall x, 0 <= G x) ->
  summable F ->
  summable (fun x => Num.min (F x) (G x)).
Proof.
move=> HF HG HsummF.
apply: (le_summable (F2 := F)); last exact: HsummF.
move=> x.
apply/andP; split.
- exact: minr_ge0.
- exact: minr_lel.
Qed.

Lemma summable_minr_nonneg
    {T : choiceType} (F G : T -> R) :
  (forall x, 0 <= F x) ->
  (forall x, 0 <= G x) ->
  summable G ->
  summable (fun x => Num.min (F x) (G x)).
Proof.
move=> HF HG HsummG.
apply: (le_summable (F2 := G)); last exact: HsummG.
move=> x.
apply/andP; split.
- exact: minr_ge0.
- exact: minr_ler.
Qed.

End RealSumExtras.

Fixpoint max_nat_lst (s : list nat) : nat :=
  match s with
  | nil => 0
  | head :: tail => max head (max_nat_lst tail)
  end.

Lemma max_nat_lst_correct (s : list nat) (x : nat) :
  x \in s -> leq x (max_nat_lst s).
Proof.
move => mem_x.
induction s.
- by rewrite in_nil in mem_x.
rewrite in_cons in mem_x.
rewrite /=.
case/orP: mem_x => mem_x; first lia.
suff: (x <= (max_nat_lst s))%N by lia.
exact: IHs.
Qed.

Definition compl (s : seq nat) (n : nat) : seq nat :=
  filter (fun x => x \notin s) (index_iota 0 n).

Lemma perm_eq_double_containment (s1 s2 : seq nat) :
  uniq s1 ->
  uniq s2 ->
  {subset s1 <= s2} ->
  {subset s2 <= s1} ->
  perm_eq s1 s2.
Proof.
move => uniq_s1 uniq_s2 sub_s1_s2 sub_s2_s1.
apply: uniq_perm => //.
apply uniq_min_size => //.
exact: uniq_leq_size.
Qed.

Lemma uniq_cat_with_compl s :
  uniq s ->
  uniq (s ++ compl s (S (max_nat_lst s))).
Proof.
move => uniq_s.
rewrite cat_uniq /=.
apply/andP; split => //=.
apply/andP; split => //=; last first.
- rewrite /compl.
  apply filter_uniq.
  exact: iota_uniq.
apply /hasP.
apply boolp.forallPNP => x.
suff: x \in s -> ¬ (x \in compl s (S (max_nat_lst s))) by tauto.
move => mem_x.
by rewrite mem_filter mem_x.
Qed.

Lemma subset_iota_complcat (s : seq nat) :
  uniq s ->
  let n := S (max_nat_lst s) in
  {subset (index_iota 0 n) <= (s ++ compl s n)}.
Proof.
move => /= uniq_s.
rewrite /sub_mem => x /=.
rewrite mem_index_iota => bounds_x.
rewrite mem_cat.
case H: (x \in s) => //=.
by rewrite /compl mem_filter H mem_iota.
Qed.

Lemma subset_complcat_iota (s : seq nat) :
  uniq s ->
  let n := S (max_nat_lst s) in
  {subset (s ++ compl s n) <= (index_iota 0 n)}.
Proof.
move => /= uniq_s.
rewrite /sub_mem => x /=.
rewrite mem_cat.
move => H.
case/orP: H => mem_x.
- rewrite mem_index_iota.
  apply/andP; split => //.
  exact: max_nat_lst_correct.
- rewrite /compl mem_filter in mem_x.
  by move/andP: mem_x => [??].
Qed.

Lemma compl_cat (s : seq nat) :
  uniq s ->
  let n := S (max_nat_lst s) in
  perm_eq (index_iota 0 n) (s ++ compl s n).
Proof.
move => uniq_s /=.
apply perm_eq_double_containment.
- apply iota_uniq.
- exact: uniq_cat_with_compl.
- exact: subset_iota_complcat.
- exact: subset_complcat_iota.
Qed.

Section FiniteBigopExtras.

Context {R : realType}.

Lemma split_domain s (f : nat -> R) :
  uniq s ->
  let n := S (max_nat_lst s) in
  \sum_(0 <= i < n) (f i) =
  \sum_(i <- s ++ compl s n) (f i).
Proof.
move => uniq_s.
apply perm_big.
exact:compl_cat.
Qed.

Lemma split_sum (s : seq nat) (f : nat -> R) :
  uniq s ->
  let n := S (max_nat_lst s) in
  \sum_(0 <= i < n) (f i) =
  \sum_(j <- s) (f j) + \sum_(k <- compl s n) (f k).
Proof.
move => uniq_s /=.
by rewrite split_domain // big_cat.
Qed.

Lemma ge0_bigsum (s : seq nat) (f : nat -> R) :
  (forall (x : nat), f x >= 0) ->
  \sum_(x <- s) (f x) >= 0.
Proof.
move => H.
induction s.
- rewrite big_nil; lra.
rewrite big_cons.
suff: 0 <= f a by lra.
apply H.
Qed.

End FiniteBigopExtras.
