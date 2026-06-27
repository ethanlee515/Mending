From Stdlib Require Import Utf8 Lia.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq choice fintype bigop order all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".
Set Warnings "-notation-incompatible-prefix".
From mathcomp Require Import xfinmap reals realsum.
From mathcomp.classical Require Import classical_sets.
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

Local Open Scope classical_set_scope.

Lemma interchange_sup_proved
    {T U : Type} (S : T -> U -> R) :
  (forall x, has_sup [set r | exists y, r = S x y]) ->
  has_sup [set r | exists x, r = sup [set r | exists y, r = S x y]] ->
  sup [set r | exists x, r = sup [set r | exists y, r = S x y]] =
  sup [set r | exists y, r == sup [set r | exists x, r = S x y]].
Proof.
move=> Hrow_sup Hrows_sup.
pose row x := [set r | exists y, r = S x y].
pose col y := [set r | exists x, r = S x y].
pose rows := [set r | exists x, r = sup (row x)].
pose cols := [set r | exists y, r == sup (col y)].
have Hcol_nonempty y : col y !=set0.
  case: Hrows_sup=> Hrows_ne _.
  case: Hrows_ne=> _ [x _].
  by exists (S x y); exists x.
have Hrow_le_rows x : sup (row x) <= sup rows.
  move/ubP: (sup_upper_bound Hrows_sup); apply.
  by exists x.
have Hcol_ub y : ubound (col y) (sup rows).
  move=> r [x ->].
  apply: (le_trans _ (Hrow_le_rows x)).
  move/ubP: (sup_upper_bound (Hrow_sup x)); apply.
  by exists y.
have Hcol_sup y : has_sup (col y).
  split; first exact: Hcol_nonempty.
  by exists (sup rows).
have Hcol_le_rows y : sup (col y) <= sup rows.
  exact: ge_sup (Hcol_nonempty y) (Hcol_ub y).
have Hcols_sup : has_sup cols.
  split.
  - case: Hrows_sup=> Hrows_ne _.
    case: Hrows_ne=> _ [x _].
    case: (Hrow_sup x)=> Hrow_ne _.
    case: Hrow_ne=> _ [y _].
    exists (sup (col y)).
    by exists y; rewrite eqxx.
  - exists (sup rows)=> r [y /eqP ->].
    exact: Hcol_le_rows.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: ge_sup; first by case: Hrows_sup.
  move=> r [x ->].
  apply: ge_sup; first by case: (Hrow_sup x).
  move=> s [y ->].
  apply: (le_trans _).
    move/ubP: (sup_upper_bound (Hcol_sup y)); apply.
    by exists x.
  move/ubP: (sup_upper_bound Hcols_sup); apply.
  by exists y; rewrite eqxx.
- apply: ge_sup; first by case: Hcols_sup.
  move=> r [y /eqP ->].
  exact: Hcol_le_rows.
Qed.

Local Close Scope classical_set_scope.

Lemma psumB_proved
    {T : choiceType} (S1 S2 : T -> R) :
  (forall x, 0 <= S2 x <= S1 x) ->
  summable S1 ->
  psum (S1 \- S2) = psum S1 - psum S2.
Proof.
move=> Hle Hsumm1.
have Hge2 x : 0 <= S2 x by have /andP[H _] := Hle x.
have Hle21 x : S2 x <= S1 x by have /andP[_ H] := Hle x.
have Hsumm2 : summable S2.
  apply: (le_summable (F2 := S1) _ Hsumm1)=> x.
  by rewrite Hge2 Hle21.
have HgeB x : 0 <= (S1 \- S2) x.
  by rewrite /= subr_ge0 Hle21.
have HsummB : summable (S1 \- S2).
  apply: (le_summable (F2 := S1) _ Hsumm1)=> x.
  by rewrite HgeB /= lerBlDr lerDl.
have <- : psum (S1 \- S2 \+ S2) = psum S1.
  apply/eq_psum=> x.
  by rewrite /= subrK.
rewrite (psumD HgeB Hge2 HsummB Hsumm2).
by rewrite addrK.
Qed.

Lemma summable_pair_from_rows_psum
    {T U : choiceType} (S : T -> U -> R) :
  (forall x, summable (S x)) ->
  summable (fun x => psum (S x)) ->
  summable (fun xy : T * U => S (fst xy) (snd xy)).
Proof.
move=> Hrow Hrows.
exists (psum (fun x => psum (S x)))=> J.
rewrite (@big_fset_seq R 0 +%R (T * U)%type J
  (fun xy : T * U => `|S (fst xy) (snd xy)|)).
rewrite (@partition_big_imfset R 0 +%R _ _ fst J
  (fun xy : T * U => `|S (fst xy) (snd xy)|)).
pose X := [fset fst xy | xy in J]%fset.
have HX := gerfin_psum X Hrows.
rewrite (@big_fset_seq R 0 +%R T X
  (fun x => `|psum (S x)|)) in HX.
apply: (le_trans _ HX).
apply: ler_sum=> x _.
rewrite ger0_norm ?ge0_psum //.
set F := [fset xy in J | fst xy == x]%fset.
have Hfiber :
    \sum_(xy <- J | fst xy == x) `|S (fst xy) (snd xy)| =
    \sum_(xy <- F) `|S x (snd xy)|.
  rewrite /F big_fset /=.
  apply: eq_bigr=> xy /eqP Hx.
  by rewrite Hx.
rewrite Hfiber.
have Huniq : uniq [seq snd xy | xy <- enum_fset F].
  rewrite map_inj_in_uniq ?uniq_fset_keys //.
  move=> [x1 y1] [x2 y2].
  rewrite /F !in_fset /=.
  move=> /andP[_ /eqP Hx1] /andP[_ /eqP Hx2] Hy.
  congr (_, _).
    move: Hx1 Hx2=> /= Hx1 Hx2.
    by rewrite Hx1 Hx2.
  exact: Hy.
rewrite -(big_map snd predT (fun y => `|S x y|)).
exact: (gerfinseq_psum Huniq (Hrow x)).
Qed.

Lemma interchange_psum_proved
    {T U : choiceType} (S : T -> U -> R) :
  (forall x, summable (S x)) ->
  summable (fun x => psum (fun y => S x y)) ->
  psum (fun x => psum (fun y => S x y)) =
  psum (fun y => psum (fun x => S x y)).
Proof.
move=> Hrow Hrows.
pose P := fun xy : T * U => S (fst xy) (snd xy).
have HP : summable P.
  exact: (summable_pair_from_rows_psum S Hrow Hrows).
change (psum (fun x : T => psum (fun y : U => P (x, y))) =
        psum (fun y : U => psum (fun x : T => P (x, y)))).
by rewrite -(@psum_pair R T U P HP) (@psum_pair_swap R T U P HP).
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
