From Stdlib Require Import Utf8 Lia.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp Require Import reals realsum exp sequences realseq distr.
From mathcomp Require Import xfinmap.
From mathcomp Require Import lra.
Import GRing.Theory Num.Theory Order.Theory.
From Stdlib Require Import Ring.
From mathcomp.algebra_tactics Require Import ring.

Local Open Scope fset_scope.
Local Open Scope ring_scope.

Section DiscreteGaussian.

Context (R: realType).

(* To construct the discrete Gaussian distribution,
 * We will normalize the Gaussian function above.
 * This requires first proving that the weight of the function is finite.
 * We will do so by showing that it is below a geometric distribution *)

(* Unnormalized Gaussian function *)
Definition gaussian (s : R) (x : int) : R :=
  expR (- (x%:~R / s) ^ 2 / 2).

Lemma ge0_gaussian (s : R) (x : int) :
  gaussian s x >= 0.
Proof. exact: expR_ge0. Qed.

Lemma ge0_geo (r : R) (i : nat) :
  r >= 0 ->
  geometric 1 r i >= 0.
Proof.
move => ge0_r.
rewrite /geometric /=.
rewrite exprnP mul1r /=.
exact: exprz_ge0.
Qed.

Lemma finite_sum_geoE (r : R) n :
  r <> 1 -> 
  \sum_(i < n) (geometric 1 r (val i)) = (1 - r ^ n) / (1 - r).
Proof.
move => ne1_r.
rewrite /geometric.
induction n as [|n IH].
- rewrite big_ord0.
  lra.
rewrite big_ord_recr /=.
rewrite IH /geometric /=.
clear IH.
rewrite exprSz exprnP.
suff: r ^ n = (r ^ n) * (1 - r) / (1 - r); first lra.
rewrite -mulrA mulrV.
- by rewrite mulr1.
- by rewrite unitfE; lra.
Qed.

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

Lemma summable_geo (r : R) :
  0 <= r < 1 ->
  summable (geometric 1 r).
Proof.
move/andP => [ge0_r lt1_r].
exists (1 / (1 - r)) => J.
rewrite (eq_bigr (fun x => geometric 1 r (\val x))); last first.
- move => i _.
  apply/normr_idP.
  by apply ge0_geo.
pose s := (map (fun x => val x) (index_enum J)). 
have uniq_s : uniq s. {
  rewrite map_inj_uniq.
  + exact: index_enum_uniq.
  + exact: val_inj.
}
have ->: \sum_(i <- index_enum J) geometric 1 r (\val i) =
  \sum_(i <- s) geometric 1 r i.
- by rewrite big_map.
apply: (le_trans (y := \sum_(0 <= i < S (max_nat_lst s)) (geometric 1 r i)));
  last first. {
  rewrite big_mkord.
  rewrite finite_sum_geoE; last lra.
  suff: r ^ (S (max_nat_lst s)) / (1 - r) >= 0 by lra.
  apply divr_ge0.
  + by apply exprz_ge0.
  + lra.
}
rewrite (split_sum s) //.
suff: \sum_(k <- compl s (max_nat_lst s).+1)  geometric 1 r k >= 0 by lra.
apply ge0_bigsum.
move => x.
exact: ge0_geo.
Qed.

Definition max_step_ratio (s : R) :=
  expR (- (1 / s) ^ 2 / 2).

Definition geom_above (s : R) := geometric 1 (max_step_ratio s).

Lemma le_gauss_geo s x :
  s > 0 ->
  gaussian s x <= geom_above s (absz x).
Proof.
move => gt0_s.
rewrite /gaussian /geom_above -exprn_geometric.
rewrite /max_step_ratio.
rewrite /exprz /=.
rewrite -expRM_natr.
rewrite ler_expR /=.
rewrite /expR.
rewrite !GRing.expr2.
have ->: - (1 / s * (1 / s)) / 2 = - (1 / (2 * s * s)) by lra.
have ->: - (x%:~R / s * (x%:~R / s)) / 2 =  -(1 / (2 * s * s)) * x%:~R * x%:~R.
- lra.
rewrite -GRing.mulrA.
rewrite ler_nM2l. {
- rewrite /Num.norm /=.
  case: (x =P 0).
  - by move => ?; subst => /=; nra.
  - move => ne0_x.
    have H: `|x| >= 1 by nia.
    rewrite -intrM.
    rewrite natr_absz.
    rewrite ler_int.
    nia.
}
rewrite oppr_lt0 div1r invr_gt0.
repeat (apply mulr_gt0 => //=).
Qed.

Lemma mirror_summable (f : nat -> R) :
  summable f ->
  summable (fun (x : int) => f (absz x)).
Proof.
move => summable_f.
rewrite summable_seqP /= in summable_f.
move:summable_f => [M ge0_M] summable_f.
apply summable_seqP; exists (2 * M) => /=; first lra.
move => J uniq_J.
pose posJ := [seq x <- J | 0 <= x].
pose negJ := filter (predC (Order.le 0)) J.
rewrite (perm_big (posJ ++ negJ)) /=; last first.
- rewrite perm_sym.
  apply permEl.
  exact: perm_filterC.
rewrite big_cat /=.
have H (a b : R): (a <= M) -> (b <= M) -> (a + b <= 2 * M) by lra.
apply H; clear H.
- rewrite -(big_map absz predT (fun u => `|f `|u|%N|)) /=.
  apply summable_f.
  rewrite map_inj_in_uniq.
  + rewrite /posJ.
    exact: filter_uniq. 
  move => x y mem_x mem_y eq_abs_xy.
  rewrite mem_filter in mem_x.
  rewrite mem_filter in mem_y.
  lia.
- rewrite -(big_map absz predT (fun u => `|f `|u|%N|)) /=.
  apply summable_f.
  rewrite map_inj_in_uniq.
  + rewrite /negJ.
    exact: filter_uniq. 
  move => x y mem_x mem_y eq_abs_xy.
  rewrite mem_filter /predC /= in mem_x.
  rewrite mem_filter /predC /= in mem_y.
  lia.
Qed.

Lemma summable_gaussian (s : R) :
  s > 0 -> summable (T := int) (gaussian s).
Proof.
move => gt0_s.
apply: (le_summable (T := int) (F2 := fun x => geom_above s (absz x))).
- move => x.
  apply/andP; split.
  + exact: ge0_gaussian.
  + exact: le_gauss_geo.
- rewrite /geom_above.
  apply mirror_summable.
  apply summable_geo.
  rewrite /max_step_ratio /=.
  apply/andP; split.
  + apply expR_ge0.
  rewrite expR_lt1.
  suff: (1 / s) ^ 2 > 0 by lra.
  rewrite /exprz /= expr2.
  have H: (1 / s > 0) by exact: divr_gt0.
  exact: mulr_gt0.
Qed.

(* Works "as expected" if s > 0.
 * null distribution otherwise. *)
Definition gaussian_pdf (s : R) (x : int) : R :=
  if s > 0 then
    gaussian s x / sum (gaussian s)
  else 0.

Lemma gt0_weight_gaussian s :
  s > 0 ->
  sum (gaussian s) > 0.
Proof.
move => gt0_s.
rewrite -psum_sum; last first.
- move => x.
  exact: ge0_gaussian.
have H (b a c : R): a < b <= c -> a < c by lra.
pose J : {fset int} := [fset 0].
apply (H (\sum_(i : J) (gaussian s (val i)))).
apply/andP; split.
- rewrite big_fset1 /gaussian /=.
  exact: expR_gt0.
rewrite (eq_bigr (F1 := _)
  ((fun i => `|gaussian s (val i)|))); first last.
- move => i _.
  symmetry.
  apply ger0_norm.
  exact: ge0_gaussian.
apply (gerfin_psum J (S := gaussian s)).
exact: summable_gaussian.
Qed.

Lemma isdistr_gaussian (s : R) :
  isdistr (gaussian_pdf s).
Proof.
case H: (s <= 0).
- have H' (m : int -> R) : (m = mnull) -> isdistr m.
  + by move => ->; exact isd_mnull.
  rewrite /gaussian_pdf. 
  apply H'.
  apply boolp.funext => x.
  by rewrite ifF //; lra.
rewrite /gaussian_pdf.
split => //=.
- move => x.
  rewrite ifT; last lra.
  apply divr_ge0.
  + exact: ge0_gaussian.
  + suff: 0 < sum (gaussian s) by lra.
    by apply gt0_weight_gaussian; lra.
move => J uniq_J.
rewrite (eq_bigr (F1 := _)
  ((fun i => (1 / sum (gaussian s)) * (gaussian s) i))); first last.
+ move => i _.
  by rewrite ifT; lra.
rewrite -big_distrr.
have H' (b a : R) : a = b -> b <= 1 -> a <= 1 by lra.
apply (H' ((1 / sum (gaussian s)) * \sum_(i <- J) (gaussian s i))).
+ by trivial.
clear H'.
have H' (a b : R) : a <> 0 -> (1 / a) * b = b / a.
+ by lra.
rewrite H'; last first.
+ suff: sum (gaussian s) > 0 by lra.
  apply gt0_weight_gaussian.
  lra.
clear H'.
rewrite ler_pdivrMr; last first.
+ by apply gt0_weight_gaussian; lra.
rewrite -psum_sum; last first.
+ move => x.
  exact: ge0_gaussian.
rewrite mul1r.
rewrite (eq_bigr (F1 := _)
  (fun i => `|gaussian s i|)); first last.
+ move => i _.
  symmetry.
  apply ger0_norm.
  apply ge0_gaussian.
apply ger_big_psum => //.
apply summable_gaussian.
lra.
Qed.

Definition centered_discrete_gaussian s : distr R int :=
  mkdistr (isdistr_gaussian s).

Definition discrete_gaussian center s : distr R int :=
  dmargin (GRing.add center) (centered_discrete_gaussian s).

End DiscreteGaussian.
