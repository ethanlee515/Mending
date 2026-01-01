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

Definition compl (s : seq nat) (n : nat) : seq nat :=
  filter (fun x => x \notin s) (index_iota 0 n).

Lemma compl_cat (s : seq nat) :
  uniq s ->
  let n := S (max_nat_lst s) in
  perm_eq (index_iota 0 n) (s ++ compl s n).
Proof.
Admitted.

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
Admitted.

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
    admit.
Admitted.

(* Works "as expected" if s > 0.
 * null distribution otherwise. *)
Definition gaussian_pdf (s : R) (x : int) :=
  if s > 0 then
    gaussian s x / sum (gaussian s)
  else 0.

Lemma isdistr_gaussian (s : R) :
  isdistr (gaussian_pdf s).
Proof.
  case H: (s < 0).
  - admit.
  - rewrite /gaussian_pdf.
Admitted.

Definition centered_discrete_gaussian s : distr R int :=
  mkdistr (isdistr_gaussian s).

Definition discrete_gaussian center s : distr R int :=
  dmargin (GRing.add center) (centered_discrete_gaussian s).

End DiscreteGaussian.
