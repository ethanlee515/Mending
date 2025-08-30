Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp Require Import reals realsum exp sequences realseq distr.
From mathcomp Require Import xfinmap.
From mathcomp Require Import lra.
Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.
Local Open Scope fset_scope.

Section DiscreteGaussian.

Context (R: realType).

(* To construct the discrete Gaussian distribution,
 * We will normalize the Gaussian function above.
 * This requires first proving that the weight of the function is finite.
 * We will do so by showing that it is below a geometric distribution *)

(**
Definition geometric (r : R) (i : nat) : R := r ^ i.
*)
(**

Lemma sum_geoE (r: R) (n : nat) :
  r <> 1 ->
  \sum_(i < n) (r ^ i) = (1 - r ^ n) / (1 - r).
Proof.
move => ne1_r.
induction n as [|n IH].
- rewrite big_ord0 /=.
  rewrite expr0z /=.
  by rewrite subrr mul0r.
rewrite big_ord_recr /=.
rewrite IH /geometric /=.
rewrite exprSz.
suff: r ^ n = (r ^ n) * (1 - r) / (1 - r).
- lra.
rewrite -mulrA mulrV.
- by rewrite mulr1.
- by rewrite unitfE; lra.
Qed. 

Lemma ge0_geo (r : R) (i : nat) :
  r >= 0 ->
  r ^ i >= 0.
Proof.
move => ge0_r.
rewrite /geometric /=.
exact: exprz_ge0.
Qed.

Lemma finite_sum_geoE (r : R) n :
  r <> 1 -> 
  \sum_(i < n) (r ^ i) = (1 - r ^ n) / (1 - r).
Proof.
move => ne1_r.
induction n as [|n IH].
- rewrite big_ord0.
  lra.
rewrite big_ord_recr /=.
rewrite IH /geometric /=.
clear IH.
rewrite exprSz.
suff: r ^ n = (r ^ n) * (1 - r) / (1 - r); first lra.
rewrite -mulrA mulrV.
- by rewrite mulr1.
- by rewrite unitfE; lra.
Qed.

Lemma summable_geo (r : R) :
  0 <= r < 1 ->
  summable (fun i => r ^ i).
Proof.
move/andP => [ge0_r lt1_r].
exists (1 / (1 - r)) => J.
rewrite (eq_bigr (fun x => r ^ (\val x))); last first.
- move => i _.
  admit. (**
  apply/normr_idP.
  apply ge0_geo.
  exact: ge0_geo.
  *)
(* Less than sum_geoE... *)
pose n : nat := 10.
apply: (le_trans (y := \sum_(i < n) (r ^ i))); last first.
- rewrite finite_sum_geoE; last lra.
  (* do math *)
  admit.
(* Nonsense with allowing negative domain... *)
Check sub_le_big.
Admitted.
*)

(* Unnormalized Gaussian function *)
Definition gaussian (s : R) (x : int) : R :=
  expR (- (x%:~R / s) ^ 2 / 2).

Lemma ge0_gaussian (s : R) (x : int) :
  gaussian s x >= 0.
Proof. exact: expR_ge0. Qed.

Definition max_step_ratio (s : R) :=
  expR (- (1 / s) ^ 2 / 2).

Definition geom_above (s : R) := geometric 1 (max_step_ratio s).

Lemma le_gauss_geo s x :
  gaussian s x <= geom_above s (absz x).
Proof.
rewrite /gaussian /geom_above -exprn_geometric.
rewrite /max_step_ratio.
(* do math *)
Admitted.

Check summable.

Lemma summable_gaussian (s : R) :
  s > 0 -> summable (T := int) (gaussian s).
Proof.
  move => gt0_s.
  apply: (le_summable (T := int) (F2 := fun x => geom_above s (absz x))).
  - move => x.
    apply/andP; split.
    + exact: ge0_gaussian.
    + exact: le_gauss_geo.
  - (* apply: summable_geometric. *)
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
