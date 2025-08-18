Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp Require Import reals realsum exp sequences realseq distr.
From mathcomp Require Import xfinmap.
Import GRing.Theory.
Import Num.Theory.
From mathcomp Require Import lra.

Section DiscreteGaussian.

Context (R: realType).

Local Open Scope ring_scope.
Local Open Scope fset_scope.

(* To construct the discrete Gaussian distribution,
 * We will normalize the Gaussian function above.
 * This requires first proving that the weight of the function is finite.
 * We will do so by showing that it is below a geometric distribution *)

Definition geometric (r : R) (i : int) : R :=
  if i < 0 then 0 else r ^ i.

Lemma sum_geoE (r: R) (n : nat) :
  r <> 1 ->
  \sum_(i < n) (geometric r i) = (1 - r ^ n) / (1 - r).
Proof.
  move => ne1_r.
  induction n.
  - rewrite big_ord0 /=.
    rewrite expr0z /=.
    by rewrite subrr mul0r.
  rewrite big_ord_recr /=.
  rewrite IHn.
  rewrite /geometric /=.
  have {2}->: r ^ n = (r ^ n) * (1 - r) / (1 - r).
  - rewrite -mulrA mulrV.
    + by rewrite mulr1.
    + rewrite unitfE.
      lra.
  by rewrite exprSz; lra.
Qed. 

Lemma ge0_geo r i :
  r >= 0 ->
  geometric r i >= 0.
Proof. Admitted.

Lemma summable_geo (r : R) :
  0 <= r < 1 ->
  summable (geometric r).
Proof.
  move/andP => [ge0_r lt1_r].
  exists (1 / (1 - r)) => J.
  rewrite (eq_bigr (fun x => geometric r (\val x))); last first.
  - move => i _.
    apply/normr_idP.
    exact: ge0_geo.
  (* Less than sum_geoE... *)
Admitted.

(* Unnormalized Gaussian function *)
Definition gaussian (s : R) (x : int) : R :=
  expR (- (x%:~R / s) ^ 2 / 2).

Lemma ge0_gaussian (s : R) (x : int) :
  gaussian s x >= 0.
Proof.
  exact: expR_ge0.
Qed.

Definition max_step_ratio (s : R) :=
  expR (- (1 / s) ^ 2 / 2).

Definition geom_above (s : R) := geometric (max_step_ratio s).

Lemma le_gauss_geo s x :
  gaussian s x <= geom_above s x.
Proof. Admitted.

Lemma summable_gaussian (s : R) :
  s > 0 -> summable (gaussian s).
Proof.
  move => gt0_s.
  apply: (le_summable (F2 := geom_above s)).
  - move => x.
    apply/andP; split.
    + exact: ge0_gaussian.
    + exact: le_gauss_geo.
  - apply: summable_geo.
    admit.
Admitted.

Definition gaussian_pdf (s : R) (x : int) :=
  gaussian s x / sum (gaussian s).

Lemma isdistr_gaussian (s : R) :
  s > 0 -> isdistr (gaussian_pdf s).
Proof.
  move => gt0_s.
  split.
  - admit.
  - admit.
Admitted.

Definition discrete_gaussian s (H : s > 0) : distr R int :=
  mkdistr (isdistr_gaussian s H).

End DiscreteGaussian.
