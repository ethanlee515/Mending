Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp Require Import reals realsum exp sequences realseq.

Set Bullet Behavior "Strict Subproofs".

Section make_generalize_realType.

Parameter (R: realType).

Local Open Scope ring_scope.

(* To construct the discrete Gaussian distribution,
 * We will normalize the Gaussian function above.
 * This requires first proving that the weight of the function is finite.
 * We will do so by showing that it is below a geometric distribution *)

Definition geometric (r : R) (i : int) : R :=
  if i < 0 then 0 else r ^ i.

Lemma summable_geo (r : R) :
  summable (geometric r).
Proof. Admitted.

(* Unnormalized Gaussian function *)
Definition gaussian (s : R) (x : int) : R :=
  expR (- (x%:~R / s) ^+ 2 / 2).

Lemma ge0_gaussian (s : R) (x : int) :
  gaussian s x >= 0.
Proof. Admitted.

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
  - exact: summable_geo.
Qed.

End make_generalize_realType.