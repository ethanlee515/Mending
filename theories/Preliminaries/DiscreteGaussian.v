From Stdlib Require Import Utf8 Lia.
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

(* Unnormalized Gaussian function *)
Definition gaussian (s : R) (x : int) : R :=
  expR (- (x%:~R / s) ^ 2 / 2).

Lemma ge0_gaussian (s : R) (x : int) :
  gaussian s x >= 0.
Proof. exact: expR_ge0. Qed.

Definition max_step_ratio (s : R) :=
  expR (- (1 / s) ^ 2 / 2).

Definition geom_above (s : R) := geometric 1 (max_step_ratio s).

(*
Lemma le_real_int (a b : int) :
  a <= b ->
  a%:~R <= b%:~R.
*)

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
  Check absz_gt0.
  Check leq_mul2r.
  case: (x =P 0).
  - by move => ?; subst => /=; nra.
  - move => ne0_x.
    have H: `|x| >= 1 by nia.
    have ->: x%:~R * x%:~R = (x * x)%:~R.
    + admit.
    have ->: `|x|%:R = `|x|%:~R.
    + admit.
    rewrite ler_int.
    nia.
}
rewrite oppr_lt0 div1r invr_gt0.
repeat (apply mulr_gt0 => //=).
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
