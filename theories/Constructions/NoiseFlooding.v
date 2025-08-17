(* This converts an IND-CPA scheme to an IND-CPA-D one *)

From Stdlib Require Import Utf8 BinInt.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
From VerifiedCKKS Require Import ApproxFHE IntVec Indcpa Indcpad DTuple DiscreteGaussian.

Local Open Scope ring_scope.

Definition n_dg (n : nat) (s : R) (H : s > 0) : distr R (n.-tuple int) :=
  nfold_distr R n (discrete_gaussian R s H).

Module Type NoiseFloodingParams.
Parameter gaussian_width_multiplier : R.
Axiom gt0_gaussian_width_multiplier :
  gaussian_width_multiplier > 0.
End NoiseFloodingParams.

Module NoiseFlooding
  (Import Scheme : ApproxFheScheme)
  (Import Metric : ApproxFheMetric(Scheme))
  (Import Params : NoiseFloodingParams)
  : ApproxFheScheme.
Definition pk_t := Scheme.pk_t.
Definition evk_t := Scheme.evk_t.
Definition sk_t := Scheme.sk_t.
Definition message := Scheme.message.
Definition encryption := Scheme.encryption.
Definition ciphertext := Scheme.ciphertext.
Definition unary_gate := Scheme.unary_gate.
Definition binary_gate := Scheme.binary_gate.
Definition interpret_unary := Scheme.interpret_unary.
Definition interpret_binary := Scheme.interpret_binary.
Definition keygen := Scheme.keygen.
Definition encrypt := Scheme.encrypt.
Definition eval1 := Scheme.eval1.
Definition eval2 := Scheme.eval2.
(* TODO find out if this is the "right" amount of noise. *)
Definition dg_stdev (error_bound : nat) : R :=
  (error_bound * error_bound + 1)%:~R * gaussian_width_multiplier.
Lemma gt0_dg_stdev e :
  dg_stdev e > 0.
Proof. Admitted.
(* Maybe it's not ideal that decrypting an invalid ciphertext crashes the entire experiment.
 * This makes any sense only if invalid ciphertexts result only from misuse. *)
Program Definition decrypt (sk: sk_t) (c: ciphertext) : distr R message :=
  match c with
  | None => dnull
  | Some (_, e) =>
    \dlet_(m <- Scheme.decrypt sk c)
    \dlet_(noise <- n_dg dim (dg_stdev e) _)
    dunit (inverse_isometry m (ivec_add noise (isometry m m)))
  end.
Next Obligation.
move => *; exact: gt0_dg_stdev.
Defined.
End NoiseFlooding.
