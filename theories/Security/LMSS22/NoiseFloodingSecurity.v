From Stdlib Require Import Utf8 BinInt.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
From Mending Require Import ApproxFHE IntVec Indcpa Indcpad NoiseFlooding.

Local Open Scope ring_scope.

(* TODO fill with actual value *)
Definition global_epsilon (max_queries : nat) (gaussian_width_multiplier : R) : R :=
  1 / 1000%R.

(* Glue code *)
Module Type NoiseFloodingIsIndCpad
  (Scheme : ApproxFheScheme)
  (Metric : ApproxFheMetric(Scheme))
  (Params : NoiseFloodingParams).
  Module NF := NoiseFlooding(Scheme)(Metric)(Params).
  Include IsIndCpad(NF).
End NoiseFloodingIsIndCpad.

(* Main theorem *)
Module NoiseFloodingSecure
  (Import Scheme : ApproxFheScheme)
  (Import Metric : ApproxFheMetric(Scheme))
  (Import Correctness : ApproxCorrectness(Scheme)(Metric))
  (Import IndCpa : IsIndCpa(Scheme))
  (Import Params : NoiseFloodingParams)
  : NoiseFloodingIsIndCpad(Scheme)(Metric)(Params).
  Module NF := NoiseFlooding(Scheme)(Metric)(Params).
  Definition crypto_assumption_oracles := IndCpa.crypto_assumption_oracles.
  Definition crypto_assumption := IndCpa.crypto_assumption.
  Definition security_loss (max_queries : nat) :=
    IndCpa.security_loss + global_epsilon max_queries gaussian_width_multiplier.
  Module IndCpadGame := IndCpad NF.
  Import IndCpadGame.
  Theorem is_secure : forall A, exists Red,
    forall max_queries,
    Advantage (IndCpadOracle max_queries) A <=
    Advantage crypto_assumption Red + (security_loss max_queries).
  Admitted.
End NoiseFloodingSecure.
