(* This converts an IND-CPA scheme to an IND-CPA-D one *)

From Stdlib Require Import Utf8 BinInt.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
From VerifiedCKKS Require Import ApproxFHE IntVec Indcpa Indcpad.

Local Open Scope ring_scope.

(* TODO *)
Parameter dtuple : forall (n : nat) (t: choiceType),
  n.-tuple (distr R t) -> distr R (n.-tuple t).
(* TODO discrete gaussian, n copies *)
Parameter n_dg : forall {n : nat} (s : int), distr R (n.-tuple int).

(* To think: Global target security?
 * Other security parameters probably will be chosen using this.
 *
 * No clue where to put this though, proof engineering wise. *)
Parameter epsilon : R.

Module NoiseFlooding
  (Import Scheme : ApproxFheScheme)
  (Import Metric : ApproxFheMetric(Scheme))
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
Definition decrypt (sk: sk_t) (c: ciphertext) : distr R message :=
  match c with
  | None => dnull
  | Some (_, e) =>
    \dlet_(m <- Scheme.decrypt sk c)
    (* TODO find out the "right" amount of noise.
     * The `e * e` below is a placeholder. *)
    \dlet_(noise <- @n_dg dim (e * e))
    dunit (inverse_isometry m (ivec_add noise (isometry m m)))
  end.
End NoiseFlooding.

(* Main theorem *)
Module NoiseFloodingSecure
  (Import Scheme : ApproxFheScheme)
  (Import Metric : ApproxFheMetric(Scheme))
  (Import IndCpa : IsIndCpa(Scheme))
  : IsIndCpad(Scheme).
  Definition crypto_assumption_oracles := IndCpa.crypto_assumption_oracles.
  Definition crypto_assumption := IndCpa.crypto_assumption.
  (* The summand is obviously placeholder.
   * Who knows what's the actual magic number... *)
  Definition security_loss (max_queries : nat) :=
    IndCpa.security_loss + (max_queries%:~R * epsilon).
  Module IndCpadGame := IndCpad Scheme.
  Import IndCpadGame.
  Theorem is_secure : forall A, exists Red,
    forall max_queries,
    Advantage (IndCpadOracle max_queries) A <=
    Advantage crypto_assumption Red + (security_loss max_queries).
  Admitted.
End NoiseFloodingSecure.
