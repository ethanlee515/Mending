From Stdlib Require Import Utf8 BinInt.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
Import PackageNotation.
Open Scope Z_scope.

Local Open Scope package_scope.
Local Open Scope ring_scope.

Module Type ApproxFheScheme.
  Parameter pk_t : choice_type.
  Parameter evk_t : choice_type.
  Parameter sk_t : choice_type.
  Parameter message : choice_type.
  Parameter encryption : choice_type.
  (* Here we consider "tagged ciphertexts".
   * That is, an encryption together with an error bound. *)
  Definition ciphertext := 'option (encryption × 'int).
  (* We assume the homomorphic encryption operates over arithmetic circuits.
   * We therefore have a set of gates for building such circuits. *)
  Parameter unary_gate : Type.
  Parameter binary_gate : Type.
  Parameter interpret_unary : unary_gate → message → message.
  Parameter interpret_binary : binary_gate → message → message → message.
  (* Now, the "usual" 4-tuple (keygen, enc, eval, dec).
   * Each member of the tuple holds additionally a "memory specification",
   * describing which (global) variables it is allowed access to. *)
  Parameter keygen : {mem_spec : Locations &
    code mem_spec [interface] (pk_t × evk_t × sk_t)}.
  Parameter encrypt : {mem_spec : Locations &
    pk_t → message →
    code mem_spec [interface] ciphertext}.
  Parameter eval1 : {mem_spec : Locations &
    evk_t → unary_gate → ciphertext →
    code mem_spec [interface] ciphertext}.
  Parameter eval2 : {mem_spec : Locations &
    evk_t → binary_gate → ciphertext → ciphertext →
    code mem_spec [interface] ciphertext}.
  Parameter decrypt : {mem_spec : Locations &
    sk_t → encryption →
    code mem_spec [interface] message}.
End ApproxFheScheme.

(* Correctness of each individual algorithm in the FHE 4-tuple *)
Module ApproxCorrectness(Import S: ApproxFheScheme).
  (* For simplicity, we consider only pure and deterministic decryption. *)
  Section simplified_decryption.
  (* Alternative definition of decryption.
   * Will require consistency later with the given scheme. *)
  Context (dec' : sk_t → encryption → message).
  Context (metric : message → message → 'int).
  (* Catch-all error probability for any step going wrong.
   * Should be negligible. *)
  Context (p_gate_error : R).
  (* Before formalizing correctness further,
   * we need a definition for the "underlying plaintext" of a ciphertext.
   * In the approximate setting, this may not be unique. *)
  Definition is_underlying_plaintext sk (c : ciphertext) m :=
    match c with
    | None => false
    | Some (data, error_bound) => metric (dec' sk data) m <? error_bound
    end.
  (* Correctness of keygen.
   * We ask for a predicate of "good keys".
   * We then require that keygen output good keys with overwhelming probability. *)
  Context (good_keys : pk_t → evk_t → sk_t → bool).
  Definition keygen_approx_correct :=
    ∀ mem,
    let d_out := Pr_code keygen.π2 mem in
    let bad_keys kg_out :=
      match kg_out.1 with (pk, evk, sk) =>
      ~~ (good_keys pk evk sk) end
    in
    \P_[ d_out ] bad_keys < p_gate_error. 
  (* Conditioned on the key being good,
   * Encryption outputs good ciphertexts with overwhelming probability. *)
  Definition encrypt_approx_correct :=
    ∀ mem pk evk sk m,
    good_keys pk evk sk →
    let d_out := Pr_code (encrypt.π2 pk m) mem in
    let bad_encryption enc_out :=
        ~~ (is_underlying_plaintext sk (fst enc_out) m)
    in
    \P_[ d_out ] bad_encryption < p_gate_error.
  Definition eval1_approx_correct :=
    ∀ mem pk evk sk op c m,
    good_keys pk evk sk →
    is_underlying_plaintext sk c m →
    let d_out := Pr_code (eval1.π2 evk op c) mem in
    let bad_eval eval_out :=
      ~~ (is_underlying_plaintext sk eval_out.1 (interpret_unary op m)) in
    \P_[ d_out ] bad_eval < p_gate_error.
  Definition eval2_approx_correct :=
    ∀ mem pk evk sk op c1 c2 m1 m2,
    good_keys pk evk sk →
    is_underlying_plaintext sk c1 m1 →
    is_underlying_plaintext sk c2 m2 →
    let d_out := Pr_code (eval2.π2 evk op c1 c2) mem in
    let bad_eval eval_out :=
      ~~ (is_underlying_plaintext sk eval_out.1 (interpret_binary op m1 m2))
    in
    \P_[ d_out ] bad_eval < p_gate_error.
  End simplified_decryption.
End ApproxCorrectness.

(* A FHE scheme S is approximately correct if all of its operations are. *)
Module Type IsApproxCorrect(S: ApproxFheScheme).
  Import S.
  Parameter dec' : sk_t → encryption → message.
  Axiom dec'_correct :
    ∀ mem sk c,
    let d_out := Pr_code (decrypt.π2 sk c) mem in
    \P_[ d_out ] (fun dec_out => dec_out.1 == dec' sk c) = 1.
  Parameter good_keys : pk_t → evk_t → sk_t → bool.
  Parameter p_gate_bad : R.
  Parameter metric : message → message → 'int.
  Module Correctness := ApproxCorrectness(S).
  Import Correctness.
  Axiom kg_correct : keygen_approx_correct p_gate_bad good_keys.
  Axiom enc_correct : encrypt_approx_correct dec' metric p_gate_bad good_keys.
  Axiom eval1_correct : eval1_approx_correct dec' metric p_gate_bad good_keys.
  Axiom eval2_correct : eval2_approx_correct dec' metric p_gate_bad good_keys.
End IsApproxCorrect.