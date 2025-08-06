From Stdlib Require Import Utf8 BinInt.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
Import PackageNotation.
Local Open Scope Z_scope.
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
  Parameter unary_gate : choice_type.
  Parameter binary_gate : choice_type.
  Parameter interpret_unary : unary_gate → message → message.
  Parameter interpret_binary : binary_gate → message → message → message.
  (* Now, the "usual" 4-tuple (keygen, enc, eval, dec). *)
  Parameter keygen : distr R (pk_t × evk_t × sk_t).
  Parameter encrypt : pk_t → message → distr R ciphertext.
  Parameter eval1 : evk_t → unary_gate → ciphertext → distr R ciphertext.
  Parameter eval2 : evk_t → binary_gate → ciphertext → ciphertext →
    distr R ciphertext.
  Parameter decrypt : sk_t → ciphertext → distr R message.
End ApproxFheScheme.

(* Correctness of each individual algorithm in the FHE 4-tuple *)
Module ApproxCorrectness(Import S: ApproxFheScheme).
  (* For simplicity, we consider only pure and deterministic decryption. *)
  Section simplified_decryption.
  (* Alternative definition of decryption.
   * Will require consistency later with the given scheme. *)
  Context (dec' : sk_t → ciphertext → message).
  Context (metric : message → message → 'option 'int).
  (* Catch-all error probability for any step going wrong.
   * Should be negligible. *)
  Context (p_gate_error : R).
  (* Before formalizing correctness further,
   * we need a definition for the "underlying plaintext" of a ciphertext.
   * In the approximate setting, this may not be unique. *)
  Definition is_underlying_plaintext sk (c : ciphertext) m :=
    match c with
    | None => false
    | Some (data, error_bound) =>
      match metric (dec' sk c) m with
      | None => false
      | Some x => x <? error_bound
      end
    end.
  (* Correctness of keygen.
   * We ask for a predicate of "good keys".
   * We then require that keygen output good keys with overwhelming probability. *)
  Context (good_keys : pk_t → evk_t → sk_t → bool).
  Definition keygen_approx_correct :=
    let bad_keys (keys : pk_t × evk_t × sk_t) :=
      let '(pk, evk, sk) := keys in ~~ (good_keys pk evk sk)
    in
    \P_[ keygen ] bad_keys < p_gate_error. 
  (* Conditioned on the key being good,
   * Encryption outputs good ciphertexts with overwhelming probability. *)
  Definition encrypt_approx_correct :=
    ∀ pk evk sk m,
    good_keys pk evk sk →
    let bad_encryption c :=
        ~~ (is_underlying_plaintext sk c m)
    in
    \P_[ encrypt pk m ] bad_encryption < p_gate_error.
  Definition eval1_approx_correct :=
    ∀ pk evk sk op c m,
    good_keys pk evk sk →
    is_underlying_plaintext sk c m →
    let bad_eval eval_out :=
      ~~ (is_underlying_plaintext sk eval_out (interpret_unary op m)) in
    \P_[ eval1 evk op c ] bad_eval < p_gate_error.
  Definition eval2_approx_correct :=
    ∀ pk evk sk op c1 c2 m1 m2,
    good_keys pk evk sk →
    is_underlying_plaintext sk c1 m1 →
    is_underlying_plaintext sk c2 m2 →
    let bad_eval eval_out :=
      ~~ (is_underlying_plaintext sk eval_out (interpret_binary op m1 m2))
    in
    \P_[ eval2 evk op c1 c2 ] bad_eval < p_gate_error.
  End simplified_decryption.
End ApproxCorrectness.

(* A FHE scheme S is approximately correct if all of its operations are. *)
Module Type IsApproxCorrect(S: ApproxFheScheme).
  Import S.
  Parameter dec' : sk_t → ciphertext → message.
  Axiom dec'_correct :
    ∀ sk c,
    \P_[ decrypt sk c ] (fun dec_out => dec_out == dec' sk c) = 1.
  Parameter good_keys : pk_t → evk_t → sk_t → bool.
  Parameter p_gate_bad : R.
  Parameter metric : message → message → 'option 'int.
  Module Correctness := ApproxCorrectness(S).
  Import Correctness.
  Axiom kg_correct :
    keygen_approx_correct p_gate_bad good_keys.
  Axiom enc_correct :
    encrypt_approx_correct dec' metric p_gate_bad good_keys.
  Axiom eval1_correct :
    eval1_approx_correct dec' metric p_gate_bad good_keys.
  Axiom eval2_correct :
    eval2_approx_correct dec' metric p_gate_bad good_keys.
End IsApproxCorrect.