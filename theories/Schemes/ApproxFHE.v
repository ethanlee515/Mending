From Stdlib Require Import Utf8 BinInt.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr.
Set Warnings "notation-overridden,ambiguous-paths".
From extructures Require Import ord fset fmap.
From SSProve.Crypt Require Import Axioms Package Prelude.
From SSProve Require Import NominalPrelude.
From Mending Require Import IntVec.
Import PackageNotation.
Import Order.Theory.
Local Open Scope package_scope.
Local Open Scope ring_scope.
Local Open Scope order_scope.

Definition GETA := 50%N.
Definition GETBC := 51%N.

Definition I_LDDH :=
  [interface
    [ GETA  ] : { 'unit ~> 'nat } ;
    [ GETBC ] : { 'unit ~> 'nat × 'nat }
  ].

Module Type ApproxFheScheme.
  Parameter pk_t : choice_type.
  Parameter evk_t : choice_type.
  Parameter sk_t : choice_type.
  Parameter message : choice_type.
  Parameter encryption : choice_type.
  (* Here we consider "tagged ciphertexts".
   * That is, an encryption together with an error bound.
   *
   * The `None` ciphertext should *only* come from evaluating unsupported operations.
   * e.g. out of circuit depth. *)
  Definition ciphertext := 'option (encryption × 'nat).
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

  Notation " 'pk_t " := pk_t (in custom pack_type at level 2).
  Notation " 'evk_t " := evk_t (in custom pack_type at level 2).
  Notation " 'sk_t " := sk_t (in custom pack_type at level 2).
  Notation " 'message_t " := message (in custom pack_type at level 2).
  Notation " 'ciphertext " := ciphertext (in custom pack_type at level 2).
  Notation " 'unary_gate " := unary_gate (in custom pack_type at level 2).
  Notation " 'binary_gate " := binary_gate (in custom pack_type at level 2).

  (*
  (* function IDs *)
  Definition keygen_l : nat := 100.
  Definition enc_l := 101%N.
  Definition eval1_l := 102%N.
  Definition eval2_l := 103%N.
  Definition dec_l := 104%N.

  (* IND-CPA oracle interface *)
  Definition Scheme_t := package
    [interface]
    [interface
      [ keygen_l ] : { 'unit ~> (pk_t × evk_t) × sk_t} ;
      [ enc_l ] : { pk_t × message ~> ciphertext } ;
      [ eval1_l ] : { (evk_t × unary_gate) × ciphertext ~> ciphertext } ;
      [ eval2_l ] : { ((evk_t × binary_gate) × ciphertext) × ciphertext ~> ciphertext } ;
      [ dec_l ] : { sk_t × ciphertext ~> message }
    ].

  Definition Scheme : Scheme_t := [package emptym ;
    #def #[keygen_l] (_: 'unit) : ('pk_t × 'evk_t) × 'sk_t
    {
      keys <$ ((pk_t × evk_t) × sk_t ; keygen) ;;
      let '(pk, evk, sk) := keys in
      ret (pk, evk, sk)
    } ;
    #def #[enc_l] ('(pk, m) : ('pk_t × 'message_t)) : 'ciphertext
    {
      c <$ (ciphertext; encrypt pk m) ;;
      ret c
    } ;
    #def #[eval1_l] ('(evk, g, c) : (('evk_t × 'unary_gate) × 'ciphertext)) : 'ciphertext
    {
      c' <$ (ciphertext; eval1 evk g c) ;;
      ret c'
    } ;
    #def #[eval2_l] ('(evk, g, c1, c2) : (('evk_t × 'binary_gate) × 'ciphertext) × 'ciphertext) : 'ciphertext
    {
      c <$ (ciphertext; eval2 evk g c1 c2) ;;
      ret c
    } ;
    #def #[dec_l] ('(sk, c) : 'sk_t ×'ciphertext) : 'message_t
    {
      m <$ (message; decrypt sk c) ;;
      ret m
    }
  ].
  *)

End ApproxFheScheme.

(* To talk about correctness, we need a metric. *)
Module Type ApproxFheMetric(Import Scheme: ApproxFheScheme).
  Parameter metric : message → message → nat.
  (* We only care about metrics that are locally isometric to Z^n.
   * e.g., polynomials of some fixed degree whose coefficients belong to a finite field. *)
  Parameter dim : nat.
  (* TODO Why not just assume center maps to 0^n? *)
  Parameter isometry_radius : message -> nat.
  Parameter isometry : message -> message -> dim.-tuple int.
  Parameter inverse_isometry : message -> dim.-tuple int -> message.
  Axiom inv_isoK :
    forall (center : message) (m : message),
    metric center m <= isometry_radius center ->
    inverse_isometry center (isometry center m) = m.
  Axiom isoK :
    forall (center : message) (v : dim.-tuple int),
    ivec_dist (isometry center center) v <= isometry_radius center ->
    isometry center (inverse_isometry center v) = v.
  Axiom iso_correct :
    forall (center : message) (a b : message),
    metric center a <= isometry_radius center ->
    metric center b <= isometry_radius center ->
    metric a b = ivec_dist (isometry center a) (isometry center b).
End ApproxFheMetric.

(* Correctness of each individual algorithm in the FHE 4-tuple *)
Module Type ApproxCorrectness (Import Scheme: ApproxFheScheme) (Import M: ApproxFheMetric(Scheme)).
  (* For simplicity, we consider only pure and deterministic decryption. *)
  Parameter (dec' : sk_t → ciphertext → message).
  (* We require consistency later with the given scheme. *)
  Axiom dec'_correct :
    ∀ sk c, \P_[ decrypt sk c ] (fun dec_out => ((dec_out == (dec' sk c)) : bool)) = 1.
  (* Catch-all error probability for any step going wrong.
   * Should be negligible. *)
  Parameter (p_gate_error : R).
  (* Before formalizing correctness further,
   * we need a definition for the "underlying plaintext" of a ciphertext.
   * In the approximate setting, this may not be unique. *)
  Definition is_underlying_plaintext sk (c : ciphertext) m :=
    match c with
    | None => false
    | Some (data, error_bound) => Order.le (metric (dec' sk c) m) error_bound
    end.
  (* Correctness of keygen.
   * We ask for a predicate of "good keys".
   * We then require that keygen output good keys with overwhelming probability. *)
  Parameter (good_keys : pk_t → evk_t → sk_t → bool).
  Axiom keygen_approx_correct :
    let bad_keys (keys : pk_t × evk_t × sk_t) :=
      let '(pk, evk, sk) := keys in ~~ (good_keys pk evk sk)
    in
    \P_[ keygen ] bad_keys < p_gate_error. 
  (* Conditioned on the key being good,
   * Encryption outputs good ciphertexts with overwhelming probability. *)
  Axiom encrypt_approx_correct :
    ∀ pk evk sk m,
    good_keys pk evk sk →
    let bad_encryption c :=
        ~~ (is_underlying_plaintext sk c m)
    in
    \P_[ encrypt pk m ] bad_encryption < p_gate_error.
  Axiom eval1_approx_correct :
    ∀ pk evk sk op c m,
    good_keys pk evk sk →
    is_underlying_plaintext sk c m →
    let bad_eval eval_out :=
      ~~ (is_underlying_plaintext sk eval_out (interpret_unary op m)) in
    \P_[ eval1 evk op c ] bad_eval < p_gate_error.
  Axiom eval2_approx_correct :
    ∀ pk evk sk op c1 c2 m1 m2,
    good_keys pk evk sk →
    is_underlying_plaintext sk c1 m1 →
    is_underlying_plaintext sk c2 m2 →
    let bad_eval eval_out :=
      ~~ (is_underlying_plaintext sk eval_out (interpret_binary op m1 m2))
    in
    \P_[ eval2 evk op c1 c2 ] bad_eval < p_gate_error.
End ApproxCorrectness.
