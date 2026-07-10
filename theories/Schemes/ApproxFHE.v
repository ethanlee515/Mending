From Stdlib Require Import Utf8 BinInt.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot all_order all_algebra reals distr.
Set Warnings "notation-overridden,ambiguous-paths".
From extructures Require Import ord fset fmap.
From SSProve.Crypt Require Import Axioms Package Prelude.
From SSProve Require Import NominalPrelude.
From Mending.Schemes.Utils Require Import IntVec.
From Mending.Probability.KL Require Import Core.
From Mending.Probability.DiscreteGaussians Require Import DiscreteGaussian.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras DTuple.
Import PackageNotation.
Import Order.Theory.
Local Open Scope package_scope.
Local Open Scope ring_scope.
Local Open Scope order_scope.

(* function IDs *)
Definition keygen_l : nat := 100.
Definition enc_l := 101%N.
Definition eval1_l := 102%N.
Definition eval2_l := 103%N.
Definition dec_l := 104%N.

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
  Axiom keygen_lossless : dweight keygen = 1.
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

End ApproxFheScheme.

(* To talk about correctness and noise flooding, we need a message metric plus
   chart maps into integer vectors.  Route-specific chart-center and finite
   encoding evidence is carried by the security lemmas that use it. *)
Module Type ApproxFheMetric(Import Scheme: ApproxFheScheme).
  Parameter metric : message → message → nat.
  Parameter dim : nat.
  (* We only care about metrics that are locally isometric to Z^n.
   * e.g., polynomials of some fixed degree whose coefficients belong to a finite field. *)
  (* Charts are origin-centered: each chosen center maps to the zero vector. *)
  Parameter isometry : message -> message -> dim.-tuple int.
  Parameter inverse_isometry : message -> dim.-tuple int -> message.
  Axiom isometry_center0 :
    forall (center : message), isometry center center = ivec_zero.
  Axiom metric_chartE :
    forall (center m : message),
    metric center m = ivec_dist ivec_zero (isometry center m).
  Axiom inverse_isometry_shift :
    forall (centerL centerR : message) (v : dim.-tuple int),
    inverse_isometry centerR v =
    inverse_isometry centerL (ivec_add v (isometry centerL centerR)).
  Definition centered_tuple_gaussian (stdev : R) :
      distr R (dim.-tuple int) :=
    nfold_distr dim (centered_discrete_gaussian stdev).
  Definition shifted_tuple_gaussian
      (center : dim.-tuple int) (stdev : R) :
    distr R (dim.-tuple int) :=
    dmargin (fun noise => ivec_add noise center)
      (centered_tuple_gaussian stdev).
End ApproxFheMetric.

(* Correctness of each individual algorithm in the FHE 4-tuple *)
Module Type ApproxCorrectness (Import Scheme: ApproxFheScheme) (Import M: ApproxFheMetric(Scheme)).
  (* For simplicity, we consider only pure and deterministic decryption. *)
  Parameter (deterministic_dec : sk_t → ciphertext → message).
  (* We require consistency later with the given scheme. *)
  Axiom deterministic_dec_correct :
    ∀ sk c, \P_[ decrypt sk c ] (fun dec_out => ((dec_out == (deterministic_dec sk c)) : bool)) = 1.
  (* Catch-all error probability for any step going wrong.
   * Should be negligible. *)
  Parameter (p_gate_error : R).
  (* Before formalizing correctness further,
   * we need a definition for the "underlying plaintext" of a ciphertext.
   * In the approximate setting, this may not be unique. *)
  Definition is_underlying_plaintext sk (c : ciphertext) m :=
    match c with
    | None => false
    | Some (data, error_bound) => Order.le (metric (deterministic_dec sk c) m) error_bound
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

(* A support-level correctness interface for proofs that want to separate the
   cryptographic argument from approximate-correctness error accounting.
   Unlike [ApproxCorrectness], bad key/encryption/evaluation events have
   probability exactly zero, so sampled outputs can be treated as valid on
   support. *)
Module Type ApproxCorrectnessPerfect
  (Import Scheme: ApproxFheScheme) (Import M: ApproxFheMetric(Scheme)).
  (* For simplicity, we consider only pure and deterministic decryption. *)
  Parameter (deterministic_dec : sk_t → ciphertext → message).
  Axiom deterministic_dec_correct :
    ∀ sk c, \P_[ decrypt sk c ] (fun dec_out => ((dec_out == (deterministic_dec sk c)) : bool)) = 1.
  Definition is_underlying_plaintext sk (c : ciphertext) m :=
    match c with
    | None => false
    | Some (data, error_bound) => Order.le (metric (deterministic_dec sk c) m) error_bound
    end.
  Parameter (good_keys : pk_t → evk_t → sk_t → bool).
  Axiom keygen_perfect_correct :
    let bad_keys (keys : pk_t × evk_t × sk_t) :=
      let '(pk, evk, sk) := keys in ~~ (good_keys pk evk sk)
    in
    \P_[ keygen ] bad_keys = 0.
  Axiom encrypt_perfect_correct :
    ∀ pk evk sk m,
    good_keys pk evk sk →
    let bad_encryption c :=
        ~~ (is_underlying_plaintext sk c m)
    in
    \P_[ encrypt pk m ] bad_encryption = 0.
  Axiom eval1_perfect_correct :
    ∀ pk evk sk op c m,
    good_keys pk evk sk →
    is_underlying_plaintext sk c m →
    let bad_eval eval_out :=
      ~~ (is_underlying_plaintext sk eval_out (interpret_unary op m)) in
    \P_[ eval1 evk op c ] bad_eval = 0.
  Axiom eval2_perfect_correct :
    ∀ pk evk sk op c1 c2 m1 m2,
    good_keys pk evk sk →
    is_underlying_plaintext sk c1 m1 →
    is_underlying_plaintext sk c2 m2 →
    let bad_eval eval_out :=
      ~~ (is_underlying_plaintext sk eval_out (interpret_binary op m1 m2))
    in
    \P_[ eval2 evk op c1 c2 ] bad_eval = 0.

  Lemma keygen_support_good keys :
    keys \in dinsupp keygen ->
    let '(pk, evk, sk) := keys in good_keys pk evk sk.
  Proof.
    case: keys=> [[pk evk] sk] Hsupp /=.
    case Hgood: (good_keys pk evk sk)=> //.
    have Hbad : ~~ good_keys pk evk sk by rewrite Hgood.
    have Hzero :=
      pr_eq0
        (mu := keygen)
        (E := fun keys : pk_t × evk_t × sk_t =>
          let '(pk, evk, sk) := keys in ~~ good_keys pk evk sk)
        keygen_perfect_correct (x := (pk, evk, sk)) Hbad.
    by move: Hsupp; rewrite in_dinsupp Hzero eqxx.
  Qed.

  Lemma encrypt_support_underlying pk evk sk m c :
    good_keys pk evk sk ->
    c \in dinsupp (encrypt pk m) ->
    is_underlying_plaintext sk c m.
  Proof.
    move=> Hkeys Hsupp.
    case Hplain: (is_underlying_plaintext sk c m)=> //.
    have Hbad : ~~ is_underlying_plaintext sk c m by rewrite Hplain.
    have Hzero :=
      pr_eq0
        (mu := encrypt pk m)
        (E := fun c => ~~ is_underlying_plaintext sk c m)
        (encrypt_perfect_correct pk evk sk m Hkeys) (x := c) Hbad.
    by move: Hsupp; rewrite in_dinsupp Hzero eqxx.
  Qed.

  Lemma eval1_support_underlying pk evk sk op c m eval_out :
    good_keys pk evk sk ->
    is_underlying_plaintext sk c m ->
    eval_out \in dinsupp (eval1 evk op c) ->
    is_underlying_plaintext sk eval_out (interpret_unary op m).
  Proof.
    move=> Hkeys Hc Hsupp.
    case Hplain:
      (is_underlying_plaintext sk eval_out (interpret_unary op m))=> //.
    have Hbad :
        ~~ is_underlying_plaintext sk eval_out (interpret_unary op m).
      by rewrite Hplain.
    have Hzero :=
      pr_eq0
        (mu := eval1 evk op c)
        (E := fun eval_out =>
          ~~ is_underlying_plaintext sk eval_out (interpret_unary op m))
        (eval1_perfect_correct pk evk sk op c m Hkeys Hc)
        (x := eval_out) Hbad.
    by move: Hsupp; rewrite in_dinsupp Hzero eqxx.
  Qed.

  Lemma eval2_support_underlying pk evk sk op c1 c2 m1 m2 eval_out :
    good_keys pk evk sk ->
    is_underlying_plaintext sk c1 m1 ->
    is_underlying_plaintext sk c2 m2 ->
    eval_out \in dinsupp (eval2 evk op c1 c2) ->
    is_underlying_plaintext sk eval_out (interpret_binary op m1 m2).
  Proof.
    move=> Hkeys Hc1 Hc2 Hsupp.
    case Hplain:
      (is_underlying_plaintext sk eval_out (interpret_binary op m1 m2))=> //.
    have Hbad :
        ~~ is_underlying_plaintext sk eval_out
          (interpret_binary op m1 m2).
      by rewrite Hplain.
    have Hzero :=
      pr_eq0
        (mu := eval2 evk op c1 c2)
        (E := fun eval_out =>
          ~~ is_underlying_plaintext sk eval_out
            (interpret_binary op m1 m2))
        (eval2_perfect_correct pk evk sk op c1 c2 m1 m2
          Hkeys Hc1 Hc2)
        (x := eval_out) Hbad.
    by move: Hsupp; rewrite in_dinsupp Hzero eqxx.
  Qed.
End ApproxCorrectnessPerfect.
