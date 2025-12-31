(* This converts an IND-CPA scheme to an IND-CPA-D one *)

From Stdlib Require Import Utf8 BinInt.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
From Mending Require Import ApproxFHE IntVec Indcpa Indcpad DTuple DiscreteGaussian.
From extructures Require Import ord fset fmap.
Import PackageNotation.
Local Open Scope package_scope.
Local Open Scope ring_scope.

Definition n_dg (n : nat) (s : R) : distr R (n.-tuple int) :=
  nfold_distr R n (centered_discrete_gaussian R s).

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
Definition Scheme_t := Scheme.Scheme_t.
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
(* Maybe it's not ideal that decrypting an invalid ciphertext crashes the entire experiment.
 * This makes any sense only if invalid ciphertexts result only from misuse. *)
Definition decrypt (sk: sk_t) (c: ciphertext) : distr R message :=
  match c with
  | None => dnull
  | Some (_, e) =>
    \dlet_(m <- Scheme.decrypt sk c)
    \dlet_(noise <- n_dg dim (dg_stdev e))
    dunit (inverse_isometry m (ivec_add noise (isometry m m)))
  end.

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

End NoiseFlooding.
