From Stdlib Require Import Utf8 BinInt.
From extructures Require Import ord fset fmap.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
From VerifiedCKKS Require Import ApproxFHE.

Import PackageNotation.
Local Open Scope package_scope.
Local Open Scope ring_scope.

Module IndCpa(Import S: ApproxFheScheme).
  (* -- Variables and their addresses -- *)
  Definition pk_addr : Location := (100, pk_t).
  Definition initialized : Location := (103, 'bool).
  (* Function labels *)
  Definition get_keys : nat := 200.
  Definition oracle_encrypt : nat := 201.
  (* Some hack that makes the oracle compile.
   * The parser can go eat it... *)
  (* Notation " 'keys " := (pk_t × evk_t × sk_t) (in custom pack_type at level 2). *)
  Notation " 'adv_keys " := (pk_t × evk_t) (in custom pack_type at level 2).
  Notation " 'message_pair " := (message × message) (in custom pack_type at level 2).
  Notation " 'ciphertext " := ciphertext (in custom pack_type at level 2).

  (* IND-CPA oracle interface *)
  Definition IndCpaOracle_t := package
    (* No dependencies *)
    [interface]
    (* public methods: two oracle calls *)
    [interface
      #val #[get_keys] : 'unit → 'adv_keys ;
      #val #[oracle_encrypt] : 'message_pair → 'ciphertext
    ].
  Definition oracle_mem_spec : Locations := [fmap pk_addr; initialized].

  Definition IndCpaOracle (b: bool) : IndCpaOracle_t :=
    [package oracle_mem_spec ;
      #def #[get_keys] (_: 'unit) : 'adv_keys
      {
        a ← get initialized ;;
        #assert (~~a) ;;
        #put initialized := true ;;
        keys <$ (pk_t × evk_t × sk_t; keygen) ;;
        let '(pk, evk, sk) := keys in
        #put pk_addr := pk ;;
        @ret (pk_t × evk_t) (pk, evk)
      } ;
      #def #[oracle_encrypt] (messages : 'message_pair) : 'ciphertext
      {
        a ← get initialized ;;
        #assert a ;;
        let (m0, m1) := messages in
        let m := if b then m1 else m0 in
        pk ← get pk_addr ;;
        c <$ (ciphertext; encrypt pk m) ;;
        @ret ciphertext c
      }
    ].
End IndCpa.

Module Type IsIndCpa(Import Scheme: ApproxFheScheme).
  Module IndCpaGame := IndCpa Scheme.
  Import IndCpaGame.
  (* Because we're in the public key setting there's no way to avoid this.
   * Pick you favorite from LWE, RLWE, or MLWE.
   * Isn't isogeny fine too?
   *
   * You can't have more than one though. That's crazy. *)
  Parameter crypto_assumption_oracles : Interface.
  Parameter crypto_assumption :
    bool -> game crypto_assumption_oracles.
  Parameter security_loss : R.
  Axiom is_secure : forall A, exists Red,
    Advantage IndCpaOracle A <=
    Advantage crypto_assumption Red + security_loss.
End IsIndCpa.
