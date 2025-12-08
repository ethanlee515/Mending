From Stdlib Require Import Utf8 BinInt.
From extructures Require Import ord fset fmap.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
From SSProve Require Import NominalPrelude.
From Mending Require Import ApproxFHE.

Import PackageNotation.
Local Open Scope package_scope.
Local Open Scope ring_scope.

Module IndCpa(Import S: ApproxFheScheme).
  (* -- Variables and their addresses -- *)
  Definition pk_addr : Location := mkloc 100 (None : 'option pk_t).
  (* Function labels *)
  Definition oracle_encrypt : nat := 200.
  Definition adv_set_keys : nat := 300.
  Definition adv_guess : nat := 301.
  Definition main : nat := 400.
  (* Some hack that makes the oracle compile.
   * The parser can go eat it... *)
  Notation " 'pk_t " := pk_t (in custom pack_type at level 2).
  Notation " 'adv_keys " := (pk_t × evk_t) (in custom pack_type at level 2).
  Notation " 'message_pair " := (message × message) (in custom pack_type at level 2).
  Notation " 'ciphertext " := ciphertext (in custom pack_type at level 2).

  (* IND-CPA oracle interface *)
  Definition IndCpaOracle_t := package
    (* No dependencies *)
    [interface]
    (* oracle initialization and two oracle calls *)
    [interface
      #val #[oracle_encrypt] : 'message_pair → 'ciphertext
    ].

  Definition IndCpaOracle (b: bool) : IndCpaOracle_t :=
    [package [fmap pk_addr] ;
      #def #[oracle_encrypt] (messages : 'message_pair) : 'ciphertext
      {
        let (m0, m1) := messages in
        let m := if b then m1 else m0 in
        o ← get pk_addr ;;
        #assert isSome o as opk ;;
        let pk := getSome o opk in
        c <$ (ciphertext; encrypt pk m) ;;
        ret c
      }
    ].

  Definition IndCpaAdv_t := package
    [interface
      #val #[oracle_encrypt] : 'message_pair → 'ciphertext
    ]
    [interface
      #val #[adv_guess] : 'adv_keys → 'bool
    ].

  Definition IndCpaChallenger_t := package
    [interface
      #val #[adv_guess] : 'adv_keys → 'bool
    ]
    [interface
      #val #[main] : 'unit → 'bool
    ].

  Definition IndCpaChallenger : IndCpaChallenger_t :=
    [package [fmap pk_addr] ;
      #def #[main] (_ : 'unit) : 'bool
      {
        keys <$ (pk_t × evk_t × sk_t; keygen) ;;
        let '(pk, evk, sk) := keys in
        #put pk_addr := Some pk ;;
        b' ← call [ adv_guess ] : { pk_t × evk_t ~> 'bool} (pk, evk) ;;
        ret true
      }
    ].
  
  Definition IndCpaGame (b : bool) (Adv: IndCpaAdv_t) :=
    IndCpaChallenger ∘ Adv ∘ IndCpaOracle b .
  
  Definition winning_probability (Adv: IndCpaAdv_t) :=
    `|Pr (IndCpaGame false Adv) true - 
      Pr (IndCpaGame true Adv) true|.
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
    winning_probability A <=
    Advantage crypto_assumption Red + security_loss.
End IsIndCpa.
