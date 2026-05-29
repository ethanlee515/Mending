From Stdlib Require Import Utf8 BinInt.
From extructures Require Import ord fset fmap.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot all_order all_algebra reals distr.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
From SSProve Require Import NominalPrelude.
From Mending.Schemes Require Import ApproxFHE.

Import PackageNotation.
Local Open Scope package_scope.
Local Open Scope sep_scope.
Local Open Scope ring_scope.

Module IndCpa(Import S: ApproxFheScheme).
  (* -- Variables and their addresses -- *)
  Definition pk_addr : Location := mkloc 100 (None : 'option pk_t).
  Definition evk_addr : Location := mkloc 101 (None : 'option evk_t).
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

  Definition IndCpa_locs : Locations := [fmap pk_addr; evk_addr].

  Definition IndCpaAdv_import :=
    [interface
      #val #[oracle_encrypt] : 'message_pair → 'ciphertext
    ].

  Definition IndCpaAdv_export :=
    [interface
      #val #[adv_guess] : 'adv_keys → 'bool
    ].

  (* IND-CPA oracle interface *)
  Definition IndCpaOracle_t := package
    (* No dependencies *)
    [interface]
    (* oracle initialization and two oracle calls *)
    [interface
      #val #[oracle_encrypt] : 'message_pair → 'ciphertext
    ].

  Definition IndCpaOracle (b: bool) : IndCpaOracle_t :=
    [package IndCpa_locs ;
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

  Definition IndCpaAdv_t := package IndCpaAdv_import IndCpaAdv_export.

  Definition IndCpaChallenger_t := package
    [interface
      #val #[adv_guess] : 'adv_keys → 'bool
    ]
    [interface
      #val #[main] : 'unit → 'bool
    ].

  Definition IndCpaChallenger : IndCpaChallenger_t :=
    [package IndCpa_locs ;
      #def #[main] (_ : 'unit) : 'bool
      {
        keys <$ (pk_t × evk_t × sk_t; keygen) ;;
        let '(pk, evk, sk) := keys in
        #put pk_addr := Some pk ;;
        #put evk_addr := Some evk ;;
        b' ← call [ adv_guess ] : { pk_t × evk_t ~> 'bool} (pk, evk) ;;
        ret b'
      }
    ].

  Definition IndCpaGame (b : bool) (Adv: nom_package) : nom_package :=
    ((IndCpaChallenger ∘ Adv)%sep ∘ IndCpaOracle b)%share.
  
  Definition game_out (b : bool) (Adv: nom_package) : distr R bool :=
    dfst (Pr_op (IndCpaGame b Adv) (main, ('unit, 'bool)) tt empty_heap).

  Definition winning_probability (Adv: nom_package) :=
    `|(game_out false Adv) true - (game_out true Adv) true|.
End IndCpa.

Module Type IsIndCpa(Import Scheme: ApproxFheScheme).
  Module IndCpaGame := IndCpa Scheme.
  Import IndCpaGame.
  Parameter security_bound : R.
  Axiom is_secure : forall (A : nom_package),
    Package IndCpaAdv_import IndCpaAdv_export A ->
    winning_probability A <= security_bound.
End IsIndCpa.
