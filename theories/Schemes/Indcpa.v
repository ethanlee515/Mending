From Stdlib Require Import Utf8 BinInt.
From extructures Require Import ord fset fmap.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
From VerifiedCKKS Require Import ApproxFHE.

Import PackageNotation.
Local Open Scope package_scope.

Module IndCpa(Import S: ApproxFheScheme).
  (* -- Variables and their addresses -- *)
  Definition pk_addr : Location := (100, pk_t).
  Definition initialized : Location := (103, 'bool).
  (* Function labels *)
  Definition get_keys : nat := 200.
  Definition oracle_encrypt : nat := 201.
  (* Some hack that makes the oracle compile.
   * The parser can go eat it... *)
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
        '(pk, evk, sk) ← keygen ;;
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
        c ← encrypt pk m ;;
        ret c
      }
    ].

End IndCpa.
