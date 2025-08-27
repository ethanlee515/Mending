(* The main reduction to IND-CPA.
 * The reduction simulates decryption results by computing in the plain:
 * Dec'(Eval(f, Enc(m)) = f(m) + e
 *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
From SSProve Require Import Adv.
From Mending Require Import Indcpad ApproxFHE.
From mathcomp Require Import seq.
From extructures Require Import ord fset fmap.
From SSProve Require Import NominalPrelude.
From Mending Require Import DiscreteGaussian.
From Mending Require Import IntVec.
From Mending Require Import ChoiceVector.
From Mending Require Import ListExtras.
From Mending Require Import Misc.
From SSProve Require Import choice_type.

Import PackageNotation.
Local Open Scope package_scope.
Local Open Scope seq_scope.
Local Open Scope fset_scope.

From Mending Require Import NoiseFlooding.

Module IndCpadSimulator (Import S: ApproxFheScheme)
  (Import Metric: ApproxFheMetric(S))
  (Import Params : NoiseFloodingParams).
  (* Copied from oracle *)
  Definition simulator_table_row := message × message × ciphertext.
  Definition simulator_table := chList simulator_table_row.
  Definition pk_addr : Location := (100, pk_t).
  Definition evk_addr : Location := (101, evk_t).
  Definition ready_addr : Location := (103, 'bool).
  Definition table_addr : Location := (104, simulator_table).
  Definition get_keys : nat := 200.
  Definition oracle_encrypt : nat := 201.
  Definition oracle_eval1 : nat := 202.
  Definition oracle_eval2 : nat := 203.
  Definition oracle_decrypt : nat := 204.
  Definition message_pair := message × message.
  Definition adv_keys := pk_t × evk_t.
  Notation " 'adv_keys " := (adv_keys) (in custom pack_type at level 2).
  Notation " 'message_pair " := (message_pair) (in custom pack_type at level 2).
  Notation " 'ciphertext " := ciphertext (in custom pack_type at level 2).
  Notation " 'adv_ev1 " := (unary_gate × 'nat) (in custom pack_type at level 2).
  Notation " 'adv_ev2 " := (binary_gate × 'nat × 'nat) (in custom pack_type at level 2).
  Notation " 'option_message " := (chOption message) (in custom pack_type at level 2).
  (* Simulator interface *)
  Definition IndCpaSim_t := package
    (* Acts as adversary to IND-CPA *)
    [interface
      #val #[get_keys] : 'unit → 'adv_keys ;
      #val #[oracle_encrypt] : 'message_pair → 'ciphertext
    ]
    (* Accepts adversary of IND-CPA-D *)
    [interface
      #val #[get_keys] : 'unit → 'adv_keys ;
      #val #[oracle_encrypt] : 'message_pair → 'ciphertext ;
      #val #[oracle_eval1] : 'adv_ev1 → 'ciphertext ;
      #val #[oracle_eval2] : 'adv_ev2 → 'ciphertext ;
      #val #[oracle_decrypt] : 'nat → 'option_message
    ].
  Definition oracle_mem_spec : Locations := [fmap pk_addr; evk_addr; ready_addr; table_addr].

  (* Some nonsense with 'int vs int vs Z... to fix with ssrZ. *)
  Parameter toIntVec : forall {n : nat}, chVec 'int n -> n.-tuple int.
  Parameter fromIntVec : forall {n : nat}, n.-tuple int -> chVec 'int n.
  (* TODO maps error bound to wide enough Gaussian *)
  Parameter noise_distr : nat -> distr R (chVec 'int dim).
  Definition IndCpadOracle (max_queries: nat) : IndCpaSim_t :=
    [package oracle_mem_spec ;
      #def #[get_keys] (_: 'unit) : 'adv_keys
      {
        ready ← get ready_addr;;
        #assert (~~ready) ;;
        #put ready_addr := true ;;
        '(pk, evk) ← call [ get_keys ] : { 'unit ~> adv_keys} tt ;;
        keys <$ (pk_t × evk_t × sk_t; keygen) ;;
        let '(pk, evk, sk) := keys in
        #put evk_addr := evk ;;
        @ret (pk_t × evk_t) (pk, evk)
      } ;
      #def #[oracle_encrypt] (messages : 'message_pair) : 'ciphertext
      {
        ready ← get ready_addr ;;
        #assert ready ;;
        c ← call [ oracle_encrypt ] : { message_pair ~> ciphertext } messages ;;
        table ← get table_addr ;;
        let '(m0, m1) := messages in
        let updated_table := (table ++ [ :: (m0, m1, c)]) in
        #assert ((length updated_table) <= max_queries) ;;
        #put table_addr := updated_table ;;
        @ret ciphertext c
      } ; 
      #def #[oracle_eval1] (a : 'adv_ev1) : 'ciphertext
      {
        ready ← get ready_addr ;;
        #assert ready ;;
        let (gate, r) := a in
        table ← get table_addr ;;
        #assert (r < length table) as r_in_range ;;
        let '(m0, m1, c) := nth_valid table r r_in_range in
        evk ← get evk_addr ;;
        let m0' := interpret_unary gate m0 in
        c' <$ (ciphertext; eval1 evk gate c) ;;
        let updated_table := (table ++ [ :: (m0', m1, c')]) in
        #assert ((length updated_table) <= max_queries) ;;
        #put table_addr := updated_table ;;
        @ret ciphertext c'
      } ;
      #def #[oracle_eval2] (a : 'adv_ev2) : 'ciphertext
      {
        ready ← get ready_addr ;;
        #assert ready ;;
        let '(gate, ri, rj) := a in
        table ← get table_addr ;;
        #assert (ri < length table) as ri_in_range ;;
        #assert (rj < length table) as rj_in_range ;;
        let '(m0i, m1i, ci) := nth_valid table ri ri_in_range in
        let '(m0j, m1j, cj) := nth_valid table rj rj_in_range in
        let m0' := interpret_binary gate m0i m0j in
        evk ← get evk_addr ;;
        c' <$ (ciphertext; eval2 evk gate ci cj) ;;
        let updated_table := (table ++ [ :: (m0', m1i, c')]) in
        #assert ((length updated_table) <= max_queries) ;;
        #put table_addr := updated_table ;;
        @ret ciphertext c'
      } ;
      #def #[oracle_decrypt] (i: 'nat) : 'option_message
      {
        ready ← get ready_addr ;;
        #assert ready ;;
        table ← get table_addr ;;
        #assert (i < length table) as i_in_range ;;
        let '(m0, m1, c) := nth_valid table i i_in_range in
        if (m0 == m1) then
          #assert (c != None) as c_valid ;;
          let '(_, error_bound) := oget_valid (c: ciphertext) c_valid in
          noise <$ (chVec 'int dim; noise_distr error_bound) ;;
          let res := inverse_isometry m0 (ivec_add (toIntVec noise) (isometry m0 m0)) in
          @ret ('option message) (Some res)
        else
          @ret ('option message) (None)
      }
    ].

(* TODO maybe adversary map from A to R in the end...
 * Should hopefully just be composition? *)
End IndCpadSimulator.


