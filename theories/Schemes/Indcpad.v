From extructures Require Import ord fset fmap.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
From Mending Require Import ApproxFHE ListExtras.
From mathcomp Require Import seq.

Import PackageNotation.
Local Open Scope package_scope.
Local Open Scope seq_scope.

Module IndCpad(Import S: ApproxFheScheme).
  Definition challenger_table_row := message × message × ciphertext.
  Definition challenger_table := chList challenger_table_row.
  (* -- Variables and their addresses -- *)
  Definition pk_addr : Location := (100, pk_t).
  Definition evk_addr : Location := (101, evk_t).
  Definition sk_addr : Location := (102, sk_t).
  Definition ready_addr : Location := (103, 'bool).
  Definition table_addr : Location := (104, challenger_table).
  (* Function labels *)
  Definition get_keys : nat := 200.
  Definition oracle_encrypt : nat := 201.
  Definition oracle_eval1 : nat := 202.
  Definition oracle_eval2 : nat := 203.
  Definition oracle_decrypt : nat := 204.
  (* Some hack that makes the oracle compile.
   * The parser can go eat it... *)
  Notation " 'adv_keys " := (pk_t × evk_t) (in custom pack_type at level 2).
  Notation " 'message_pair " := (message × message) (in custom pack_type at level 2).
  Notation " 'ciphertext " := ciphertext (in custom pack_type at level 2).
  Notation " 'adv_ev1 " := (unary_gate × 'nat) (in custom pack_type at level 2).
  Notation " 'adv_ev2 " := (binary_gate × 'nat × 'nat) (in custom pack_type at level 2).
  Notation " 'option_message " := (chOption message) (in custom pack_type at level 2).

  (* IND-CPA oracle interface *)
  Definition IndCpaOracle_t := package
    (* No dependencies *)
    [interface]
    (* public methods: two oracle calls *)
    [interface
      #val #[get_keys] : 'unit → 'adv_keys ;
      #val #[oracle_encrypt] : 'message_pair → 'ciphertext ;
      #val #[oracle_eval1] : 'adv_ev1 → 'ciphertext ;
      #val #[oracle_eval2] : 'adv_ev2 → 'ciphertext ;
      #val #[oracle_decrypt] : 'nat → 'option_message
    ].
  Definition oracle_mem_spec : Locations := [fmap pk_addr; evk_addr; sk_addr; ready_addr; table_addr].

  Definition IndCpadOracle (max_queries: nat) (b: bool) : IndCpaOracle_t :=
    [package oracle_mem_spec ;
      #def #[get_keys] (_: 'unit) : 'adv_keys
      {
        ready ← get ready_addr;;
        #assert (~~ready) ;;
        #put ready_addr := true ;;
        keys <$ (pk_t × evk_t × sk_t; keygen) ;;
        let '(pk, evk, sk) := keys in
        #put pk_addr := pk ;;
        #put evk_addr := evk ;;
        #put sk_addr := sk ;;
        @ret (pk_t × evk_t) (pk, evk)
      } ;
      #def #[oracle_encrypt] (messages : 'message_pair) : 'ciphertext
      {
        ready ← get ready_addr ;;
        #assert ready ;;
        let (m0, m1) := messages in
        let m := if b then m1 else m0 in
        pk ← get pk_addr ;;
        c <$ (ciphertext; encrypt pk m) ;;
        table ← get table_addr ;;
        let updated_table := (table ++ [ :: (m0,m1, c)]) in
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
        let m1' := interpret_unary gate m1 in
        c' <$ (ciphertext; eval1 evk gate c) ;;
        let updated_table := (table ++ [ :: (m0', m1', c')]) in
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
        let m1' := interpret_binary gate m1i m1j in
        evk ← get evk_addr ;;
        c' <$ (ciphertext; eval2 evk gate ci cj) ;;
        let updated_table := (table ++ [ :: (m0', m1', c')]) in
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
        if m0 == m1 then
          sk ← get sk_addr ;;
          m <$ (message; decrypt sk c) ;;
          @ret ('option message) (Some m)
        else
          @ret ('option message) None
      }
    ].

End IndCpad.

Local Open Scope ring_scope.

Module Type IsIndCpad(Import Scheme: ApproxFheScheme).
  Module IndCpadGame := IndCpad Scheme.
  Import IndCpadGame.
  Parameter crypto_assumption_oracles : Interface.
  Parameter crypto_assumption :
    bool -> game crypto_assumption_oracles.
  (* Security loss depends on max queries*)
  Parameter security_loss : nat -> R.
  Axiom is_secure : forall A, exists Red,
    forall max_queries,
    Advantage (IndCpadOracle max_queries) A <=
    Advantage crypto_assumption Red + (security_loss max_queries).
End IsIndCpad.