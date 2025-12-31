From extructures Require Import ord fset fmap.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
From SSProve Require Import NominalPrelude.
From Mending Require Import ApproxFHE ListExtras.
From mathcomp Require Import seq.
From Mending Require Import ApproxFHE.

Import PackageNotation.
Local Open Scope package_scope.
Local Open Scope seq_scope.

Module IndCpad(Import S: ApproxFheScheme).
  Definition challenger_table_row := message × message × ciphertext.
  Definition challenger_table := chList challenger_table_row.
  (* -- Variables and their addresses -- *)
  Definition pk_addr : Location := mkloc 100 (None : 'option pk_t).
  Definition evk_addr : Location := mkloc 101 (None : 'option evk_t).
  Definition sk_addr : Location := mkloc 102 (None : 'option sk_t).
  Definition table_addr : Location := mkloc 104 (nil : challenger_table).
  (* Function labels *)
  Definition get_keys : nat := 200.
  Definition oracle_encrypt : nat := 201.
  Definition oracle_eval1 : nat := 202.
  Definition oracle_eval2 : nat := 203.
  Definition oracle_decrypt : nat := 204.

  Notation " 'message " := message (in custom pack_type at level 2).
  Notation " 'ciphertext " := ciphertext (in custom pack_type at level 2).

  (* IND-CPA oracle interface *)
  Definition IndCpaOracle_t := package
    [interface]
    [interface
      [oracle_encrypt] : { message × message ~> ciphertext } ;
      [oracle_eval1] : {unary_gate × 'nat ~> ciphertext } ;
      [oracle_eval2] : { binary_gate × 'nat× 'nat ~> ciphertext } ;
      [oracle_decrypt] :{ 'nat ~> 'option message }
    ].
  Definition oracle_mem_spec : Locations := [fmap pk_addr; evk_addr; sk_addr; table_addr].

  Definition IndCpadOracle (b: bool) : IndCpaOracle_t :=
    [package oracle_mem_spec ;
      #def #[oracle_encrypt] ('(m0, m1) : 'message × 'message ) : 'ciphertext
      {
        let m := if b then m1 else m0 in
        o ← get pk_addr ;;
        #assert isSome o as opk ;;
        let pk := getSome o opk in
        c <$ (ciphertext; encrypt pk m) ;;
        table ← get table_addr ;;
        let updated_table := (table ++ [ :: (m0,m1, c)]) in
        #put table_addr := updated_table ;;
        ret c
      } ; 
      #def #[oracle_eval1] ('(gate, r) : 'unary_gate × 'nat) : 'ciphertext
      {
        table ← get table_addr ;;
        #assert (r < length table) as r_in_range ;;
        let '(m0, m1, c) := nth_valid table r r_in_range in
        o ← get evk_addr ;;
        #assert isSome o as oevk ;;
        let evk := getSome o oevk in
        let m0' := interpret_unary gate m0 in
        let m1' := interpret_unary gate m1 in
        c' <$ (ciphertext; eval1 evk gate c) ;;
        let updated_table := (table ++ [ :: (m0', m1', c')]) in
        #put table_addr := updated_table ;;
        ret c'
      } ;
      #def #[oracle_eval2] ('((gate, ri), rj) : ('binary_gate × 'nat) × 'nat) : 'ciphertext
      {
        table ← get table_addr ;;
        #assert (ri < length table) as ri_in_range ;;
        #assert (rj < length table) as rj_in_range ;;
        let '(m0i, m1i, ci) := nth_valid table ri ri_in_range in
        let '(m0j, m1j, cj) := nth_valid table rj rj_in_range in
        let m0' := interpret_binary gate m0i m0j in
        let m1' := interpret_binary gate m1i m1j in
        o ← get evk_addr ;;
        #assert isSome o as oevk ;;
        let evk := getSome o oevk in
        c' <$ (ciphertext; eval2 evk gate ci cj) ;;
        let updated_table := (table ++ [ :: (m0', m1', c')]) in
        #put table_addr := updated_table ;;
        ret c'
      } ;
      #def #[oracle_decrypt] (i: 'nat) : 'option 'message
      {
        table ← get table_addr ;;
        #assert (i < length table) as i_in_range ;;
        let '(m0, m1, c) := nth_valid table i i_in_range in
        if m0 == m1 then
          o ← get sk_addr ;;
          #assert isSome o as osk ;;
          let sk := getSome o osk in
          m <$ (message; decrypt sk c) ;;
          ret (Some m)
        else
          ret None
      }
    ].
    
  (* -- Adversary factorization -- *)
  (* function labels *)
  Definition send_next_input := 500%N.
  Definition receive_output := 501%N.
  Definition guess := 502%N.

  Definition FactoredAdversary_t := package
    [interface
      [oracle_encrypt] : { message × message ~> ciphertext } ;
      [oracle_eval1] : { unary_gate × nat ~> ciphertext } ;
      [oracle_eval2] : { binary_gate × nat × nat ~> ciphertext }
    ]
    [interface
      [send_next_input] : { 'unit ~> 'nat } ;
      [receive_output] : { 'option message ~> 'unit } ;
      [guess] : {'unit ~> 'bool}
    ].
  
  Definition AdvTop_t := package
    [interface
      [send_next_input] : { 'unit ~> 'nat } ;
      [receive_output] : { 'option message ~> 'unit } ;
      [oracle_decrypt] : { 'nat ~> 'option message } ;
      [guess] : { 'unit ~> 'bool }
    ]
    [interface
      [guess] : { 'unit ~> 'bool }
    ].

  Definition AdvTop (num_dec_queries : nat) : AdvTop_t :=
    [package emptym ;
      #def #[guess] (a : 'unit ) : 'bool
      {
        for_loop (fun _ =>
          i ← call [ send_next_input ] : { 'unit ~> 'nat } tt ;;
          o ← call [ oracle_decrypt ] : { 'nat ~> 'option message } i ;;
          _ ← call [ receive_output ] : { 'option message ~> 'unit } o ;;
          ret tt
        ) num_dec_queries ;;
        b ← call [ guess ] : { 'unit ~> 'bool} tt ;;
        ret b
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
  (*
  Axiom is_secure : forall A, exists Red,
    forall max_queries,
    Advantage (IndCpadOracle) A <=
    Advantage crypto_assumption Red + (security_loss max_queries).
    *)
End IsIndCpad.
