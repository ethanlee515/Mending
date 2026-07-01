From extructures Require Import ord fset fmap.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot all_order all_algebra reals distr.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
From SSProve Require Import NominalPrelude.
From Mending.Schemes Require Import ApproxFHE.
From Mending.LibExtras.MathcompExtras Require Import ListExtras.
From mathcomp Require Import seq.
From Mending.Schemes Require Import ApproxFHE.

Import PackageNotation.
Local Open Scope package_scope.
Local Open Scope sep_scope.
Local Open Scope seq_scope.

Module IndCpad(Import S: ApproxFheScheme).
  Definition challenger_table_row := message × message × ciphertext.
  Definition challenger_table := chList challenger_table_row.
  (* -- Variables and their addresses -- *)
  Definition pk_addr : Location := mkloc 100 (None : 'option pk_t).
  Definition evk_addr : Location := mkloc 101 (None : 'option evk_t).
  Definition sk_addr : Location := mkloc 102 (None : 'option sk_t).
  Definition bit_addr : Location := mkloc 103 false.
  Definition table_addr : Location := mkloc 104 (nil : challenger_table).
  Definition decrypt_count_addr : Location := mkloc 105 0.
  (* Function labels *)
  Definition oracle_encrypt : nat := 200.
  Definition oracle_eval1 : nat := 202.
  Definition oracle_eval2 : nat := 203.
  Definition oracle_decrypt : nat := 204.
  Definition guess := 301%N.

  Notation " 'pk_t " := pk_t (in custom pack_type at level 2).
  Notation " 'evk_t " := evk_t (in custom pack_type at level 2).
  Notation " 'message " := message (in custom pack_type at level 2).
  Notation " 'ciphertext " := ciphertext (in custom pack_type at level 2).
  Notation " 'adv_keys " := (pk_t × evk_t) (in custom pack_type at level 2).

  Definition IndCpadAdv_import :=
    [interface
      [oracle_encrypt] : { message × message ~> ciphertext } ;
      [oracle_eval1] : { unary_gate × nat ~> ciphertext } ;
      [oracle_eval2] : { binary_gate × nat × nat ~> ciphertext } ;
      [oracle_decrypt] : { 'nat ~> 'option message }
    ].

  Definition IndCpadAdv_export :=
    [interface
      [guess] : { pk_t × evk_t ~> 'bool }
    ].

  (* IND-CPA oracle interface *)
  Definition IndCpaOracle_t := package
    [interface]
    [interface
      [oracle_encrypt] : { message × message ~> ciphertext } ;
      [oracle_eval1] : {unary_gate × 'nat ~> ciphertext } ;
      [oracle_eval2] : { binary_gate × 'nat× 'nat ~> ciphertext } ;
      [oracle_decrypt] :{ 'nat ~> 'option message }
    ].
  Definition oracle_mem_spec : Locations :=
    [fmap pk_addr; evk_addr; sk_addr; bit_addr; table_addr;
      decrypt_count_addr].

  Definition IndCpadOracle (max_queries : nat) : IndCpaOracle_t :=
    [package oracle_mem_spec ;
      #def #[oracle_encrypt] ('(m0, m1) : 'message × 'message ) : 'ciphertext
      {
        b ← get bit_addr ;;
        let m := if b then m1 else m0 in
        o ← get pk_addr ;;
        #assert isSome o as opk ;;
        let pk := getSome o opk in
        c <$ (ciphertext; encrypt pk m) ;;
        table ← get table_addr ;;
        let updated_table := (table ++ [ :: (m0,m1, c)]) in
        #assert ((length updated_table) <= max_queries) ;;
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
        #assert ((length updated_table) <= max_queries) ;;
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
        #assert ((length updated_table) <= max_queries) ;;
        #put table_addr := updated_table ;;
        ret c'
      } ;
      #def #[oracle_decrypt] (i: 'nat) : 'option 'message
      {
        decrypt_count ← get decrypt_count_addr ;;
        #assert (decrypt_count < max_queries) ;;
        #put decrypt_count_addr := decrypt_count.+1 ;;
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
  Definition main : nat := 503%N.

  Definition IndCpadAdv_t := package IndCpadAdv_import IndCpadAdv_export.

  Definition IndCpadChallenger_t := package
    [interface
      [guess] : { pk_t × evk_t ~> 'bool }
    ]
    [interface
      [main] : { 'unit ~> 'bool }
    ].

  Definition IndCpadChallenger : IndCpadChallenger_t :=
    [package oracle_mem_spec ;
      #def #[main] (_ : 'unit) : 'bool
      {
        b <$ ('bool; dflip (1 / 2)) ;;
        keys <$ (pk_t × evk_t × sk_t; keygen) ;;
        let '(pk, evk, sk) := keys in
        #put bit_addr := b ;;
        #put pk_addr := Some pk ;;
        #put evk_addr := Some evk ;;
        #put sk_addr := Some sk ;;
        b' ← call [ guess ] : { pk_t × evk_t ~> 'bool} (pk, evk) ;;
        ret (eq_op b' b)
      }
    ].

  Definition IndCpadGame
    (max_queries : nat) (Adv : nom_package) : nom_package :=
    ((IndCpadChallenger ∘ Adv)%sep ∘ IndCpadOracle max_queries)%share.

  Definition game_out
    (max_queries : nat) (Adv : nom_package) : distr R bool :=
    dfst (Pr_op (IndCpadGame max_queries Adv)
      (main, ('unit, 'bool)) tt empty_heap).

  Local Open Scope ring_scope.

  Definition success_probability
    (max_queries : nat) (Adv : nom_package) :=
    game_out max_queries Adv true.

  Definition winning_probability (max_queries : nat) (Adv : nom_package) :=
    `|success_probability max_queries Adv - 1 / 2|.

End IndCpad.

Local Open Scope ring_scope.

Module Type IsIndCpad(Import Scheme: ApproxFheScheme).
  Module IndCpadGame := IndCpad Scheme.
  Import IndCpadGame.
  (* Security bound depends on max queries. *)
  Parameter security_bound : nat -> R.
  Axiom is_secure : forall (A : nom_package) max_queries,
    Package IndCpadAdv_import IndCpadAdv_export A ->
    winning_probability max_queries A <= security_bound max_queries.
End IsIndCpad.
