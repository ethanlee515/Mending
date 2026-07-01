From Stdlib Require Import BinInt.

(* The main reduction to IND-CPA.
 * The reduction simulates decryption results by computing in the plain:
 * Dec'(Eval(f, Enc(m)) = f(m) + e
 *)

 (* TODO FIX, broken by SSProve update *)


Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot all_order all_algebra reals distr.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
From SSProve Require Import Adv.
From SSProve Require Import NominalPrelude.
From Mending.Schemes Require Import Indcpa Indcpad ApproxFHE.
From mathcomp Require Import seq ssrZ.
From extructures Require Import ord fset fmap.
From Mending.Probability.DiscreteGaussians Require Import DiscreteGaussian.
From Mending.Schemes.Utils Require Import IntVec.
From Mending.LibExtras.SSProveExtras Require Import ChoiceVector DiscreteGaussian.
From Mending.LibExtras.MathcompExtras Require Import DTuple ListExtras.
From SSProve Require Import choice_type.

Import PackageNotation.
Local Open Scope package_scope.
Local Open Scope sep_scope.
Local Open Scope seq_scope.
Local Open Scope fset_scope.

From Mending.Constructions Require Import NoiseFlooding.

Module IndCpadSimulator (Import S: ApproxFheScheme)
  (Import Metric: ApproxFheMetric(S))
  (Import Params : NoiseFloodingParams).
  Module NF := NoiseFlooding(S)(Metric)(Params).
  Module IndCpaGame := IndCpa S.
  Module IndCpadGame := IndCpad NF.
  Import IndCpadGame.
  (* Copied from oracle *)
  Definition simulator_table_row := message × message × ciphertext.
  Definition simulator_table := chList simulator_table_row.
  Definition pk_addr : Location := mkloc 1100 (None : 'option pk_t).
  Definition evk_addr : Location := mkloc 1101 (None : 'option evk_t).
  Definition ready_addr : Location := mkloc 1103 (false : 'bool).
  Definition table_addr : Location := IndCpadGame.table_addr.
  Definition decrypt_count_addr : Location := IndCpadGame.decrypt_count_addr.
  Definition message_pair := message × message.
  Definition adv_keys := pk_t × evk_t.
  Notation " 'adv_keys " := (adv_keys) (in custom pack_type at level 2).
  Notation " 'message_pair " := (message_pair) (in custom pack_type at level 2).
  Notation " 'ciphertext " := ciphertext (in custom pack_type at level 2).
  Notation " 'adv_ev1 " := (unary_gate × 'nat) (in custom pack_type at level 2).
  Notation " 'adv_ev2 " := (binary_gate × 'nat × 'nat) (in custom pack_type at level 2).
  Notation " 'option_message " := (chOption message) (in custom pack_type at level 2).
  Definition IndCpadAdv_import :=
    IndCpadGame.IndCpadAdv_import.

  Definition IndCpadAdv_export :=
    IndCpadGame.IndCpadAdv_export.

  Definition IndCpadAdv_t := IndCpadGame.IndCpadAdv_t.

  (* Simulator interface *)
  Definition IndCpaSim_t := package
    (* Uses the IND-CPA encryption oracle. *)
    [interface
      #val #[oracle_encrypt] : 'message_pair → 'ciphertext
    ]
    (* Provides the IND-CPA-D oracle surface. *)
    IndCpadAdv_import.
  Definition oracle_mem_spec : Locations :=
    [fmap pk_addr; evk_addr; ready_addr; table_addr; decrypt_count_addr].

  (* Bridge SSProve package integers to the MathComp integer vectors used by the metric. *)
  Fixpoint toIntVec {n : nat} : chVec chInt n -> n.-tuple int :=
    match n with
    | 0 => fun _ => [tuple]
    | S n' => fun v =>
      let '(h, t) := v in
      cons_tuple (int_of_Z h) (toIntVec t)
    end.

  Fixpoint zeroChVec (n : nat) : chVec chInt n :=
    match n with
    | 0 => tt
    | S n' => (BinNums.Z0, zeroChVec n')
    end.

  Lemma dmargin_toIntVec_discrete_gaussians_zero (n : nat) (s : R) :
    dmargin (@toIntVec n) (discrete_gaussians (zeroChVec n) s) =1
      n_dg n s.
  Proof.
    elim: n=> [|n IH] y.
    - rewrite /discrete_gaussians /n_dg /nfold_distr /=.
      by rewrite dmargin_dunit.
    rewrite /discrete_gaussians /=.
    transitivity
      ((dlet (fun x : 'int =>
          \dlet_(ys <- n_dg n s)
            dunit (cons_tuple (int_of_Z x) ys))
        (ssp_dg BinNums.Z0 s)) y).
    - rewrite dmargin_dlet.
      apply: eq_in_dlet=> // x _ z.
      rewrite dmargin_dlet.
      transitivity
        ((\dlet_(ys <- dmargin (@toIntVec n)
            (discrete_gaussians (zeroChVec n) s))
          dunit (cons_tuple (int_of_Z x) ys)) z).
      + transitivity
          ((\dlet_(xs <- discrete_gaussians (zeroChVec n) s)
            dunit (cons_tuple (int_of_Z x) (toIntVec xs))) z).
        * apply: eq_in_dlet=> // xs _ w.
          by rewrite dmargin_dunit.
        rewrite -(dlet_dmargin (discrete_gaussians (zeroChVec n) s)
          (@toIntVec n)
          (fun ys => dunit (cons_tuple (int_of_Z x) ys)) z).
        by [].
      apply: eq_in_dlet.
      + by move=> ys _ w.
      exact: IH.
    have Hscalar :
        dmargin (fun z : 'int => int_of_Z z) (ssp_dg BinNums.Z0 s) =1
          centered_discrete_gaussian s.
      apply: dmargin_int_of_Z_ssp_dg_centered.
      change (int_of_Z BinNums.Z0) with (0 : int).
      by [].
    rewrite -(dlet_dmargin (ssp_dg BinNums.Z0 s)
      (fun z : 'int => int_of_Z z)
      (fun x : int =>
        \dlet_(ys <- n_dg n s) dunit (cons_tuple x ys)) y).
    rewrite /n_dg /nfold_distr /=.
    apply: eq_in_dlet.
    - move=> x _ z.
      have Hbehead :
          behead_tuple (nseq_tuple n.+1 (centered_discrete_gaussian s)) =
          nseq_tuple n (centered_discrete_gaussian s).
        by apply: val_inj.
      by rewrite Hbehead.
    exact: Hscalar.
  Qed.

  Definition IndCpadOracle (max_queries: nat) : IndCpaSim_t :=
    [package oracle_mem_spec ;
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
        o ← get evk_addr ;;
        #assert isSome o as oevk ;;
        let evk := getSome o oevk in
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
        o ← get evk_addr ;;
        #assert isSome o as oevk ;;
        let evk := getSome o oevk in
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
        decrypt_count ← get decrypt_count_addr ;;
        #assert (decrypt_count < max_queries) ;;
        #put decrypt_count_addr := decrypt_count.+1 ;;
        table ← get table_addr ;;
        #assert (i < length table) as i_in_range ;;
        let '(m0, m1, c) := nth_valid table i i_in_range in
        if (m0 == m1) then
          #assert isSome c as c_valid ;;
          let '(_, error_bound) := getSome c c_valid in
          noise <$ (chVec chInt dim;
            discrete_gaussians (zeroChVec dim)
              (noise_flooding_dg_stdev gaussian_width_multiplier error_bound)) ;;
          let res := inverse_isometry m0 (ivec_add (toIntVec noise) (isometry m0 m0)) in
          @ret ('option message) (Some res)
        else
          @ret ('option message) (None)
      }
    ].


  Definition IndCpaSimTop_t := package
    IndCpadAdv_export
    IndCpadAdv_export.

  Definition IndCpaSimTop : IndCpaSimTop_t :=
    [package oracle_mem_spec ;
      #def #[guess] ('(pk, evk) : 'adv_keys) : 'bool
      {
        ready ← get ready_addr ;;
        #assert (~~ ready) ;;
        #put ready_addr := true ;;
        #put pk_addr := Some pk ;;
        #put evk_addr := Some evk ;;
        b ← call [ guess ] : { pk_t × evk_t ~> 'bool } (pk, evk) ;;
        ret b
      }
    ].

  Definition IndCpaReduction (A : nom_package) (max_queries: nat) : nom_package :=
    ((IndCpaSimTop ∘ A)%sep ∘ IndCpadOracle max_queries)%share.

  Definition IndCpaReduction_locs (A : nom_package) (max_queries: nat) : Locations :=
    loc (IndCpaReduction A max_queries).

  Lemma IndCpaReduction_valid :
    forall (A : nom_package) max_queries,
      Package IndCpadAdv_import IndCpadAdv_export A ->
      Package IndCpaGame.IndCpaAdv_import
        IndCpaGame.IndCpaAdv_export
        (IndCpaReduction A max_queries).
  Proof.
    move=> A max_queries A_valid.
    rewrite /IndCpaReduction_locs /IndCpaReduction.
    typeclasses eauto with ssprove_valid_db.
    Unshelve.
    all: try fmap_solve.
    all: try (rewrite sep_linkE /=; apply union_fcompat; [fmap_solve|]).
    apply fseparate_compat.
    rewrite fseparate_disj.
    change (disj (fresh (IndCpaSimTop : nom_package) (A : nom_package) ∙ (A : nom_package))
      (IndCpaSimTop : nom_package)).
    rewrite disjC.
    apply fresh_disjoint.
  Qed.

(* TODO maybe adversary map from A to R in the end...
 * Should hopefully just be composition? *)
End IndCpadSimulator.
