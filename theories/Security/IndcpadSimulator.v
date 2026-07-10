From Stdlib Require Import BinInt.

(* The main reduction to IND-CPA.
 * The reduction simulates decryption results by computing in the plain:
 * Dec'(Eval(f, Enc(m)) = f(m) + e
 *)

 (* TODO FIX, broken by SSProve update *)


Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot all_order all_algebra reals distr realsum.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
From SSProve Require Import Adv.
From SSProve Require Import NominalPrelude.
From Mending.Schemes Require Import Indcpa Indcpad ApproxFHE.
From mathcomp Require Import seq ssrZ.
From extructures Require Import ord fset fmap.
From Mending.Probability.DiscreteGaussians Require Import DiscreteGaussian.
From Mending.Probability.KL Require Core.
From Mending.Schemes.Utils Require Import IntVec.
From Mending.LibExtras.SSProveExtras Require Import ChoiceVector DiscreteGaussian.
From Mending.LibExtras.MathcompExtras Require Import DTuple ListExtras.
From SSProve Require Import choice_type.

Import PackageNotation.
Import GRing.Theory Num.Theory.
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

  Fixpoint toChIntVec {n : nat} : n.-tuple int -> chVec chInt n :=
    match n with
    | 0 => fun _ => tt
    | S n' => fun v =>
      (Z_of_int (thead v), toChIntVec (behead_tuple v))
    end.

  Fixpoint zeroChVec (n : nat) : chVec chInt n :=
    match n with
    | 0 => tt
    | S n' => (BinNums.Z0, zeroChVec n')
    end.

  Lemma toIntVec_toChIntVec {n : nat} (v : n.-tuple int) :
    toIntVec (toChIntVec v) = v.
  Proof.
    elim: n v=> [|n IH] v.
    - by rewrite [v](tuple0 v).
    rewrite /= IH Z_of_intK.
    by rewrite [RHS](tuple_eta v).
  Qed.

  Lemma toChIntVec_toIntVec {n : nat} (v : chVec chInt n) :
    toChIntVec (toIntVec v) = v.
  Proof.
    elim: n v=> [|n IH] v.
    - by case: v.
    by case: v=> h t /=; rewrite theadE behead_tuple_cons int_of_ZK (IH t).
  Qed.

  Lemma toIntVec_injective {n : nat} :
    injective (@toIntVec n).
  Proof.
    move=> x y Hxy.
    by rewrite -(toChIntVec_toIntVec x) Hxy toChIntVec_toIntVec.
  Qed.

  Local Open Scope ring_scope.

  Lemma dlet_pairE {A B : choiceType}
      (P : distr R A) (Q : distr R B) (y : (A * B)%type) :
    (\dlet_(x <- P)
     \dlet_(xs <- Q)
       dunit (x, xs)) y =
      (P y.1 * Q y.2)%R.
  Proof.
    case: y=> y1 y2.
    rewrite !dletE.
    rewrite (psum_finseq (r := [:: y1])).
    - rewrite big_seq1 ger0_norm ?mulr_ge0 ?ge0_mu //.
      congr (_ * _)%R.
      rewrite dletE.
      rewrite (psum_finseq (r := [:: y2])).
      + rewrite big_seq1 dunit1E eqxx mulr1.
        by rewrite ger0_norm ?ge0_mu.
      + by [].
      move=> x Hnz.
      rewrite inE.
      apply/eqP.
      move: Hnz.
      rewrite !inE dunit1E.
      rewrite mulf_eq0 negb_or=> /andP[_ Hunit].
      move: Hunit.
      rewrite pnatr_eq0 eqb0 negbK=> /eqP Hpair.
      exact: (congr1 snd Hpair).
    - by [].
    move=> x Hnz.
    rewrite inE.
    case: (x =P y1)=> [Hx|Hx].
      by [].
    move: Hnz.
    rewrite !inE dletE.
    have Hinner0 :
        psum (fun xs : B => (Q xs * dunit (x, xs) (y1, y2))%R) = (0 : R).
      apply: psum_eq0=> xs.
      rewrite dunit1E.
      apply/eqP.
      rewrite mulf_eq0.
      apply/orP; right.
      rewrite pnatr_eq0 eqb0.
      apply/negP=> /eqP Hpair.
      have Hx_eq : x = y1 by exact: (congr1 fst Hpair).
      by case: Hx.
    by rewrite Hinner0 mulr0 eqxx.
  Qed.

  Lemma ssp_dg_zero_Z_of_intE (s : R) (x : int) :
    ssp_dg BinNums.Z0 s (Z_of_int x) =
      centered_discrete_gaussian s x.
  Proof.
    rewrite /ssp_dg.
    change (int_of_Z BinNums.Z0) with (0 : int).
    rewrite (@Core.dmargin_injectiveE R int 'int Z_of_int
      (discrete_gaussian 0 s) Z_of_int_injective x).
    by rewrite discrete_gaussian_centered_subE subr0.
  Qed.

  Lemma discrete_gaussians_zero_toChIntVecE {n : nat}
      (s : R) (y : n.-tuple int) :
    discrete_gaussians (zeroChVec n) s (toChIntVec y) =
      n_dg n s y.
  Proof.
    elim: n y=> [|n IH] y.
    - rewrite [y](tuple0 y) /discrete_gaussians /n_dg /nfold_distr /=.
      by rewrite !dunit1E eqxx.
    case/tupleP: y=> x xs.
    rewrite /discrete_gaussians /=.
    rewrite theadE.
    have Hbehead :
        behead_tuple [tuple of x :: xs] = xs.
      by apply: val_inj.
    rewrite Hbehead.
    rewrite dlet_pairE.
    rewrite ssp_dg_zero_Z_of_intE.
    rewrite n_dg_consE theadE Hbehead.
    by rewrite IH.
  Qed.

  Lemma dmargin_toIntVec_discrete_gaussians_zero (n : nat) (s : R) :
    dmargin (@toIntVec n) (discrete_gaussians (zeroChVec n) s) =1
      n_dg n s.
  Proof.
    move=> y.
    transitivity (discrete_gaussians (zeroChVec n) s (toChIntVec y)).
    - transitivity
        (dmargin (@toIntVec n) (discrete_gaussians (zeroChVec n) s)
          (toIntVec (toChIntVec y))).
      + by rewrite toIntVec_toChIntVec.
      rewrite (Core.dmargin_injectiveE
        (@toIntVec n) (discrete_gaussians (zeroChVec n) s)
        toIntVec_injective (toChIntVec y)).
      by [].
    exact: discrete_gaussians_zero_toChIntVecE.
  Qed.

  Local Close Scope ring_scope.

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
