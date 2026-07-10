From Stdlib Require Import Utf8 Unicode.Utf8 BinInt Lia.
From extructures Require Import ord fset fmap fperm.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot all_order all_algebra reals distr realsum ssrZ lra.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp.algebra_tactics Require Import ring.
From SSProve.Crypt Require Import Axioms ChoiceAsOrd Couplings Package Prelude
  StateTransformingLaxMorph choice_type fmap_extra SubDistr.
From SSProve Require Import NominalPrelude.
From Mending.Schemes Require Import ApproxFHE Indcpa Indcpad.
From Mending.Constructions Require Import NoiseFlooding.
From Mending.Security Require Import IndcpadSimulator.
From Mending.Schemes.Utils Require Import IntVec.
From Mending.ProgramLogics Require Import Ae.
From Mending.ProgramLogics Require Import Hoare.
From Mending.ProgramLogics Require Import Pyth.
From Mending.ProgramLogics Require Import PythCompile.
From Mending.NextMessage Require Import Trace.
From Mending.Probability Require Import Ae OutputHeap.
From Mending.Probability.KL Require Import Core Pyth.
From Mending.Probability.DiscreteGaussians Require Import
  DiscreteGaussian DiscreteGaussianKL.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras ListExtras
  TupleExtras.
From Mending.LibExtras.SSProveExtras Require Import ChoiceVector
  DiscreteGaussian NominalExtras.

Import PackageNotation.
Import GRing.Theory Num.Theory Order.Theory Order.POrderTheory.

Local Open Scope package_scope.
Local Open Scope sep_scope.
Local Open Scope seq_scope.
Local Open Scope ring_scope.
Local Open Scope AeNotations.
Local Open Scope HoareNotations.
Local Open Scope PythNotations.

From Mending.Security.NoiseFloodingSecurity Require Import Prelude OracleSetup.

Module NoiseFloodingSecureOperationBridges
  (Import Scheme : ApproxFheScheme)
  (Import Metric : ApproxFheMetric(Scheme))
  (Import Correctness : ApproxCorrectnessPerfect(Scheme)(Metric))
  (Import IndCpaSecurity : IsIndCpa(Scheme))
  (Import Params : NoiseFloodingParams).
  Include OracleSetup.NoiseFloodingSecureOracleSetup(Scheme)(Metric)(Correctness)(IndCpaSecurity)(Params).

  Definition ind_cpad_real_encrypt_code
      (max_queries : nat) (x : message * message) : raw_code ciphertext :=
    let '(m0, m1) := x in
    b ← get IndCpadGame.bit_addr ;;
    let m := if b then m1 else m0 in
    o ← get IndCpadGame.pk_addr ;;
    #assert isSome o as opk ;;
    let pk := getSome o opk in
    c <$ (ciphertext; encrypt pk m) ;;
    table ← get IndCpadGame.table_addr ;;
    let updated_table := table ++ [:: (m0, m1, c)] in
    #put IndCpadGame.table_addr := updated_table ;;
    ret c.

  Lemma ind_cpad_real_encrypt_resolveE max_queries x :
    resolve (IndCpadGame.IndCpadOracle max_queries)
      (mkopsig IndCpadGame.oracle_encrypt
        (chProd message message) ciphertext) x =
    ind_cpad_real_encrypt_code max_queries x.
  Proof.
    case: x=> m0 m1.
    rewrite /ind_cpad_real_encrypt_code
      /IndCpadGame.IndCpadOracle /=.
    rewrite !resolve_set /=.
    rewrite coerce_kleisliE /=.
    by [].
  Qed.

  Lemma ind_cpad_sim_decrypt_encrypt_resolveE max_queries x :
    resolve (IndCpadSimDecryptOracle max_queries)
      (mkopsig IndCpadGame.oracle_encrypt
        (chProd message message) ciphertext) x =
    ind_cpad_real_encrypt_code max_queries x.
  Proof.
    case: x=> m0 m1.
    rewrite /ind_cpad_real_encrypt_code
      /IndCpadSimDecryptOracle /=.
    rewrite !resolve_set /=.
    rewrite coerce_kleisliE /=.
    by [].
  Qed.

  Definition ind_cpa_reduction_sim_encrypt_code
      (max_queries : nat) (x : message * message) : raw_code ciphertext :=
    let '(m0, m1) := x in
    ready ← get IndCpaDSim.ready_addr ;;
    #assert ready ;;
    c ← call [ IndCpaSecurity.IndCpaGame.oracle_encrypt ] :
      { chProd message message ~> ciphertext } (m0, m1) ;;
    table ← get IndCpaDSim.table_addr ;;
    let updated_table := table ++ [:: (m0, m1, c)] in
    #put IndCpaDSim.table_addr := updated_table ;;
    ret c.

  Definition ind_cpa_reduction_sim_encrypt_linked_code
      (max_queries : nat) (x : message * message) : raw_code ciphertext :=
    let '(m0, m1) := x in
    ready ← get IndCpaDSim.ready_addr ;;
    #assert ready ;;
    b ← get IndCpaSecurity.IndCpaGame.bit_addr ;;
    let m := if b then m1 else m0 in
    o ← get IndCpaSecurity.IndCpaGame.pk_addr ;;
    #assert isSome o as opk ;;
    let pk := getSome o opk in
    c <$ (ciphertext; encrypt pk m) ;;
    table ← get IndCpaDSim.table_addr ;;
    let updated_table := table ++ [:: (m0, m1, c)] in
    #put IndCpaDSim.table_addr := updated_table ;;
    ret c.

  Lemma ind_cpa_reduction_sim_encrypt_resolveE max_queries x :
    resolve (IndCpaDSim.IndCpadOracle max_queries)
      (mkopsig IndCpadGame.oracle_encrypt
        (chProd message message) ciphertext) x =
    ind_cpa_reduction_sim_encrypt_code max_queries x.
  Proof.
    case: x=> m0 m1.
    rewrite /ind_cpa_reduction_sim_encrypt_code
      /IndCpaDSim.IndCpadOracle /=.
    rewrite !resolve_set /=.
    rewrite coerce_kleisliE /=.
    by [].
  Qed.

  Lemma ind_cpa_reduction_sim_encrypt_linked_resolve_Pr_codeE
      max_queries x mem :
    Pr_code
      (code_link
        (resolve (IndCpaDSim.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_encrypt
            (chProd message message) ciphertext) x)
        IndCpaSecurity.IndCpaGame.IndCpaOracle)
      mem =1
    Pr_code (ind_cpa_reduction_sim_encrypt_linked_code max_queries x) mem.
  Proof.
    case: x=> m0 m1 out.
    rewrite ind_cpa_reduction_sim_encrypt_resolveE.
    rewrite /ind_cpa_reduction_sim_encrypt_code
      /ind_cpa_reduction_sim_encrypt_linked_code
      /IndCpaSecurity.IndCpaGame.IndCpaOracle /=.
    rewrite !Pr_code_get.
    case Hready: (get_heap mem IndCpaDSim.ready_addr)=> /=.
    - rewrite !Pr_code_get.
      rewrite /assertD /=.
      rewrite /resolve /= coerce_kleisliE /=.
      rewrite !Pr_code_get.
      case Hpk:
          (get_heap mem IndCpaSecurity.IndCpaGame.pk_addr)=> [pk|] /=.
      + first [
          rewrite !Pr_code_sample;
          apply: eq_in_dlet=> // c _ out';
          rewrite !Pr_code_get !Pr_code_put !Pr_code_ret;
          by rewrite !dlet_unit
        | rewrite /fail !Pr_code_fail;
          by rewrite !dlet_null_ext
        ].
      + rewrite Pr_code_sample dlet_null_ext Pr_code_fail.
        by [].
    - by rewrite /assertD /= !Pr_code_fail.
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_encrypt_linked_result_eq
      max_queries m0 m1 memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    dmargin fst
      (Pr_code (ind_cpad_real_encrypt_code max_queries (m0, m1)) memL) =1
    dmargin fst
      (Pr_code
        (ind_cpa_reduction_sim_encrypt_linked_code max_queries (m0, m1))
        memR).
  Proof.
    move=> Hrel out.
    rewrite !dmarginE.
    rewrite /ind_cpad_real_encrypt_code
      /ind_cpa_reduction_sim_encrypt_linked_code.
    rewrite !Pr_code_get.
    rewrite /assertD (sim_decrypt_reduction_heap_rel_ready Hrel) /=.
    have Hbit := sim_decrypt_reduction_heap_rel_bit Hrel.
    have Hpk := sim_decrypt_reduction_heap_rel_pk_outer Hrel.
    rewrite Hbit.
    rewrite Hpk.
    case HpkR:
        (get_heap memR IndCpaSecurity.IndCpaGame.pk_addr)=> [pk|] /=.
    - rewrite !Pr_code_get HpkR /assertD /=.
      rewrite !Pr_code_sample.
      rewrite !__deprecated__dlet_dlet.
      apply: eq_in_dlet=> // c _ z.
      rewrite !Pr_code_get.
      have Htable := sim_decrypt_reduction_heap_rel_table Hrel.
      rewrite -Htable.
      rewrite /= !Pr_code_put !Pr_code_ret.
      by rewrite !dlet_unit.
    - rewrite !Pr_code_get HpkR /assertD /=.
      by rewrite !Pr_code_fail !dlet_null_ext.
  Qed.

  Lemma ind_cpa_reduction_sim_encrypt_linked_code_left_support_rel
      max_queries m0 m1 memL memR outR :
    sim_decrypt_reduction_heap_rel memL memR ->
    outR \in dinsupp
      (Pr_code
        (ind_cpa_reduction_sim_encrypt_linked_code max_queries (m0, m1))
        memR) ->
    exists outL,
      outL \in dinsupp
        (Pr_code
          (resolve (IndCpadSimDecryptOracle max_queries)
            (mkopsig IndCpadGame.oracle_encrypt
              (chProd message message) ciphertext) (m0, m1))
          memL) /\
      outL.1 = outR.1 /\
      sim_decrypt_reduction_heap_rel outL.2 outR.2.
  Proof.
    move=> Hrel HoutR.
    rewrite /ind_cpa_reduction_sim_encrypt_linked_code in HoutR.
    rewrite Pr_code_get in HoutR.
    have [Hready Hafter_ready] := dinsupp_assertD _ _ _ _ HoutR.
    rewrite Pr_code_get in Hafter_ready.
    rewrite Pr_code_get in Hafter_ready.
    have [Hpk_some Hafter_pk] := dinsupp_assertD _ _ _ _ Hafter_ready.
    case HpkR:
        (get_heap memR IndCpaSecurity.IndCpaGame.pk_addr)
        Hpk_some Hafter_pk=> [pk|] Hpk_some Hafter_pk.
    - rewrite Pr_code_sample in Hafter_pk.
      have [c Hc Hinner] := @dinsupp_dlet R _ _ _ _ _ Hafter_pk.
      rewrite Pr_code_get Pr_code_put Pr_code_ret in Hinner.
      have -> :
          outR =
          (c, set_heap memR IndCpaDSim.table_addr
            (get_heap memR IndCpaDSim.table_addr ++ [:: (m0, m1, c)])).
        exact: in_dunit Hinner.
      have HpkL : get_heap memL IndCpadGame.pk_addr = Some pk.
        have Hpk := sim_decrypt_reduction_heap_rel_pk_outer Hrel.
        by rewrite Hpk HpkR.
      have [evk [sk [HevkL HskL _ _]]] :=
        challenge_heap_valid_pk_initialized memL pk
          (sim_decrypt_reduction_heap_rel_challenge_valid Hrel) HpkL.
      have HcL :
          c \in dinsupp
            (encrypt pk
              (if get_heap memL IndCpadGame.bit_addr then m1 else m0)).
        have Hbit := sim_decrypt_reduction_heap_rel_bit Hrel.
        move: Hc.
        by rewrite Hbit.
      exists
        (c, set_heap memL IndCpadGame.table_addr
          (get_heap memL IndCpadGame.table_addr ++ [:: (m0, m1, c)])).
      split.
      + rewrite ind_cpad_sim_decrypt_encrypt_resolveE.
        rewrite /ind_cpad_real_encrypt_code.
        rewrite Pr_code_get.
        rewrite Pr_code_get HpkL /assertD /=.
        rewrite Pr_code_sample.
        apply: dlet_dinsupp.
        * exact: HcL.
        * rewrite Pr_code_get Pr_code_put Pr_code_ret.
          apply/dinsuppP.
          rewrite dunit1E eqxx.
          exact/eqP/oner_neq0.
      + split; first by [].
        exact: (sim_decrypt_reduction_heap_rel_set_table_encrypt_right
          memL memR pk evk sk m0 m1 c Hrel HpkR HevkL HskL Hc).
    - by [].
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_encrypt_resolve_linked_left_support_rel
      max_queries m0 m1 memL memR outR :
    sim_decrypt_reduction_heap_rel memL memR ->
    outR \in dinsupp
      (Pr_code
        (ind_cpa_reduction_sim_encrypt_linked_code max_queries (m0, m1))
        memR) ->
    exists outL,
      outL \in dinsupp
        (Pr_code
          (resolve (IndCpadSimDecryptOracle max_queries)
            (mkopsig IndCpadGame.oracle_encrypt
              (chProd message message) ciphertext) (m0, m1))
          memL) /\
      outL.1 = outR.1 /\
      sim_decrypt_reduction_heap_rel outL.2 outR.2.
  Proof.
    exact: ind_cpa_reduction_sim_encrypt_linked_code_left_support_rel.
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_encrypt_linked_result_tv_le0
      max_queries m0 m1 memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    total_variation
      (complete
        (dmargin fst
          (Pr_code (ind_cpad_real_encrypt_code max_queries (m0, m1))
            memL)))
      (complete
        (dmargin fst
          (Pr_code
            (ind_cpa_reduction_sim_encrypt_linked_code max_queries (m0, m1))
            memR))) <= 0.
  Proof.
    move=> Hrel.
    apply: total_variation_eq_le0.
    apply: complete_ext=> out.
    exact: (ind_cpad_sim_decrypt_reduction_encrypt_linked_result_eq
      max_queries m0 m1 memL memR Hrel out).
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_encrypt_resolve_linked_result_tv_le0
      max_queries m0 m1 memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    total_variation
      (complete
        (dmargin fst
          (Pr_code
            (resolve (IndCpadSimDecryptOracle max_queries)
              (mkopsig IndCpadGame.oracle_encrypt
                (chProd message message) ciphertext) (m0, m1))
            memL)))
      (complete
        (dmargin fst
          (Pr_code
            (ind_cpa_reduction_sim_encrypt_linked_code max_queries (m0, m1))
            memR))) <= 0.
  Proof.
    move=> Hrel.
    rewrite ind_cpad_sim_decrypt_encrypt_resolveE.
    exact: (ind_cpad_sim_decrypt_reduction_encrypt_linked_result_tv_le0
      max_queries m0 m1 memL memR Hrel).
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_encrypt_resolve_linked_ae
      max_queries :
    ⊨AE_opt
    ⦃ same_input_sim_decrypt_reduction_pre ⦄
      (fun x : message * message =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_encrypt
            (chProd message message) ciphertext) x)
    ≈( 0 )
      (fun x : message * message =>
        ind_cpa_reduction_sim_encrypt_linked_code max_queries x)
    ⦃ same_result_opt ⦄.
  Proof.
    apply: additiveErrorOptSameResultTvdEqRule.
    - exact: lexx.
    - move=> memL memR [m0 m1] [m0' m1'] Hpre.
      rewrite /same_input_sim_decrypt_reduction_pre in Hpre.
      move/andP: Hpre=> [/eqP Hx Hrel].
      inversion Hx; subst m0' m1'.
      exact: (ind_cpad_sim_decrypt_reduction_encrypt_resolve_linked_result_tv_le0
        max_queries m0 m1 memL memR Hrel).
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_encrypt_resolve_linked_rel_ae
      max_queries :
    ⊨AE_opt
    ⦃ same_input_sim_decrypt_reduction_pre ⦄
      (fun x : message * message =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_encrypt
            (chProd message message) ciphertext) x)
    ≈( 0 )
      (fun x : message * message =>
        ind_cpa_reduction_sim_encrypt_linked_code max_queries x)
    ⦃ same_result_sim_decrypt_reduction_opt ⦄.
  Proof.
    split; first exact: lexx.
    move=> memL memR [m0 m1] [m0' m1'] Hpre.
    rewrite /same_input_sim_decrypt_reduction_pre in Hpre.
    move/andP: Hpre=> [/eqP Hx Hrel].
    inversion Hx; subst m0' m1'.
    rewrite ind_cpad_sim_decrypt_encrypt_resolveE.
    have Hready := sim_decrypt_reduction_heap_rel_ready Hrel.
    have Hbit := sim_decrypt_reduction_heap_rel_bit Hrel.
    have Hpk_outer := sim_decrypt_reduction_heap_rel_pk_outer Hrel.
    rewrite /ind_cpad_real_encrypt_code
      /ind_cpa_reduction_sim_encrypt_linked_code.
    case HpkR:
        (get_heap memR IndCpaSecurity.IndCpaGame.pk_addr)=> [pk|].
    - have HpkL : get_heap memL IndCpadGame.pk_addr = Some pk.
        by rewrite Hpk_outer HpkR.
      have [evk [sk [HevkL HskL _ _]]] :=
        challenge_heap_valid_pk_initialized memL pk
          (sim_decrypt_reduction_heap_rel_challenge_valid Hrel) HpkL.
      pose m := if get_heap memR IndCpaSecurity.IndCpaGame.bit_addr
        then m1 else m0.
      pose outL c :=
        (c, set_heap memL IndCpadGame.table_addr
          (get_heap memL IndCpadGame.table_addr ++ [:: (m0, m1, c)])).
      pose outR c :=
        (c, set_heap memR IndCpaDSim.table_addr
          (get_heap memR IndCpaDSim.table_addr ++ [:: (m0, m1, c)])).
      exists (shared_complete_sample_coupling (encrypt pk m) outL outR).
      split.
      + have [HmarginL HmarginR] :=
          shared_complete_sample_coupling_margins (encrypt pk m) outL outR.
        split.
        * move=> z.
          rewrite HmarginL.
          apply: complete_ext=> y.
          rewrite /m /outL.
          rewrite dmarginE.
          rewrite !Pr_code_get HpkL /assertD /=.
          rewrite Hbit.
          rewrite Pr_code_sample.
          apply: eq_in_dlet=> // c _ y'.
          by rewrite Pr_code_get Pr_code_put Pr_code_ret.
        * move=> z.
          rewrite HmarginR.
          apply: complete_ext=> y.
          rewrite /m /outR.
          rewrite dmarginE.
          rewrite Pr_code_get /assertD Hready /=.
          rewrite !Pr_code_get HpkR /assertD /=.
          rewrite Pr_code_sample.
          apply: eq_in_dlet=> // c _ y'.
          by rewrite Pr_code_get Pr_code_put Pr_code_ret.
      + rewrite subr0.
        apply: shared_complete_sample_coupling_pr_ge1.
        * move=> c Hc /=.
          rewrite /same_result_sim_decrypt_reduction_opt /outL /outR /= eqxx.
          apply/andP; split; first exact/eqP.
          have HcR :
              c \in dinsupp
                (encrypt pk
                  (if get_heap memR IndCpaSecurity.IndCpaGame.bit_addr
                   then m1 else m0)).
            exact: Hc.
          exact: (sim_decrypt_reduction_heap_rel_set_table_encrypt_right
            memL memR pk evk sk m0 m1 c Hrel HpkR HevkL HskL HcR).
        * by rewrite /same_result_sim_decrypt_reduction_opt.
    - exists (shared_complete_sample_coupling
        (dnull : {distr ciphertext / R})
        (fun c => (c, memL)) (fun c => (c, memR))).
      split.
      + have [HmarginL HmarginR] :=
          shared_complete_sample_coupling_margins
            (dnull : {distr ciphertext / R})
            (fun c => (c, memL)) (fun c => (c, memR)).
        split.
        * move=> z.
          rewrite HmarginL.
          rewrite complete_dmargin_dnull.
          rewrite /ind_cpad_real_encrypt_code.
          rewrite !Pr_code_get Hpk_outer HpkR /assertD /= Pr_code_fail.
          exact/esym/complete_dnull.
        * move=> z.
          rewrite HmarginR.
          rewrite complete_dmargin_dnull.
          rewrite /ind_cpa_reduction_sim_encrypt_linked_code.
          rewrite Pr_code_get /assertD Hready /=.
          rewrite !Pr_code_get HpkR /assertD /= Pr_code_fail.
          exact/esym/complete_dnull.
      + rewrite subr0.
        apply: shared_complete_sample_coupling_pr_ge1.
        * by move=> c Hc; move/dinsuppP: Hc; rewrite dnullE.
        * by rewrite /same_result_sim_decrypt_reduction_opt.
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_encrypt_resolve_outer_link_rel_ae
      max_queries :
    ⊨AE_opt
    ⦃ same_input_sim_decrypt_reduction_pre ⦄
      (fun x : message * message =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_encrypt
            (chProd message message) ciphertext) x)
    ≈( 0 )
      (fun x : message * message =>
        code_link
          (resolve (IndCpaDSim.IndCpadOracle max_queries)
            (mkopsig IndCpadGame.oracle_encrypt
              (chProd message message) ciphertext) x)
          IndCpaSecurity.IndCpaGame.IndCpaOracle)
    ⦃ same_result_sim_decrypt_reduction_opt ⦄.
  Proof.
    have Hbase :=
      ind_cpad_sim_decrypt_reduction_encrypt_resolve_linked_rel_ae max_queries.
    split; first exact: Hbase.1.
    move=> memL memR xL xR Hpre.
    have [d [Hd Hpost]] := Hbase.2 memL memR xL xR Hpre.
    exists d.
    split; last exact: Hpost.
    move: Hd=> [HdL HdR].
    split; first exact: HdL.
    move=> z.
    rewrite HdR.
    apply: complete_ext=> out.
    symmetry.
    exact: (ind_cpa_reduction_sim_encrypt_linked_resolve_Pr_codeE
      max_queries xR memR out).
  Qed.

  Lemma ind_cpad_real_encrypt_code_preserves_challenge_heap_valid
      max_queries :
    ⊨Hoare ⦃ fun in_mem => challenge_heap_valid in_mem.2 ⦄
      (ind_cpad_real_encrypt_code max_queries)
    ⦃ fun out_mem => challenge_heap_valid out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> [[m0 m1] mem Hinv] out Hout.
    rewrite /ind_cpad_real_encrypt_code in Hout.
    rewrite Pr_code_get in Hout.
    rewrite Pr_code_get in Hout.
    case Hpk: (get_heap mem IndCpadGame.pk_addr)=> [pk|].
    - case Hevk: (get_heap mem IndCpadGame.evk_addr)=> [evk|].
      + case Hsk: (get_heap mem IndCpadGame.sk_addr)=> [sk|].
        * rewrite Hpk /assertD /= in Hout.
          rewrite Pr_code_sample in Hout.
          have [c Hc Hinner] := @dinsupp_dlet R _ _ _ _ _ Hout.
          rewrite Pr_code_get in Hinner.
          rewrite Pr_code_put Pr_code_ret in Hinner.
          have -> :
              out =
              (c, set_heap mem IndCpadGame.table_addr
                (get_heap mem IndCpadGame.table_addr ++
                 [:: (m0, m1, c)])).
            exact: in_dunit Hinner.
          exact: (challenge_heap_valid_set_table_encrypt
            mem pk evk sk m0 m1 c Hinv Hpk Hevk Hsk Hc).
        * move: Hinv.
          rewrite /challenge_heap_valid Hpk Hevk Hsk.
          by [].
      + move: Hinv.
        rewrite /challenge_heap_valid Hpk Hevk.
        by case: (get_heap mem IndCpadGame.sk_addr).
    - rewrite Hpk /assertD /= Pr_code_fail in Hout.
      by move/dinsuppP: Hout; rewrite dnullE.
  Qed.

  Lemma ind_cpad_real_encrypt_resolve_preserves_challenge_heap_valid
      max_queries :
    ⊨Hoare ⦃ fun in_mem => challenge_heap_valid in_mem.2 ⦄
      (fun x : message * message =>
        resolve (IndCpadGame.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_encrypt
            (chProd message message) ciphertext) x)
    ⦃ fun out_mem => challenge_heap_valid out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> x mem Hinv out Hout.
    rewrite ind_cpad_real_encrypt_resolveE in Hout.
    exact: (ind_cpad_real_encrypt_code_preserves_challenge_heap_valid
      max_queries x mem Hinv out Hout).
  Qed.

  Lemma ind_cpad_sim_decrypt_encrypt_resolve_preserves_challenge_heap_valid
      max_queries :
    ⊨Hoare ⦃ fun in_mem => challenge_heap_valid in_mem.2 ⦄
      (fun x : message * message =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_encrypt
            (chProd message message) ciphertext) x)
    ⦃ fun out_mem => challenge_heap_valid out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> x mem Hinv out Hout.
    rewrite ind_cpad_sim_decrypt_encrypt_resolveE in Hout.
    exact: (ind_cpad_real_encrypt_code_preserves_challenge_heap_valid
      max_queries x mem Hinv out Hout).
  Qed.

  Definition ind_cpad_real_eval1_code
      (max_queries : nat) (x : unary_gate * nat) : raw_code ciphertext :=
    let '(gate, r) := x in
    table ← get IndCpadGame.table_addr ;;
    #assert (r < length table)%N as r_in_range ;;
    let '(m0, m1, c) := nth_valid table r r_in_range in
    o ← get IndCpadGame.evk_addr ;;
    #assert isSome o as oevk ;;
    let evk := getSome o oevk in
    let m0' := interpret_unary gate m0 in
    let m1' := interpret_unary gate m1 in
    c' <$ (ciphertext; eval1 evk gate c) ;;
    let updated_table := table ++ [:: (m0', m1', c')] in
    #put IndCpadGame.table_addr := updated_table ;;
    ret c'.

  Definition ind_cpad_real_eval2_code
      (max_queries : nat)
      (x : (binary_gate * nat) * nat) : raw_code ciphertext :=
    let '((gate, ri), rj) := x in
    table ← get IndCpadGame.table_addr ;;
    #assert (ri < length table)%N as ri_in_range ;;
    #assert (rj < length table)%N as rj_in_range ;;
    let '(m0i, m1i, ci) := nth_valid table ri ri_in_range in
    let '(m0j, m1j, cj) := nth_valid table rj rj_in_range in
    let m0' := interpret_binary gate m0i m0j in
    let m1' := interpret_binary gate m1i m1j in
    o ← get IndCpadGame.evk_addr ;;
    #assert isSome o as oevk ;;
    let evk := getSome o oevk in
    c' <$ (ciphertext; eval2 evk gate ci cj) ;;
    let updated_table := table ++ [:: (m0', m1', c')] in
    #put IndCpadGame.table_addr := updated_table ;;
    ret c'.

  Lemma ind_cpad_real_eval1_resolveE max_queries x :
    resolve (IndCpadGame.IndCpadOracle max_queries)
      (mkopsig IndCpadGame.oracle_eval1
        (chProd unary_gate nat) ciphertext) x =
    ind_cpad_real_eval1_code max_queries x.
  Proof.
    case: x=> gate r.
    rewrite /ind_cpad_real_eval1_code
      /IndCpadGame.IndCpadOracle /=.
    rewrite !resolve_set /=.
    rewrite coerce_kleisliE /=.
    by [].
  Qed.

  Lemma ind_cpad_sim_decrypt_eval1_resolveE max_queries x :
    resolve (IndCpadSimDecryptOracle max_queries)
      (mkopsig IndCpadGame.oracle_eval1
        (chProd unary_gate nat) ciphertext) x =
    ind_cpad_real_eval1_code max_queries x.
  Proof.
    case: x=> gate r.
    rewrite /ind_cpad_real_eval1_code
      /IndCpadSimDecryptOracle /=.
    rewrite !resolve_set /=.
    rewrite coerce_kleisliE /=.
    by [].
  Qed.

  Lemma ind_cpad_real_eval2_resolveE max_queries x :
    resolve (IndCpadGame.IndCpadOracle max_queries)
      (mkopsig IndCpadGame.oracle_eval2
        (chProd (chProd binary_gate nat) nat) ciphertext) x =
    ind_cpad_real_eval2_code max_queries x.
  Proof.
    case: x=> [[gate ri] rj].
    rewrite /ind_cpad_real_eval2_code
      /IndCpadGame.IndCpadOracle /=.
    rewrite !resolve_set /=.
    rewrite coerce_kleisliE /=.
    by [].
  Qed.

  Lemma ind_cpad_sim_decrypt_eval2_resolveE max_queries x :
    resolve (IndCpadSimDecryptOracle max_queries)
      (mkopsig IndCpadGame.oracle_eval2
        (chProd (chProd binary_gate nat) nat) ciphertext) x =
    ind_cpad_real_eval2_code max_queries x.
  Proof.
    case: x=> [[gate ri] rj].
    rewrite /ind_cpad_real_eval2_code
      /IndCpadSimDecryptOracle /=.
    rewrite !resolve_set /=.
    rewrite coerce_kleisliE /=.
    by [].
  Qed.

  Lemma ind_cpad_real_eval1_code_preserves_challenge_heap_valid
      max_queries :
    ⊨Hoare ⦃ fun in_mem => challenge_heap_valid in_mem.2 ⦄
      (ind_cpad_real_eval1_code max_queries)
    ⦃ fun out_mem => challenge_heap_valid out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> [[gate r] mem Hinv] out Hout.
    rewrite /ind_cpad_real_eval1_code in Hout.
    rewrite Pr_code_get in Hout.
    have [Hr Hrange] := dinsupp_assertD _ _ _ _ Hout.
    rewrite /= in Hrange.
    case Hnth:
        (nth_valid (get_heap mem IndCpadGame.table_addr) r Hr)=>
      [[m0 m1] c] in Hrange *.
    rewrite Pr_code_get in Hrange.
    have [Hoevk Hevk_body] := dinsupp_assertD _ _ _ _ Hrange.
    case Hevk: (get_heap mem IndCpadGame.evk_addr) Hoevk Hevk_body=> [evk|]
      Hoevk Hevk_body.
    - have [pk [sk [Hpk Hsk Hkeys Htable]]] :=
        challenge_heap_valid_evk_initialized mem evk Hinv Hevk.
      rewrite Pr_code_sample in Hevk_body.
      have [c' Hc' Hinner] := @dinsupp_dlet R _ _ _ _ _ Hevk_body.
      rewrite Pr_code_put Pr_code_ret in Hinner.
      have -> :
          out =
          (c', set_heap mem IndCpadGame.table_addr
            (get_heap mem IndCpadGame.table_addr ++
              [:: (interpret_unary gate m0,
                   interpret_unary gate m1, c')])).
        exact: in_dunit Hinner.
      have Hc'_eval : c' \in dinsupp (eval1 evk gate c).
        move: Hc'.
        by rewrite /=.
      have Hc'_row :
          c' \in dinsupp
            (let '(_, _, c0) :=
              nth_valid (get_heap mem IndCpadGame.table_addr) r Hr in
             eval1 evk gate c0).
        by rewrite Hnth.
      move: (challenge_heap_valid_set_table_eval1
        mem pk evk sk gate r Hr c'
        Hinv Hpk Hevk Hsk Hc'_row).
      by rewrite Hnth.
    - by [].
  Qed.

  Lemma ind_cpad_real_eval1_resolve_preserves_challenge_heap_valid
      max_queries :
    ⊨Hoare ⦃ fun in_mem => challenge_heap_valid in_mem.2 ⦄
      (fun x : unary_gate * nat =>
        resolve (IndCpadGame.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_eval1
            (chProd unary_gate nat) ciphertext) x)
    ⦃ fun out_mem => challenge_heap_valid out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> x mem Hinv out Hout.
    rewrite ind_cpad_real_eval1_resolveE in Hout.
    exact: (ind_cpad_real_eval1_code_preserves_challenge_heap_valid
      max_queries x mem Hinv out Hout).
  Qed.

  Lemma ind_cpad_sim_decrypt_eval1_resolve_preserves_challenge_heap_valid
      max_queries :
    ⊨Hoare ⦃ fun in_mem => challenge_heap_valid in_mem.2 ⦄
      (fun x : unary_gate * nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_eval1
            (chProd unary_gate nat) ciphertext) x)
    ⦃ fun out_mem => challenge_heap_valid out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> x mem Hinv out Hout.
    rewrite ind_cpad_sim_decrypt_eval1_resolveE in Hout.
    exact: (ind_cpad_real_eval1_code_preserves_challenge_heap_valid
      max_queries x mem Hinv out Hout).
  Qed.

  Definition ind_cpa_reduction_sim_eval1_code
      (max_queries : nat) (x : unary_gate * nat) : raw_code ciphertext :=
    let '(gate, r) := x in
    ready ← get IndCpaDSim.ready_addr ;;
    #assert ready ;;
    table ← get IndCpaDSim.table_addr ;;
    #assert (r < length table)%N as r_in_range ;;
    let '(m0, m1, c) := nth_valid table r r_in_range in
    o ← get IndCpaDSim.evk_addr ;;
    #assert isSome o as oevk ;;
    let evk := getSome o oevk in
    let m0' := interpret_unary gate m0 in
    let m1' := interpret_unary gate m1 in
    c' <$ (ciphertext; eval1 evk gate c) ;;
    let updated_table := table ++ [:: (m0', m1', c')] in
    #put IndCpaDSim.table_addr := updated_table ;;
    ret c'.

  Lemma ind_cpa_reduction_sim_eval1_resolveE max_queries x :
    resolve (IndCpaDSim.IndCpadOracle max_queries)
      (mkopsig IndCpadGame.oracle_eval1
        (chProd unary_gate nat) ciphertext) x =
    ind_cpa_reduction_sim_eval1_code max_queries x.
  Proof.
    case: x=> gate r.
    rewrite /ind_cpa_reduction_sim_eval1_code
      /IndCpaDSim.IndCpadOracle /=.
    rewrite !resolve_set /=.
    rewrite coerce_kleisliE /=.
    by [].
  Qed.

  Lemma ind_cpa_reduction_sim_eval1_code_closed max_queries x :
    ValidCode IndCpaDSim.oracle_mem_spec [interface]
      (ind_cpa_reduction_sim_eval1_code max_queries x).
  Proof.
    case: x=> gate r.
    rewrite /ind_cpa_reduction_sim_eval1_code.
    typeclasses eauto with ssprove_valid_db.
  Qed.

  Lemma ind_cpa_reduction_sim_eval1_resolve_link_closed max_queries x :
    code_link
      (resolve (IndCpaDSim.IndCpadOracle max_queries)
        (mkopsig IndCpadGame.oracle_eval1
          (chProd unary_gate nat) ciphertext) x)
      IndCpaSecurity.IndCpaGame.IndCpaOracle =
    resolve (IndCpaDSim.IndCpadOracle max_queries)
      (mkopsig IndCpadGame.oracle_eval1
        (chProd unary_gate nat) ciphertext) x.
  Proof.
    rewrite ind_cpa_reduction_sim_eval1_resolveE.
    rewrite (@code_link_closed ciphertext IndCpaDSim.oracle_mem_spec
      IndCpaSecurity.IndCpaGame.IndCpaOracle
      (ind_cpa_reduction_sim_eval1_code max_queries x)
      (ind_cpa_reduction_sim_eval1_code_closed max_queries x)).
    by rewrite -ind_cpa_reduction_sim_eval1_resolveE.
  Qed.

  Lemma ind_cpa_reduction_sim_eval1_code_support_rel
      max_queries gate r memL memR outR :
    sim_decrypt_reduction_heap_rel memL memR ->
    outR \in dinsupp
      (Pr_code (ind_cpa_reduction_sim_eval1_code max_queries (gate, r))
        memR) ->
    exists outL,
      outL.1 = outR.1 /\
      sim_decrypt_reduction_heap_rel outL.2 outR.2.
  Proof.
    move=> Hrel Hout.
    rewrite /ind_cpa_reduction_sim_eval1_code in Hout.
    rewrite Pr_code_get in Hout.
    have [Hready Hafter_ready] := dinsupp_assertD _ _ _ _ Hout.
    rewrite Pr_code_get in Hafter_ready.
    have [HrR Hafter_range] := dinsupp_assertD _ _ _ _ Hafter_ready.
    case HnthR:
        (nth_valid (get_heap memR IndCpaDSim.table_addr) r HrR)=>
      [[m0 m1] c] in Hafter_range *.
    rewrite Pr_code_get in Hafter_range.
    have [Hoevk Hevk_body] := dinsupp_assertD _ _ _ _ Hafter_range.
    case HevkR: (get_heap memR IndCpaDSim.evk_addr) Hoevk Hevk_body=>
      [evk|] Hoevk Hevk_body.
    - have HevkL :=
        sim_decrypt_reduction_heap_rel_evk_from_sim Hrel HevkR.
      have [pk [sk [HpkL HskL _ _]]] :=
        challenge_heap_valid_evk_initialized memL evk
          (sim_decrypt_reduction_heap_rel_challenge_valid Hrel) HevkL.
      rewrite Pr_code_sample in Hevk_body.
      have [c' Hc' Hinner] := @dinsupp_dlet R _ _ _ _ _ Hevk_body.
      rewrite Pr_code_put Pr_code_ret in Hinner.
      have -> :
          outR =
          (c', set_heap memR IndCpaDSim.table_addr
            (get_heap memR IndCpaDSim.table_addr ++
              [:: (interpret_unary gate m0,
                   interpret_unary gate m1, c')])).
        exact: in_dunit Hinner.
      have Htable := sim_decrypt_reduction_heap_rel_table Hrel.
      have HrL : (r < length (get_heap memL IndCpadGame.table_addr))%N.
        by rewrite Htable.
      have Hc'_row :
          c' \in dinsupp
            (let '(_, _, c0) :=
              nth_valid (get_heap memR IndCpaDSim.table_addr) r HrR in
             eval1 evk gate c0).
        by rewrite HnthR.
      exists
        (c', set_heap memL IndCpadGame.table_addr
          (get_heap memL IndCpadGame.table_addr ++
            [:: let '(m0L, m1L, _) :=
                  nth_valid (get_heap memL IndCpadGame.table_addr) r HrL in
                (interpret_unary gate m0L, interpret_unary gate m1L, c')])).
      split; first by [].
      move: (sim_decrypt_reduction_heap_rel_set_table_eval1_right
        memL memR pk evk sk gate r HrL HrR c'
        Hrel HpkL HevkR HskL Hc'_row).
      by rewrite HnthR.
    - by [].
  Qed.

  Lemma ind_cpa_reduction_sim_eval1_code_left_support_rel
      max_queries gate r memL memR outR :
    sim_decrypt_reduction_heap_rel memL memR ->
    outR \in dinsupp
      (Pr_code (ind_cpa_reduction_sim_eval1_code max_queries (gate, r))
        memR) ->
    exists outL,
      outL \in dinsupp
        (Pr_code
          (resolve (IndCpadSimDecryptOracle max_queries)
            (mkopsig IndCpadGame.oracle_eval1
              (chProd unary_gate nat) ciphertext) (gate, r))
          memL) /\
      outL.1 = outR.1 /\
      sim_decrypt_reduction_heap_rel outL.2 outR.2.
  Proof.
    move=> Hrel Hout.
    rewrite /ind_cpa_reduction_sim_eval1_code in Hout.
    rewrite Pr_code_get in Hout.
    have [Hready Hafter_ready] := dinsupp_assertD _ _ _ _ Hout.
    rewrite Pr_code_get in Hafter_ready.
    have [HrR Hafter_range] := dinsupp_assertD _ _ _ _ Hafter_ready.
    case HnthR:
        (nth_valid (get_heap memR IndCpaDSim.table_addr) r HrR)=>
      [[m0 m1] c] in Hafter_range *.
    rewrite Pr_code_get in Hafter_range.
    have [Hoevk Hevk_body] := dinsupp_assertD _ _ _ _ Hafter_range.
    case HevkR: (get_heap memR IndCpaDSim.evk_addr) Hoevk Hevk_body=>
      [evk|] Hoevk Hevk_body.
    - have HevkL :=
        sim_decrypt_reduction_heap_rel_evk_from_sim Hrel HevkR.
      have [pk [sk [HpkL HskL _ _]]] :=
        challenge_heap_valid_evk_initialized memL evk
          (sim_decrypt_reduction_heap_rel_challenge_valid Hrel) HevkL.
      rewrite Pr_code_sample in Hevk_body.
      have [c' Hc' Hinner] := @dinsupp_dlet R _ _ _ _ _ Hevk_body.
      rewrite Pr_code_put Pr_code_ret in Hinner.
      have -> :
          outR =
          (c', set_heap memR IndCpaDSim.table_addr
            (get_heap memR IndCpaDSim.table_addr ++
              [:: (interpret_unary gate m0,
                   interpret_unary gate m1, c')])).
        exact: in_dunit Hinner.
      have Htable := sim_decrypt_reduction_heap_rel_table Hrel.
      have HrL : (r < length (get_heap memL IndCpadGame.table_addr))%N.
        by rewrite Htable.
      have HnthL :
          nth_valid (get_heap memL IndCpadGame.table_addr) r HrL =
          (m0, m1, c).
        rewrite -(sim_decrypt_reduction_heap_rel_eval1_row HrL HrR Hrel).
        exact: HnthR.
      have Hc'_row :
          c' \in dinsupp
            (let '(_, _, c0) :=
              nth_valid (get_heap memR IndCpaDSim.table_addr) r HrR in
             eval1 evk gate c0).
        by rewrite HnthR.
      exists
        (c', set_heap memL IndCpadGame.table_addr
          (get_heap memL IndCpadGame.table_addr ++
            [:: let '(m0L, m1L, _) :=
                  nth_valid (get_heap memL IndCpadGame.table_addr) r HrL in
                (interpret_unary gate m0L, interpret_unary gate m1L, c')])).
      split.
      + rewrite ind_cpad_sim_decrypt_eval1_resolveE.
        rewrite /ind_cpad_real_eval1_code.
        rewrite Pr_code_get.
        apply: (dinsupp_assertD_intro _ _ _ _ HrL).
        rewrite HnthL.
        rewrite Pr_code_get HevkL /assertD /=.
        rewrite Pr_code_sample.
        apply: dlet_dinsupp.
        * exact: Hc'.
        * rewrite Pr_code_put Pr_code_ret.
          apply/dinsuppP.
          rewrite dunit1E eqxx.
          exact/eqP/oner_neq0.
      + split; first by [].
        move: (sim_decrypt_reduction_heap_rel_set_table_eval1_right
          memL memR pk evk sk gate r HrL HrR c'
          Hrel HpkL HevkR HskL Hc'_row).
        by rewrite HnthR.
    - by [].
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_eval1_result_eq
      max_queries gate r memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    dmargin fst
      (Pr_code (ind_cpad_real_eval1_code max_queries (gate, r)) memL) =1
    dmargin fst
      (Pr_code (ind_cpa_reduction_sim_eval1_code max_queries (gate, r))
        memR).
  Proof.
    move=> Hrel out.
    rewrite !dmarginE.
    rewrite /ind_cpad_real_eval1_code /ind_cpa_reduction_sim_eval1_code.
    rewrite !Pr_code_get.
    rewrite /assertD (sim_decrypt_reduction_heap_rel_ready Hrel) /=.
    rewrite Pr_code_get.
    have Htable := sim_decrypt_reduction_heap_rel_table Hrel.
    rewrite -Htable.
    rewrite -!dmarginE.
    apply: dmargin_fst_assertD_ext=> Hr out'.
    rewrite !dmarginE /=.
    case Hrow:
        (nth_valid (get_heap memL IndCpadGame.table_addr) r Hr)=>
      [[m0 m1] c].
    rewrite !Pr_code_get.
    have Hevk := sim_decrypt_reduction_heap_rel_evk_sim Hrel.
    rewrite -Hevk.
    case HevkL: (get_heap memL IndCpadGame.evk_addr)=> [evk|] /=.
    - rewrite !Pr_code_sample.
      rewrite !__deprecated__dlet_dlet.
      apply: eq_in_dlet=> // c' _ z.
      rewrite /= !Pr_code_put !Pr_code_ret.
      by rewrite !dlet_unit.
    - by rewrite !Pr_code_fail !dlet_null_ext.
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_eval1_result_tv_le0
      max_queries gate r memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    total_variation
      (complete
        (dmargin fst
          (Pr_code (ind_cpad_real_eval1_code max_queries (gate, r)) memL)))
      (complete
        (dmargin fst
          (Pr_code
            (ind_cpa_reduction_sim_eval1_code max_queries (gate, r))
            memR))) <= 0.
  Proof.
    move=> Hrel.
    apply: total_variation_eq_le0.
    apply: complete_ext=> out.
    exact: (ind_cpad_sim_decrypt_reduction_eval1_result_eq
      max_queries gate r memL memR Hrel out).
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_eval1_resolve_result_tv_le0
      max_queries gate r memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    total_variation
      (complete
        (dmargin fst
          (Pr_code
            (resolve (IndCpadSimDecryptOracle max_queries)
              (mkopsig IndCpadGame.oracle_eval1
                (chProd unary_gate nat) ciphertext) (gate, r))
            memL)))
      (complete
        (dmargin fst
          (Pr_code
            (resolve (IndCpaDSim.IndCpadOracle max_queries)
              (mkopsig IndCpadGame.oracle_eval1
                (chProd unary_gate nat) ciphertext) (gate, r))
            memR))) <= 0.
  Proof.
    move=> Hrel.
    rewrite ind_cpad_sim_decrypt_eval1_resolveE.
    rewrite ind_cpa_reduction_sim_eval1_resolveE.
    exact: (ind_cpad_sim_decrypt_reduction_eval1_result_tv_le0
      max_queries gate r memL memR Hrel).
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_eval1_resolve_left_support_rel
      max_queries gate r memL memR outR :
    sim_decrypt_reduction_heap_rel memL memR ->
    outR \in dinsupp
      (Pr_code
        (resolve (IndCpaDSim.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_eval1
            (chProd unary_gate nat) ciphertext) (gate, r))
        memR) ->
    exists outL,
      outL \in dinsupp
        (Pr_code
          (resolve (IndCpadSimDecryptOracle max_queries)
            (mkopsig IndCpadGame.oracle_eval1
              (chProd unary_gate nat) ciphertext) (gate, r))
          memL) /\
      outL.1 = outR.1 /\
      sim_decrypt_reduction_heap_rel outL.2 outR.2.
  Proof.
    move=> Hrel HoutR.
    rewrite ind_cpa_reduction_sim_eval1_resolveE in HoutR.
    exact: (ind_cpa_reduction_sim_eval1_code_left_support_rel
      max_queries gate r memL memR outR Hrel HoutR).
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_eval1_resolve_ae
      max_queries :
    ⊨AE_opt
    ⦃ same_input_sim_decrypt_reduction_pre ⦄
      (fun x : unary_gate * nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_eval1
            (chProd unary_gate nat) ciphertext) x)
    ≈( 0 )
      (fun x : unary_gate * nat =>
        resolve (IndCpaDSim.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_eval1
            (chProd unary_gate nat) ciphertext) x)
    ⦃ same_result_opt ⦄.
  Proof.
    apply: additiveErrorOptSameResultTvdEqRule.
    - exact: lexx.
    - move=> memL memR [gate r] [gate' r'] Hpre.
      rewrite /same_input_sim_decrypt_reduction_pre in Hpre.
      move/andP: Hpre=> [/eqP Hx Hrel].
      inversion Hx; subst gate' r'.
      exact: (ind_cpad_sim_decrypt_reduction_eval1_resolve_result_tv_le0
        max_queries gate r memL memR Hrel).
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_eval1_resolve_rel_ae
      max_queries :
    ⊨AE_opt
    ⦃ same_input_sim_decrypt_reduction_pre ⦄
      (fun x : unary_gate * nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_eval1
            (chProd unary_gate nat) ciphertext) x)
    ≈( 0 )
      (fun x : unary_gate * nat =>
        resolve (IndCpaDSim.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_eval1
            (chProd unary_gate nat) ciphertext) x)
    ⦃ same_result_sim_decrypt_reduction_opt ⦄.
  Proof.
    split; first exact: lexx.
    move=> memL memR [gate r] [gate' r'] Hpre.
    rewrite /same_input_sim_decrypt_reduction_pre in Hpre.
    move/andP: Hpre=> [/eqP Hx Hrel].
    inversion Hx; subst gate' r'.
    rewrite ind_cpad_sim_decrypt_eval1_resolveE.
    rewrite ind_cpa_reduction_sim_eval1_resolveE.
    rewrite /ind_cpad_real_eval1_code /ind_cpa_reduction_sim_eval1_code.
    rewrite Pr_code_get.
    rewrite Pr_code_get /assertD (sim_decrypt_reduction_heap_rel_ready Hrel) /=.
    rewrite Pr_code_get.
    have Htable := sim_decrypt_reduction_heap_rel_table Hrel.
    rewrite -Htable.
    apply: assertD_same_guard_coupling; first exact: lexx.
    - move=> HrL_eq HrR_eq.
      pose HrL := bool_eq_true_is_true _ HrL_eq.
      have HrR_true :
          (r < length (get_heap memR IndCpaDSim.table_addr))%N = true.
        by rewrite -Htable.
      pose HrR := bool_eq_true_is_true _ HrR_true.
      case Hrow:
          (nth_valid (get_heap memL IndCpadGame.table_addr) r HrL)=>
        [[m0 m1] c].
      have HrowR :
          nth_valid (get_heap memR IndCpaDSim.table_addr) r HrR =
          (m0, m1, c).
        rewrite (sim_decrypt_reduction_heap_rel_eval1_row HrL HrR Hrel).
        exact: Hrow.
      rewrite (nth_valid_irrel
        (get_heap memL IndCpadGame.table_addr) r _ HrL).
      rewrite Hrow.
      rewrite !Pr_code_get.
      case HevkR: (get_heap memR IndCpaDSim.evk_addr)=> [evk|].
      + have HevkL :=
          sim_decrypt_reduction_heap_rel_evk_from_sim Hrel HevkR.
        have [pk [sk [HpkL HskL _ _]]] :=
          challenge_heap_valid_evk_initialized memL evk
            (sim_decrypt_reduction_heap_rel_challenge_valid Hrel) HevkL.
        rewrite HevkL /assertD /=.
        pose outL c' :=
          (c', set_heap memL IndCpadGame.table_addr
            (get_heap memL IndCpadGame.table_addr ++
              [:: (interpret_unary gate m0,
                   interpret_unary gate m1, c')])).
        pose outR c' :=
          (c', set_heap memR IndCpaDSim.table_addr
            (get_heap memR IndCpaDSim.table_addr ++
              [:: (interpret_unary gate m0,
                   interpret_unary gate m1, c')])).
        exists (shared_complete_sample_coupling
          (eval1 evk gate c) outL outR).
        split.
        * have [HmarginL HmarginR] :=
            shared_complete_sample_coupling_margins
              (eval1 evk gate c) outL outR.
          split.
          -- move=> z.
             rewrite HmarginL.
             apply: complete_distr_ext=> y.
             rewrite /outL dmarginE Pr_code_sample.
             apply: eq_in_dlet=> // c' _ y'.
             by rewrite Pr_code_put Pr_code_ret.
          -- move=> z.
             rewrite HmarginR.
             apply: complete_distr_ext=> y.
             rewrite /outR dmarginE.
             rewrite (nth_valid_irrel
               (get_heap memL IndCpadGame.table_addr) r _ HrL).
             rewrite Hrow Htable.
             rewrite Pr_code_get HevkR /assertD /= Pr_code_sample.
             apply: eq_in_dlet=> // c' _ y'.
             by rewrite Pr_code_put Pr_code_ret.
        * rewrite subr0.
          apply: shared_complete_sample_coupling_pr_ge1.
          -- move=> c' Hc' /=.
             rewrite /same_result_sim_decrypt_reduction_opt /outL /outR /= eqxx.
             apply/andP; split; first exact/eqP.
             have Hc'_row :
                 c' \in dinsupp
                   (let '(_, _, c0) :=
                     nth_valid (get_heap memR IndCpaDSim.table_addr) r HrR in
                    eval1 evk gate c0).
               by rewrite HrowR.
             move: (sim_decrypt_reduction_heap_rel_set_table_eval1_right
               memL memR pk evk sk gate r HrL HrR c'
               Hrel HpkL HevkR HskL Hc'_row).
             by rewrite Hrow HrowR.
          -- by rewrite /same_result_sim_decrypt_reduction_opt.
      + have HevkL_none :
            get_heap memL IndCpadGame.evk_addr = None.
          have Hevk := sim_decrypt_reduction_heap_rel_evk_sim Hrel.
          by rewrite Hevk HevkR.
        rewrite HevkL_none /assertD /= !Pr_code_fail.
        exists (dunit (None, None)).
        split.
        * split.
          -- move=> z.
             rewrite dmargin_dunit.
             exact/esym/complete_dnull.
          -- move=> z.
             rewrite dmargin_dunit.
             rewrite (nth_valid_irrel
               (get_heap memL IndCpadGame.table_addr) r _ HrL).
             rewrite Hrow Htable.
             rewrite Pr_code_get HevkR /assertD /= Pr_code_fail.
             exact/esym/complete_dnull.
        * rewrite pr_dunit /same_result_sim_decrypt_reduction_opt /=.
          by rewrite lerBlDr lerDl.
    - by rewrite /same_result_sim_decrypt_reduction_opt.
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_eval1_resolve_outer_link_rel_ae
      max_queries :
    ⊨AE_opt
    ⦃ same_input_sim_decrypt_reduction_pre ⦄
      (fun x : unary_gate * nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_eval1
            (chProd unary_gate nat) ciphertext) x)
    ≈( 0 )
      (fun x : unary_gate * nat =>
        code_link
          (resolve (IndCpaDSim.IndCpadOracle max_queries)
            (mkopsig IndCpadGame.oracle_eval1
              (chProd unary_gate nat) ciphertext) x)
          IndCpaSecurity.IndCpaGame.IndCpaOracle)
    ⦃ same_result_sim_decrypt_reduction_opt ⦄.
  Proof.
    have Hbase :=
      ind_cpad_sim_decrypt_reduction_eval1_resolve_rel_ae max_queries.
    split; first exact: Hbase.1.
    move=> memL memR xL xR Hpre.
    have [d [Hd Hpost]] := Hbase.2 memL memR xL xR Hpre.
    exists d.
    split; last exact: Hpost.
    move: Hd=> [HdL HdR].
    split; first exact: HdL.
    rewrite ind_cpa_reduction_sim_eval1_resolve_link_closed.
    exact: HdR.
  Qed.

  Lemma ind_cpad_real_eval2_code_preserves_challenge_heap_valid
      max_queries :
    ⊨Hoare ⦃ fun in_mem => challenge_heap_valid in_mem.2 ⦄
      (ind_cpad_real_eval2_code max_queries)
    ⦃ fun out_mem => challenge_heap_valid out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> [[[gate ri] rj] mem Hinv] out Hout.
    rewrite /ind_cpad_real_eval2_code in Hout.
    rewrite Pr_code_get in Hout.
    have [Hri Hafter_ri] := dinsupp_assertD _ _ _ _ Hout.
    rewrite /= in Hafter_ri.
    have [Hrj Hafter_rj] := dinsupp_assertD _ _ _ _ Hafter_ri.
    rewrite /= in Hafter_rj.
    case Hnthi:
        (nth_valid (get_heap mem IndCpadGame.table_addr) ri Hri)=>
      [[m0i m1i] ci] in Hafter_rj *.
    case Hnthj:
        (nth_valid (get_heap mem IndCpadGame.table_addr) rj Hrj)=>
      [[m0j m1j] cj] in Hafter_rj *.
    rewrite Pr_code_get in Hafter_rj.
    have [Hoevk Hevk_body] := dinsupp_assertD _ _ _ _ Hafter_rj.
    case Hevk: (get_heap mem IndCpadGame.evk_addr) Hoevk Hevk_body=> [evk|]
      Hoevk Hevk_body.
    - have [pk [sk [Hpk Hsk Hkeys Htable]]] :=
        challenge_heap_valid_evk_initialized mem evk Hinv Hevk.
      rewrite Pr_code_sample in Hevk_body.
      have [c' Hc' Hinner] := @dinsupp_dlet R _ _ _ _ _ Hevk_body.
      rewrite Pr_code_put Pr_code_ret in Hinner.
      have -> :
          out =
          (c', set_heap mem IndCpadGame.table_addr
            (get_heap mem IndCpadGame.table_addr ++
              [:: (interpret_binary gate m0i m0j,
                   interpret_binary gate m1i m1j, c')])).
        exact: in_dunit Hinner.
      have Hc'_eval : c' \in dinsupp (eval2 evk gate ci cj).
        move: Hc'.
        by rewrite /=.
      have Hc'_row :
          c' \in dinsupp
            (let '(_, _, ci0) :=
              nth_valid (get_heap mem IndCpadGame.table_addr) ri Hri in
             let '(_, _, cj0) :=
              nth_valid (get_heap mem IndCpadGame.table_addr) rj Hrj in
             eval2 evk gate ci0 cj0).
        by rewrite Hnthi Hnthj.
      move: (challenge_heap_valid_set_table_eval2
        mem pk evk sk gate ri rj Hri Hrj c'
        Hinv Hpk Hevk Hsk Hc'_row).
      by rewrite Hnthi Hnthj.
    - by [].
  Qed.

  Lemma ind_cpad_real_eval2_resolve_preserves_challenge_heap_valid
      max_queries :
    ⊨Hoare ⦃ fun in_mem => challenge_heap_valid in_mem.2 ⦄
      (fun x : (binary_gate * nat) * nat =>
        resolve (IndCpadGame.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_eval2
            (chProd (chProd binary_gate nat) nat) ciphertext) x)
    ⦃ fun out_mem => challenge_heap_valid out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> x mem Hinv out Hout.
    rewrite ind_cpad_real_eval2_resolveE in Hout.
    exact: (ind_cpad_real_eval2_code_preserves_challenge_heap_valid
      max_queries x mem Hinv out Hout).
  Qed.

  Lemma ind_cpad_sim_decrypt_eval2_resolve_preserves_challenge_heap_valid
      max_queries :
    ⊨Hoare ⦃ fun in_mem => challenge_heap_valid in_mem.2 ⦄
      (fun x : (binary_gate * nat) * nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_eval2
            (chProd (chProd binary_gate nat) nat) ciphertext) x)
    ⦃ fun out_mem => challenge_heap_valid out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> x mem Hinv out Hout.
    rewrite ind_cpad_sim_decrypt_eval2_resolveE in Hout.
    exact: (ind_cpad_real_eval2_code_preserves_challenge_heap_valid
      max_queries x mem Hinv out Hout).
  Qed.

  Definition ind_cpa_reduction_sim_eval2_code
      (max_queries : nat)
      (x : (binary_gate * nat) * nat) : raw_code ciphertext :=
    let '((gate, ri), rj) := x in
    ready ← get IndCpaDSim.ready_addr ;;
    #assert ready ;;
    table ← get IndCpaDSim.table_addr ;;
    #assert (ri < length table)%N as ri_in_range ;;
    #assert (rj < length table)%N as rj_in_range ;;
    let '(m0i, m1i, ci) := nth_valid table ri ri_in_range in
    let '(m0j, m1j, cj) := nth_valid table rj rj_in_range in
    let m0' := interpret_binary gate m0i m0j in
    let m1' := interpret_binary gate m1i m1j in
    o ← get IndCpaDSim.evk_addr ;;
    #assert isSome o as oevk ;;
    let evk := getSome o oevk in
    c' <$ (ciphertext; eval2 evk gate ci cj) ;;
    let updated_table := table ++ [:: (m0', m1', c')] in
    #put IndCpaDSim.table_addr := updated_table ;;
    ret c'.

  Lemma ind_cpa_reduction_sim_eval2_resolveE max_queries x :
    resolve (IndCpaDSim.IndCpadOracle max_queries)
      (mkopsig IndCpadGame.oracle_eval2
        (chProd (chProd binary_gate nat) nat) ciphertext) x =
    ind_cpa_reduction_sim_eval2_code max_queries x.
  Proof.
    case: x=> [[gate ri] rj].
    rewrite /ind_cpa_reduction_sim_eval2_code
      /IndCpaDSim.IndCpadOracle /=.
    rewrite !resolve_set /=.
    rewrite coerce_kleisliE /=.
    by [].
  Qed.

  Lemma ind_cpa_reduction_sim_eval2_code_closed max_queries x :
    ValidCode IndCpaDSim.oracle_mem_spec [interface]
      (ind_cpa_reduction_sim_eval2_code max_queries x).
  Proof.
    case: x=> [[gate ri] rj].
    rewrite /ind_cpa_reduction_sim_eval2_code.
    typeclasses eauto with ssprove_valid_db.
  Qed.

  Lemma ind_cpa_reduction_sim_eval2_resolve_link_closed max_queries x :
    code_link
      (resolve (IndCpaDSim.IndCpadOracle max_queries)
        (mkopsig IndCpadGame.oracle_eval2
          (chProd (chProd binary_gate nat) nat) ciphertext) x)
      IndCpaSecurity.IndCpaGame.IndCpaOracle =
    resolve (IndCpaDSim.IndCpadOracle max_queries)
      (mkopsig IndCpadGame.oracle_eval2
        (chProd (chProd binary_gate nat) nat) ciphertext) x.
  Proof.
    rewrite ind_cpa_reduction_sim_eval2_resolveE.
    rewrite (@code_link_closed ciphertext IndCpaDSim.oracle_mem_spec
      IndCpaSecurity.IndCpaGame.IndCpaOracle
      (ind_cpa_reduction_sim_eval2_code max_queries x)
      (ind_cpa_reduction_sim_eval2_code_closed max_queries x)).
    by rewrite -ind_cpa_reduction_sim_eval2_resolveE.
  Qed.

  Lemma ind_cpa_reduction_sim_eval2_code_support_rel
      max_queries gate ri rj memL memR outR :
    sim_decrypt_reduction_heap_rel memL memR ->
    outR \in dinsupp
      (Pr_code
        (ind_cpa_reduction_sim_eval2_code max_queries ((gate, ri), rj))
        memR) ->
    exists outL,
      outL.1 = outR.1 /\
      sim_decrypt_reduction_heap_rel outL.2 outR.2.
  Proof.
    move=> Hrel Hout.
    rewrite /ind_cpa_reduction_sim_eval2_code in Hout.
    rewrite Pr_code_get in Hout.
    have [Hready Hafter_ready] := dinsupp_assertD _ _ _ _ Hout.
    rewrite Pr_code_get in Hafter_ready.
    have [HriR Hafter_ri] := dinsupp_assertD _ _ _ _ Hafter_ready.
    rewrite /= in Hafter_ri.
    have [HrjR Hafter_rj] := dinsupp_assertD _ _ _ _ Hafter_ri.
    rewrite /= in Hafter_rj.
    case HnthiR:
        (nth_valid (get_heap memR IndCpaDSim.table_addr) ri HriR)=>
      [[m0i m1i] ci] in Hafter_rj *.
    case HnthjR:
        (nth_valid (get_heap memR IndCpaDSim.table_addr) rj HrjR)=>
      [[m0j m1j] cj] in Hafter_rj *.
    rewrite Pr_code_get in Hafter_rj.
    have [Hoevk Hevk_body] := dinsupp_assertD _ _ _ _ Hafter_rj.
    case HevkR: (get_heap memR IndCpaDSim.evk_addr) Hoevk Hevk_body=>
      [evk|] Hoevk Hevk_body.
    - have HevkL :=
        sim_decrypt_reduction_heap_rel_evk_from_sim Hrel HevkR.
      have [pk [sk [HpkL HskL _ _]]] :=
        challenge_heap_valid_evk_initialized memL evk
          (sim_decrypt_reduction_heap_rel_challenge_valid Hrel) HevkL.
      rewrite Pr_code_sample in Hevk_body.
      have [c' Hc' Hinner] := @dinsupp_dlet R _ _ _ _ _ Hevk_body.
      rewrite Pr_code_put Pr_code_ret in Hinner.
      have -> :
          outR =
          (c', set_heap memR IndCpaDSim.table_addr
            (get_heap memR IndCpaDSim.table_addr ++
              [:: (interpret_binary gate m0i m0j,
                   interpret_binary gate m1i m1j, c')])).
        exact: in_dunit Hinner.
      have Htable := sim_decrypt_reduction_heap_rel_table Hrel.
      have HriL :
          (ri < length (get_heap memL IndCpadGame.table_addr))%N.
        by rewrite Htable.
      have HrjL :
          (rj < length (get_heap memL IndCpadGame.table_addr))%N.
        by rewrite Htable.
      have Hc'_row :
          c' \in dinsupp
            (let '(_, _, ci0) :=
              nth_valid (get_heap memR IndCpaDSim.table_addr) ri HriR in
             let '(_, _, cj0) :=
              nth_valid (get_heap memR IndCpaDSim.table_addr) rj HrjR in
             eval2 evk gate ci0 cj0).
        by rewrite HnthiR HnthjR.
      exists
        (c', set_heap memL IndCpadGame.table_addr
          (get_heap memL IndCpadGame.table_addr ++
            [:: let '(m0iL, m1iL, _) :=
                  nth_valid (get_heap memL IndCpadGame.table_addr)
                    ri HriL in
                let '(m0jL, m1jL, _) :=
                  nth_valid (get_heap memL IndCpadGame.table_addr)
                    rj HrjL in
                (interpret_binary gate m0iL m0jL,
                 interpret_binary gate m1iL m1jL, c')])).
      split; first by [].
      move: (sim_decrypt_reduction_heap_rel_set_table_eval2_right
        memL memR pk evk sk gate ri rj HriL HrjL HriR HrjR c'
        Hrel HpkL HevkR HskL Hc'_row).
      by rewrite HnthiR HnthjR.
    - by [].
  Qed.

  Lemma ind_cpa_reduction_sim_eval2_code_left_support_rel
      max_queries gate ri rj memL memR outR :
    sim_decrypt_reduction_heap_rel memL memR ->
    outR \in dinsupp
      (Pr_code
        (ind_cpa_reduction_sim_eval2_code max_queries ((gate, ri), rj))
        memR) ->
    exists outL,
      outL \in dinsupp
        (Pr_code
          (resolve (IndCpadSimDecryptOracle max_queries)
            (mkopsig IndCpadGame.oracle_eval2
              (chProd (chProd binary_gate nat) nat) ciphertext)
            ((gate, ri), rj))
          memL) /\
      outL.1 = outR.1 /\
      sim_decrypt_reduction_heap_rel outL.2 outR.2.
  Proof.
    move=> Hrel Hout.
    rewrite /ind_cpa_reduction_sim_eval2_code in Hout.
    rewrite Pr_code_get in Hout.
    have [Hready Hafter_ready] := dinsupp_assertD _ _ _ _ Hout.
    rewrite Pr_code_get in Hafter_ready.
    have [HriR Hafter_ri] := dinsupp_assertD _ _ _ _ Hafter_ready.
    rewrite /= in Hafter_ri.
    have [HrjR Hafter_rj] := dinsupp_assertD _ _ _ _ Hafter_ri.
    rewrite /= in Hafter_rj.
    case HnthiR:
        (nth_valid (get_heap memR IndCpaDSim.table_addr) ri HriR)=>
      [[m0i m1i] ci] in Hafter_rj *.
    case HnthjR:
        (nth_valid (get_heap memR IndCpaDSim.table_addr) rj HrjR)=>
      [[m0j m1j] cj] in Hafter_rj *.
    rewrite Pr_code_get in Hafter_rj.
    have [Hoevk Hevk_body] := dinsupp_assertD _ _ _ _ Hafter_rj.
    case HevkR: (get_heap memR IndCpaDSim.evk_addr) Hoevk Hevk_body=>
      [evk|] Hoevk Hevk_body.
    - have HevkL :=
        sim_decrypt_reduction_heap_rel_evk_from_sim Hrel HevkR.
      have [pk [sk [HpkL HskL _ _]]] :=
        challenge_heap_valid_evk_initialized memL evk
          (sim_decrypt_reduction_heap_rel_challenge_valid Hrel) HevkL.
      rewrite Pr_code_sample in Hevk_body.
      have [c' Hc' Hinner] := @dinsupp_dlet R _ _ _ _ _ Hevk_body.
      rewrite Pr_code_put Pr_code_ret in Hinner.
      have -> :
          outR =
          (c', set_heap memR IndCpaDSim.table_addr
            (get_heap memR IndCpaDSim.table_addr ++
              [:: (interpret_binary gate m0i m0j,
                   interpret_binary gate m1i m1j, c')])).
        exact: in_dunit Hinner.
      have Htable := sim_decrypt_reduction_heap_rel_table Hrel.
      have HriL :
          (ri < length (get_heap memL IndCpadGame.table_addr))%N.
        by rewrite Htable.
      have HrjL :
          (rj < length (get_heap memL IndCpadGame.table_addr))%N.
        by rewrite Htable.
      have HnthiL :
          nth_valid (get_heap memL IndCpadGame.table_addr) ri HriL =
          (m0i, m1i, ci).
        rewrite -(sim_decrypt_reduction_heap_rel_eval2_row_i
          HriL HriR Hrel).
        exact: HnthiR.
      have HnthjL :
          nth_valid (get_heap memL IndCpadGame.table_addr) rj HrjL =
          (m0j, m1j, cj).
        rewrite -(sim_decrypt_reduction_heap_rel_eval2_row_j
          HrjL HrjR Hrel).
        exact: HnthjR.
      have Hc'_row :
          c' \in dinsupp
            (let '(_, _, ci0) :=
              nth_valid (get_heap memR IndCpaDSim.table_addr) ri HriR in
             let '(_, _, cj0) :=
              nth_valid (get_heap memR IndCpaDSim.table_addr) rj HrjR in
             eval2 evk gate ci0 cj0).
        by rewrite HnthiR HnthjR.
      exists
        (c', set_heap memL IndCpadGame.table_addr
          (get_heap memL IndCpadGame.table_addr ++
            [:: let '(m0iL, m1iL, _) :=
                  nth_valid (get_heap memL IndCpadGame.table_addr)
                    ri HriL in
                let '(m0jL, m1jL, _) :=
                  nth_valid (get_heap memL IndCpadGame.table_addr)
                    rj HrjL in
                (interpret_binary gate m0iL m0jL,
                 interpret_binary gate m1iL m1jL, c')])).
      split.
      + rewrite ind_cpad_sim_decrypt_eval2_resolveE.
        rewrite /ind_cpad_real_eval2_code.
        rewrite Pr_code_get.
        apply: (dinsupp_assertD_intro _ _ _ _ HriL).
        rewrite /=.
        apply: (dinsupp_assertD_intro _ _ _ _ HrjL).
        rewrite HnthiL HnthjL.
        rewrite Pr_code_get HevkL /assertD /=.
        rewrite Pr_code_sample.
        apply: dlet_dinsupp.
        * exact: Hc'.
        * rewrite Pr_code_put Pr_code_ret.
          apply/dinsuppP.
          rewrite dunit1E eqxx.
          exact/eqP/oner_neq0.
      + split; first by [].
        move: (sim_decrypt_reduction_heap_rel_set_table_eval2_right
          memL memR pk evk sk gate ri rj HriL HrjL HriR HrjR c'
          Hrel HpkL HevkR HskL Hc'_row).
        by rewrite HnthiR HnthjR.
    - by [].
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_eval2_result_eq
      max_queries gate ri rj memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    dmargin fst
      (Pr_code (ind_cpad_real_eval2_code max_queries ((gate, ri), rj))
        memL) =1
    dmargin fst
      (Pr_code
        (ind_cpa_reduction_sim_eval2_code max_queries ((gate, ri), rj))
        memR).
  Proof.
    move=> Hrel out.
    rewrite !dmarginE.
    rewrite /ind_cpad_real_eval2_code /ind_cpa_reduction_sim_eval2_code.
    rewrite !Pr_code_get.
    rewrite /assertD (sim_decrypt_reduction_heap_rel_ready Hrel) /=.
    rewrite Pr_code_get.
    have Htable := sim_decrypt_reduction_heap_rel_table Hrel.
    rewrite -Htable.
    rewrite -!dmarginE.
    apply: dmargin_fst_assertD_ext=> Hri out'.
    apply: dmargin_fst_assertD_ext=> Hrj out''.
    rewrite !dmarginE /=.
    case Hrowi:
        (nth_valid (get_heap memL IndCpadGame.table_addr) ri Hri)=>
      [[m0i m1i] ci].
    case Hrowj:
        (nth_valid (get_heap memL IndCpadGame.table_addr) rj Hrj)=>
      [[m0j m1j] cj].
    rewrite !Pr_code_get.
    have Hevk := sim_decrypt_reduction_heap_rel_evk_sim Hrel.
    rewrite -Hevk.
    case HevkL: (get_heap memL IndCpadGame.evk_addr)=> [evk|] /=.
    - rewrite !Pr_code_sample.
      rewrite !__deprecated__dlet_dlet.
      apply: eq_in_dlet=> // c' _ z.
      rewrite /= !Pr_code_put !Pr_code_ret.
      by rewrite !dlet_unit.
    - by rewrite !Pr_code_fail !dlet_null_ext.
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_eval2_result_tv_le0
      max_queries gate ri rj memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    total_variation
      (complete
        (dmargin fst
          (Pr_code
            (ind_cpad_real_eval2_code max_queries ((gate, ri), rj))
            memL)))
      (complete
        (dmargin fst
          (Pr_code
            (ind_cpa_reduction_sim_eval2_code max_queries ((gate, ri), rj))
            memR))) <= 0.
  Proof.
    move=> Hrel.
    apply: total_variation_eq_le0.
    apply: complete_ext=> out.
    exact: (ind_cpad_sim_decrypt_reduction_eval2_result_eq
      max_queries gate ri rj memL memR Hrel out).
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_eval2_resolve_result_tv_le0
      max_queries gate ri rj memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    total_variation
      (complete
        (dmargin fst
          (Pr_code
            (resolve (IndCpadSimDecryptOracle max_queries)
              (mkopsig IndCpadGame.oracle_eval2
                (chProd (chProd binary_gate nat) nat) ciphertext)
              ((gate, ri), rj))
            memL)))
      (complete
        (dmargin fst
          (Pr_code
            (resolve (IndCpaDSim.IndCpadOracle max_queries)
              (mkopsig IndCpadGame.oracle_eval2
                (chProd (chProd binary_gate nat) nat) ciphertext)
              ((gate, ri), rj))
            memR))) <= 0.
  Proof.
    move=> Hrel.
    rewrite ind_cpad_sim_decrypt_eval2_resolveE.
    rewrite ind_cpa_reduction_sim_eval2_resolveE.
    exact: (ind_cpad_sim_decrypt_reduction_eval2_result_tv_le0
      max_queries gate ri rj memL memR Hrel).
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_eval2_resolve_left_support_rel
      max_queries gate ri rj memL memR outR :
    sim_decrypt_reduction_heap_rel memL memR ->
    outR \in dinsupp
      (Pr_code
        (resolve (IndCpaDSim.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_eval2
            (chProd (chProd binary_gate nat) nat) ciphertext)
          ((gate, ri), rj))
        memR) ->
    exists outL,
      outL \in dinsupp
        (Pr_code
          (resolve (IndCpadSimDecryptOracle max_queries)
            (mkopsig IndCpadGame.oracle_eval2
              (chProd (chProd binary_gate nat) nat) ciphertext)
            ((gate, ri), rj))
          memL) /\
      outL.1 = outR.1 /\
      sim_decrypt_reduction_heap_rel outL.2 outR.2.
  Proof.
    move=> Hrel HoutR.
    rewrite ind_cpa_reduction_sim_eval2_resolveE in HoutR.
    exact: (ind_cpa_reduction_sim_eval2_code_left_support_rel
      max_queries gate ri rj memL memR outR Hrel HoutR).
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_eval2_resolve_ae
      max_queries :
    ⊨AE_opt
    ⦃ same_input_sim_decrypt_reduction_pre ⦄
      (fun x : (binary_gate * nat) * nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_eval2
            (chProd (chProd binary_gate nat) nat) ciphertext) x)
    ≈( 0 )
      (fun x : (binary_gate * nat) * nat =>
        resolve (IndCpaDSim.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_eval2
            (chProd (chProd binary_gate nat) nat) ciphertext) x)
    ⦃ same_result_opt ⦄.
  Proof.
    apply: additiveErrorOptSameResultTvdEqRule.
    - exact: lexx.
    - move=> memL memR [[gate ri] rj] [[gate' ri'] rj'] Hpre.
      rewrite /same_input_sim_decrypt_reduction_pre in Hpre.
      move/andP: Hpre=> [/eqP Hx Hrel].
      inversion Hx; subst gate' ri' rj'.
      exact: (ind_cpad_sim_decrypt_reduction_eval2_resolve_result_tv_le0
        max_queries gate ri rj memL memR Hrel).
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_eval2_resolve_rel_ae
      max_queries :
    ⊨AE_opt
    ⦃ same_input_sim_decrypt_reduction_pre ⦄
      (fun x : (binary_gate * nat) * nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_eval2
            (chProd (chProd binary_gate nat) nat) ciphertext) x)
    ≈( 0 )
      (fun x : (binary_gate * nat) * nat =>
        resolve (IndCpaDSim.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_eval2
            (chProd (chProd binary_gate nat) nat) ciphertext) x)
    ⦃ same_result_sim_decrypt_reduction_opt ⦄.
  Proof.
    split; first exact: lexx.
    move=> memL memR [[gate ri] rj] [[gate' ri'] rj'] Hpre.
    rewrite /same_input_sim_decrypt_reduction_pre in Hpre.
    move/andP: Hpre=> [/eqP Hx Hrel].
    inversion Hx; subst gate' ri' rj'.
    rewrite ind_cpad_sim_decrypt_eval2_resolveE.
    rewrite ind_cpa_reduction_sim_eval2_resolveE.
    rewrite /ind_cpad_real_eval2_code /ind_cpa_reduction_sim_eval2_code.
    rewrite Pr_code_get.
    rewrite Pr_code_get /assertD (sim_decrypt_reduction_heap_rel_ready Hrel) /=.
    rewrite Pr_code_get.
    have Htable := sim_decrypt_reduction_heap_rel_table Hrel.
    rewrite -Htable.
    apply: assertD_same_guard_coupling; first exact: lexx.
    - move=> HriL_eq HriR_eq.
      pose HriL := bool_eq_true_is_true _ HriL_eq.
      have HriR_true :
          (ri < length (get_heap memR IndCpaDSim.table_addr))%N = true.
        by rewrite -Htable.
      pose HriR := bool_eq_true_is_true _ HriR_true.
      case Hrowi:
          (nth_valid (get_heap memL IndCpadGame.table_addr) ri HriL)=>
        [[m0i m1i] ci].
      have HrowiR :
          nth_valid (get_heap memR IndCpaDSim.table_addr) ri HriR =
          (m0i, m1i, ci).
        rewrite (sim_decrypt_reduction_heap_rel_eval2_row_i
          HriL HriR Hrel).
        exact: Hrowi.
      rewrite (nth_valid_irrel
        (get_heap memL IndCpadGame.table_addr) ri _ HriL).
      rewrite Hrowi /=.
      apply: assertD_same_guard_coupling; first exact: lexx.
      + move=> HrjL_eq HrjR_eq.
        pose HrjL := bool_eq_true_is_true _ HrjL_eq.
        have HrjR_true :
            (rj < length (get_heap memR IndCpaDSim.table_addr))%N = true.
          by rewrite -Htable.
        pose HrjR := bool_eq_true_is_true _ HrjR_true.
        case Hrowj:
            (nth_valid (get_heap memL IndCpadGame.table_addr) rj HrjL)=>
          [[m0j m1j] cj].
        have HrowjR :
            nth_valid (get_heap memR IndCpaDSim.table_addr) rj HrjR =
            (m0j, m1j, cj).
          rewrite (sim_decrypt_reduction_heap_rel_eval2_row_j
            HrjL HrjR Hrel).
          exact: Hrowj.
        rewrite (nth_valid_irrel
          (get_heap memL IndCpadGame.table_addr) rj _ HrjL).
        rewrite Hrowj.
        rewrite !Pr_code_get.
        case HevkR: (get_heap memR IndCpaDSim.evk_addr)=> [evk|].
        * have HevkL :=
            sim_decrypt_reduction_heap_rel_evk_from_sim Hrel HevkR.
          have [pk [sk [HpkL HskL _ _]]] :=
            challenge_heap_valid_evk_initialized memL evk
              (sim_decrypt_reduction_heap_rel_challenge_valid Hrel) HevkL.
          rewrite HevkL /assertD /=.
          pose outL c' :=
            (c', set_heap memL IndCpadGame.table_addr
              (get_heap memL IndCpadGame.table_addr ++
                [:: (interpret_binary gate m0i m0j,
                     interpret_binary gate m1i m1j, c')])).
          pose outR c' :=
            (c', set_heap memR IndCpaDSim.table_addr
              (get_heap memR IndCpaDSim.table_addr ++
                [:: (interpret_binary gate m0i m0j,
                     interpret_binary gate m1i m1j, c')])).
          exists (shared_complete_sample_coupling
            (eval2 evk gate ci cj) outL outR).
          split.
          -- have [HmarginL HmarginR] :=
              shared_complete_sample_coupling_margins
                (eval2 evk gate ci cj) outL outR.
             split.
             ++ move=> z.
                rewrite HmarginL.
                apply: complete_distr_ext=> y.
                rewrite /outL dmarginE Pr_code_sample.
                apply: eq_in_dlet=> // c' _ y'.
                by rewrite Pr_code_put Pr_code_ret.
             ++ move=> z.
                rewrite HmarginR.
                apply: complete_distr_ext=> y.
                rewrite /outR dmarginE.
                rewrite (nth_valid_irrel
                  (get_heap memL IndCpadGame.table_addr) ri _ HriL).
                rewrite Hrowi.
                rewrite (nth_valid_irrel
                  (get_heap memL IndCpadGame.table_addr) rj _ HrjL).
                rewrite Hrowj Htable.
                rewrite Pr_code_get HevkR /assertD /= Pr_code_sample.
                apply: eq_in_dlet=> // c' _ y'.
                by rewrite Pr_code_put Pr_code_ret.
          -- rewrite subr0.
             apply: shared_complete_sample_coupling_pr_ge1.
             ++ move=> c' Hc' /=.
                rewrite /same_result_sim_decrypt_reduction_opt /outL /outR /= eqxx.
                apply/andP; split; first exact/eqP.
                have Hc'_row :
                    c' \in dinsupp
                      (let '(_, _, ci0) :=
                        nth_valid (get_heap memR IndCpaDSim.table_addr)
                          ri HriR in
                       let '(_, _, cj0) :=
                        nth_valid (get_heap memR IndCpaDSim.table_addr)
                          rj HrjR in
                       eval2 evk gate ci0 cj0).
                  by rewrite HrowiR HrowjR.
                move: (sim_decrypt_reduction_heap_rel_set_table_eval2_right
                  memL memR pk evk sk gate ri rj HriL HrjL HriR HrjR c'
                  Hrel HpkL HevkR HskL Hc'_row).
                by rewrite Hrowi Hrowj HrowiR HrowjR.
             ++ by rewrite /same_result_sim_decrypt_reduction_opt.
        * have HevkL_none :
              get_heap memL IndCpadGame.evk_addr = None.
            have Hevk := sim_decrypt_reduction_heap_rel_evk_sim Hrel.
            by rewrite Hevk HevkR.
          rewrite HevkL_none /assertD /= !Pr_code_fail.
          exists (dunit (None, None)).
          split.
          -- split.
             ++ move=> z.
                rewrite dmargin_dunit.
                exact/esym/complete_dnull.
             ++ move=> z.
                rewrite dmargin_dunit.
                rewrite (nth_valid_irrel
                  (get_heap memL IndCpadGame.table_addr) ri _ HriL).
                rewrite Hrowi.
                rewrite (nth_valid_irrel
                  (get_heap memL IndCpadGame.table_addr) rj _ HrjL).
                rewrite Hrowj Htable.
                rewrite Pr_code_get HevkR /assertD /= Pr_code_fail.
                exact/esym/complete_dnull.
          -- rewrite pr_dunit /same_result_sim_decrypt_reduction_opt /=.
             by rewrite lerBlDr lerDl.
      + by rewrite /same_result_sim_decrypt_reduction_opt.
    - by rewrite /same_result_sim_decrypt_reduction_opt.
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_eval2_resolve_outer_link_rel_ae
      max_queries :
    ⊨AE_opt
    ⦃ same_input_sim_decrypt_reduction_pre ⦄
      (fun x : (binary_gate * nat) * nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_eval2
            (chProd (chProd binary_gate nat) nat) ciphertext) x)
    ≈( 0 )
      (fun x : (binary_gate * nat) * nat =>
        code_link
          (resolve (IndCpaDSim.IndCpadOracle max_queries)
            (mkopsig IndCpadGame.oracle_eval2
              (chProd (chProd binary_gate nat) nat) ciphertext) x)
          IndCpaSecurity.IndCpaGame.IndCpaOracle)
    ⦃ same_result_sim_decrypt_reduction_opt ⦄.
  Proof.
    have Hbase :=
      ind_cpad_sim_decrypt_reduction_eval2_resolve_rel_ae max_queries.
    split; first exact: Hbase.1.
    move=> memL memR xL xR Hpre.
    have [d [Hd Hpost]] := Hbase.2 memL memR xL xR Hpre.
    exists d.
    split; last exact: Hpost.
    move: Hd=> [HdL HdR].
    split; first exact: HdL.
    rewrite ind_cpa_reduction_sim_eval2_resolve_link_closed.
    exact: HdR.
  Qed.

  Definition ind_cpad_decrypt_prefix_code
      (max_queries : nat) (i : nat) :
      raw_code IndCpadGame.challenger_table_row :=
    decrypt_count ← get IndCpadGame.decrypt_count_addr ;;
    #assert (decrypt_count < max_queries)%N ;;
    #put IndCpadGame.decrypt_count_addr := decrypt_count.+1 ;;
    table ← get IndCpadGame.table_addr ;;
    #assert (i < length table)%N as i_in_range ;;
    ret (nth_valid table i i_in_range).

  Definition ind_cpad_real_decrypt_cont
      (row : IndCpadGame.challenger_table_row) :
      raw_code (chOption message) :=
    let '(m0, m1, c) := row in
    if m0 == m1 then
      o ← get IndCpadGame.sk_addr ;;
      #assert isSome o as osk ;;
      let sk := getSome o osk in
      m <$ (message; NF.decrypt sk c) ;;
      ret (Some m)
    else
      ret None.

  Definition ind_cpad_sim_decrypt_cont
      (row : IndCpadGame.challenger_table_row) :
      raw_code (chOption message) :=
    let '(m0, m1, c) := row in
    if m0 == m1 then
      #assert isSome c as c_valid ;;
      let '(_, error_bound) := getSome c c_valid in
      noise <$ (chVec chInt dim;
        discrete_gaussians (IndCpaDSim.zeroChVec dim)
          (noise_flooding_dg_stdev
            gaussian_width_multiplier error_bound)) ;;
      let res :=
        inverse_isometry m0
          (ivec_add (IndCpaDSim.toIntVec noise) (isometry m0 m0)) in
      @ret ('option message) (Some res)
    else
      @ret ('option message) None.

  Definition ind_cpad_real_decrypt_code
      (max_queries : nat) (i : nat) : raw_code (chOption message) :=
    decrypt_count ← get IndCpadGame.decrypt_count_addr ;;
    #assert (decrypt_count < max_queries)%N ;;
    #put IndCpadGame.decrypt_count_addr := decrypt_count.+1 ;;
    table ← get IndCpadGame.table_addr ;;
    #assert (i < length table)%N as i_in_range ;;
    let '(m0, m1, c) := nth_valid table i i_in_range in
    if m0 == m1 then
      o ← get IndCpadGame.sk_addr ;;
      #assert isSome o as osk ;;
      let sk := getSome o osk in
      m <$ (message; NF.decrypt sk c) ;;
      ret (Some m)
    else
      ret None.

  Definition ind_cpad_sim_decrypt_code
      (max_queries : nat) (i : nat) : raw_code (chOption message) :=
    decrypt_count ← get IndCpadGame.decrypt_count_addr ;;
    #assert (decrypt_count < max_queries)%N ;;
    #put IndCpadGame.decrypt_count_addr := decrypt_count.+1 ;;
    table ← get IndCpadGame.table_addr ;;
    #assert (i < length table)%N as i_in_range ;;
    let '(m0, m1, c) := nth_valid table i i_in_range in
    if m0 == m1 then
      #assert isSome c as c_valid ;;
      let '(_, error_bound) := getSome c c_valid in
      noise <$ (chVec chInt dim;
        discrete_gaussians (IndCpaDSim.zeroChVec dim)
          (noise_flooding_dg_stdev
            gaussian_width_multiplier error_bound)) ;;
      let res :=
        inverse_isometry m0
          (ivec_add (IndCpaDSim.toIntVec noise) (isometry m0 m0)) in
      @ret ('option message) (Some res)
    else
      @ret ('option message) None.

  Lemma ind_cpad_real_decrypt_resolveE max_queries x :
    resolve (IndCpadGame.IndCpadOracle max_queries)
      (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x =
    ind_cpad_real_decrypt_code max_queries x.
  Proof.
    rewrite /ind_cpad_real_decrypt_code
      /IndCpadGame.IndCpadOracle /=.
    rewrite !resolve_set /=.
    rewrite coerce_kleisliE /=.
    by [].
  Qed.

  Lemma ind_cpad_sim_decrypt_resolveE max_queries x :
    resolve (IndCpadSimDecryptOracle max_queries)
      (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x =
    ind_cpad_sim_decrypt_code max_queries x.
  Proof.
    rewrite /ind_cpad_sim_decrypt_code
      /IndCpadSimDecryptOracle /=.
    rewrite !resolve_set /=.
    rewrite coerce_kleisliE /=.
    by [].
  Qed.

  Definition ind_cpa_reduction_sim_decrypt_code
      (max_queries : nat) (i : nat) : raw_code (chOption message) :=
    ready ← get IndCpaDSim.ready_addr ;;
    #assert ready ;;
    decrypt_count ← get IndCpaDSim.decrypt_count_addr ;;
    #assert (decrypt_count < max_queries)%N ;;
    #put IndCpaDSim.decrypt_count_addr := decrypt_count.+1 ;;
    table ← get IndCpaDSim.table_addr ;;
    #assert (i < length table)%N as i_in_range ;;
    let '(m0, m1, c) := nth_valid table i i_in_range in
    if m0 == m1 then
      #assert isSome c as c_valid ;;
      let '(_, error_bound) := getSome c c_valid in
      noise <$ (chVec chInt dim;
        discrete_gaussians (IndCpaDSim.zeroChVec dim)
          (noise_flooding_dg_stdev
            gaussian_width_multiplier error_bound)) ;;
      let res :=
        inverse_isometry m0
          (ivec_add (IndCpaDSim.toIntVec noise) (isometry m0 m0)) in
      @ret ('option message) (Some res)
    else
      @ret ('option message) None.

  Lemma ind_cpa_reduction_sim_decrypt_resolveE max_queries x :
    resolve (IndCpaDSim.IndCpadOracle max_queries)
      (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x =
    ind_cpa_reduction_sim_decrypt_code max_queries x.
  Proof.
    rewrite /ind_cpa_reduction_sim_decrypt_code
      /IndCpaDSim.IndCpadOracle /=.
    rewrite !resolve_set /=.
    rewrite coerce_kleisliE /=.
    by [].
  Qed.

  Lemma ind_cpa_reduction_sim_decrypt_code_closed max_queries x :
    ValidCode IndCpaDSim.oracle_mem_spec [interface]
      (ind_cpa_reduction_sim_decrypt_code max_queries x).
  Proof.
    rewrite /ind_cpa_reduction_sim_decrypt_code.
    typeclasses eauto with ssprove_valid_db.
  Qed.

  Lemma ind_cpa_reduction_sim_decrypt_resolve_link_closed max_queries x :
    code_link
      (resolve (IndCpaDSim.IndCpadOracle max_queries)
        (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
      IndCpaSecurity.IndCpaGame.IndCpaOracle =
    resolve (IndCpaDSim.IndCpadOracle max_queries)
      (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x.
  Proof.
    rewrite ind_cpa_reduction_sim_decrypt_resolveE.
    rewrite (@code_link_closed (chOption message) IndCpaDSim.oracle_mem_spec
      IndCpaSecurity.IndCpaGame.IndCpaOracle
      (ind_cpa_reduction_sim_decrypt_code max_queries x)
      (ind_cpa_reduction_sim_decrypt_code_closed max_queries x)).
    by rewrite -ind_cpa_reduction_sim_decrypt_resolveE.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_decrypt_row
      memL memR i
      (iL : (i < length (get_heap memL IndCpadGame.table_addr))%N)
      (iR : (i < length (get_heap memR IndCpaDSim.table_addr))%N) :
    sim_decrypt_reduction_heap_rel memL memR ->
    nth_valid (get_heap memR IndCpaDSim.table_addr) i iR =
    nth_valid (get_heap memL IndCpadGame.table_addr) i iL.
  Proof.
    exact: sim_decrypt_reduction_heap_rel_eval1_row.
  Qed.

  Arguments sim_decrypt_reduction_heap_rel_decrypt_row {memL memR i}.

  Lemma sim_decrypt_reduction_heap_rel_decrypt_row_after_count
      memL memR i nL nR
      (iL : (i < length (get_heap
        (set_heap memL IndCpadGame.decrypt_count_addr nL)
        IndCpadGame.table_addr))%N)
      (iR : (i < length (get_heap
        (set_heap memR IndCpaDSim.decrypt_count_addr nR)
        IndCpaDSim.table_addr))%N) :
    sim_decrypt_reduction_heap_rel memL memR ->
    nth_valid
      (get_heap
        (set_heap memR IndCpaDSim.decrypt_count_addr nR)
        IndCpaDSim.table_addr) i iR =
    nth_valid
      (get_heap
        (set_heap memL IndCpadGame.decrypt_count_addr nL)
        IndCpadGame.table_addr) i iL.
  Proof.
    move=> Hrel.
    have Htable :
        get_heap
          (set_heap memR IndCpaDSim.decrypt_count_addr nR)
          IndCpaDSim.table_addr =
        get_heap
          (set_heap memL IndCpadGame.decrypt_count_addr nL)
          IndCpadGame.table_addr.
      rewrite !get_set_heap_neq; try neq_loc_auto.
      symmetry.
      exact: (sim_decrypt_reduction_heap_rel_table Hrel).
    have HR := nth_valid_nth_error
      (get_heap
        (set_heap memR IndCpaDSim.decrypt_count_addr nR)
        IndCpaDSim.table_addr) i iR.
    have HL := nth_valid_nth_error
      (get_heap
        (set_heap memL IndCpadGame.decrypt_count_addr nL)
        IndCpadGame.table_addr) i iL.
    have HRL :
        List.nth_error
          (get_heap
            (set_heap memL IndCpadGame.decrypt_count_addr nL)
            IndCpadGame.table_addr) i =
        Some
          (nth_valid
            (get_heap
              (set_heap memR IndCpaDSim.decrypt_count_addr nR)
              IndCpaDSim.table_addr) i iR).
      rewrite -Htable.
      exact: HR.
    move: HRL.
    rewrite HL.
    by case.
  Qed.

  Arguments sim_decrypt_reduction_heap_rel_decrypt_row_after_count
    {memL memR i nL nR}.

  Lemma ind_cpa_reduction_sim_decrypt_code_support_rel_none
      max_queries i memL memR outR :
    sim_decrypt_reduction_heap_rel memL memR ->
    outR \in dinsupp
      (Pr_code (ind_cpa_reduction_sim_decrypt_code max_queries i) memR) ->
    outR.1 = None ->
    exists outL,
      outL.1 = outR.1 /\
      sim_decrypt_reduction_heap_rel outL.2 outR.2.
  Proof.
    move=> Hrel Hout Hnone.
    rewrite /ind_cpa_reduction_sim_decrypt_code in Hout.
    rewrite Pr_code_get in Hout.
    have [Hready Hafter_ready] := dinsupp_assertD _ _ _ _ Hout.
    rewrite Pr_code_get in Hafter_ready.
    have [HcountR Hafter_count] := dinsupp_assertD _ _ _ _ Hafter_ready.
    rewrite Pr_code_put Pr_code_get in Hafter_count.
    have [HiR Hafter_range] := dinsupp_assertD _ _ _ _ Hafter_count.
    case HnthR:
        (nth_valid
          (get_heap
            (set_heap memR IndCpaDSim.decrypt_count_addr
              (get_heap memR IndCpaDSim.decrypt_count_addr).+1)
            IndCpaDSim.table_addr) i HiR)=> [[m0 m1] c] in Hafter_range *.
    case: ifP Hafter_range=> Heq Hafter_range.
    - have [Hc_some Hafter_c] := dinsupp_assertD _ _ _ _ Hafter_range.
      case Hc: c Hc_some Hafter_c=> [[data error_bound]|] //=
        Hc_some Hafter_c.
      rewrite Pr_code_sample in Hafter_c.
      have [noise Hnoise Hinner] := @dinsupp_dlet R _ _ _ _ _ Hafter_c.
      rewrite Pr_code_ret in Hinner.
      have HoutR := in_dunit Hinner.
      move: Hnone.
      rewrite HoutR /=.
      by discriminate.
    - rewrite Pr_code_ret in Hafter_range.
      have -> : outR =
          (None,
            set_heap memR IndCpaDSim.decrypt_count_addr
              (get_heap memR IndCpaDSim.decrypt_count_addr).+1).
        exact: in_dunit Hafter_range.
      have HcountL :
          (get_heap memL IndCpadGame.decrypt_count_addr < max_queries)%N.
        rewrite (sim_decrypt_reduction_heap_rel_decrypt_count Hrel).
        exact: HcountR.
      have Hrel_count :=
        sim_decrypt_reduction_heap_rel_set_decrypt_count_valid
          memL memR (get_heap memR IndCpaDSim.decrypt_count_addr).+1 Hrel.
      have Htable := sim_decrypt_reduction_heap_rel_table Hrel_count.
      have HiL :
          (i < length (get_heap
            (set_heap memL IndCpadGame.decrypt_count_addr
              (get_heap memL IndCpadGame.decrypt_count_addr).+1)
            IndCpadGame.table_addr))%N.
        have HiR_copy := HiR.
        move: HiR_copy.
        rewrite !get_set_heap_neq; try neq_loc_auto.
        by rewrite -(sim_decrypt_reduction_heap_rel_table Hrel).
      have HnthL :
          nth_valid
            (get_heap
              (set_heap memL IndCpadGame.decrypt_count_addr
                (get_heap memL IndCpadGame.decrypt_count_addr).+1)
              IndCpadGame.table_addr) i HiL =
          (m0, m1, c).
        transitivity
          (nth_valid
            (get_heap
              (set_heap memR IndCpaDSim.decrypt_count_addr
                (get_heap memR IndCpaDSim.decrypt_count_addr).+1)
              IndCpaDSim.table_addr) i HiR).
        - symmetry.
          exact: (sim_decrypt_reduction_heap_rel_decrypt_row_after_count
            HiL HiR Hrel).
        - exact: HnthR.
      exists
        (None,
          set_heap memL IndCpadGame.decrypt_count_addr
            (get_heap memR IndCpaDSim.decrypt_count_addr).+1).
      split; first by [].
      exact: Hrel_count.
  Qed.

  Lemma ind_cpa_reduction_sim_decrypt_code_support_rel
      max_queries i memL memR outR :
    sim_decrypt_reduction_heap_rel memL memR ->
    outR \in dinsupp
      (Pr_code (ind_cpa_reduction_sim_decrypt_code max_queries i) memR) ->
    exists outL,
      outL.1 = outR.1 /\
      sim_decrypt_reduction_heap_rel outL.2 outR.2.
  Proof.
    move=> Hrel Hout.
    rewrite /ind_cpa_reduction_sim_decrypt_code in Hout.
    rewrite Pr_code_get in Hout.
    have [Hready Hafter_ready] := dinsupp_assertD _ _ _ _ Hout.
    rewrite Pr_code_get in Hafter_ready.
    have [HcountR Hafter_count] := dinsupp_assertD _ _ _ _ Hafter_ready.
    rewrite Pr_code_put Pr_code_get in Hafter_count.
    have [HiR Hafter_range] := dinsupp_assertD _ _ _ _ Hafter_count.
    case HnthR:
        (nth_valid
          (get_heap
            (set_heap memR IndCpaDSim.decrypt_count_addr
              (get_heap memR IndCpaDSim.decrypt_count_addr).+1)
            IndCpaDSim.table_addr) i HiR)=> [[m0 m1] c] in Hafter_range *.
    have Hrel_count :=
      sim_decrypt_reduction_heap_rel_set_decrypt_count_valid
        memL memR (get_heap memR IndCpaDSim.decrypt_count_addr).+1 Hrel.
    case: ifP Hafter_range=> Heq Hafter_range.
    - have [Hc_some Hafter_c] := dinsupp_assertD _ _ _ _ Hafter_range.
      case Hc: c Hc_some Hafter_c=> [[data error_bound]|] //=
        Hc_some Hafter_c.
      rewrite Pr_code_sample in Hafter_c.
      have [noise Hnoise Hinner] := @dinsupp_dlet R _ _ _ _ _ Hafter_c.
      rewrite Pr_code_ret in Hinner.
      have -> :
          outR =
          (Some
            (inverse_isometry m0
              (ivec_add (IndCpaDSim.toIntVec noise) (isometry m0 m0))),
            set_heap memR IndCpaDSim.decrypt_count_addr
              (get_heap memR IndCpaDSim.decrypt_count_addr).+1).
        exact: in_dunit Hinner.
      exists
        (Some
          (inverse_isometry m0
            (ivec_add (IndCpaDSim.toIntVec noise) (isometry m0 m0))),
          set_heap memL IndCpadGame.decrypt_count_addr
            (get_heap memR IndCpaDSim.decrypt_count_addr).+1).
      split; first by [].
      exact: Hrel_count.
    - rewrite Pr_code_ret in Hafter_range.
      have -> : outR =
          (None,
            set_heap memR IndCpaDSim.decrypt_count_addr
              (get_heap memR IndCpaDSim.decrypt_count_addr).+1).
        exact: in_dunit Hafter_range.
      exists
        (None,
          set_heap memL IndCpadGame.decrypt_count_addr
            (get_heap memR IndCpaDSim.decrypt_count_addr).+1).
      split; first by [].
      exact: Hrel_count.
  Qed.

  Lemma ind_cpa_reduction_sim_decrypt_code_left_support_rel
      max_queries i memL memR outR :
    sim_decrypt_reduction_heap_rel memL memR ->
    outR \in dinsupp
      (Pr_code (ind_cpa_reduction_sim_decrypt_code max_queries i) memR) ->
    exists outL,
      outL \in dinsupp
        (Pr_code (ind_cpad_sim_decrypt_code max_queries i) memL) /\
      outL.1 = outR.1 /\
      sim_decrypt_reduction_heap_rel outL.2 outR.2.
  Proof.
    move=> Hrel Hout.
    rewrite /ind_cpa_reduction_sim_decrypt_code in Hout.
    rewrite Pr_code_get in Hout.
    have [Hready Hafter_ready] := dinsupp_assertD _ _ _ _ Hout.
    rewrite Pr_code_get in Hafter_ready.
    have [HcountR Hafter_count] := dinsupp_assertD _ _ _ _ Hafter_ready.
    rewrite Pr_code_put Pr_code_get in Hafter_count.
    have [HiR Hafter_range] := dinsupp_assertD _ _ _ _ Hafter_count.
    case HnthR:
        (nth_valid
          (get_heap
            (set_heap memR IndCpaDSim.decrypt_count_addr
              (get_heap memR IndCpaDSim.decrypt_count_addr).+1)
            IndCpaDSim.table_addr) i HiR)=> [[m0 m1] c] in Hafter_range *.
    have HcountL :
        (get_heap memL IndCpadGame.decrypt_count_addr < max_queries)%N.
      rewrite (sim_decrypt_reduction_heap_rel_decrypt_count Hrel).
      exact: HcountR.
    have Hrel_count :=
      sim_decrypt_reduction_heap_rel_set_decrypt_count_valid
        memL memR (get_heap memL IndCpadGame.decrypt_count_addr).+1 Hrel.
    set memL1 := set_heap memL IndCpadGame.decrypt_count_addr
      (get_heap memL IndCpadGame.decrypt_count_addr).+1.
    set tableL := get_heap memL1 IndCpadGame.table_addr.
    have HiL :
        (i < length tableL)%N.
      have HiR_copy := HiR.
      move: HiR_copy.
      rewrite /tableL /memL1.
      rewrite !get_set_heap_neq; try neq_loc_auto.
      by rewrite -(sim_decrypt_reduction_heap_rel_table Hrel).
    have HnthL :
        nth_valid tableL i HiL =
        (m0, m1, c).
      transitivity
        (nth_valid
          (get_heap
            (set_heap memR IndCpaDSim.decrypt_count_addr
              (get_heap memR IndCpaDSim.decrypt_count_addr).+1)
            IndCpaDSim.table_addr) i HiR).
      - symmetry.
        exact: (sim_decrypt_reduction_heap_rel_decrypt_row_after_count
          HiL HiR Hrel).
      - exact: HnthR.
    case: ifP Hafter_range=> Heq Hafter_range.
    - have [Hc_some Hafter_c] := dinsupp_assertD _ _ _ _ Hafter_range.
      case Hc: c Hc_some Hafter_c=> [[data error_bound]|] //=
        Hc_some Hafter_c.
      rewrite Pr_code_sample in Hafter_c.
      have [noise Hnoise Hinner] := @dinsupp_dlet R _ _ _ _ _ Hafter_c.
      rewrite Pr_code_ret in Hinner.
      have -> :
          outR =
          (Some
            (inverse_isometry m0
              (ivec_add (IndCpaDSim.toIntVec noise) (isometry m0 m0))),
            set_heap memR IndCpaDSim.decrypt_count_addr
              (get_heap memR IndCpaDSim.decrypt_count_addr).+1).
        exact: in_dunit Hinner.
      exists
        (Some
          (inverse_isometry m0
            (ivec_add (IndCpaDSim.toIntVec noise) (isometry m0 m0))),
          memL1).
      split.
      + rewrite /ind_cpad_sim_decrypt_code.
        rewrite Pr_code_get /assertD HcountL /=.
        rewrite Pr_code_put Pr_code_get.
        apply: (dinsupp_assertD_intro _ _ _ _ HiL).
        rewrite HnthL Heq.
        rewrite /assertD Hc /= Pr_code_sample.
        apply: dlet_dinsupp.
        * exact: Hnoise.
        * rewrite Pr_code_ret dunit1E eqxx.
          exact: oner_neq0.
      + split; first by [].
        rewrite -(sim_decrypt_reduction_heap_rel_decrypt_count Hrel).
        exact: Hrel_count.
    - rewrite Pr_code_ret in Hafter_range.
      have -> : outR =
          (None,
            set_heap memR IndCpaDSim.decrypt_count_addr
              (get_heap memR IndCpaDSim.decrypt_count_addr).+1).
        exact: in_dunit Hafter_range.
      exists
        (None,
          memL1).
      split.
      + rewrite /ind_cpad_sim_decrypt_code.
        rewrite Pr_code_get /assertD HcountL /=.
        rewrite Pr_code_put Pr_code_get.
        apply: (dinsupp_assertD_intro _ _ _ _ HiL).
        rewrite HnthL Heq Pr_code_ret.
        apply/dinsuppP.
        rewrite dunit1E eqxx.
        exact/eqP/oner_neq0.
      + split; first by [].
        rewrite -(sim_decrypt_reduction_heap_rel_decrypt_count Hrel).
        exact: Hrel_count.
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_decrypt_result_eq
      max_queries i memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    dmargin fst
      (Pr_code (ind_cpad_sim_decrypt_code max_queries i) memL) =1
    dmargin fst
      (Pr_code (ind_cpa_reduction_sim_decrypt_code max_queries i) memR).
  Proof.
    move=> Hrel out.
    rewrite !dmarginE.
    rewrite /ind_cpad_sim_decrypt_code /ind_cpa_reduction_sim_decrypt_code.
    rewrite !Pr_code_get.
    rewrite /assertD (sim_decrypt_reduction_heap_rel_ready Hrel) /=.
    have Hcount := sim_decrypt_reduction_heap_rel_decrypt_count Hrel.
    case Hcount_okR:
        (get_heap memR IndCpaDSim.decrypt_count_addr < max_queries)%N.
    - have Hcount_okL :
          (get_heap memL IndCpadGame.decrypt_count_addr < max_queries)%N =
          true.
        by rewrite Hcount Hcount_okR.
      rewrite /assertD Hcount_okL /= !Pr_code_put !Pr_code_get.
      rewrite /assertD Hcount_okR /= !Pr_code_put !Pr_code_get.
      rewrite ?get_set_heap_eq.
      rewrite ?get_set_heap_neq; try neq_loc_auto.
      have Htable0 := sim_decrypt_reduction_heap_rel_table Hrel.
      rewrite -!dmarginE.
      apply: dmargin_fst_assertD_ext_eq.
      + repeat (rewrite get_set_heap_neq; [| neq_loc_auto]).
        by rewrite Htable0.
      + move=> HiL HiR out'.
        rewrite !dmarginE /=.
        repeat (rewrite get_set_heap_neq; [| neq_loc_auto]).
        case Hrow:
            (nth_valid (get_heap memL IndCpadGame.table_addr) i HiL)=>
          [[m0 m1] c].
        have HrowR :
            nth_valid (get_heap memR IndCpaDSim.table_addr) i HiR =
            (m0, m1, c).
          rewrite (sim_decrypt_reduction_heap_rel_decrypt_row HiL HiR Hrel).
          exact: Hrow.
        rewrite HrowR.
        case: ifP=> Heq.
        * case Hc: c=> [[data error_bound]|] /=.
          -- rewrite !Pr_code_sample.
             rewrite !__deprecated__dlet_dlet.
             apply: eq_in_dlet=> // noise _ z.
             by rewrite !Pr_code_ret !dlet_unit.
          -- by rewrite !Pr_code_fail !dlet_null_ext.
        * by rewrite !Pr_code_ret !dlet_unit.
    - have Hcount_okL :
          (get_heap memL IndCpadGame.decrypt_count_addr < max_queries)%N =
          false.
        by rewrite Hcount Hcount_okR.
      rewrite /assertD Hcount_okL /= Pr_code_fail.
      by rewrite Pr_code_get /assertD Hcount_okR /= Pr_code_fail !dlet_null_ext.
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_decrypt_result_tv_le0
      max_queries i memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    total_variation
      (complete
        (dmargin fst
          (Pr_code (ind_cpad_sim_decrypt_code max_queries i) memL)))
      (complete
        (dmargin fst
          (Pr_code (ind_cpa_reduction_sim_decrypt_code max_queries i)
            memR))) <= 0.
  Proof.
    move=> Hrel.
    apply: total_variation_eq_le0.
    apply: complete_ext=> out.
    exact: (ind_cpad_sim_decrypt_reduction_decrypt_result_eq
      max_queries i memL memR Hrel out).
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_decrypt_resolve_result_tv_le0
      max_queries i memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    total_variation
      (complete
        (dmargin fst
          (Pr_code
            (resolve (IndCpadSimDecryptOracle max_queries)
              (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) i)
            memL)))
      (complete
        (dmargin fst
          (Pr_code
            (resolve (IndCpaDSim.IndCpadOracle max_queries)
              (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) i)
            memR))) <= 0.
  Proof.
    move=> Hrel.
    rewrite ind_cpad_sim_decrypt_resolveE.
    rewrite ind_cpa_reduction_sim_decrypt_resolveE.
    exact: (ind_cpad_sim_decrypt_reduction_decrypt_result_tv_le0
      max_queries i memL memR Hrel).
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_decrypt_resolve_left_support_rel
      max_queries i memL memR outR :
    sim_decrypt_reduction_heap_rel memL memR ->
    outR \in dinsupp
      (Pr_code
        (resolve (IndCpaDSim.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) i)
        memR) ->
    exists outL,
      outL \in dinsupp
        (Pr_code
          (resolve (IndCpadSimDecryptOracle max_queries)
            (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) i)
          memL) /\
      outL.1 = outR.1 /\
      sim_decrypt_reduction_heap_rel outL.2 outR.2.
  Proof.
    move=> Hrel HoutR.
    rewrite ind_cpa_reduction_sim_decrypt_resolveE in HoutR.
    rewrite ind_cpad_sim_decrypt_resolveE.
    exact: (ind_cpa_reduction_sim_decrypt_code_left_support_rel
      max_queries i memL memR outR Hrel HoutR).
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_decrypt_resolve_ae
      max_queries :
    ⊨AE_opt
    ⦃ same_input_sim_decrypt_reduction_pre ⦄
      (fun x : nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
    ≈( 0 )
      (fun x : nat =>
        resolve (IndCpaDSim.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
    ⦃ same_result_opt ⦄.
  Proof.
    apply: additiveErrorOptSameResultTvdEqRule.
    - exact: lexx.
    - move=> memL memR i i' Hpre.
      rewrite /same_input_sim_decrypt_reduction_pre in Hpre.
      move/andP: Hpre=> [/eqP Hx Hrel].
      subst i'.
      exact: (ind_cpad_sim_decrypt_reduction_decrypt_resolve_result_tv_le0
        max_queries i memL memR Hrel).
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_decrypt_resolve_rel_ae
      max_queries :
    ⊨AE_opt
    ⦃ same_input_sim_decrypt_reduction_pre ⦄
      (fun x : nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
    ≈( 0 )
      (fun x : nat =>
        resolve (IndCpaDSim.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
    ⦃ same_result_sim_decrypt_reduction_opt ⦄.
  Proof.
    split; first exact: lexx.
    move=> memL memR i i' Hpre.
    rewrite /same_input_sim_decrypt_reduction_pre in Hpre.
    move/andP: Hpre=> [/eqP Hx Hrel].
    subst i'.
    rewrite ind_cpad_sim_decrypt_resolveE.
    rewrite ind_cpa_reduction_sim_decrypt_resolveE.
    rewrite /ind_cpad_sim_decrypt_code /ind_cpa_reduction_sim_decrypt_code.
    rewrite Pr_code_get.
    rewrite Pr_code_get /assertD (sim_decrypt_reduction_heap_rel_ready Hrel) /=.
    rewrite Pr_code_get.
    have Hcount := sim_decrypt_reduction_heap_rel_decrypt_count Hrel.
    rewrite Hcount.
    apply: assertD_same_guard_coupling; first exact: lexx.
    - move=> HcountL_eq HcountR_eq.
      pose next_count := (get_heap memR IndCpaDSim.decrypt_count_addr).+1.
      pose memL1 := set_heap memL IndCpadGame.decrypt_count_addr next_count.
      pose memR1 := set_heap memR IndCpaDSim.decrypt_count_addr next_count.
      have Hrel_count : sim_decrypt_reduction_heap_rel memL1 memR1.
        rewrite /memL1 /memR1 /next_count.
        exact: (sim_decrypt_reduction_heap_rel_set_decrypt_count_valid
          memL memR (get_heap memR IndCpaDSim.decrypt_count_addr).+1 Hrel).
      rewrite !Pr_code_put !Pr_code_get.
      rewrite /memL1 /memR1 /next_count.
      rewrite -/next_count -/memL1 -/memR1.
      have Htable := sim_decrypt_reduction_heap_rel_table Hrel_count.
      rewrite -Htable.
      apply: assertD_same_guard_coupling; first exact: lexx.
      + move=> HiL_eq HiR_eq.
        pose HiL := bool_eq_true_is_true _ HiL_eq.
        case Hrow:
            (nth_valid (get_heap memL1 IndCpadGame.table_addr) i HiL)=>
          [[m0 m1] c].
        rewrite (nth_valid_irrel
          (get_heap memL1 IndCpadGame.table_addr) i _ HiL).
        rewrite Hrow.
        case: ifP=> Heq.
        * case Hc: c=> [[data error_bound]|] /=.
          -- pose D := discrete_gaussians (IndCpaDSim.zeroChVec dim)
               (noise_flooding_dg_stdev
                 gaussian_width_multiplier error_bound).
             pose decode noise :=
               inverse_isometry m0
                 (ivec_add (IndCpaDSim.toIntVec noise) (isometry m0 m0)).
             pose outL noise := (Some (decode noise), memL1).
             pose outR noise := (Some (decode noise), memR1).
             exists (shared_complete_sample_coupling D outL outR).
             split.
             ++ have [HmarginL HmarginR] :=
                  shared_complete_sample_coupling_margins D outL outR.
                split.
                ** move=> z.
                   rewrite HmarginL.
                   apply: complete_distr_ext=> y.
                   rewrite /outL /D dmarginE Pr_code_sample.
                   apply: eq_in_dlet=> // noise _ y'.
                   by rewrite /decode Pr_code_ret.
                ** move=> z.
                   rewrite HmarginR.
                   apply: complete_distr_ext=> y.
                   rewrite /outR /D dmarginE.
                   rewrite (nth_valid_irrel
                     (get_heap memL1 IndCpadGame.table_addr) i _ HiL).
                   rewrite Hrow Heq Hc /= Pr_code_sample.
                   apply: eq_in_dlet=> // noise _ y'.
                   by rewrite /decode Pr_code_ret.
             ++ rewrite subr0.
                apply: shared_complete_sample_coupling_pr_ge1.
                ** move=> noise Hnoise /=.
                   rewrite /same_result_sim_decrypt_reduction_opt
                     /outL /outR /= eqxx.
                   by rewrite Hrel_count.
                ** by rewrite /same_result_sim_decrypt_reduction_opt.
          -- rewrite /assertD /= !Pr_code_fail.
             exists (dunit (None, None)).
             split.
             ++ split.
                ** move=> z.
                   rewrite dmargin_dunit.
                   exact/esym/complete_dnull.
                ** move=> z.
                   rewrite dmargin_dunit.
                   rewrite (nth_valid_irrel
                     (get_heap memL1 IndCpadGame.table_addr) i _ HiL).
                   rewrite Hrow Heq Hc /= Pr_code_fail.
                   exact/esym/complete_dnull.
             ++ rewrite pr_dunit /same_result_sim_decrypt_reduction_opt /=.
                by rewrite lerBlDr lerDl.
        * pose outL (_ : chUnit) := (None : chOption message, memL1).
          pose outR (_ : chUnit) := (None : chOption message, memR1).
          pose Dnone : {distr chUnit / R} := dunit tt.
          exists (shared_complete_sample_coupling Dnone outL outR).
          split.
          -- have [HmarginL HmarginR] :=
               shared_complete_sample_coupling_margins Dnone outL outR.
             split.
             ++ move=> z.
                rewrite HmarginL.
                apply: complete_distr_ext=> y.
                rewrite /outL dmargin_dunit Pr_code_ret.
                by [].
             ++ move=> z.
                rewrite HmarginR.
                apply: complete_distr_ext=> y.
                rewrite /outR dmargin_dunit.
                rewrite (nth_valid_irrel
                  (get_heap memL1 IndCpadGame.table_addr) i _ HiL).
                rewrite Hrow Heq /= Pr_code_ret.
                by [].
          -- rewrite subr0.
             apply: shared_complete_sample_coupling_pr_ge1.
             ++ move=> [] _ /=.
                rewrite /same_result_sim_decrypt_reduction_opt
                  /outL /outR /=.
                by rewrite Hrel_count.
             ++ by rewrite /same_result_sim_decrypt_reduction_opt.
      + by rewrite /same_result_sim_decrypt_reduction_opt.
    - by rewrite /same_result_sim_decrypt_reduction_opt.
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_decrypt_resolve_outer_link_rel_ae
      max_queries :
    ⊨AE_opt
    ⦃ same_input_sim_decrypt_reduction_pre ⦄
      (fun x : nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
    ≈( 0 )
      (fun x : nat =>
        code_link
          (resolve (IndCpaDSim.IndCpadOracle max_queries)
            (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
          IndCpaSecurity.IndCpaGame.IndCpaOracle)
    ⦃ same_result_sim_decrypt_reduction_opt ⦄.
  Proof.
    have Hbase :=
      ind_cpad_sim_decrypt_reduction_decrypt_resolve_rel_ae max_queries.
    split; first exact: Hbase.1.
    move=> memL memR xL xR Hpre.
    have [d [Hd Hpost]] := Hbase.2 memL memR xL xR Hpre.
    exists d.
    split; last exact: Hpost.
    move: Hd=> [HdL HdR].
    split; first exact: HdL.
    rewrite ind_cpa_reduction_sim_decrypt_resolve_link_closed.
    exact: HdR.
  Qed.

End NoiseFloodingSecureOperationBridges.
