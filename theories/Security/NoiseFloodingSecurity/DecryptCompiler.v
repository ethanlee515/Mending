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

From Mending.Security.NoiseFloodingSecurity Require Import Prelude OperationBridges.

Module NoiseFloodingSecureDecryptCompiler
  (Import Scheme : ApproxFheScheme)
  (Import Metric : ApproxFheMetric(Scheme))
  (Import Correctness : ApproxCorrectnessPerfect(Scheme)(Metric))
  (Import IndCpaSecurity : IsIndCpa(Scheme))
  (Import Params : NoiseFloodingParams).
  Include OperationBridges.NoiseFloodingSecureOperationBridges(Scheme)(Metric)(Correctness)(IndCpaSecurity)(Params).

  Definition ind_cpad_decrypt_fused_code
      {out_t : choice_type} (max_queries : nat) (i : nat)
      (cont : IndCpadGame.challenger_table_row -> raw_code out_t) :
      raw_code out_t :=
    decrypt_count ← get IndCpadGame.decrypt_count_addr ;;
    #assert (decrypt_count < max_queries)%N ;;
    #put IndCpadGame.decrypt_count_addr := decrypt_count.+1 ;;
    table ← get IndCpadGame.table_addr ;;
    #assert (i < length table)%N as i_in_range ;;
    cont (nth_valid table i i_in_range).

  Lemma ind_cpad_decrypt_prefix_bind_contE
      {out_t : choice_type} max_queries i
      (cont : IndCpadGame.challenger_table_row -> raw_code out_t) mem :
    Pr_code
      (row ← ind_cpad_decrypt_prefix_code max_queries i ;;
       cont row)
      mem =1
    Pr_code (ind_cpad_decrypt_fused_code max_queries i cont) mem.
  Proof.
    move=> out.
    rewrite /ind_cpad_decrypt_prefix_code /ind_cpad_decrypt_fused_code.
    rewrite Pr_code_bind Pr_code_get /assertD.
    case Hcount:
        (get_heap mem IndCpadGame.decrypt_count_addr < max_queries)%N.
    - rewrite Pr_code_put Pr_code_get.
      rewrite Pr_code_get /assertD Hcount /=.
      rewrite Pr_code_put Pr_code_get.
      rewrite -Pr_code_bind.
      exact: (Pr_code_bind_assertD
        (i < length (get_heap
          (set_heap mem IndCpadGame.decrypt_count_addr
            (get_heap mem IndCpadGame.decrypt_count_addr).+1)
          IndCpadGame.table_addr))%N
        (fun i_in_range =>
          ret (nth_valid
            (get_heap
              (set_heap mem IndCpadGame.decrypt_count_addr
                (get_heap mem IndCpadGame.decrypt_count_addr).+1)
              IndCpadGame.table_addr) i i_in_range))
        cont
        (set_heap mem IndCpadGame.decrypt_count_addr
          (get_heap mem IndCpadGame.decrypt_count_addr).+1) out).
    rewrite Pr_code_get /assertD Hcount /=.
    by rewrite !Pr_code_fail dlet_null_ext.
  Qed.

  Lemma ind_cpad_real_decrypt_code_fusedE max_queries i mem :
    Pr_code (ind_cpad_real_decrypt_code max_queries i) mem =1
    Pr_code
      (ind_cpad_decrypt_fused_code max_queries i
        ind_cpad_real_decrypt_cont)
      mem.
  Proof.
    move=> out.
    rewrite /ind_cpad_real_decrypt_code
      /ind_cpad_decrypt_fused_code
      /ind_cpad_real_decrypt_cont.
    by [].
  Qed.

  Lemma ind_cpad_sim_decrypt_code_fusedE max_queries i mem :
    Pr_code (ind_cpad_sim_decrypt_code max_queries i) mem =1
    Pr_code
      (ind_cpad_decrypt_fused_code max_queries i
        ind_cpad_sim_decrypt_cont)
      mem.
  Proof.
    move=> out.
    rewrite /ind_cpad_sim_decrypt_code
      /ind_cpad_decrypt_fused_code
      /ind_cpad_sim_decrypt_cont.
    by [].
  Qed.

  Lemma ind_cpad_real_decrypt_code_factorE max_queries i mem :
    Pr_code (ind_cpad_real_decrypt_code max_queries i) mem =1
    Pr_code
      (row ← ind_cpad_decrypt_prefix_code max_queries i ;;
       ind_cpad_real_decrypt_cont row)
      mem.
  Proof.
    move=> out.
    rewrite (ind_cpad_real_decrypt_code_fusedE max_queries i mem out).
    symmetry.
    exact: (ind_cpad_decrypt_prefix_bind_contE
      max_queries i ind_cpad_real_decrypt_cont mem out).
  Qed.

  Lemma ind_cpad_sim_decrypt_code_factorE max_queries i mem :
    Pr_code (ind_cpad_sim_decrypt_code max_queries i) mem =1
    Pr_code
      (row ← ind_cpad_decrypt_prefix_code max_queries i ;;
       ind_cpad_sim_decrypt_cont row)
      mem.
  Proof.
    move=> out.
    rewrite (ind_cpad_sim_decrypt_code_fusedE max_queries i mem out).
    symmetry.
    exact: (ind_cpad_decrypt_prefix_bind_contE
      max_queries i ind_cpad_sim_decrypt_cont mem out).
  Qed.

  Lemma ind_cpad_real_decrypt_code_over_bound_null max_queries i mem :
    ~~ (get_heap mem IndCpadGame.decrypt_count_addr < max_queries)%N ->
    Pr_code (ind_cpad_real_decrypt_code max_queries i) mem =1 dnull.
  Proof.
    move=> Hcount out.
    rewrite /ind_cpad_real_decrypt_code.
    rewrite Pr_code_get /assertD (negbTE Hcount) /=.
    by rewrite Pr_code_fail.
  Qed.

  Lemma ind_cpad_sim_decrypt_code_over_bound_null max_queries i mem :
    ~~ (get_heap mem IndCpadGame.decrypt_count_addr < max_queries)%N ->
    Pr_code (ind_cpad_sim_decrypt_code max_queries i) mem =1 dnull.
  Proof.
    move=> Hcount out.
    rewrite /ind_cpad_sim_decrypt_code.
    rewrite Pr_code_get /assertD (negbTE Hcount) /=.
    by rewrite Pr_code_fail.
  Qed.

  Lemma ind_cpad_real_decrypt_resolve_over_bound_null max_queries i mem :
    ~~ (get_heap mem IndCpadGame.decrypt_count_addr < max_queries)%N ->
    Pr_code
      (resolve (IndCpadGame.IndCpadOracle max_queries)
        (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) i)
      mem =1 dnull.
  Proof.
    move=> Hcount.
    rewrite ind_cpad_real_decrypt_resolveE.
    exact: (ind_cpad_real_decrypt_code_over_bound_null
      max_queries i mem Hcount).
  Qed.

  Lemma ind_cpad_sim_decrypt_resolve_over_bound_null max_queries i mem :
    ~~ (get_heap mem IndCpadGame.decrypt_count_addr < max_queries)%N ->
    Pr_code
      (resolve (IndCpadSimDecryptOracle max_queries)
        (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) i)
      mem =1 dnull.
  Proof.
    move=> Hcount.
    rewrite ind_cpad_sim_decrypt_resolveE.
    exact: (ind_cpad_sim_decrypt_code_over_bound_null
      max_queries i mem Hcount).
  Qed.

  Lemma ind_cpad_real_sim_decrypt_resolve_over_bound_result_tv_le0
      max_queries i mem :
    ~~ (get_heap mem IndCpadGame.decrypt_count_addr < max_queries)%N ->
    total_variation
      (complete (dmargin fst (Pr_code
        (resolve (IndCpadGame.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) i)
        mem)))
      (complete (dmargin fst (Pr_code
        (resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) i)
        mem))) <= 0.
  Proof.
    move=> Hcount.
    apply: total_variation_eq_le0=> z.
    rewrite (complete_distr_ext _ _
      (dmargin_ext fst _ _
        (ind_cpad_real_decrypt_resolve_over_bound_null
          max_queries i mem Hcount)) z).
    rewrite (complete_distr_ext _ _
      (dmargin_ext fst _ _
        (ind_cpad_sim_decrypt_resolve_over_bound_null
          max_queries i mem Hcount)) z).
    by [].
  Qed.

  Lemma ind_cpad_real_sim_decrypt_resolve_over_bound_output_tv_le0
      max_queries i mem :
    ~~ (get_heap mem IndCpadGame.decrypt_count_addr < max_queries)%N ->
    total_variation
      (complete (Pr_code
        (resolve (IndCpadGame.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) i)
        mem))
      (complete (Pr_code
        (resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) i)
        mem)) <= 0.
  Proof.
    move=> Hcount.
    apply: total_variation_eq_le0=> z.
    rewrite (complete_distr_ext _ _
      (ind_cpad_real_decrypt_resolve_over_bound_null
        max_queries i mem Hcount) z).
    rewrite (complete_distr_ext _ _
      (ind_cpad_sim_decrypt_resolve_over_bound_null
        max_queries i mem Hcount) z).
    by [].
  Qed.

  Definition decrypt_count_over_bound (max_queries : nat) : pred heap :=
    fun mem =>
      ~~ (get_heap mem IndCpadGame.decrypt_count_addr < max_queries)%N.

  Lemma decrypt_count_over_bound_set_table
      max_queries mem table :
    decrypt_count_over_bound max_queries mem ->
    decrypt_count_over_bound max_queries
      (set_heap mem IndCpadGame.table_addr table).
  Proof.
    rewrite /decrypt_count_over_bound.
    by rewrite get_set_heap_neq; [| neq_loc_auto].
  Qed.

  Definition same_input_decrypt_over_bound_pre (max_queries : nat) :
      pred ((nat * heap) * (nat * heap)) :=
    fun inps =>
      let '((iL, memL), (iR, memR)) := inps in
      (iL == iR) && (memL == memR) &&
      decrypt_count_over_bound max_queries memL.

  Lemma ind_cpad_real_sim_decrypt_resolve_over_bound_ae max_queries :
    ⊨AE ⦃ same_input_decrypt_over_bound_pre max_queries ⦄
      (fun i : nat =>
        resolve (IndCpadGame.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) i)
    ≈( 0 )
      (fun i : nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) i)
    ⦃ same_result_opt ⦄.
  Proof.
    apply: additiveErrorSameResultTvdEqRule.
    - exact: lexx.
    - move=> memL memR iL iR Hpre.
      rewrite /same_input_decrypt_over_bound_pre in Hpre.
      move/andP: Hpre=> [/andP [/eqP Hi /eqP Hmem] Hcount].
      subst iR memR.
      exact: (ind_cpad_real_sim_decrypt_resolve_over_bound_result_tv_le0
        max_queries iL memL Hcount).
  Qed.

  Lemma ind_cpad_real_sim_decrypt_resolve_over_bound_output_ae
      max_queries :
    ⊨AE ⦃ same_input_decrypt_over_bound_pre max_queries ⦄
      (fun i : nat =>
        resolve (IndCpadGame.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) i)
    ≈( 0 )
      (fun i : nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) i)
    ⦃ same_output_heap_opt ⦄.
  Proof.
    apply: additiveErrorSameOutputTvdEqRule.
    - exact: lexx.
    - move=> memL memR iL iR Hpre.
      rewrite /same_input_decrypt_over_bound_pre in Hpre.
      move/andP: Hpre=> [/andP [/eqP Hi /eqP Hmem] Hcount].
      subst iR memR.
      exact: (ind_cpad_real_sim_decrypt_resolve_over_bound_output_tv_le0
        max_queries iL memL Hcount).
  Qed.

  Lemma ind_cpad_real_sim_decrypt_resolve_over_bound_eq
      max_queries (o : opsig) (x : src o) mem :
    fhas IndCpadGame.IndCpadAdv_import o ->
    ~~ (get_heap mem IndCpadGame.decrypt_count_addr < max_queries)%N ->
    Pr_code (resolve (IndCpadGame.IndCpadOracle max_queries) o x) mem =1
    Pr_code (resolve (IndCpadSimDecryptOracle max_queries) o x) mem.
  Proof.
    move: o x=> [f [S T]] x Hhas Hcount.
    destruct ((f == IndCpadGame.oracle_encrypt)%bool) eqn:Ho_encrypt.
    - have Hfid : f = IndCpadGame.oracle_encrypt :=
        ident_eqb_eq f IndCpadGame.oracle_encrypt Ho_encrypt.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_encrypt
            (chProd message message) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      move=> out.
      by rewrite ind_cpad_real_encrypt_resolveE
        ind_cpad_sim_decrypt_encrypt_resolveE.
    destruct ((f == IndCpadGame.oracle_eval1)%bool) eqn:Ho_eval1.
    - have Hfid : f = IndCpadGame.oracle_eval1 :=
        ident_eqb_eq f IndCpadGame.oracle_eval1 Ho_eval1.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_eval1
            (chProd unary_gate nat) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      move=> out.
      by rewrite ind_cpad_real_eval1_resolveE
        ind_cpad_sim_decrypt_eval1_resolveE.
    destruct ((f == IndCpadGame.oracle_eval2)%bool) eqn:Ho_eval2.
    - have Hfid : f = IndCpadGame.oracle_eval2 :=
        ident_eqb_eq f IndCpadGame.oracle_eval2 Ho_eval2.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_eval2
            (chProd (chProd binary_gate nat) nat) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      move=> out.
      by rewrite ind_cpad_real_eval2_resolveE
        ind_cpad_sim_decrypt_eval2_resolveE.
    destruct ((f == IndCpadGame.oracle_decrypt)%bool) eqn:Ho_decrypt.
    - have Hfid : f = IndCpadGame.oracle_decrypt :=
        ident_eqb_eq f IndCpadGame.oracle_decrypt Ho_decrypt.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_decrypt nat (chOption message).
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      move=> out.
      rewrite (ind_cpad_real_decrypt_resolve_over_bound_null
        max_queries x mem Hcount out).
      rewrite (ind_cpad_sim_decrypt_resolve_over_bound_null
        max_queries x mem Hcount out).
      by [].
    exfalso.
    rewrite /IndCpadGame.IndCpadAdv_import in Hhas.
    fmap_invert Hhas.
    - by move: Ho_encrypt; rewrite eqxx.
    - by move: Ho_eval1; rewrite eqxx.
    - by move: Ho_eval2; rewrite eqxx.
    - by move: Ho_decrypt; rewrite eqxx.
  Qed.

  Lemma ind_cpad_real_sim_decrypt_resolve_not_decrypt_eq
      max_queries (o : opsig) (x : src o) mem :
    fhas IndCpadGame.IndCpadAdv_import o ->
    o.1 != IndCpadGame.oracle_decrypt ->
    Pr_code (resolve (IndCpadGame.IndCpadOracle max_queries) o x) mem =1
    Pr_code (resolve (IndCpadSimDecryptOracle max_queries) o x) mem.
  Proof.
    move: o x=> [f [S T]] x Hhas Hnot_decrypt.
    destruct ((f == IndCpadGame.oracle_encrypt)%bool) eqn:Ho_encrypt.
    - have Hfid : f = IndCpadGame.oracle_encrypt :=
        ident_eqb_eq f IndCpadGame.oracle_encrypt Ho_encrypt.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_encrypt
            (chProd message message) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      move=> out.
      by rewrite ind_cpad_real_encrypt_resolveE
        ind_cpad_sim_decrypt_encrypt_resolveE.
    destruct ((f == IndCpadGame.oracle_eval1)%bool) eqn:Ho_eval1.
    - have Hfid : f = IndCpadGame.oracle_eval1 :=
        ident_eqb_eq f IndCpadGame.oracle_eval1 Ho_eval1.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_eval1
            (chProd unary_gate nat) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      move=> out.
      by rewrite ind_cpad_real_eval1_resolveE
        ind_cpad_sim_decrypt_eval1_resolveE.
    destruct ((f == IndCpadGame.oracle_eval2)%bool) eqn:Ho_eval2.
    - have Hfid : f = IndCpadGame.oracle_eval2 :=
        ident_eqb_eq f IndCpadGame.oracle_eval2 Ho_eval2.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_eval2
            (chProd (chProd binary_gate nat) nat) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      move=> out.
      by rewrite ind_cpad_real_eval2_resolveE
        ind_cpad_sim_decrypt_eval2_resolveE.
    destruct ((f == IndCpadGame.oracle_decrypt)%bool) eqn:Ho_decrypt.
    - have Hfid : f = IndCpadGame.oracle_decrypt :=
        ident_eqb_eq f IndCpadGame.oracle_decrypt Ho_decrypt.
      by move: Hnot_decrypt; rewrite Hfid eqxx.
    exfalso.
    rewrite /IndCpadGame.IndCpadAdv_import in Hhas.
    fmap_invert Hhas.
    - by move: Ho_encrypt; rewrite eqxx.
    - by move: Ho_eval1; rewrite eqxx.
    - by move: Ho_eval2; rewrite eqxx.
    - by move: Ho_decrypt; rewrite eqxx.
  Qed.

  Lemma ind_cpad_real_encrypt_code_preserves_decrypt_count
      max_queries x mem out :
    out \in dinsupp
      (Pr_code (ind_cpad_real_encrypt_code max_queries x) mem) ->
    get_heap out.2 IndCpadGame.decrypt_count_addr =
      get_heap mem IndCpadGame.decrypt_count_addr.
  Proof.
    case: x=> m0 m1 Hout.
    rewrite /ind_cpad_real_encrypt_code in Hout.
    rewrite Pr_code_get Pr_code_get in Hout.
    case Hpk: (get_heap mem IndCpadGame.pk_addr)=> [pk|].
    - rewrite Hpk /assertD /= in Hout.
      rewrite Pr_code_sample in Hout.
      have [c _ Hinner] := @dinsupp_dlet R _ _ _ _ _ Hout.
      rewrite Pr_code_get Pr_code_put Pr_code_ret in Hinner.
      have -> :
          out =
          (c, set_heap mem IndCpadGame.table_addr
            (get_heap mem IndCpadGame.table_addr ++ [:: (m0, m1, c)])).
        exact: in_dunit Hinner.
      by rewrite get_set_heap_neq; [|neq_loc_auto].
    - rewrite Hpk /assertD /= Pr_code_fail in Hout.
      by move/dinsuppP: Hout; rewrite dnullE.
  Qed.

  Lemma ind_cpad_real_eval1_code_preserves_decrypt_count
      max_queries x mem out :
    out \in dinsupp
      (Pr_code (ind_cpad_real_eval1_code max_queries x) mem) ->
    get_heap out.2 IndCpadGame.decrypt_count_addr =
      get_heap mem IndCpadGame.decrypt_count_addr.
  Proof.
    case: x=> gate r Hout.
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
    - rewrite Pr_code_sample in Hevk_body.
      have [c' _ Hinner] := @dinsupp_dlet R _ _ _ _ _ Hevk_body.
      rewrite Pr_code_put Pr_code_ret in Hinner.
      have -> :
          out =
          (c', set_heap mem IndCpadGame.table_addr
            (get_heap mem IndCpadGame.table_addr ++
              [:: (interpret_unary gate m0,
                   interpret_unary gate m1, c')])).
        exact: in_dunit Hinner.
      by rewrite get_set_heap_neq; [|neq_loc_auto].
    - by [].
  Qed.

  Lemma ind_cpad_real_eval2_code_preserves_decrypt_count
      max_queries x mem out :
    out \in dinsupp
      (Pr_code (ind_cpad_real_eval2_code max_queries x) mem) ->
    get_heap out.2 IndCpadGame.decrypt_count_addr =
      get_heap mem IndCpadGame.decrypt_count_addr.
  Proof.
    case: x=> [[gate ri] rj] Hout.
    rewrite /ind_cpad_real_eval2_code in Hout.
    rewrite Pr_code_get in Hout.
    have [Hri Hafter_ri] := dinsupp_assertD _ _ _ _ Hout.
    rewrite /= in Hafter_ri.
    have [Hrj Hafter_rj] := dinsupp_assertD _ _ _ _ Hafter_ri.
    rewrite /= in Hafter_rj.
    case Hrow_i:
        (nth_valid (get_heap mem IndCpadGame.table_addr) ri Hri)=>
      [[m0i m1i] ci] in Hafter_rj *.
    case Hrow_j:
        (nth_valid (get_heap mem IndCpadGame.table_addr) rj Hrj)=>
      [[m0j m1j] cj] in Hafter_rj *.
    rewrite Pr_code_get in Hafter_rj.
    have [Hoevk Hevk_body] := dinsupp_assertD _ _ _ _ Hafter_rj.
    case Hevk: (get_heap mem IndCpadGame.evk_addr) Hoevk Hevk_body=> [evk|]
      Hoevk Hevk_body.
    - rewrite Pr_code_sample in Hevk_body.
      have [c' _ Hinner] := @dinsupp_dlet R _ _ _ _ _ Hevk_body.
      rewrite Pr_code_put Pr_code_ret in Hinner.
      have -> :
          out =
          (c', set_heap mem IndCpadGame.table_addr
            (get_heap mem IndCpadGame.table_addr ++
              [:: (interpret_binary gate m0i m0j,
                   interpret_binary gate m1i m1j, c')])).
        exact: in_dunit Hinner.
      by rewrite get_set_heap_neq; [|neq_loc_auto].
    - by [].
  Qed.

  Lemma ind_cpad_real_resolve_not_decrypt_preserves_decrypt_count
      max_queries (o : opsig) (x : src o) mem out :
    fhas IndCpadGame.IndCpadAdv_import o ->
    o.1 != IndCpadGame.oracle_decrypt ->
    out \in dinsupp
      (Pr_code (resolve (IndCpadGame.IndCpadOracle max_queries) o x) mem) ->
    get_heap out.2 IndCpadGame.decrypt_count_addr =
      get_heap mem IndCpadGame.decrypt_count_addr.
  Proof.
    move: o x out=> [f [S T]] x out Hhas Hnot_decrypt Hout.
    destruct ((f == IndCpadGame.oracle_encrypt)%bool) eqn:Ho_encrypt.
    - have Hfid : f = IndCpadGame.oracle_encrypt :=
        ident_eqb_eq f IndCpadGame.oracle_encrypt Ho_encrypt.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_encrypt
            (chProd message message) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      rewrite ind_cpad_real_encrypt_resolveE in Hout.
      exact: (ind_cpad_real_encrypt_code_preserves_decrypt_count
        max_queries x mem out Hout).
    destruct ((f == IndCpadGame.oracle_eval1)%bool) eqn:Ho_eval1.
    - have Hfid : f = IndCpadGame.oracle_eval1 :=
        ident_eqb_eq f IndCpadGame.oracle_eval1 Ho_eval1.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_eval1
            (chProd unary_gate nat) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      rewrite ind_cpad_real_eval1_resolveE in Hout.
      exact: (ind_cpad_real_eval1_code_preserves_decrypt_count
        max_queries x mem out Hout).
    destruct ((f == IndCpadGame.oracle_eval2)%bool) eqn:Ho_eval2.
    - have Hfid : f = IndCpadGame.oracle_eval2 :=
        ident_eqb_eq f IndCpadGame.oracle_eval2 Ho_eval2.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_eval2
            (chProd (chProd binary_gate nat) nat) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      rewrite ind_cpad_real_eval2_resolveE in Hout.
      exact: (ind_cpad_real_eval2_code_preserves_decrypt_count
        max_queries x mem out Hout).
    destruct ((f == IndCpadGame.oracle_decrypt)%bool) eqn:Ho_decrypt.
    - have Hfid : f = IndCpadGame.oracle_decrypt :=
        ident_eqb_eq f IndCpadGame.oracle_decrypt Ho_decrypt.
      by move: Hnot_decrypt; rewrite Hfid eqxx.
    exfalso.
    rewrite /IndCpadGame.IndCpadAdv_import in Hhas.
    fmap_invert Hhas.
    - by move: Ho_encrypt; rewrite eqxx.
    - by move: Ho_eval1; rewrite eqxx.
    - by move: Ho_eval2; rewrite eqxx.
    - by move: Ho_decrypt; rewrite eqxx.
  Qed.

  Lemma ind_cpad_real_sim_decrypt_resolve_over_bound_opsig_output_tv_le0
      max_queries (o : opsig) (x : src o) mem :
    fhas IndCpadGame.IndCpadAdv_import o ->
    ~~ (get_heap mem IndCpadGame.decrypt_count_addr < max_queries)%N ->
    total_variation
      (complete (Pr_code
        (resolve (IndCpadGame.IndCpadOracle max_queries) o x) mem))
      (complete (Pr_code
        (resolve (IndCpadSimDecryptOracle max_queries) o x) mem)) <= 0.
  Proof.
    move=> Hhas Hcount.
    apply: total_variation_eq_le0=> z.
    exact: (complete_distr_ext _ _
      (ind_cpad_real_sim_decrypt_resolve_over_bound_eq
        max_queries o x mem Hhas Hcount) z).
  Qed.

  Lemma ind_cpad_real_encrypt_code_preserves_decrypt_count_over_bound
      max_queries :
    ⊨Hoare ⦃ fun in_mem =>
        decrypt_count_over_bound max_queries in_mem.2 ⦄
      (ind_cpad_real_encrypt_code max_queries)
    ⦃ fun out_mem =>
        decrypt_count_over_bound max_queries out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> [[m0 m1] mem Hbound] out Hout.
    rewrite /ind_cpad_real_encrypt_code in Hout.
    rewrite Pr_code_get Pr_code_get in Hout.
    case Hpk: (get_heap mem IndCpadGame.pk_addr)=> [pk|].
    - rewrite Hpk /assertD /= in Hout.
      rewrite Pr_code_sample in Hout.
      have [c _ Hinner] := @dinsupp_dlet R _ _ _ _ _ Hout.
      rewrite Pr_code_get Pr_code_put Pr_code_ret in Hinner.
      have -> :
          out =
          (c, set_heap mem IndCpadGame.table_addr
            (get_heap mem IndCpadGame.table_addr ++
             [:: (m0, m1, c)])).
        exact: in_dunit Hinner.
      exact: decrypt_count_over_bound_set_table.
    - rewrite Hpk /assertD /= Pr_code_fail in Hout.
      by move/dinsuppP: Hout; rewrite dnullE.
  Qed.

  Lemma ind_cpad_real_eval1_code_preserves_decrypt_count_over_bound
      max_queries :
    ⊨Hoare ⦃ fun in_mem =>
        decrypt_count_over_bound max_queries in_mem.2 ⦄
      (ind_cpad_real_eval1_code max_queries)
    ⦃ fun out_mem =>
        decrypt_count_over_bound max_queries out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> [[gate r] mem Hbound] out Hout.
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
    - rewrite Pr_code_sample in Hevk_body.
      have [c' _ Hinner] := @dinsupp_dlet R _ _ _ _ _ Hevk_body.
      rewrite Pr_code_put Pr_code_ret in Hinner.
      have -> :
          out =
          (c', set_heap mem IndCpadGame.table_addr
            (get_heap mem IndCpadGame.table_addr ++
              [:: (interpret_unary gate m0,
                   interpret_unary gate m1, c')])).
        exact: in_dunit Hinner.
      exact: decrypt_count_over_bound_set_table.
    - by [].
  Qed.

  Lemma ind_cpad_real_eval2_code_preserves_decrypt_count_over_bound
      max_queries :
    ⊨Hoare ⦃ fun in_mem =>
        decrypt_count_over_bound max_queries in_mem.2 ⦄
      (ind_cpad_real_eval2_code max_queries)
    ⦃ fun out_mem =>
        decrypt_count_over_bound max_queries out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> [[[gate ri] rj] mem Hbound] out Hout.
    rewrite /ind_cpad_real_eval2_code in Hout.
    rewrite Pr_code_get in Hout.
    have [Hri Hafter_ri] := dinsupp_assertD _ _ _ _ Hout.
    rewrite /= in Hafter_ri.
    have [Hrj Hafter_rj] := dinsupp_assertD _ _ _ _ Hafter_ri.
    rewrite /= in Hafter_rj.
    case Hrow_i:
        (nth_valid (get_heap mem IndCpadGame.table_addr) ri Hri)=>
      [[m0i m1i] ci] in Hafter_rj *.
    case Hrow_j:
        (nth_valid (get_heap mem IndCpadGame.table_addr) rj Hrj)=>
      [[m0j m1j] cj] in Hafter_rj *.
    rewrite Pr_code_get in Hafter_rj.
    have [Hoevk Hevk_body] := dinsupp_assertD _ _ _ _ Hafter_rj.
    case Hevk: (get_heap mem IndCpadGame.evk_addr) Hoevk Hevk_body=> [evk|]
      Hoevk Hevk_body.
    - rewrite Pr_code_sample in Hevk_body.
      have [c' _ Hinner] := @dinsupp_dlet R _ _ _ _ _ Hevk_body.
      rewrite Pr_code_put Pr_code_ret in Hinner.
      have -> :
          out =
          (c', set_heap mem IndCpadGame.table_addr
            (get_heap mem IndCpadGame.table_addr ++
              [:: (interpret_binary gate m0i m0j,
                   interpret_binary gate m1i m1j, c')])).
        exact: in_dunit Hinner.
      exact: decrypt_count_over_bound_set_table.
    - by [].
  Qed.

  Lemma ind_cpad_real_decrypt_code_preserves_decrypt_count_over_bound
      max_queries :
    ⊨Hoare ⦃ fun in_mem =>
        decrypt_count_over_bound max_queries in_mem.2 ⦄
      (ind_cpad_real_decrypt_code max_queries)
    ⦃ fun out_mem =>
        decrypt_count_over_bound max_queries out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> [i mem Hbound] out Hout.
    rewrite /decrypt_count_over_bound in Hbound.
    rewrite /ind_cpad_real_decrypt_code in Hout.
    rewrite Pr_code_get /assertD (negbTE Hbound) /= Pr_code_fail in Hout.
    by move/dinsuppP: Hout; rewrite dnullE.
  Qed.

  Lemma ind_cpad_sim_decrypt_code_preserves_decrypt_count_over_bound
      max_queries :
    ⊨Hoare ⦃ fun in_mem =>
        decrypt_count_over_bound max_queries in_mem.2 ⦄
      (ind_cpad_sim_decrypt_code max_queries)
    ⦃ fun out_mem =>
        decrypt_count_over_bound max_queries out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> [i mem Hbound] out Hout.
    rewrite /decrypt_count_over_bound in Hbound.
    rewrite /ind_cpad_sim_decrypt_code in Hout.
    rewrite Pr_code_get /assertD (negbTE Hbound) /= Pr_code_fail in Hout.
    by move/dinsuppP: Hout; rewrite dnullE.
  Qed.

  Lemma ind_cpad_real_resolve_preserves_decrypt_count_over_bound
      max_queries (o : opsig) (x : src o) :
    fhas IndCpadGame.IndCpadAdv_import o ->
    ⊨Hoare ⦃ fun in_mem =>
        decrypt_count_over_bound max_queries in_mem.2 ⦄
      (fun x => resolve (IndCpadGame.IndCpadOracle max_queries) o x)
    ⦃ fun out_mem =>
        decrypt_count_over_bound max_queries out_mem.2 ⦄.
  Proof.
    move: o x=> [f [S T]] x Hhas.
    destruct ((f == IndCpadGame.oracle_encrypt)%bool) eqn:Ho_encrypt.
    - have Hfid : f = IndCpadGame.oracle_encrypt :=
        ident_eqb_eq f IndCpadGame.oracle_encrypt Ho_encrypt.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_encrypt
            (chProd message message) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      rewrite /hoareJudgment=> x0 mem Hbound out Hout.
      rewrite ind_cpad_real_encrypt_resolveE in Hout.
      exact: (ind_cpad_real_encrypt_code_preserves_decrypt_count_over_bound
        max_queries x0 mem Hbound out Hout).
    destruct ((f == IndCpadGame.oracle_eval1)%bool) eqn:Ho_eval1.
    - have Hfid : f = IndCpadGame.oracle_eval1 :=
        ident_eqb_eq f IndCpadGame.oracle_eval1 Ho_eval1.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_eval1
            (chProd unary_gate nat) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      rewrite /hoareJudgment=> x0 mem Hbound out Hout.
      rewrite ind_cpad_real_eval1_resolveE in Hout.
      exact: (ind_cpad_real_eval1_code_preserves_decrypt_count_over_bound
        max_queries x0 mem Hbound out Hout).
    destruct ((f == IndCpadGame.oracle_eval2)%bool) eqn:Ho_eval2.
    - have Hfid : f = IndCpadGame.oracle_eval2 :=
        ident_eqb_eq f IndCpadGame.oracle_eval2 Ho_eval2.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_eval2
            (chProd (chProd binary_gate nat) nat) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      rewrite /hoareJudgment=> x0 mem Hbound out Hout.
      rewrite ind_cpad_real_eval2_resolveE in Hout.
      exact: (ind_cpad_real_eval2_code_preserves_decrypt_count_over_bound
        max_queries x0 mem Hbound out Hout).
    destruct ((f == IndCpadGame.oracle_decrypt)%bool) eqn:Ho_decrypt.
    - have Hfid : f = IndCpadGame.oracle_decrypt :=
        ident_eqb_eq f IndCpadGame.oracle_decrypt Ho_decrypt.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_decrypt nat (chOption message).
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      rewrite /hoareJudgment=> x0 mem Hbound out Hout.
      rewrite ind_cpad_real_decrypt_resolveE in Hout.
      exact: (ind_cpad_real_decrypt_code_preserves_decrypt_count_over_bound
        max_queries x0 mem Hbound out Hout).
    exfalso.
    rewrite /IndCpadGame.IndCpadAdv_import in Hhas.
    fmap_invert Hhas.
    - by move: Ho_encrypt; rewrite eqxx.
    - by move: Ho_eval1; rewrite eqxx.
    - by move: Ho_eval2; rewrite eqxx.
    - by move: Ho_decrypt; rewrite eqxx.
  Qed.

  Lemma ind_cpad_sim_decrypt_resolve_preserves_decrypt_count_over_bound
      max_queries (o : opsig) (x : src o) :
    fhas IndCpadGame.IndCpadAdv_import o ->
    ⊨Hoare ⦃ fun in_mem =>
        decrypt_count_over_bound max_queries in_mem.2 ⦄
      (fun x => resolve (IndCpadSimDecryptOracle max_queries) o x)
    ⦃ fun out_mem =>
        decrypt_count_over_bound max_queries out_mem.2 ⦄.
  Proof.
    move: o x=> [f [S T]] x Hhas.
    destruct ((f == IndCpadGame.oracle_encrypt)%bool) eqn:Ho_encrypt.
    - have Hfid : f = IndCpadGame.oracle_encrypt :=
        ident_eqb_eq f IndCpadGame.oracle_encrypt Ho_encrypt.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_encrypt
            (chProd message message) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      rewrite /hoareJudgment=> x0 mem Hbound out Hout.
      rewrite ind_cpad_sim_decrypt_encrypt_resolveE in Hout.
      exact: (ind_cpad_real_encrypt_code_preserves_decrypt_count_over_bound
        max_queries x0 mem Hbound out Hout).
    destruct ((f == IndCpadGame.oracle_eval1)%bool) eqn:Ho_eval1.
    - have Hfid : f = IndCpadGame.oracle_eval1 :=
        ident_eqb_eq f IndCpadGame.oracle_eval1 Ho_eval1.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_eval1
            (chProd unary_gate nat) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      rewrite /hoareJudgment=> x0 mem Hbound out Hout.
      rewrite ind_cpad_sim_decrypt_eval1_resolveE in Hout.
      exact: (ind_cpad_real_eval1_code_preserves_decrypt_count_over_bound
        max_queries x0 mem Hbound out Hout).
    destruct ((f == IndCpadGame.oracle_eval2)%bool) eqn:Ho_eval2.
    - have Hfid : f = IndCpadGame.oracle_eval2 :=
        ident_eqb_eq f IndCpadGame.oracle_eval2 Ho_eval2.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_eval2
            (chProd (chProd binary_gate nat) nat) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      rewrite /hoareJudgment=> x0 mem Hbound out Hout.
      rewrite ind_cpad_sim_decrypt_eval2_resolveE in Hout.
      exact: (ind_cpad_real_eval2_code_preserves_decrypt_count_over_bound
        max_queries x0 mem Hbound out Hout).
    destruct ((f == IndCpadGame.oracle_decrypt)%bool) eqn:Ho_decrypt.
    - have Hfid : f = IndCpadGame.oracle_decrypt :=
        ident_eqb_eq f IndCpadGame.oracle_decrypt Ho_decrypt.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_decrypt nat (chOption message).
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      rewrite /hoareJudgment=> x0 mem Hbound out Hout.
      rewrite ind_cpad_sim_decrypt_resolveE in Hout.
      exact: (ind_cpad_sim_decrypt_code_preserves_decrypt_count_over_bound
        max_queries x0 mem Hbound out Hout).
    exfalso.
    rewrite /IndCpadGame.IndCpadAdv_import in Hhas.
    fmap_invert Hhas.
    - by move: Ho_encrypt; rewrite eqxx.
    - by move: Ho_eval1; rewrite eqxx.
    - by move: Ho_eval2; rewrite eqxx.
    - by move: Ho_decrypt; rewrite eqxx.
  Qed.

  Lemma decrypt_count_over_bound_depends_only_on_oracle_mem_spec
      max_queries :
    heap_pred_depends_only_on IndCpadGame.oracle_mem_spec
      (decrypt_count_over_bound max_queries).
  Proof.
    rewrite /heap_pred_depends_only_on /heap_eq_on
      /decrypt_count_over_bound.
    move=> mem0 mem1 Heq.
    by rewrite (Heq IndCpadGame.decrypt_count_addr); [| fmap_solve].
  Qed.

  Lemma code_link_real_sim_decrypt_over_bound_eq
      (A : choice_type) (L : Locations)
      (prog : raw_code A) max_queries mem :
    ValidCode L IndCpadGame.IndCpadAdv_import prog ->
    fseparate IndCpadGame.oracle_mem_spec L ->
    decrypt_count_over_bound max_queries mem ->
    Pr_code
      (code_link prog (IndCpadGame.IndCpadOracle max_queries)) mem =1
    Pr_code
      (code_link prog (IndCpadSimDecryptOracle max_queries)) mem.
  Proof.
    move=> Hvalid Hsep.
    have Hvc := valid_code_from_class L
      IndCpadGame.IndCpadAdv_import A prog Hvalid.
    elim: Hvc mem=> [a|o x k Ho Hk IH|l k Hl Hk IH
        |l v k Hl Hk IH|op k Hk IH] mem Hbound out /=.
    - by [].
    - rewrite !Pr_code_bind.
      apply: eq_in_dlet.
      + move=> y Hsupp out'.
        case: y Hsupp=> y mem' Hsupp.
        have Hpres :=
          ind_cpad_real_resolve_preserves_decrypt_count_over_bound
            max_queries o x Ho.
        have Hbound' :
            decrypt_count_over_bound max_queries mem'.
          exact: (Hpres x mem Hbound (y, mem') Hsupp).
        exact: (IH y mem' Hbound' out').
      + exact: (ind_cpad_real_sim_decrypt_resolve_over_bound_eq
          max_queries o x mem Ho Hbound).
    - rewrite !Pr_code_get.
      exact: (IH (get_heap mem l) mem Hbound out).
    - rewrite !Pr_code_put.
      have Hbound' :
          decrypt_count_over_bound max_queries (set_heap mem l v).
        have Hdep :=
          decrypt_count_over_bound_depends_only_on_oracle_mem_spec
            max_queries mem (set_heap mem l v).
        move: (Hdep (heap_eq_on_set_heap_separate
          IndCpadGame.oracle_mem_spec L mem l v Hsep Hl)).
        by move=> <-.
      exact: (IH (set_heap mem l v) Hbound' out).
    - rewrite !Pr_code_sample.
      apply: eq_in_dlet=> // a _ out'.
      exact: (IH a mem Hbound out').
  Qed.

  Lemma code_link_real_sim_decrypt_over_bound_output_tv_le0
      (A : choice_type) (L : Locations)
      (prog : raw_code A) max_queries mem :
    ValidCode L IndCpadGame.IndCpadAdv_import prog ->
    fseparate IndCpadGame.oracle_mem_spec L ->
    decrypt_count_over_bound max_queries mem ->
    total_variation
      (complete (Pr_code
        (code_link prog (IndCpadGame.IndCpadOracle max_queries)) mem))
      (complete (Pr_code
        (code_link prog (IndCpadSimDecryptOracle max_queries)) mem)) <= 0.
  Proof.
    move=> Hvalid Hsep Hbound.
    apply: total_variation_eq_le0=> out.
    exact: (complete_distr_ext _ _
      (code_link_real_sim_decrypt_over_bound_eq
        A L prog max_queries mem Hvalid Hsep Hbound) out).
  Qed.

  Lemma code_link_run_until_next_call_aux_real_sim_decrypt_eq
      (A : choice_type) (L : Locations)
      (prog : raw_code A) trace max_queries mem :
    ValidCode L IndCpadGame.IndCpadAdv_import prog ->
    Pr_code
      (code_link
        (run_until_next_call_aux prog IndCpadGame.oracle_decrypt trace)
        (IndCpadGame.IndCpadOracle max_queries)) mem =1
    Pr_code
      (code_link
        (run_until_next_call_aux prog IndCpadGame.oracle_decrypt trace)
        (IndCpadSimDecryptOracle max_queries)) mem.
  Proof.
    move=> Hvalid.
    have Hvc := valid_code_from_class L
      IndCpadGame.IndCpadAdv_import A prog Hvalid.
    elim: Hvc trace mem=> [a|o x k Ho Hk IH|l k Hl Hk IH
        |l v k Hl Hk IH|op k Hk IH] trace mem out /=.
    - by [].
    - case: o Ho x k Hk IH=> f [S T] Ho x k Hk IH /=.
      case Hfid: (f == IndCpadGame.oracle_decrypt)%bool.
      + by [].
      + rewrite !Pr_code_bind.
        apply: eq_in_dlet.
        * move=> ymem _ out'.
          case: ymem=> y mem'.
          exact: (IH y (rcons trace (call_entry (pickle y)))
            mem' out').
        * have Hneq : (f, (S, T)).1 != IndCpadGame.oracle_decrypt.
            by rewrite /= Hfid.
          exact: (ind_cpad_real_sim_decrypt_resolve_not_decrypt_eq
            max_queries (f, (S, T)) x mem Ho Hneq).
    - rewrite !Pr_code_get.
      exact: (IH (get_heap mem l)
        (rcons trace (get_entry (pickle (get_heap mem l)))) mem out).
    - rewrite !Pr_code_put.
      exact: (IH (rcons trace put_entry) (set_heap mem l v) out).
    - rewrite !Pr_code_sample.
      apply: eq_in_dlet=> // a _ out'.
      exact: (IH a (rcons trace (sample_entry (pickle a))) mem out').
  Qed.

  Lemma code_link_run_until_next_call_real_sim_decrypt_eq
      (A : choice_type) (L : Locations)
      (prog : raw_code A) max_queries mem :
    ValidCode L IndCpadGame.IndCpadAdv_import prog ->
    Pr_code
      (code_link
        (run_until_next_call prog IndCpadGame.oracle_decrypt)
        (IndCpadGame.IndCpadOracle max_queries)) mem =1
    Pr_code
      (code_link
        (run_until_next_call prog IndCpadGame.oracle_decrypt)
        (IndCpadSimDecryptOracle max_queries)) mem.
  Proof.
    rewrite /run_until_next_call.
    exact: code_link_run_until_next_call_aux_real_sim_decrypt_eq.
  Qed.

  Lemma code_link_run_until_next_call_aux_real_preserves_decrypt_count
      (A : choice_type) (L : Locations)
      (prog : raw_code A) trace max_queries mem out :
    ValidCode L IndCpadGame.IndCpadAdv_import prog ->
    fseparate IndCpadGame.oracle_mem_spec L ->
    out \in dinsupp (Pr_code
      (code_link
        (run_until_next_call_aux prog IndCpadGame.oracle_decrypt trace)
        (IndCpadGame.IndCpadOracle max_queries)) mem) ->
    get_heap out.2 IndCpadGame.decrypt_count_addr =
      get_heap mem IndCpadGame.decrypt_count_addr.
  Proof.
    move=> Hvalid Hsep.
    have Hvc := valid_code_from_class L
      IndCpadGame.IndCpadAdv_import A prog Hvalid.
    elim: Hvc trace mem out=> [a|o x k Ho Hk IH|l k Hl Hk IH
        |l v k Hl Hk IH|op k Hk IH] trace mem out Hout /=.
    - rewrite /code_link /= Pr_code_ret in Hout.
      have -> : out = ((inr a, pack_trace trace), mem).
        exact: in_dunit Hout.
      by [].
    - move: out Hout.
      case: o Ho x k Hk IH=> f [S T] Ho x k Hk IH out Hout /=.
      case Hfid: (f == IndCpadGame.oracle_decrypt)%bool.
      + rewrite /= Hfid /code_link /= Pr_code_ret in Hout.
        have -> : out = ((inl (pickle x), pack_trace trace), mem).
          exact: in_dunit Hout.
        by rewrite /=.
      + rewrite /= Hfid /code_link /= Pr_code_bind in Hout.
        have [mid Hmid Hinner] := @dinsupp_dlet R _ _ _ _ _ Hout.
        case: mid Hmid Hinner=> y mem_mid Hmid Hinner.
        have Hneq : (f, (S, T)).1 != IndCpadGame.oracle_decrypt.
          by rewrite /= Hfid.
        have Hmid_count :=
          ind_cpad_real_resolve_not_decrypt_preserves_decrypt_count
            max_queries (f, (S, T)) x mem (y, mem_mid) Ho Hneq Hmid.
        have Htail := IH y (rcons trace (call_entry (pickle y)))
          mem_mid out Hinner.
        by rewrite Htail Hmid_count.
    - rewrite Pr_code_get in Hout.
      exact: (IH (get_heap mem l)
        (rcons trace (get_entry (pickle (get_heap mem l)))) mem out Hout).
    - rewrite Pr_code_put in Hout.
      have Htail := IH (rcons trace put_entry)
        (set_heap mem l v) out Hout.
      rewrite Htail.
      have Heq := heap_eq_on_set_heap_separate
        IndCpadGame.oracle_mem_spec L mem l v Hsep Hl.
      by rewrite -(Heq IndCpadGame.decrypt_count_addr); [|fmap_solve].
    - rewrite Pr_code_sample in Hout.
      have [a _ Hinner] := @dinsupp_dlet R _ _ _ _ _ Hout.
      exact: (IH a (rcons trace (sample_entry (pickle a)))
        mem out Hinner).
  Qed.

  Lemma code_link_run_until_next_call_real_preserves_decrypt_count
      (A : choice_type) (L : Locations)
      (prog : raw_code A) max_queries mem out :
    ValidCode L IndCpadGame.IndCpadAdv_import prog ->
    fseparate IndCpadGame.oracle_mem_spec L ->
    out \in dinsupp (Pr_code
      (code_link
        (run_until_next_call prog IndCpadGame.oracle_decrypt)
        (IndCpadGame.IndCpadOracle max_queries)) mem) ->
    get_heap out.2 IndCpadGame.decrypt_count_addr =
      get_heap mem IndCpadGame.decrypt_count_addr.
  Proof.
    rewrite /run_until_next_call.
    exact: code_link_run_until_next_call_aux_real_preserves_decrypt_count.
  Qed.

  Lemma code_link_compile_calls_real_sim_decrypt_step_reduction
      (q : nat) (A : choice_type) (L : Locations)
      (prog : raw_code A) max_queries mem :
    ValidCode L IndCpadGame.IndCpadAdv_import prog ->
    (forall s mem',
      (s, mem') \in dinsupp (Pr_code
        (code_link
          (run_until_next_call prog IndCpadGame.oracle_decrypt)
          (IndCpadGame.IndCpadOracle max_queries)) mem) ->
      Pr_code
        (code_link
          (compile_calls_from_trace_step_cont q
            (X := nat) (Y := chOption message)
            (IndCpadSimDecryptOracle max_queries)
            IndCpadGame.oracle_decrypt prog nil s)
          (IndCpadGame.IndCpadOracle max_queries)) mem' =1
      Pr_code
        (code_link
          (compile_calls_from_trace_step_cont q
            (X := nat) (Y := chOption message)
            (IndCpadSimDecryptOracle max_queries)
            IndCpadGame.oracle_decrypt prog nil s)
          (IndCpadSimDecryptOracle max_queries)) mem') ->
    Pr_code
      (code_link
        (compile_calls q.+1
          (X := nat) (Y := chOption message)
          (IndCpadSimDecryptOracle max_queries)
          IndCpadGame.oracle_decrypt prog)
        (IndCpadGame.IndCpadOracle max_queries)) mem =1
    Pr_code
      (code_link
        (compile_calls q.+1
          (X := nat) (Y := chOption message)
          (IndCpadSimDecryptOracle max_queries)
          IndCpadGame.oracle_decrypt prog)
        (IndCpadSimDecryptOracle max_queries)) mem.
  Proof.
    move=> Hvalid Hstep out.
    rewrite -!compile_calls_from_trace_nil.
    rewrite (@codeLinkCompileCallsFromTraceS_decompose q
      nat (chOption message) A
      (IndCpadSimDecryptOracle max_queries)
      (IndCpadGame.IndCpadOracle max_queries)
      IndCpadGame.oracle_decrypt prog prog nil
      (continue_from_trace_nil prog)).
    rewrite (@codeLinkCompileCallsFromTraceS_decompose q
      nat (chOption message) A
      (IndCpadSimDecryptOracle max_queries)
      (IndCpadSimDecryptOracle max_queries)
      IndCpadGame.oracle_decrypt prog prog nil
      (continue_from_trace_nil prog)).
    rewrite !Pr_code_bind.
    apply: eq_in_dlet.
    - move=> smem Hsmem out'.
      case: smem Hsmem=> s mem' Hsmem.
      exact: (Hstep s mem' Hsmem out').
    - exact: (code_link_run_until_next_call_real_sim_decrypt_eq
        A L prog max_queries mem Hvalid).
  Qed.

  Lemma compile_calls_step_cont_invalid_call_real_sim_decrypt_eq
      (q : nat) (A : choice_type) (root : raw_code A)
      trace_prefix packed_x packed_local_trace max_queries mem :
    call_from_package (X := nat) (Y := chOption message)
      (IndCpadSimDecryptOracle max_queries)
      IndCpadGame.oracle_decrypt packed_x = None ->
    Pr_code
      (code_link
        (compile_calls_from_trace_step_cont q
          (X := nat) (Y := chOption message)
          (IndCpadSimDecryptOracle max_queries)
          IndCpadGame.oracle_decrypt root trace_prefix
          (inl packed_x, packed_local_trace))
        (IndCpadGame.IndCpadOracle max_queries)) mem =1
    Pr_code
      (code_link
        (compile_calls_from_trace_step_cont q
          (X := nat) (Y := chOption message)
          (IndCpadSimDecryptOracle max_queries)
          IndCpadGame.oracle_decrypt root trace_prefix
          (inl packed_x, packed_local_trace))
        (IndCpadSimDecryptOracle max_queries)) mem.
  Proof.
    move=> Hcall out.
    rewrite /compile_calls_from_trace_step_cont Hcall /=.
    by rewrite !Pr_code_link_bind_invalid_trace_code.
  Qed.

  Lemma compile_calls_step_cont_valid_call_real_sim_decrypt_reduction
      (q : nat) (A : choice_type) (root : raw_code A)
      trace_prefix packed_x packed_local_trace i max_queries mem :
    (unpickle packed_x : option nat) = Some i ->
    (forall y mem',
      (y, mem') \in dinsupp (Pr_code
        (resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) i)
        mem) ->
      Pr_code
        (code_link
          (compile_calls_from_trace q
            (X := nat) (Y := chOption message)
            (IndCpadSimDecryptOracle max_queries)
            IndCpadGame.oracle_decrypt root
            (rcons (trace_prefix ++ unpack_trace packed_local_trace)
              (call_entry (pickle y))))
          (IndCpadGame.IndCpadOracle max_queries)) mem' =1
      Pr_code
        (code_link
          (compile_calls_from_trace q
            (X := nat) (Y := chOption message)
            (IndCpadSimDecryptOracle max_queries)
            IndCpadGame.oracle_decrypt root
            (rcons (trace_prefix ++ unpack_trace packed_local_trace)
              (call_entry (pickle y))))
          (IndCpadSimDecryptOracle max_queries)) mem') ->
    Pr_code
      (code_link
        (compile_calls_from_trace_step_cont q
          (X := nat) (Y := chOption message)
          (IndCpadSimDecryptOracle max_queries)
          IndCpadGame.oracle_decrypt root trace_prefix
          (inl packed_x, packed_local_trace))
        (IndCpadGame.IndCpadOracle max_queries)) mem =1
    Pr_code
      (code_link
        (compile_calls_from_trace_step_cont q
          (X := nat) (Y := chOption message)
          (IndCpadSimDecryptOracle max_queries)
          IndCpadGame.oracle_decrypt root trace_prefix
          (inl packed_x, packed_local_trace))
        (IndCpadSimDecryptOracle max_queries)) mem.
  Proof.
    move=> Hx Hrec out.
    rewrite /compile_calls_from_trace_step_cont /call_from_package Hx /=.
    rewrite !code_link_bind.
    rewrite (@code_link_resolve_closed_with nat (chOption message)
      IndCpadGame.oracle_mem_spec IndCpadGame.IndCpadAdv_import
      (IndCpadSimDecryptOracle max_queries)
      (IndCpadGame.IndCpadOracle max_queries)
      IndCpadGame.oracle_decrypt i
      (IndCpadSimDecryptOracle_valid max_queries)
      ind_cpad_decrypt_in_adv_import).
    rewrite (@code_link_resolve_closed_with nat (chOption message)
      IndCpadGame.oracle_mem_spec IndCpadGame.IndCpadAdv_import
      (IndCpadSimDecryptOracle max_queries)
      (IndCpadSimDecryptOracle max_queries)
      IndCpadGame.oracle_decrypt i
      (IndCpadSimDecryptOracle_valid max_queries)
      ind_cpad_decrypt_in_adv_import).
    rewrite !Pr_code_bind.
    apply: eq_in_dlet.
    - move=> ymem Hymem out'.
      case: ymem Hymem=> y mem' Hymem.
      exact: (Hrec y mem' Hymem out').
    - by [].
  Qed.

  Lemma run_until_next_call_aux_done_continue_from_trace
      (A : choice_type) (root prog : raw_code A) fn
      trace_prefix local_trace P mem b packed_local_trace mem' :
    continue_from_trace root (trace_prefix ++ local_trace) = Some prog ->
    ((inr b, packed_local_trace), mem') \in
      dinsupp (Pr_code
        (code_link (run_until_next_call_aux prog fn local_trace) P) mem) ->
    continue_from_trace root
      (trace_prefix ++ unpack_trace packed_local_trace) = Some (ret b).
  Proof.
    move: root trace_prefix local_trace mem b packed_local_trace mem'.
    elim: prog=> [a|o x k IH|l k IH|l v k IH|op k IH]
      root trace_prefix local_trace mem b packed_local_trace mem'
      Hcur Hsupp /=.
    - rewrite /code_link /= Pr_code_ret in Hsupp.
      have Heq := @in_dunit R
        (F_choice_prod_obj
          (Base.npair (suspended_program (A := A) : choiceType)
            (heap : choiceType)))
        ((inr a, pack_trace local_trace), mem)
        ((inr b, packed_local_trace), mem') Hsupp.
      inversion Heq; subst.
      by rewrite unpack_pack_trace.
    - case: o x k IH Hcur Hsupp=> f [S T] x k IH Hcur Hsupp /=.
      case Hfid: (f == fn)%bool.
      + rewrite /= Hfid /code_link /= Pr_code_ret in Hsupp.
        have Heq := @in_dunit R
          (F_choice_prod_obj
            (Base.npair (suspended_program (A := A) : choiceType)
              (heap : choiceType)))
          ((inl (pickle x), pack_trace local_trace), mem)
          ((inr b, packed_local_trace), mem') Hsupp.
        by inversion Heq.
      + rewrite /= Hfid /code_link /= Pr_code_bind in Hsupp.
        have [mid Hmid Hinner] := @dinsupp_dlet R _ _ _ _ _ Hsupp.
        case: mid Hmid Hinner=> y mem_mid Hmid Hinner.
        have Hnext :
            continue_from_trace root
              (trace_prefix ++ rcons local_trace (call_entry (pickle y))) =
            Some (k y).
          rewrite -rcons_cat -cats1.
          rewrite (@continue_from_trace_cat A root
            (opr (f, (S, T)) x k)
            (trace_prefix ++ local_trace) [:: call_entry (pickle y)]
            Hcur) /= /decode_call_entry.
          by rewrite pickleK continue_from_trace_nil.
        exact: (IH y root trace_prefix
          (rcons local_trace (call_entry (pickle y))) mem_mid b
          packed_local_trace mem' Hnext Hinner).
    - rewrite Pr_code_get in Hsupp.
      have Hnext :
          continue_from_trace root
            (trace_prefix ++ rcons local_trace
              (get_entry (pickle (get_heap mem l)))) =
          Some (k (get_heap mem l)).
        rewrite -rcons_cat -cats1.
        rewrite (@continue_from_trace_cat A root (getr l k)
          (trace_prefix ++ local_trace)
          [:: get_entry (pickle (get_heap mem l))] Hcur)
          /= /decode_get_entry.
        by rewrite pickleK continue_from_trace_nil.
      exact: (IH (get_heap mem l) root trace_prefix
        (rcons local_trace (get_entry (pickle (get_heap mem l)))) mem b
        packed_local_trace mem' Hnext Hsupp).
    - rewrite Pr_code_put in Hsupp.
      have Hnext :
          continue_from_trace root
            (trace_prefix ++ rcons local_trace put_entry) = Some k.
        rewrite -rcons_cat -cats1.
        by rewrite (@continue_from_trace_cat A root (putr l v k)
          (trace_prefix ++ local_trace) [:: put_entry] Hcur)
          /= continue_from_trace_nil.
      exact: (IH root trace_prefix (rcons local_trace put_entry)
        (set_heap mem l v) b packed_local_trace mem' Hnext Hsupp).
    - rewrite Pr_code_sample in Hsupp.
      have [a _ Hinner] := @dinsupp_dlet R _ _ _ _ _ Hsupp.
      have Hnext :
          continue_from_trace root
            (trace_prefix ++ rcons local_trace
              (sample_entry (pickle a))) =
          Some (k a).
        rewrite -rcons_cat -cats1.
        rewrite (@continue_from_trace_cat A root (sampler op k)
          (trace_prefix ++ local_trace)
          [:: sample_entry (pickle a)] Hcur)
          /= /decode_sample_entry.
        by rewrite pickleK continue_from_trace_nil.
      exact: (IH a root trace_prefix
        (rcons local_trace (sample_entry (pickle a))) mem b
        packed_local_trace mem' Hnext Hinner).
  Qed.

  Lemma run_until_next_call_done_continue_from_trace
      (A : choice_type) (root prog : raw_code A) fn
      trace_prefix P mem b packed_local_trace mem' :
    continue_from_trace root trace_prefix = Some prog ->
    ((inr b, packed_local_trace), mem') \in
      dinsupp (Pr_code
        (code_link (run_until_next_call prog fn) P) mem) ->
    continue_from_trace root
      (trace_prefix ++ unpack_trace packed_local_trace) = Some (ret b).
  Proof.
    rewrite /run_until_next_call.
    move=> Hcur Hsupp.
    have Hcur0 :
        continue_from_trace root (trace_prefix ++ [::]) = Some prog.
      by rewrite cats0.
    exact: (run_until_next_call_aux_done_continue_from_trace
      A root prog fn trace_prefix [::] P mem b packed_local_trace mem'
      Hcur0 Hsupp).
  Qed.

  Lemma run_until_next_call_aux_decrypt_call_continue_from_trace
      (A : choice_type) (L : Locations) (root prog : raw_code A)
      trace_prefix local_trace P mem packed_x packed_local_trace mem'
      i (y : chOption message) :
    ValidCode L IndCpadGame.IndCpadAdv_import prog ->
    continue_from_trace root (trace_prefix ++ local_trace) = Some prog ->
    ((inl packed_x, packed_local_trace), mem') \in
      dinsupp (Pr_code
        (code_link
          (run_until_next_call_aux prog IndCpadGame.oracle_decrypt
            local_trace) P) mem) ->
    (unpickle packed_x : option nat) = Some i ->
    exists prog',
      continue_from_trace root
        (rcons (trace_prefix ++ unpack_trace packed_local_trace)
          (call_entry (pickle y))) = Some prog'.
  Proof.
    move=> Hvalid.
    have Hvc := valid_code_from_class L
      IndCpadGame.IndCpadAdv_import A prog Hvalid.
    move: root trace_prefix local_trace mem packed_x packed_local_trace mem' i.
    elim: Hvc=> [a|o x k Ho Hk IH|l k Hl Hk IH
        |l v k Hl Hk IH|op k Hk IH]
      root trace_prefix local_trace mem packed_x packed_local_trace mem' i
      Hcur Hsupp Hx /=.
    - rewrite /code_link /= Pr_code_ret in Hsupp.
      have Heq := @in_dunit R
        (F_choice_prod_obj
          (Base.npair (suspended_program (A := A) : choiceType)
            (heap : choiceType)))
        ((inr a, pack_trace local_trace), mem)
        ((inl packed_x, packed_local_trace), mem') Hsupp.
      by inversion Heq.
    - case: o Ho x k Hk IH Hcur Hsupp=> f [S T] Ho x k Hk IH
        Hcur Hsupp /=.
      case Hfid: (f == IndCpadGame.oracle_decrypt)%bool.
      + rewrite /= Hfid /code_link /= Pr_code_ret in Hsupp.
        have Heq := @in_dunit R
          (F_choice_prod_obj
            (Base.npair (suspended_program (A := A) : choiceType)
              (heap : choiceType)))
          ((inl (pickle x), pack_trace local_trace), mem)
          ((inl packed_x, packed_local_trace), mem') Hsupp.
        inversion Heq; subst.
        have Hfid_eq : f = IndCpadGame.oracle_decrypt :=
          ident_eqb_eq f IndCpadGame.oracle_decrypt Hfid.
        have Hop : (f, (S, T)) =
            mkopsig IndCpadGame.oracle_decrypt nat (chOption message).
          apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
          * exact: ind_cpad_decrypt_in_adv_import.
          * exact: Ho.
          * exact: Hfid_eq.
        subst f.
        inversion Hop; subst S T.
        exists (k y).
        rewrite unpack_pack_trace -cats1.
        rewrite (@continue_from_trace_cat A root
          (opr (mkopsig IndCpadGame.oracle_decrypt nat (chOption message))
            x k)
          (trace_prefix ++ local_trace) [:: call_entry (pickle y)]
          Hcur) /= /decode_call_entry.
        have HySome :
            (unpickle (pickle y) : option (chOption message)) = Some y.
          by rewrite pickleK.
        move: HySome=> [= Hy].
        by rewrite Hy continue_from_trace_nil.
      + rewrite /= Hfid /code_link /= Pr_code_bind in Hsupp.
        have [mid Hmid Hinner] := @dinsupp_dlet R _ _ _ _ _ Hsupp.
        case: mid Hmid Hinner=> y0 mem_mid Hmid Hinner.
        have Hnext :
            continue_from_trace root
              (trace_prefix ++ rcons local_trace
                (call_entry (pickle y0))) =
            Some (k y0).
          rewrite -rcons_cat -cats1.
          rewrite (@continue_from_trace_cat A root
            (opr (f, (S, T)) x k)
            (trace_prefix ++ local_trace) [:: call_entry (pickle y0)]
            Hcur) /= /decode_call_entry.
          by rewrite pickleK continue_from_trace_nil.
        exact: (IH y0 root trace_prefix
          (rcons local_trace (call_entry (pickle y0))) mem_mid
          packed_x packed_local_trace mem' i Hnext Hinner Hx).
    - rewrite Pr_code_get in Hsupp.
      have Hnext :
          continue_from_trace root
            (trace_prefix ++ rcons local_trace
              (get_entry (pickle (get_heap mem l)))) =
          Some (k (get_heap mem l)).
        rewrite -rcons_cat -cats1.
        rewrite (@continue_from_trace_cat A root (getr l k)
          (trace_prefix ++ local_trace)
          [:: get_entry (pickle (get_heap mem l))] Hcur)
          /= /decode_get_entry.
        by rewrite pickleK continue_from_trace_nil.
      exact: (IH (get_heap mem l) root trace_prefix
        (rcons local_trace (get_entry (pickle (get_heap mem l)))) mem
        packed_x packed_local_trace mem' i Hnext Hsupp Hx).
    - rewrite Pr_code_put in Hsupp.
      have Hnext :
          continue_from_trace root
            (trace_prefix ++ rcons local_trace put_entry) = Some k.
        rewrite -rcons_cat -cats1.
        by rewrite (@continue_from_trace_cat A root (putr l v k)
          (trace_prefix ++ local_trace) [:: put_entry] Hcur)
          /= continue_from_trace_nil.
      exact: (IH root trace_prefix (rcons local_trace put_entry)
        (set_heap mem l v) packed_x packed_local_trace mem' i
        Hnext Hsupp Hx).
    - rewrite Pr_code_sample in Hsupp.
      have [a _ Hinner] := @dinsupp_dlet R _ _ _ _ _ Hsupp.
      have Hnext :
          continue_from_trace root
            (trace_prefix ++ rcons local_trace
              (sample_entry (pickle a))) =
          Some (k a).
        rewrite -rcons_cat -cats1.
        rewrite (@continue_from_trace_cat A root (sampler op k)
          (trace_prefix ++ local_trace)
          [:: sample_entry (pickle a)] Hcur)
          /= /decode_sample_entry.
        by rewrite pickleK continue_from_trace_nil.
      exact: (IH a root trace_prefix
        (rcons local_trace (sample_entry (pickle a))) mem packed_x
        packed_local_trace mem' i Hnext Hinner Hx).
  Qed.

  Lemma run_until_next_call_decrypt_call_continue_from_trace
      (A : choice_type) (L : Locations) (root prog : raw_code A)
      trace_prefix P mem packed_x packed_local_trace mem'
      i (y : chOption message) :
    ValidCode L IndCpadGame.IndCpadAdv_import prog ->
    continue_from_trace root trace_prefix = Some prog ->
    ((inl packed_x, packed_local_trace), mem') \in
      dinsupp (Pr_code
        (code_link
          (run_until_next_call prog IndCpadGame.oracle_decrypt) P) mem) ->
    (unpickle packed_x : option nat) = Some i ->
    exists prog',
      continue_from_trace root
        (rcons (trace_prefix ++ unpack_trace packed_local_trace)
          (call_entry (pickle y))) = Some prog'.
  Proof.
    rewrite /run_until_next_call.
    move=> Hvalid Hcur Hsupp Hx.
    have Hcur0 :
        continue_from_trace root (trace_prefix ++ [::]) = Some prog.
      by rewrite cats0.
    exact: (run_until_next_call_aux_decrypt_call_continue_from_trace
      A L root prog trace_prefix [::] P mem packed_x packed_local_trace
      mem' i y Hvalid Hcur0 Hsupp Hx).
  Qed.

  Lemma compile_calls_step_cont_done_real_sim_decrypt_eq
      (q : nat) (A : choice_type) (root : raw_code A)
      trace_prefix b packed_local_trace max_queries mem :
    continue_from_trace root
      (trace_prefix ++ unpack_trace packed_local_trace) = Some (ret b) ->
    Pr_code
      (code_link
        (compile_calls_from_trace_step_cont q
          (X := nat) (Y := chOption message)
          (IndCpadSimDecryptOracle max_queries)
          IndCpadGame.oracle_decrypt root trace_prefix
          (inr b, packed_local_trace))
        (IndCpadGame.IndCpadOracle max_queries)) mem =1
    Pr_code
      (code_link
        (compile_calls_from_trace_step_cont q
          (X := nat) (Y := chOption message)
          (IndCpadSimDecryptOracle max_queries)
          IndCpadGame.oracle_decrypt root trace_prefix
          (inr b, packed_local_trace))
        (IndCpadSimDecryptOracle max_queries)) mem.
  Proof.
    move=> Hcont out.
    by rewrite /compile_calls_from_trace_step_cont /= unpack_pack_trace Hcont.
  Qed.

  Lemma ind_cpad_sim_decrypt_code_increments_decrypt_count
      max_queries i mem out :
    out \in dinsupp (Pr_code (ind_cpad_sim_decrypt_code max_queries i) mem) ->
    get_heap out.2 IndCpadGame.decrypt_count_addr =
      (get_heap mem IndCpadGame.decrypt_count_addr).+1.
  Proof.
    rewrite /ind_cpad_sim_decrypt_code=> Hout.
    rewrite Pr_code_get in Hout.
    have [Hcount Hafter_count] := dinsupp_assertD _ _ _ _ Hout.
    rewrite Pr_code_put in Hafter_count.
    set mem1 := set_heap mem IndCpadGame.decrypt_count_addr
      (get_heap mem IndCpadGame.decrypt_count_addr).+1.
    rewrite Pr_code_get in Hafter_count.
    have [Hi Hafter_i] := dinsupp_assertD _ _ _ _ Hafter_count.
    rewrite /= in Hafter_i.
    case Hnth:
        (nth_valid (get_heap mem1 IndCpadGame.table_addr) i Hi)=>
      [[m0 m1] c] in Hafter_i *.
    destruct (eq_op m0 m1) eqn:Heq.
    - have [Hc Hafter_c] := dinsupp_assertD _ _ _ _ Hafter_i.
      case Hcopt: c Hc Hafter_c=> [[data error_bound]|] Hc Hafter_c.
      + rewrite Pr_code_sample in Hafter_c.
        have [noise _ Hinner] := @dinsupp_dlet R _ _ _ _ _ Hafter_c.
        rewrite Pr_code_ret in Hinner.
        have -> :
            out =
            (Some
              (inverse_isometry m0
                (ivec_add (IndCpaDSim.toIntVec noise)
                  (isometry m0 m0))), mem1).
          exact: in_dunit Hinner.
        by rewrite /mem1 get_set_heap_eq.
      + by [].
    - rewrite Pr_code_ret in Hafter_i.
      have -> : out = (None, mem1).
        exact: in_dunit Hafter_i.
      by rewrite /mem1 get_set_heap_eq.
  Qed.

  Lemma ind_cpad_sim_decrypt_resolve_increments_decrypt_count
      max_queries i mem out :
    out \in dinsupp (Pr_code
      (resolve (IndCpadSimDecryptOracle max_queries)
        (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) i)
      mem) ->
    get_heap out.2 IndCpadGame.decrypt_count_addr =
      (get_heap mem IndCpadGame.decrypt_count_addr).+1.
  Proof.
    rewrite ind_cpad_sim_decrypt_resolveE.
    exact: ind_cpad_sim_decrypt_code_increments_decrypt_count.
  Qed.

  Lemma code_link_compile_calls_from_trace_real_sim_decrypt_budget_eq
      (q : nat) (A : choice_type) (L : Locations)
      (root prog : raw_code A) trace_prefix max_queries mem :
    ValidCode L IndCpadGame.IndCpadAdv_import root ->
    fseparate IndCpadGame.oracle_mem_spec L ->
    continue_from_trace root trace_prefix = Some prog ->
    (max_queries <=
      get_heap mem IndCpadGame.decrypt_count_addr + q)%N ->
    Pr_code
      (code_link
        (compile_calls_from_trace q
          (X := nat) (Y := chOption message)
          (IndCpadSimDecryptOracle max_queries)
          IndCpadGame.oracle_decrypt root trace_prefix)
        (IndCpadGame.IndCpadOracle max_queries)) mem =1
    Pr_code
      (code_link
        (compile_calls_from_trace q
          (X := nat) (Y := chOption message)
          (IndCpadSimDecryptOracle max_queries)
          IndCpadGame.oracle_decrypt root trace_prefix)
        (IndCpadSimDecryptOracle max_queries)) mem.
  Proof.
    move=> Hvalid Hsep.
    move: q trace_prefix prog mem.
    elim=> [|q IH] trace_prefix prog mem Htrace Hbudget out.
    - rewrite /compile_calls_from_trace /= unpack_pack_trace Htrace.
      have Hprog_valid :
          ValidCode L IndCpadGame.IndCpadAdv_import prog.
        exact: (continue_from_trace_valid L
          IndCpadGame.IndCpadAdv_import root prog trace_prefix
          Hvalid Htrace).
      have Hbound : decrypt_count_over_bound max_queries mem.
        rewrite /decrypt_count_over_bound.
        move: Hbudget.
        by rewrite addn0 -leqNgt.
      exact: (code_link_real_sim_decrypt_over_bound_eq
        A L prog max_queries mem Hprog_valid Hsep Hbound out).
    - have Hprog_valid :
          ValidCode L IndCpadGame.IndCpadAdv_import prog.
        exact: (continue_from_trace_valid L
          IndCpadGame.IndCpadAdv_import root prog trace_prefix
          Hvalid Htrace).
      rewrite (@codeLinkCompileCallsFromTraceS_decompose q
        nat (chOption message) A
        (IndCpadSimDecryptOracle max_queries)
        (IndCpadGame.IndCpadOracle max_queries)
        IndCpadGame.oracle_decrypt root prog trace_prefix Htrace).
      rewrite (@codeLinkCompileCallsFromTraceS_decompose q
        nat (chOption message) A
        (IndCpadSimDecryptOracle max_queries)
        (IndCpadSimDecryptOracle max_queries)
        IndCpadGame.oracle_decrypt root prog trace_prefix Htrace).
      rewrite !Pr_code_bind.
      apply: eq_in_dlet.
      + move=> smem Hsmem out'.
        case: smem Hsmem=> s mem' Hsmem.
        case: s Hsmem=> [[packed_x|b] packed_local_trace] Hsmem.
        * case Hx: (unpickle packed_x : option nat)=> [i|].
          -- apply: (compile_calls_step_cont_valid_call_real_sim_decrypt_reduction
              q A root trace_prefix packed_x packed_local_trace i
              max_queries mem' Hx).
             move=> y mem'' Hy out''.
             have Hprefix_count :=
               code_link_run_until_next_call_real_preserves_decrypt_count
                 A L prog max_queries mem
                 ((inl packed_x, packed_local_trace), mem')
                 Hprog_valid Hsep Hsmem.
             have Hinc :=
               ind_cpad_sim_decrypt_resolve_increments_decrypt_count
                 max_queries i mem' (y, mem'') Hy.
             have [prog' Htrace'] :=
               run_until_next_call_decrypt_call_continue_from_trace
                 A L root prog trace_prefix
                 (IndCpadGame.IndCpadOracle max_queries) mem
                 packed_x packed_local_trace mem' i y
                 Hprog_valid Htrace Hsmem Hx.
             have Hbudget' :
                 (max_queries <=
                   get_heap mem'' IndCpadGame.decrypt_count_addr + q)%N.
               rewrite Hinc Hprefix_count.
               by rewrite addSn -addnS.
             exact: (IH
               (rcons (trace_prefix ++ unpack_trace packed_local_trace)
                 (call_entry (pickle y)))
               prog' mem'' Htrace' Hbudget' out'').
          -- have Hcall :
                call_from_package (X := nat) (Y := chOption message)
                  (IndCpadSimDecryptOracle max_queries)
                  IndCpadGame.oracle_decrypt packed_x = None.
               by rewrite /call_from_package Hx.
             exact: (compile_calls_step_cont_invalid_call_real_sim_decrypt_eq
               q A root trace_prefix packed_x packed_local_trace
               max_queries mem' Hcall out').
        * have Hcont :=
            run_until_next_call_done_continue_from_trace
              A root prog IndCpadGame.oracle_decrypt trace_prefix
              (IndCpadGame.IndCpadOracle max_queries) mem b
              packed_local_trace mem' Htrace Hsmem.
          exact: (compile_calls_step_cont_done_real_sim_decrypt_eq
            q A root trace_prefix b packed_local_trace max_queries mem'
            Hcont out').
      + exact: (code_link_run_until_next_call_real_sim_decrypt_eq
          A L prog max_queries mem Hprog_valid).
  Qed.

  Lemma ind_cpad_decrypt_prefix_code_preserves_challenge_heap_valid
      max_queries :
    ⊨Hoare ⦃ fun in_mem => challenge_heap_valid in_mem.2 ⦄
      (ind_cpad_decrypt_prefix_code max_queries)
    ⦃ fun out_mem => challenge_heap_valid out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> [i mem Hinv] out Hout.
    rewrite /ind_cpad_decrypt_prefix_code in Hout.
    rewrite Pr_code_get in Hout.
    have [Hcount Hafter_count] := dinsupp_assertD _ _ _ _ Hout.
    rewrite Pr_code_put in Hafter_count.
    set mem1 := set_heap mem IndCpadGame.decrypt_count_addr
      (get_heap mem IndCpadGame.decrypt_count_addr).+1.
    have Hinv1 : challenge_heap_valid mem1.
      rewrite /mem1.
      exact: challenge_heap_valid_set_decrypt_count.
    rewrite Pr_code_get in Hafter_count.
    have [Hi Hafter_i] := dinsupp_assertD _ _ _ _ Hafter_count.
    rewrite Pr_code_ret in Hafter_i.
    have -> : out =
        (nth_valid (get_heap mem1 IndCpadGame.table_addr) i Hi, mem1).
      exact: in_dunit Hafter_i.
    exact: Hinv1.
  Qed.

  Definition challenge_decrypt_prefix_row_valid
      (row : IndCpadGame.challenger_table_row) (mem : heap) : bool :=
    challenge_heap_valid mem &&
    match get_heap mem IndCpadGame.sk_addr with
    | Some sk =>
        row_valid_for_branch sk (get_heap mem IndCpadGame.bit_addr) row
    | None => true
    end.

  Definition challenge_decrypt_prefix_row_ready
      (row : IndCpadGame.challenger_table_row) (mem : heap) : bool :=
    challenge_heap_valid mem &&
    match get_heap mem IndCpadGame.sk_addr with
    | Some sk =>
        row_valid_for_branch sk (get_heap mem IndCpadGame.bit_addr) row
    | None => false
    end.

  Definition challenge_decrypt_prefix_row_vector_bound
      (row : IndCpadGame.challenger_table_row) (mem : heap) : bool :=
    let '(m0, m1, c) := row in
    if m0 == m1 then
      match get_heap mem IndCpadGame.sk_addr, c with
      | Some sk, Some (data, error_bound) =>
          (ivec_dist ivec_zero (isometry (deterministic_dec sk c) m0)
            <= error_bound)%N
      | _, _ => false
      end
    else true.

  Definition challenge_decrypt_prefix_row_ready_vector_bound
      (row : IndCpadGame.challenger_table_row) (mem : heap) : bool :=
    challenge_decrypt_prefix_row_ready row mem &&
    challenge_decrypt_prefix_row_vector_bound row mem.

  Definition decrypt_prefix_ready_vector_bound_cert max_queries : Prop :=
    ⊨Hoare ⦃ fun in_mem => challenge_heap_valid in_mem.2 ⦄
      (ind_cpad_decrypt_prefix_code max_queries)
    ⦃ fun out_mem =>
      challenge_decrypt_prefix_row_ready_vector_bound out_mem.1 out_mem.2 ⦄.

  Lemma challenge_decrypt_prefix_row_valid_equal_messages_some
      mem sk m c :
    challenge_decrypt_prefix_row_valid (m, m, c) mem ->
    get_heap mem IndCpadGame.sk_addr = Some sk ->
    exists data error_bound,
      c = Some (data, error_bound) /\
      (metric (deterministic_dec sk c) m <= error_bound)%N.
  Proof.
    rewrite /challenge_decrypt_prefix_row_valid=> /andP [_ Hrow] Hsk.
    rewrite Hsk in Hrow.
    exact: (row_valid_for_branch_equal_messages_some sk
      (get_heap mem IndCpadGame.bit_addr) m c Hrow).
  Qed.

  Lemma challenge_decrypt_prefix_row_ready_equal_messages_some
      mem m c :
    challenge_decrypt_prefix_row_ready (m, m, c) mem ->
    exists sk data error_bound,
      get_heap mem IndCpadGame.sk_addr = Some sk /\
      c = Some (data, error_bound) /\
      (metric (deterministic_dec sk c) m <= error_bound)%N.
  Proof.
    rewrite /challenge_decrypt_prefix_row_ready=> /andP [Hinv Hrow].
    case Hsk: (get_heap mem IndCpadGame.sk_addr)=> [sk|] //= in Hrow.
    have [data [error_bound [Hc Hmetric]]] :=
      row_valid_for_branch_equal_messages_some sk
        (get_heap mem IndCpadGame.bit_addr) m c Hrow.
    by exists sk, data, error_bound.
  Qed.

  Lemma challenge_decrypt_prefix_row_ready_vector_bound_equal_messages_some
      mem m c :
    challenge_decrypt_prefix_row_ready_vector_bound (m, m, c) mem ->
    exists sk data error_bound,
      get_heap mem IndCpadGame.sk_addr = Some sk /\
      c = Some (data, error_bound) /\
      (ivec_dist ivec_zero (isometry (deterministic_dec sk c) m)
        <= error_bound)%N.
  Proof.
    rewrite /challenge_decrypt_prefix_row_ready_vector_bound=>
      /andP [Hready Hvec].
    rewrite /challenge_decrypt_prefix_row_vector_bound eqxx in Hvec.
    case Hsk: (get_heap mem IndCpadGame.sk_addr)=> [sk|] //= in Hvec.
    case Hc: c=> [[data error_bound]|] //= in Hvec.
    exists sk, data, error_bound.
    split; first exact: Hsk.
    split; first exact: Hc.
    by rewrite Hc.
  Qed.

  Lemma challenge_decrypt_prefix_row_ready_vector_bound_from_ready
      row mem :
    challenge_decrypt_prefix_row_ready row mem ->
    challenge_decrypt_prefix_row_ready_vector_bound row mem.
  Proof.
    move=> Hready.
    rewrite /challenge_decrypt_prefix_row_ready_vector_bound Hready /=.
    case: row Hready=> [[m0 m1] c] Hready.
    rewrite /challenge_decrypt_prefix_row_vector_bound.
    destruct (eq_op m0 m1) eqn:Heq=> //.
    have Hm : m0 = m1 := eqP Heq.
    subst m1.
    have [sk [data [error_bound [Hsk [Hc Hmetric]]]]] :=
      challenge_decrypt_prefix_row_ready_equal_messages_some
        mem m0 c Hready.
    rewrite Hsk Hc /=.
    rewrite Hc in Hmetric.
    by rewrite -metric_chartE.
  Qed.

  Lemma ind_cpad_decrypt_prefix_code_certifies_row max_queries :
    ⊨Hoare ⦃ fun in_mem => challenge_heap_valid in_mem.2 ⦄
      (ind_cpad_decrypt_prefix_code max_queries)
    ⦃ fun out_mem =>
      challenge_decrypt_prefix_row_valid out_mem.1 out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> [i mem Hinv] out Hout.
    rewrite /ind_cpad_decrypt_prefix_code in Hout.
    rewrite Pr_code_get in Hout.
    have [Hcount Hafter_count] := dinsupp_assertD _ _ _ _ Hout.
    rewrite Pr_code_put in Hafter_count.
    set mem1 := set_heap mem IndCpadGame.decrypt_count_addr
      (get_heap mem IndCpadGame.decrypt_count_addr).+1.
    have Hinv1 : challenge_heap_valid mem1.
      rewrite /mem1.
      exact: challenge_heap_valid_set_decrypt_count.
    rewrite Pr_code_get in Hafter_count.
    have [Hi Hafter_i] := dinsupp_assertD _ _ _ _ Hafter_count.
    rewrite Pr_code_ret in Hafter_i.
    have -> : out =
        (nth_valid (get_heap mem1 IndCpadGame.table_addr) i Hi, mem1).
      exact: in_dunit Hafter_i.
    rewrite /challenge_decrypt_prefix_row_valid Hinv1 /=.
    case Hsk: (get_heap mem1 IndCpadGame.sk_addr)=> [sk|] //=.
    have [pk [evk [_ _ _ Htable]]] :=
      challenge_heap_valid_sk_initialized mem1 sk Hinv1 Hsk.
    exact: (table_valid_for_branch_nth sk
      (get_heap mem1 IndCpadGame.bit_addr)
      (get_heap mem1 IndCpadGame.table_addr) i Hi Htable).
  Qed.

  Lemma ind_cpad_decrypt_prefix_code_readies_row max_queries :
    ⊨Hoare ⦃ fun in_mem => challenge_heap_valid in_mem.2 ⦄
      (ind_cpad_decrypt_prefix_code max_queries)
    ⦃ fun out_mem =>
      challenge_decrypt_prefix_row_ready out_mem.1 out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> [i mem Hinv] out Hout.
    rewrite /ind_cpad_decrypt_prefix_code in Hout.
    rewrite Pr_code_get in Hout.
    have [Hcount Hafter_count] := dinsupp_assertD _ _ _ _ Hout.
    rewrite Pr_code_put in Hafter_count.
    set mem1 := set_heap mem IndCpadGame.decrypt_count_addr
      (get_heap mem IndCpadGame.decrypt_count_addr).+1.
    have Hinv1 : challenge_heap_valid mem1.
      rewrite /mem1.
      exact: challenge_heap_valid_set_decrypt_count.
    rewrite Pr_code_get in Hafter_count.
    have [Hi Hafter_i] := dinsupp_assertD _ _ _ _ Hafter_count.
    rewrite Pr_code_ret in Hafter_i.
    have -> : out =
        (nth_valid (get_heap mem1 IndCpadGame.table_addr) i Hi, mem1).
      exact: in_dunit Hafter_i.
    rewrite /challenge_decrypt_prefix_row_ready Hinv1 /=.
    case Hsk: (get_heap mem1 IndCpadGame.sk_addr)=> [sk|] /=.
    - have [pk [evk [_ _ _ Htable]]] :=
        challenge_heap_valid_sk_initialized mem1 sk Hinv1 Hsk.
      exact: (table_valid_for_branch_nth sk
        (get_heap mem1 IndCpadGame.bit_addr)
        (get_heap mem1 IndCpadGame.table_addr) i Hi Htable).
    case Hpk: (get_heap mem1 IndCpadGame.pk_addr)=> [pk|].
      move: Hinv1; rewrite /challenge_heap_valid Hpk Hsk.
      by case: (get_heap mem1 IndCpadGame.evk_addr).
    case Hevk: (get_heap mem1 IndCpadGame.evk_addr)=> [evk|].
      by move: Hinv1; rewrite /challenge_heap_valid Hpk Hevk.
    move: Hinv1.
    rewrite /challenge_heap_valid Hpk Hevk Hsk=> /eqP Htable_empty.
    clear Hafter_i.
    move: Hi.
    by rewrite Htable_empty.
  Qed.

  Lemma ind_cpad_decrypt_prefix_code_readies_row_vector_bound
      max_queries :
    decrypt_prefix_ready_vector_bound_cert max_queries.
  Proof.
    rewrite /decrypt_prefix_ready_vector_bound_cert /hoareJudgment=>
      [i mem Hinv] out Hout.
    have Hready := ind_cpad_decrypt_prefix_code_readies_row max_queries.
    move: Hready; rewrite /hoareJudgment=> Hready.
    exact: (challenge_decrypt_prefix_row_ready_vector_bound_from_ready
      out.1 out.2 (Hready i mem Hinv out Hout)).
  Qed.

  Lemma ind_cpad_decrypt_cont_neq_pyth m0 m1 c :
    m0 != m1 ->
    ⊨Pyth1 ⦃ fun inps =>
      let '((_, memL), (_, memR)) := inps in eq_op memL memR ⦄
      (fun _ : chUnit => ind_cpad_real_decrypt_cont (m0, m1, c))
      ≈( 0 )
      (fun _ : chUnit => ind_cpad_sim_decrypt_cont (m0, m1, c))
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    move=> Hneq.
    rewrite /ind_cpad_real_decrypt_cont /ind_cpad_sim_decrypt_cont.
    rewrite (negbTE Hneq).
    apply: pythReflRule.
    - by move=> i; rewrite [i]ord1.
    - move=> memL memR [] [] /eqP Hmem.
      by split.
    - by move=> mem [] y Hpre Hy.
  Qed.

  Lemma ind_cpad_real_decrypt_cont_eq_codeE mem sk m c :
    get_heap mem IndCpadGame.sk_addr = Some sk ->
    Pr_code (ind_cpad_real_decrypt_cont (m, m, c)) mem =1
    Pr_code
      (m' <$ (message; NF.decrypt sk c) ;;
       ret (Some m'))
      mem.
  Proof.
    move=> Hsk out.
    rewrite /ind_cpad_real_decrypt_cont eqxx Pr_code_get Hsk.
    by rewrite /assertD.
  Qed.

  Lemma ind_cpad_sim_decrypt_cont_eq_codeE mem m c data error_bound :
    c = Some (data, error_bound) ->
    Pr_code (ind_cpad_sim_decrypt_cont (m, m, c)) mem =1
    Pr_code
      (noise <$ (chVec chInt dim;
        discrete_gaussians (IndCpaDSim.zeroChVec dim)
          (noise_flooding_dg_stdev
            gaussian_width_multiplier error_bound)) ;;
       let res :=
         inverse_isometry m
           (ivec_add (IndCpaDSim.toIntVec noise) (isometry m m)) in
       ret (Some res))
      mem.
  Proof.
    move=> -> out.
    rewrite /ind_cpad_sim_decrypt_cont eqxx.
    by rewrite /assertD.
  Qed.

  Lemma ind_cpad_decrypt_cont_eq_pyth m c :
    ⊨Pyth ⦃ fun inps =>
      let '((_, memL), (_, memR)) := inps in
      (eq_op memL memR) &&
      challenge_decrypt_prefix_row_ready (m, m, c) memL ⦄
      (fun _ : chUnit => ind_cpad_real_decrypt_cont (m, m, c))
      ≈( cat_tuple
        [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0] )
      (fun _ : chUnit => ind_cpad_sim_decrypt_cont (m, m, c))
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    split.
    - move=> i.
      apply: (cat_tuple_nonneg
        [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0] i).
      + move=> j.
        by rewrite [j]ord1 noise_flooding_call_error_nonnegative.
      + by move=> j; rewrite [j]ord1.
    move=> memL memR [] [] Hpre.
    move/andP: Hpre=> [/eqP Hmem Hready].
    subst memR.
    have [sk [data [error_bound [Hsk [Hc Hmetric]]]]] :=
      challenge_decrypt_prefix_row_ready_equal_messages_some
        memL m c Hready.
    subst c.
    have Hpyth :=
      noise_flooding_successful_decrypt_code_pyth
        sk data error_bound m Hmetric.
    move: Hpyth=> [_ Hpyth].
    have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
      Hpyth memL memL tt tt (eqxx memL).
    exists P, Q.
    split; first exact: Hdist.
    split.
    - move=> out.
      rewrite (HmarginL out).
      symmetry.
      apply: complete_output_heap_ext=> out'.
      exact: (ind_cpad_real_decrypt_cont_eq_codeE
        memL sk m (Some (data, error_bound)) Hsk out').
    split.
    - move=> out.
      rewrite (HmarginR out).
      symmetry.
      apply: complete_output_heap_ext=> out'.
      exact: (ind_cpad_sim_decrypt_cont_eq_codeE
        memL m (Some (data, error_bound)) data error_bound erefl out').
    split.
    - by move=> y Hy.
    - by move=> y Hy.
  Qed.

  Lemma ind_cpad_decrypt_cont_eq_pyth_from_metric_encoding_ready_vector_bound
      m c :
    ⊨Pyth ⦃ fun inps =>
      let '((_, memL), (_, memR)) := inps in
      (eq_op memL memR) &&
      challenge_decrypt_prefix_row_ready_vector_bound (m, m, c) memL ⦄
      (fun _ : chUnit => ind_cpad_real_decrypt_cont (m, m, c))
      ≈( cat_tuple
        [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0] )
      (fun _ : chUnit => ind_cpad_sim_decrypt_cont (m, m, c))
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    split.
    - move=> i.
      apply: (cat_tuple_nonneg
        [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0] i).
      + move=> j.
        by rewrite [j]ord1 noise_flooding_call_error_nonnegative.
      + by move=> j; rewrite [j]ord1.
    move=> memL memR [] [] Hpre.
    move/andP: Hpre=> [/eqP Hmem Hready].
    subst memR.
    move/andP: Hready=> [Hready _].
    have [sk [data [error_bound [Hsk [Hc Hmetric]]]]] :=
      challenge_decrypt_prefix_row_ready_equal_messages_some
        memL m c Hready.
    subst c.
    have Hpyth :=
      noise_flooding_successful_decrypt_code_pyth_one_chart
        sk data error_bound m Hmetric.
    move: Hpyth=> [_ Hpyth].
    have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
      Hpyth memL memL tt tt (eqxx memL).
    exists P, Q.
    split; first exact: Hdist.
    split.
    - move=> out.
      rewrite (HmarginL out).
      symmetry.
      apply: complete_output_heap_ext=> out'.
      exact: (ind_cpad_real_decrypt_cont_eq_codeE
        memL sk m (Some (data, error_bound)) Hsk out').
    split.
    - move=> out.
      rewrite (HmarginR out).
      symmetry.
      apply: complete_output_heap_ext=> out'.
      exact: (ind_cpad_sim_decrypt_cont_eq_codeE
        memL m (Some (data, error_bound)) data error_bound erefl out').
    split.
    - by move=> y Hy.
    - by move=> y Hy.
  Qed.

  Lemma ind_cpad_decrypt_cont_pyth_from_metric_encoding_ready_vector_bound
      (row : IndCpadGame.challenger_table_row) :
    ⊨Pyth ⦃ fun inps =>
      let '((_, memL), (_, memR)) := inps in
      (eq_op memL memR) &&
      challenge_decrypt_prefix_row_ready_vector_bound row memL ⦄
      (fun _ : chUnit => ind_cpad_real_decrypt_cont row)
      ≈( cat_tuple
        [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0] )
      (fun _ : chUnit => ind_cpad_sim_decrypt_cont row)
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    case: row=> [[m0 m1] c].
    destruct (eq_op m0 m1) eqn:Heq.
    - have Hm : m0 = m1 := eqP Heq.
      subst m1.
      exact: (ind_cpad_decrypt_cont_eq_pyth_from_metric_encoding_ready_vector_bound
        m0 c).
    rewrite /ind_cpad_real_decrypt_cont /ind_cpad_sim_decrypt_cont Heq.
    apply: pythReflRule.
    - move=> i.
      apply: (cat_tuple_nonneg
        [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0] i).
      + move=> j.
        by rewrite [j]ord1 noise_flooding_call_error_nonnegative.
      + by move=> j; rewrite [j]ord1.
    - move=> memL memR [] [] Hpre.
      move/andP: Hpre=> [/eqP Hmem _].
      by split.
    - by move=> mem [] y Hpre Hy.
  Qed.

  Lemma ind_cpad_decrypt_cont_pyth
      (row : IndCpadGame.challenger_table_row) :
    ⊨Pyth ⦃ fun inps =>
      let '((_, memL), (_, memR)) := inps in
      (eq_op memL memR) &&
      challenge_decrypt_prefix_row_ready row memL ⦄
      (fun _ : chUnit => ind_cpad_real_decrypt_cont row)
      ≈( cat_tuple
        [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0] )
      (fun _ : chUnit => ind_cpad_sim_decrypt_cont row)
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    case: row=> [[m0 m1] c].
    destruct (eq_op m0 m1) eqn:Heq.
    - have Hm : m0 = m1 := eqP Heq.
      subst m1.
      exact: (ind_cpad_decrypt_cont_eq_pyth m0 c).
    rewrite /ind_cpad_real_decrypt_cont /ind_cpad_sim_decrypt_cont Heq.
    apply: pythReflRule.
    - move=> i.
      apply: (cat_tuple_nonneg
        [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0] i).
      + move=> j.
        by rewrite [j]ord1 noise_flooding_call_error_nonnegative.
      + by move=> j; rewrite [j]ord1.
    - move=> memL memR [] [] Hpre.
      move/andP: Hpre=> [/eqP Hmem _].
      by split.
    - by move=> mem [] y Hpre Hy.
  Qed.

  Lemma ind_cpad_decrypt_cont_kernel_pyth :
    ⊨Pyth ⦃ fun inps =>
      let '((rowL, memL), (rowR, memR)) := inps in
      (rowL == rowR) && (memL == memR) &&
      challenge_decrypt_prefix_row_ready rowL memL ⦄
      ind_cpad_real_decrypt_cont
      ≈( cat_tuple
        [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0] )
      ind_cpad_sim_decrypt_cont
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    split.
    - move=> i.
      apply: (cat_tuple_nonneg
        [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0] i).
      + move=> j.
        by rewrite [j]ord1 noise_flooding_call_error_nonnegative.
      + by move=> j; rewrite [j]ord1.
    move=> memL memR rowL rowR Hpre.
    move/andP: Hpre=> [/andP [/eqP Hrow /eqP Hmem] Hready].
    subst rowR.
    subst memR.
    have [_ Hpyth] := ind_cpad_decrypt_cont_pyth rowL.
    have Hpre_unit :
        (let '((_, memL0), (_, memR0)) :=
            ((tt, memL), (tt, memL)) in eq_op memL0 memR0) &&
        challenge_decrypt_prefix_row_ready rowL memL.
      by rewrite eqxx Hready.
    exact: (Hpyth memL memL tt tt Hpre_unit).
  Qed.

  Lemma ind_cpad_decrypt_cont_kernel_pyth_from_metric_encoding_ready_vector_bound :
    ⊨Pyth ⦃ fun inps =>
      let '((rowL, memL), (rowR, memR)) := inps in
      (rowL == rowR) && (memL == memR) &&
      challenge_decrypt_prefix_row_ready_vector_bound rowL memL ⦄
      ind_cpad_real_decrypt_cont
      ≈( cat_tuple
        [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0] )
      ind_cpad_sim_decrypt_cont
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    split.
    - move=> i.
      apply: (cat_tuple_nonneg
        [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0] i).
      + move=> j.
        by rewrite [j]ord1 noise_flooding_call_error_nonnegative.
      + by move=> j; rewrite [j]ord1.
    move=> memL memR rowL rowR Hpre.
    move/andP: Hpre=> [/andP [/eqP Hrow /eqP Hmem] Hready].
    subst rowR.
    subst memR.
    have [_ Hpyth] :=
      ind_cpad_decrypt_cont_pyth_from_metric_encoding_ready_vector_bound
        rowL.
    have Hpre_unit :
        (let '((_, memL0), (_, memR0)) :=
            ((tt, memL), (tt, memL)) in eq_op memL0 memR0) &&
        challenge_decrypt_prefix_row_ready_vector_bound rowL memL.
      by rewrite eqxx Hready.
    exact: (Hpyth memL memL tt tt Hpre_unit).
  Qed.

  Lemma ind_cpad_decrypt_factored_pyth max_queries :
    ⊨Pyth ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (fun i : nat =>
        row ← ind_cpad_decrypt_prefix_code max_queries i ;;
        ind_cpad_real_decrypt_cont row)
      ≈( cat_tuple [tuple 0]
        (cat_tuple
          [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0]) )
      (fun i : nat =>
        row ← ind_cpad_decrypt_prefix_code max_queries i ;;
        ind_cpad_sim_decrypt_cont row)
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    apply: (pythHoareSeqRule
      (ind_cpad_decrypt_prefix_code max_queries)
      ind_cpad_real_decrypt_cont
      ind_cpad_sim_decrypt_cont
      (fun in_mem => challenge_heap_valid in_mem.2)
      (same_input_invariant_pre challenge_heap_valid)
      (fun out_mem =>
        challenge_decrypt_prefix_row_ready out_mem.1 out_mem.2)
      (fun _ : chOption message * heap => true)
      (cat_tuple
        [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0])).
    - move=> memL memR iL iR Hpre.
      move/andP: Hpre=> [/andP [/eqP Hi /eqP Hmem] Hinv].
      by split; [exact: Hi | split].
    - exact: ind_cpad_decrypt_prefix_code_readies_row.
    - exact: ind_cpad_decrypt_cont_kernel_pyth.
  Qed.

  Lemma ind_cpad_decrypt_factored_pyth_from_metric_encoding_ready_vector_bound
      max_queries :
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    ⊨Pyth ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (fun i : nat =>
        row ← ind_cpad_decrypt_prefix_code max_queries i ;;
        ind_cpad_real_decrypt_cont row)
      ≈( cat_tuple [tuple 0]
        (cat_tuple
          [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0]) )
      (fun i : nat =>
        row ← ind_cpad_decrypt_prefix_code max_queries i ;;
        ind_cpad_sim_decrypt_cont row)
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    move=> Hprefix_vector.
    apply: (pythHoareSeqRule
      (ind_cpad_decrypt_prefix_code max_queries)
      ind_cpad_real_decrypt_cont
      ind_cpad_sim_decrypt_cont
      (fun in_mem => challenge_heap_valid in_mem.2)
      (same_input_invariant_pre challenge_heap_valid)
      (fun out_mem =>
        challenge_decrypt_prefix_row_ready_vector_bound out_mem.1 out_mem.2)
      (fun _ : chOption message * heap => true)
      (cat_tuple
        [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0])).
    - move=> memL memR iL iR Hpre.
      move/andP: Hpre=> [/andP [/eqP Hi /eqP Hmem] Hinv].
      by split; [exact: Hi | split].
    - exact: Hprefix_vector.
    - exact: ind_cpad_decrypt_cont_kernel_pyth_from_metric_encoding_ready_vector_bound.
  Qed.

  Lemma ind_cpad_decrypt_factored_pyth_from_metric_encoding
      max_queries :
    ⊨Pyth ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (fun i : nat =>
        row ← ind_cpad_decrypt_prefix_code max_queries i ;;
        ind_cpad_real_decrypt_cont row)
      ≈( cat_tuple [tuple 0]
        (cat_tuple
          [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0]) )
      (fun i : nat =>
        row ← ind_cpad_decrypt_prefix_code max_queries i ;;
        ind_cpad_sim_decrypt_cont row)
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    exact: (ind_cpad_decrypt_factored_pyth_from_metric_encoding_ready_vector_bound
      max_queries
      (ind_cpad_decrypt_prefix_code_readies_row_vector_bound
        max_queries)).
  Qed.

  Lemma ind_cpad_decrypt_code_pyth max_queries :
    ⊨Pyth ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (ind_cpad_real_decrypt_code max_queries)
      ≈( cat_tuple [tuple 0]
        (cat_tuple
          [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0]) )
      (ind_cpad_sim_decrypt_code max_queries)
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    have Hfactored := ind_cpad_decrypt_factored_pyth
      max_queries.
    move: Hfactored=> [Hs Hpyth].
    split; first exact: Hs.
    move=> memL memR iL iR Hpre.
    have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
      Hpyth memL memR iL iR Hpre.
    exists P, Q.
    split; first exact: Hdist.
    split.
    - move=> out.
      rewrite (HmarginL out).
      symmetry.
      apply: complete_output_heap_ext=> out'.
      exact: (ind_cpad_real_decrypt_code_factorE
        max_queries iL memL out').
    split.
    - move=> out.
      rewrite (HmarginR out).
      symmetry.
      apply: complete_output_heap_ext=> out'.
      exact: (ind_cpad_sim_decrypt_code_factorE
        max_queries iR memR out').
    split.
    - by move=> y Hy.
    - by move=> y Hy.
  Qed.

  Lemma ind_cpad_decrypt_code_pyth_from_metric_encoding_ready_vector_bound
      max_queries :
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    ⊨Pyth ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (ind_cpad_real_decrypt_code max_queries)
      ≈( cat_tuple [tuple 0]
        (cat_tuple
          [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0]) )
      (ind_cpad_sim_decrypt_code max_queries)
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    move=> Hprefix_vector.
    have Hfactored :=
      ind_cpad_decrypt_factored_pyth_from_metric_encoding_ready_vector_bound
        max_queries Hprefix_vector.
    move: Hfactored=> [Hs Hpyth].
    split; first exact: Hs.
    move=> memL memR iL iR Hpre.
    have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
      Hpyth memL memR iL iR Hpre.
    exists P, Q.
    split; first exact: Hdist.
    split.
    - move=> out.
      rewrite (HmarginL out).
      symmetry.
      apply: complete_output_heap_ext=> out'.
      exact: (ind_cpad_real_decrypt_code_factorE
        max_queries iL memL out').
    split.
    - move=> out.
      rewrite (HmarginR out).
      symmetry.
      apply: complete_output_heap_ext=> out'.
      exact: (ind_cpad_sim_decrypt_code_factorE
        max_queries iR memR out').
    split.
    - by move=> y Hy.
    - by move=> y Hy.
  Qed.

  Lemma ind_cpad_decrypt_code_pyth_from_metric_encoding
      max_queries :
    ⊨Pyth ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (ind_cpad_real_decrypt_code max_queries)
      ≈( cat_tuple [tuple 0]
        (cat_tuple
          [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0]) )
      (ind_cpad_sim_decrypt_code max_queries)
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    exact: (ind_cpad_decrypt_code_pyth_from_metric_encoding_ready_vector_bound
      max_queries
      (ind_cpad_decrypt_prefix_code_readies_row_vector_bound
        max_queries)).
  Qed.

  Lemma ind_cpad_real_decrypt_code_preserves_challenge_heap_valid
      max_queries :
    ⊨Hoare ⦃ fun in_mem => challenge_heap_valid in_mem.2 ⦄
      (ind_cpad_real_decrypt_code max_queries)
    ⦃ fun out_mem => challenge_heap_valid out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> [i mem Hinv] out Hout.
    rewrite /ind_cpad_real_decrypt_code in Hout.
    rewrite Pr_code_get in Hout.
    have [Hcount Hafter_count] := dinsupp_assertD _ _ _ _ Hout.
    rewrite Pr_code_put in Hafter_count.
    set mem1 := set_heap mem IndCpadGame.decrypt_count_addr
      (get_heap mem IndCpadGame.decrypt_count_addr).+1.
    have Hinv1 : challenge_heap_valid mem1.
      rewrite /mem1.
      exact: challenge_heap_valid_set_decrypt_count.
    rewrite Pr_code_get in Hafter_count.
    have [Hi Hafter_i] := dinsupp_assertD _ _ _ _ Hafter_count.
    rewrite /= in Hafter_i.
    case Hnth:
        (nth_valid (get_heap mem1 IndCpadGame.table_addr) i Hi)=>
      [[m0 m1] c] in Hafter_i *.
    destruct (eq_op m0 m1) eqn:Heq.
    - rewrite Pr_code_get in Hafter_i.
      have [Hosk Hafter_sk] := dinsupp_assertD _ _ _ _ Hafter_i.
      case Hsk: (get_heap mem1 IndCpadGame.sk_addr) Hosk Hafter_sk=> [sk|]
        Hosk Hafter_sk.
      + rewrite Pr_code_sample in Hafter_sk.
        have [m Hm Hinner] := @dinsupp_dlet R _ _ _ _ _ Hafter_sk.
        rewrite Pr_code_ret in Hinner.
        have -> : out = (Some m, mem1).
          exact: in_dunit Hinner.
        exact: Hinv1.
      + by [].
    - rewrite Pr_code_ret in Hafter_i.
      have -> : out = (None, mem1).
        exact: in_dunit Hafter_i.
      exact: Hinv1.
  Qed.

  Lemma ind_cpad_sim_decrypt_code_preserves_challenge_heap_valid
      max_queries :
    ⊨Hoare ⦃ fun in_mem => challenge_heap_valid in_mem.2 ⦄
      (ind_cpad_sim_decrypt_code max_queries)
    ⦃ fun out_mem => challenge_heap_valid out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> [i mem Hinv] out Hout.
    rewrite /ind_cpad_sim_decrypt_code in Hout.
    rewrite Pr_code_get in Hout.
    have [Hcount Hafter_count] := dinsupp_assertD _ _ _ _ Hout.
    rewrite Pr_code_put in Hafter_count.
    set mem1 := set_heap mem IndCpadGame.decrypt_count_addr
      (get_heap mem IndCpadGame.decrypt_count_addr).+1.
    have Hinv1 : challenge_heap_valid mem1.
      rewrite /mem1.
      exact: challenge_heap_valid_set_decrypt_count.
    rewrite Pr_code_get in Hafter_count.
    have [Hi Hafter_i] := dinsupp_assertD _ _ _ _ Hafter_count.
    rewrite /= in Hafter_i.
    case Hnth:
        (nth_valid (get_heap mem1 IndCpadGame.table_addr) i Hi)=>
      [[m0 m1] c] in Hafter_i *.
    destruct (eq_op m0 m1) eqn:Heq.
    - have [Hc Hafter_c] := dinsupp_assertD _ _ _ _ Hafter_i.
      case Hcopt: c Hc Hafter_c=> [[data error_bound]|] Hc Hafter_c.
      + rewrite Pr_code_sample in Hafter_c.
        have [noise Hnoise Hinner] := @dinsupp_dlet R _ _ _ _ _ Hafter_c.
        rewrite Pr_code_ret in Hinner.
        have -> :
            out =
            (Some
              (inverse_isometry m0
                (ivec_add (IndCpaDSim.toIntVec noise)
                  (isometry m0 m0))), mem1).
          exact: in_dunit Hinner.
        exact: Hinv1.
      + by [].
    - rewrite Pr_code_ret in Hafter_i.
      have -> : out = (None, mem1).
        exact: in_dunit Hafter_i.
      exact: Hinv1.
  Qed.

  Lemma ind_cpad_real_decrypt_resolve_preserves_challenge_heap_valid
      max_queries :
    ⊨Hoare ⦃ fun in_mem => challenge_heap_valid in_mem.2 ⦄
      (fun x : nat =>
        resolve (IndCpadGame.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
    ⦃ fun out_mem => challenge_heap_valid out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> x mem Hinv out Hout.
    rewrite ind_cpad_real_decrypt_resolveE in Hout.
    exact: (ind_cpad_real_decrypt_code_preserves_challenge_heap_valid
      max_queries x mem Hinv out Hout).
  Qed.

  Lemma ind_cpad_sim_decrypt_resolve_preserves_challenge_heap_valid
      max_queries :
    ⊨Hoare ⦃ fun in_mem => challenge_heap_valid in_mem.2 ⦄
      (fun x : nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
    ⦃ fun out_mem => challenge_heap_valid out_mem.2 ⦄.
  Proof.
    rewrite /hoareJudgment=> x mem Hinv out Hout.
    rewrite ind_cpad_sim_decrypt_resolveE in Hout.
    exact: (ind_cpad_sim_decrypt_code_preserves_challenge_heap_valid
      max_queries x mem Hinv out Hout).
  Qed.

  Lemma ind_cpad_decrypt_resolve_pyth_from_metric_encoding_ready_vector_bound
      max_queries :
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    ⊨Pyth ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (fun x : nat =>
        resolve (IndCpadGame.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
      ≈( cat_tuple [tuple 0]
        (cat_tuple
          [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0]) )
      (fun x : nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
    ⦃ fun out =>
      let '(_, mem) := out in challenge_heap_valid mem ⦄.
  Proof.
    move=> Hprefix_vector.
    have Hcode :=
      ind_cpad_decrypt_code_pyth_from_metric_encoding_ready_vector_bound
        max_queries Hprefix_vector.
    move: Hcode=> [Hs Hpyth].
    split; first exact: Hs.
    move=> memL memR iL iR Hpre.
    have [P [Q [Hdist [HmarginL [HmarginR [_ _]]]]]] :=
      Hpyth memL memR iL iR Hpre.
    exists P, Q.
    split; first exact: Hdist.
    split.
    - move=> out.
      rewrite (HmarginL out).
      symmetry.
      apply: complete_output_heap_ext=> out'.
      rewrite ind_cpad_real_decrypt_resolveE.
      by [].
    split.
    - move=> out.
      rewrite (HmarginR out).
      symmetry.
      apply: complete_output_heap_ext=> out'.
      rewrite ind_cpad_sim_decrypt_resolveE.
      by [].
    split.
    - move=> y Hy.
      move/andP: Hpre=> [/andP [/eqP _ /eqP Hmem] Hinv].
      subst memR.
      case: y Hy=> y mem Hy /=.
      have Hy_code :
          (y, mem) \in dinsupp
            (Pr_code (ind_cpad_real_decrypt_code max_queries iL) memL).
        by rewrite -ind_cpad_real_decrypt_resolveE.
      exact: (ind_cpad_real_decrypt_code_preserves_challenge_heap_valid
        max_queries iL memL Hinv (y, mem) Hy_code).
    - move=> y Hy.
      move/andP: Hpre=> [/andP [/eqP _ /eqP Hmem] Hinv].
      subst memR.
      case: y Hy=> y mem Hy /=.
      have Hy_code :
          (y, mem) \in dinsupp
            (Pr_code (ind_cpad_sim_decrypt_code max_queries iR) memL).
        by rewrite -ind_cpad_sim_decrypt_resolveE.
      exact: (ind_cpad_sim_decrypt_code_preserves_challenge_heap_valid
        max_queries iR memL Hinv (y, mem) Hy_code).
  Qed.

  Lemma ind_cpad_decrypt_resolve_pyth_from_metric_encoding
      max_queries :
    ⊨Pyth ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (fun x : nat =>
        resolve (IndCpadGame.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
      ≈( cat_tuple [tuple 0]
        (cat_tuple
          [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0]) )
      (fun x : nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
    ⦃ fun out =>
      let '(_, mem) := out in challenge_heap_valid mem ⦄.
  Proof.
    exact: (ind_cpad_decrypt_resolve_pyth_from_metric_encoding_ready_vector_bound
      max_queries
      (ind_cpad_decrypt_prefix_code_readies_row_vector_bound
        max_queries)).
  Qed.

  Lemma tuple_sum_noise_flooding_vector_call_error :
    tuple_sum
      (cat_tuple [tuple 0]
        (cat_tuple
          [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0])) =
    (dim%:R / (2 * gaussian_width_multiplier ^+ 2)).
  Proof.
    by rewrite !tuple_sum_cat !tuple_sum_singleton add0r addr0.
  Qed.

  Lemma ind_cpad_real_oracle_preserves_challenge_heap_valid_except_decrypt
      max_queries :
    package_preserves_heap_pred_except
      IndCpadGame.IndCpadAdv_import
      (IndCpadGame.IndCpadOracle max_queries)
      IndCpadGame.oracle_decrypt
      challenge_heap_valid.
  Proof.
    rewrite /package_preserves_heap_pred_except.
    move=> o.
    case: o=> f [S T] x Hhas Hnot_decrypt.
    destruct ((f == IndCpadGame.oracle_encrypt)%bool) eqn:Ho_encrypt.
    - have Hfid : f = IndCpadGame.oracle_encrypt :=
        ident_eqb_eq f IndCpadGame.oracle_encrypt Ho_encrypt.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_encrypt
            (chProd message message) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      exact: ind_cpad_real_encrypt_resolve_preserves_challenge_heap_valid.
    destruct ((f == IndCpadGame.oracle_eval1)%bool) eqn:Ho_eval1.
    - have Hfid : f = IndCpadGame.oracle_eval1 :=
        ident_eqb_eq f IndCpadGame.oracle_eval1 Ho_eval1.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_eval1
            (chProd unary_gate nat) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      exact: ind_cpad_real_eval1_resolve_preserves_challenge_heap_valid.
    destruct ((f == IndCpadGame.oracle_eval2)%bool) eqn:Ho_eval2.
    - have Hfid : f = IndCpadGame.oracle_eval2 :=
        ident_eqb_eq f IndCpadGame.oracle_eval2 Ho_eval2.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_eval2
            (chProd (chProd binary_gate nat) nat) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      exact: ind_cpad_real_eval2_resolve_preserves_challenge_heap_valid.
    destruct ((f == IndCpadGame.oracle_decrypt)%bool) eqn:Ho_decrypt.
    - have Hdecrypt_eq : f = IndCpadGame.oracle_decrypt :=
        ident_eqb_eq f IndCpadGame.oracle_decrypt Ho_decrypt.
      by move: Hnot_decrypt; rewrite Hdecrypt_eq eqxx.
    exfalso.
    rewrite /IndCpadGame.IndCpadAdv_import in Hhas.
    fmap_invert Hhas.
    - by move: Ho_encrypt; rewrite eqxx.
    - by move: Ho_eval1; rewrite eqxx.
    - by move: Ho_eval2; rewrite eqxx.
    - by move: Ho_decrypt; rewrite eqxx.
  Qed.

  Lemma ind_cpad_sim_decrypt_oracle_preserves_challenge_heap_valid_except_decrypt
      max_queries :
    package_preserves_heap_pred_except
      IndCpadGame.IndCpadAdv_import
      (IndCpadSimDecryptOracle max_queries)
      IndCpadGame.oracle_decrypt
      challenge_heap_valid.
  Proof.
    rewrite /package_preserves_heap_pred_except.
    move=> o.
    case: o=> f [S T] x Hhas Hnot_decrypt.
    destruct ((f == IndCpadGame.oracle_encrypt)%bool) eqn:Ho_encrypt.
    - have Hfid : f = IndCpadGame.oracle_encrypt :=
        ident_eqb_eq f IndCpadGame.oracle_encrypt Ho_encrypt.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_encrypt
            (chProd message message) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      exact: ind_cpad_sim_decrypt_encrypt_resolve_preserves_challenge_heap_valid.
    destruct ((f == IndCpadGame.oracle_eval1)%bool) eqn:Ho_eval1.
    - have Hfid : f = IndCpadGame.oracle_eval1 :=
        ident_eqb_eq f IndCpadGame.oracle_eval1 Ho_eval1.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_eval1
            (chProd unary_gate nat) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      exact: ind_cpad_sim_decrypt_eval1_resolve_preserves_challenge_heap_valid.
    destruct ((f == IndCpadGame.oracle_eval2)%bool) eqn:Ho_eval2.
    - have Hfid : f = IndCpadGame.oracle_eval2 :=
        ident_eqb_eq f IndCpadGame.oracle_eval2 Ho_eval2.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_eval2
            (chProd (chProd binary_gate nat) nat) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Hhas.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      exact: ind_cpad_sim_decrypt_eval2_resolve_preserves_challenge_heap_valid.
    destruct ((f == IndCpadGame.oracle_decrypt)%bool) eqn:Ho_decrypt.
    - have Hdecrypt_eq : f = IndCpadGame.oracle_decrypt :=
        ident_eqb_eq f IndCpadGame.oracle_decrypt Ho_decrypt.
      by move: Hnot_decrypt; rewrite Hdecrypt_eq eqxx.
    exfalso.
    rewrite /IndCpadGame.IndCpadAdv_import in Hhas.
    fmap_invert Hhas.
    - by move: Ho_encrypt; rewrite eqxx.
    - by move: Ho_eval1; rewrite eqxx.
    - by move: Ho_eval2; rewrite eqxx.
    - by move: Ho_decrypt; rewrite eqxx.
  Qed.

End NoiseFloodingSecureDecryptCompiler.
