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

From Mending.Security.NoiseFloodingSecurity Require Import Prelude GaussianBasics.

Module NoiseFloodingSecureOracleSetup
  (Import Scheme : ApproxFheScheme)
  (Import Metric : ApproxFheMetric(Scheme))
  (Import Correctness : ApproxCorrectnessPerfect(Scheme)(Metric))
  (Import IndCpaSecurity : IsIndCpa(Scheme))
  (Import Params : NoiseFloodingParams).
  Include GaussianBasics.NoiseFloodingSecureGaussianBasics(Scheme)(Metric)(Correctness)(IndCpaSecurity)(Params).

  Notation " 'adv_keys " := (pk_t × evk_t) (in custom pack_type at level 2).
  Notation " 'message " := message (in custom pack_type at level 2).
  Notation " 'message_pair " := (message × message)
    (in custom pack_type at level 2).
  Notation " 'ciphertext " := ciphertext (in custom pack_type at level 2).
  Notation " 'unary_gate " := unary_gate (in custom pack_type at level 2).
  Notation " 'binary_gate " := binary_gate (in custom pack_type at level 2).
  Notation " 'option_message " := (chOption message)
    (in custom pack_type at level 2).

  Definition IndCpadSimDecryptOracle
      (max_queries : nat) : IndCpadGame.IndCpaOracle_t :=
    [package IndCpadGame.oracle_mem_spec ;
      #def #[IndCpadGame.oracle_encrypt]
          ('(m0, m1) : 'message × 'message ) : 'ciphertext
      {
        b ← get IndCpadGame.bit_addr ;;
        let m := if b then m1 else m0 in
        o ← get IndCpadGame.pk_addr ;;
        #assert isSome o as opk ;;
        let pk := getSome o opk in
        c <$ (ciphertext; encrypt pk m) ;;
        table ← get IndCpadGame.table_addr ;;
        let updated_table := (table ++ [ :: (m0,m1, c)]) in
        #put IndCpadGame.table_addr := updated_table ;;
        ret c
      } ;
      #def #[IndCpadGame.oracle_eval1]
          ('(gate, r) : 'unary_gate × 'nat) : 'ciphertext
      {
        table ← get IndCpadGame.table_addr ;;
        #assert (r < length table)%N as r_in_range ;;
        let '(m0, m1, c) := nth_valid table r r_in_range in
        o ← get IndCpadGame.evk_addr ;;
        #assert isSome o as oevk ;;
        let evk := getSome o oevk in
        let m0' := interpret_unary gate m0 in
        let m1' := interpret_unary gate m1 in
        c' <$ (ciphertext; eval1 evk gate c) ;;
        let updated_table := (table ++ [ :: (m0', m1', c')]) in
        #put IndCpadGame.table_addr := updated_table ;;
        ret c'
      } ;
      #def #[IndCpadGame.oracle_eval2]
          ('((gate, ri), rj) : ('binary_gate × 'nat) × 'nat)
            : 'ciphertext
      {
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
        let updated_table := (table ++ [ :: (m0', m1', c')]) in
        #put IndCpadGame.table_addr := updated_table ;;
        ret c'
      } ;
      #def #[IndCpadGame.oracle_decrypt] (i: 'nat) : 'option_message
      {
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
          @ret ('option message) None
      }
    ].

  Lemma IndCpadRealOracle_valid max_queries :
    ValidPackage IndCpadGame.oracle_mem_spec
      [interface] IndCpadGame.IndCpadAdv_import
      (IndCpadGame.IndCpadOracle max_queries).
  Proof.
    typeclasses eauto with ssprove_valid_db.
  Qed.

  Lemma IndCpadSimDecryptOracle_valid max_queries :
    ValidPackage IndCpadGame.oracle_mem_spec
      [interface] IndCpadGame.IndCpadAdv_import
      (IndCpadSimDecryptOracle max_queries).
  Proof.
    typeclasses eauto with ssprove_valid_db.
  Qed.

  Lemma IndCpaDSimOracle_valid max_queries :
    ValidPackage IndCpaDSim.oracle_mem_spec
      IndCpaSecurity.IndCpaGame.IndCpaAdv_import
      IndCpadGame.IndCpadAdv_import
      (IndCpaDSim.IndCpadOracle max_queries).
  Proof.
    typeclasses eauto with ssprove_valid_db.
  Qed.

  Lemma ind_cpad_decrypt_in_adv_import :
    fhas IndCpadGame.IndCpadAdv_import
      (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)).
  Proof.
    rewrite /IndCpadGame.IndCpadAdv_import.
    fmap_solve.
  Qed.

  Lemma ind_cpad_sim_decrypt_resolve_preserves_heap_eq_on
      max_queries K (o : opsig) (x : src o) mem out :
    fseparate K IndCpadGame.oracle_mem_spec ->
    fhas IndCpadGame.IndCpadAdv_import o ->
    out \in dinsupp
      (Pr_code (resolve (IndCpadSimDecryptOracle max_queries) o x) mem) ->
    heap_eq_on K mem out.2.
  Proof.
    move=> HK Ho Hout.
    have Hvalid :
        ValidCode IndCpadGame.oracle_mem_spec [interface]
          (resolve (IndCpadSimDecryptOracle max_queries) o x).
      exact: (@valid_resolve IndCpadGame.oracle_mem_spec [interface]
        IndCpadGame.IndCpadAdv_import
        (IndCpadSimDecryptOracle max_queries) o x
        (IndCpadSimDecryptOracle_valid max_queries) Ho).
    exact: (closed_code_preserves_heap_eq_on
      K IndCpadGame.oracle_mem_spec
      (resolve (IndCpadSimDecryptOracle max_queries) o x)
      mem out Hvalid HK Hout).
  Qed.

  Lemma ind_cpa_reduction_sim_outer_resolve_preserves_heap_eq_on
      max_queries K (o : opsig) (x : src o) mem out :
    fseparate K IndCpaDSim.oracle_mem_spec ->
    fseparate K IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    fhas IndCpadGame.IndCpadAdv_import o ->
    out \in dinsupp
      (Pr_code
        (code_link
          (resolve (IndCpaDSim.IndCpadOracle max_queries) o x)
          IndCpaSecurity.IndCpaGame.IndCpaOracle)
        mem) ->
    heap_eq_on K mem out.2.
  Proof.
    move=> HKsim HKouter Ho Hout.
    have Hbody_valid :
        ValidCode IndCpaDSim.oracle_mem_spec
          IndCpaSecurity.IndCpaGame.IndCpaAdv_import
          (resolve (IndCpaDSim.IndCpadOracle max_queries) o x).
      exact: (@valid_resolve IndCpaDSim.oracle_mem_spec
        IndCpaSecurity.IndCpaGame.IndCpaAdv_import
        IndCpadGame.IndCpadAdv_import
        (IndCpaDSim.IndCpadOracle max_queries) o x
        (IndCpaDSimOracle_valid max_queries) Ho).
    have Houter_valid :
        ValidPackage IndCpaSecurity.IndCpaGame.IndCpa_locs
          [interface]
          IndCpaSecurity.IndCpaGame.IndCpaAdv_import
          IndCpaSecurity.IndCpaGame.IndCpaOracle.
      typeclasses eauto with ssprove_valid_db.
    exact: (linked_code_preserves_heap_eq_on
      K IndCpaDSim.oracle_mem_spec
      IndCpaSecurity.IndCpaGame.IndCpa_locs
      IndCpaSecurity.IndCpaGame.IndCpaAdv_import
      IndCpaSecurity.IndCpaGame.IndCpaOracle
      (resolve (IndCpaDSim.IndCpadOracle max_queries) o x)
      mem out Hbody_valid Houter_valid HKsim HKouter Hout).
  Qed.

  Definition same_input_invariant_pre
      {A : choice_type} (call_invariant : pred heap) :
    pred ((A * heap) * (A * heap)) :=
    fun inps =>
      let '((xL, memL), (xR, memR)) := inps in
      (xL == xR) && (memL == memR) &&
      call_invariant memL.

  Definition same_game_output_opt
    (outs : option (bool * heap) * option (bool * heap)) : bool :=
    let '(outL, outR) := outs in
    eq_op outL outR.

  Definition same_game_result_opt
    (outs : option (bool * heap) * option (bool * heap)) : bool :=
    let '(outL, outR) := outs in
    omap fst outL == omap fst outR.

  Definition same_result_opt {out_t : choice_type}
    (outs : option (out_t * heap) * option (out_t * heap)) : bool :=
    let '(outL, outR) := outs in
    omap fst outL == omap fst outR.

  Lemma rename_empty_heap {π} :
    π ∙ empty_heap = empty_heap.
  Proof.
    apply/eq_fmap=> n.
    by rewrite /empty_heap /rename /=.
  Qed.

  Lemma dmargin_fst_Pr_code_rename_empty
      {out_t : choice_type} {π} (c : raw_code out_t) :
    dmargin fst (Pr_code (π ∙ c) empty_heap) =1
    dmargin fst (Pr_code c empty_heap).
  Proof.
    move=> y.
    rewrite !dmarginE !dletE.
    rewrite (reindex_psum (P := predT)
      (h := fun out : out_t * heap => (out.1, π ∙ out.2))) //=.
    - apply/eq_psum=> [[x h]].
      rewrite /=.
      rewrite -(@rename_empty_heap π).
      rewrite -(Pr_code_rename π c x h empty_heap).
      by [].
    - exists (fun out : out_t * heap => (out.1, π^-1%fperm ∙ out.2)).
      + move=> [x h] _ /=.
        by rewrite renameK.
      + move=> [x h] _ /=.
        by rewrite renameKV.
  Qed.

  Lemma same_game_output_result_opt outs :
    same_game_output_opt outs -> same_game_result_opt outs.
  Proof.
    case: outs=> [outL outR].
    rewrite /same_game_output_opt /same_game_result_opt /=.
    by move/eqP=> ->; rewrite eqxx.
  Qed.

  Lemma same_output_heap_game_output_opt
      (outs : option (bool * heap) * option (bool * heap)) :
    same_output_heap_opt outs -> same_game_output_opt outs.
  Proof.
    by case: outs=> outL outR; rewrite /same_output_heap_opt
      /same_game_output_opt.
  Qed.

  Lemma same_game_output_same_output_heap_opt
      (outs : option (bool * heap) * option (bool * heap)) :
    same_game_output_opt outs -> same_output_heap_opt outs.
  Proof.
    by case: outs=> outL outR; rewrite /same_output_heap_opt
      /same_game_output_opt.
  Qed.

  Lemma bool_eq_true_is_true (b : bool) :
    b = true -> b.
  Proof. by move=> ->. Qed.

  Lemma Pr_code_assertD_true_ext
      {out_t : choice_type} (b : bool)
      (k : b = true -> raw_code out_t) (Hb : b = true) mem :
    Pr_code (@assertD out_t b k) mem =1 Pr_code (k Hb) mem.
  Proof.
    case: b k Hb=> k Hb out.
    - rewrite /assertD /=.
      by rewrite (eq_irrelevance Hb erefl).
    - discriminate Hb.
  Qed.

  Lemma assertD_same_guard_coupling
      {outL_t outR_t : choice_type} (b : bool)
      (kL : b = true -> raw_code outL_t)
      (kR : b = true -> raw_code outR_t)
      memL memR (post : pred (option (outL_t * heap) *
        option (outR_t * heap))) ε :
    0 <= ε ->
    (forall HbL HbR,
      exists d,
        coupling d
          (complete (Pr_code (kL HbL) memL))
          (complete (Pr_code (kR HbR) memR)) /\
        \P_[d] post >= 1 - ε) ->
    post (None, None) ->
    exists d,
      coupling d
        (complete (Pr_code (@assertD outL_t b kL) memL))
        (complete (Pr_code (@assertD outR_t b kR) memR)) /\
      \P_[d] post >= 1 - ε.
  Proof.
    case: b kL kR=> kL kR Heps Hcont Hnone.
    - have [d [Hd Hprob]] := Hcont erefl erefl.
      exists d.
      split; last exact: Hprob.
      have [HdL HdR] := coupling_margins Hd.
      apply: coupling_of_margins; split.
      + move=> z.
        rewrite HdL.
        symmetry.
        exact: (complete_distr_ext
          (Pr_code (@assertD outL_t true kL) memL)
          (Pr_code (kL erefl) memL)
          (Pr_code_assertD_true_ext true kL erefl memL) z).
      + move=> z.
        rewrite HdR.
        symmetry.
        exact: (complete_distr_ext
          (Pr_code (@assertD outR_t true kR) memR)
          (Pr_code (kR erefl) memR)
          (Pr_code_assertD_true_ext true kR erefl memR) z).
    - exists (dunit (None, None)).
      split.
      + apply: coupling_of_margins; split.
        * move=> z.
          rewrite dmargin_dunit.
          rewrite /assertD Pr_code_fail.
          exact/esym/complete_dnull.
        * move=> z.
          rewrite dmargin_dunit.
          rewrite /assertD Pr_code_fail.
          exact/esym/complete_dnull.
      + rewrite pr_dunit.
        rewrite Hnone.
        clear Hnone Hcont kL kR.
        by rewrite lerBlDr lerDl.
  Qed.

  Definition selected_plaintext
      (b : bool) (row : IndCpadGame.challenger_table_row) : message :=
    let '(m0, m1, _) := row in if b then m1 else m0.

  Definition row_valid_for_branch
      (sk : sk_t) (b : bool)
      (row : IndCpadGame.challenger_table_row) : bool :=
    let '(_, _, c) := row in
    is_underlying_plaintext sk c (selected_plaintext b row).

  Definition table_valid_for_branch
      (sk : sk_t) (b : bool) (table : IndCpadGame.challenger_table) : bool :=
    all (row_valid_for_branch sk b) table.

  Definition challenge_heap_valid (mem : heap) : bool :=
    let b := get_heap mem IndCpadGame.bit_addr in
    let table := get_heap mem IndCpadGame.table_addr in
    match get_heap mem IndCpadGame.pk_addr,
          get_heap mem IndCpadGame.evk_addr,
          get_heap mem IndCpadGame.sk_addr with
    | Some pk, Some evk, Some sk =>
        good_keys pk evk sk && table_valid_for_branch sk b table
    | None, None, None => table == [::]
    | _, _, _ => false
    end.

  Definition challenge_initialized_heap
      (b : bool) (pk : pk_t) (evk : evk_t) (sk : sk_t) : heap :=
    set_heap
      (set_heap
        (set_heap
          (set_heap empty_heap IndCpadGame.bit_addr b)
          IndCpadGame.pk_addr (Some pk))
        IndCpadGame.evk_addr (Some evk))
      IndCpadGame.sk_addr (Some sk).

  Definition reduction_initialized_heap
      (b : bool) (pk : pk_t) (evk : evk_t) : heap :=
    set_heap
      (set_heap
        (set_heap
          (set_heap
            (set_heap
              (set_heap empty_heap IndCpaSecurity.IndCpaGame.bit_addr b)
              IndCpaSecurity.IndCpaGame.pk_addr (Some pk))
            IndCpaSecurity.IndCpaGame.evk_addr (Some evk))
          IndCpaDSim.ready_addr true)
        IndCpaDSim.pk_addr (Some pk))
      IndCpaDSim.evk_addr (Some evk).

  Definition reduction_outer_initialized_heap
      (b : bool) (pk : pk_t) (evk : evk_t) : heap :=
    set_heap
      (set_heap
        (set_heap empty_heap IndCpaSecurity.IndCpaGame.bit_addr b)
        IndCpaSecurity.IndCpaGame.pk_addr (Some pk))
      IndCpaSecurity.IndCpaGame.evk_addr (Some evk).

  Definition sim_decrypt_reduction_heap_rel
      (memL memR : heap) : bool :=
    challenge_heap_valid memL &&
    (get_heap memR IndCpaDSim.ready_addr == true) &&
    (get_heap memL IndCpadGame.bit_addr ==
      get_heap memR IndCpaSecurity.IndCpaGame.bit_addr) &&
    (get_heap memL IndCpadGame.pk_addr ==
      get_heap memR IndCpaSecurity.IndCpaGame.pk_addr) &&
    (get_heap memL IndCpadGame.evk_addr ==
      get_heap memR IndCpaSecurity.IndCpaGame.evk_addr) &&
    (get_heap memL IndCpadGame.pk_addr ==
      get_heap memR IndCpaDSim.pk_addr) &&
    (get_heap memL IndCpadGame.evk_addr ==
      get_heap memR IndCpaDSim.evk_addr) &&
    (get_heap memL IndCpadGame.table_addr ==
      get_heap memR IndCpaDSim.table_addr) &&
    (get_heap memL IndCpadGame.decrypt_count_addr ==
      get_heap memR IndCpaDSim.decrypt_count_addr).

  Definition same_input_sim_decrypt_reduction_pre {A : choice_type} :
    pred ((A * heap) * (A * heap)) :=
    fun inps =>
      let '((xL, memL), (xR, memR)) := inps in
      (xL == xR) && sim_decrypt_reduction_heap_rel memL memR.

  Definition same_result_sim_decrypt_reduction_opt {out_t : choice_type}
    (outs : option (out_t * heap) * option (out_t * heap)) : bool :=
    match outs with
    | (Some (outL, memL), Some (outR, memR)) =>
        (outL == outR) && sim_decrypt_reduction_heap_rel memL memR
    | (None, None) => true
    | _ => false
    end.

  Lemma same_result_sim_decrypt_reduction_result_opt
      {out_t : choice_type}
      (outs : option (out_t * heap) * option (out_t * heap)) :
    same_result_sim_decrypt_reduction_opt outs -> same_result_opt outs.
  Proof.
    case: outs=> outL outR.
    case: outL=> [[outL memL]|]; case: outR=> [[outR memR]|] //=.
    by move/andP=> [/eqP -> _]; rewrite /same_result_opt /= eqxx.
  Qed.

  Lemma challenge_initialized_heap_bit b pk evk sk :
    get_heap (challenge_initialized_heap b pk evk sk)
      IndCpadGame.bit_addr = b.
  Proof.
    rewrite /challenge_initialized_heap.
    repeat first [
      rewrite get_set_heap_eq
    | rewrite get_set_heap_neq; [| neq_loc_auto]
    ].
    by [].
  Qed.

  Lemma challenge_initialized_heap_pk b pk evk sk :
    get_heap (challenge_initialized_heap b pk evk sk)
      IndCpadGame.pk_addr = Some pk.
  Proof.
    rewrite /challenge_initialized_heap.
    repeat first [
      rewrite get_set_heap_eq
    | rewrite get_set_heap_neq; [| neq_loc_auto]
    ].
    by [].
  Qed.

  Lemma challenge_initialized_heap_evk b pk evk sk :
    get_heap (challenge_initialized_heap b pk evk sk)
      IndCpadGame.evk_addr = Some evk.
  Proof.
    rewrite /challenge_initialized_heap.
    repeat first [
      rewrite get_set_heap_eq
    | rewrite get_set_heap_neq; [| neq_loc_auto]
    ].
    by [].
  Qed.

  Lemma challenge_initialized_heap_sk b pk evk sk :
    get_heap (challenge_initialized_heap b pk evk sk)
      IndCpadGame.sk_addr = Some sk.
  Proof.
    rewrite /challenge_initialized_heap.
    repeat first [
      rewrite get_set_heap_eq
    | rewrite get_set_heap_neq; [| neq_loc_auto]
    ].
    by [].
  Qed.

  Lemma challenge_initialized_heap_table b pk evk sk :
    get_heap (challenge_initialized_heap b pk evk sk)
      IndCpadGame.table_addr = [::].
  Proof.
    rewrite /challenge_initialized_heap.
    repeat first [
      rewrite get_set_heap_eq
    | rewrite get_set_heap_neq; [| neq_loc_auto]
    | rewrite get_empty_heap
    ].
    by [].
  Qed.

  Lemma challenge_initialized_heap_decrypt_count b pk evk sk :
    get_heap (challenge_initialized_heap b pk evk sk)
      IndCpadGame.decrypt_count_addr = 0.
  Proof.
    rewrite /challenge_initialized_heap.
    repeat first [
      rewrite get_set_heap_eq
    | rewrite get_set_heap_neq; [| neq_loc_auto]
    | rewrite get_empty_heap
    ].
    by [].
  Qed.

  Lemma reduction_outer_initialized_heap_ready b pk evk :
    get_heap (reduction_outer_initialized_heap b pk evk)
      IndCpaDSim.ready_addr = false.
  Proof.
    rewrite /reduction_outer_initialized_heap.
    repeat first [
      rewrite get_set_heap_eq
    | rewrite get_set_heap_neq; [| neq_loc_auto]
    | rewrite get_empty_heap
    ].
    by [].
  Qed.

  Lemma challenge_heap_valid_initialized_good_keys b pk evk sk :
    good_keys pk evk sk ->
    challenge_heap_valid (challenge_initialized_heap b pk evk sk).
  Proof.
    move=> Hkeys.
    rewrite /challenge_heap_valid.
    rewrite challenge_initialized_heap_bit
      challenge_initialized_heap_table
      challenge_initialized_heap_pk
      challenge_initialized_heap_evk
      challenge_initialized_heap_sk.
    by rewrite Hkeys.
  Qed.

  Lemma challenge_heap_valid_initialized b keys :
    keys \in dinsupp keygen ->
    let '(pk, evk, sk) := keys in
    challenge_heap_valid (challenge_initialized_heap b pk evk sk).
  Proof.
    case: keys=> [[pk evk] sk] Hkeys /=.
    apply: challenge_heap_valid_initialized_good_keys.
    exact: (keygen_support_good (pk, evk, sk) Hkeys).
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_initialized b pk evk sk :
    good_keys pk evk sk ->
    sim_decrypt_reduction_heap_rel
      (challenge_initialized_heap b pk evk sk)
      (reduction_initialized_heap b pk evk).
  Proof.
    move=> Hkeys.
    rewrite /sim_decrypt_reduction_heap_rel.
    rewrite (challenge_heap_valid_initialized_good_keys _ _ _ _ Hkeys).
    rewrite /reduction_initialized_heap.
    rewrite challenge_initialized_heap_bit
      challenge_initialized_heap_pk
      challenge_initialized_heap_evk
      challenge_initialized_heap_table
      challenge_initialized_heap_decrypt_count.
    repeat first [
      rewrite get_set_heap_eq
    | rewrite get_set_heap_neq; [| neq_loc_auto]
    | rewrite get_empty_heap
    ].
    by rewrite !eqxx.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_challenge_valid memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    challenge_heap_valid memL.
  Proof.
    rewrite /sim_decrypt_reduction_heap_rel -!andbA=> /andP [H _].
    exact: H.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_ready memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memR IndCpaDSim.ready_addr = true.
  Proof.
    rewrite /sim_decrypt_reduction_heap_rel -!andbA.
    move/andP=> [_ /andP [/eqP Hready _]].
    exact: Hready.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_bit memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memL IndCpadGame.bit_addr =
      get_heap memR IndCpaSecurity.IndCpaGame.bit_addr.
  Proof.
    rewrite /sim_decrypt_reduction_heap_rel -!andbA.
    move/andP=> [_ /andP [_ /andP [/eqP Hbit _]]].
    exact: Hbit.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_pk_outer memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memL IndCpadGame.pk_addr =
      get_heap memR IndCpaSecurity.IndCpaGame.pk_addr.
  Proof.
    rewrite /sim_decrypt_reduction_heap_rel -!andbA.
    move/andP=> [_ /andP [_ /andP [_ /andP [/eqP Hpk _]]]].
    exact: Hpk.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_evk_outer memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memL IndCpadGame.evk_addr =
      get_heap memR IndCpaSecurity.IndCpaGame.evk_addr.
  Proof.
    rewrite /sim_decrypt_reduction_heap_rel -!andbA.
    move/andP=> [_ /andP [_ /andP [_ /andP [_ /andP [/eqP Hevk _]]]]].
    exact: Hevk.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_pk_sim memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memL IndCpadGame.pk_addr =
      get_heap memR IndCpaDSim.pk_addr.
  Proof.
    rewrite /sim_decrypt_reduction_heap_rel -!andbA.
    move/andP=> [_ /andP [_ /andP [_ /andP [_ /andP [_ /andP [/eqP Hpk _]]]]]].
    exact: Hpk.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_evk_sim memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memL IndCpadGame.evk_addr =
      get_heap memR IndCpaDSim.evk_addr.
  Proof.
    rewrite /sim_decrypt_reduction_heap_rel -!andbA.
    move/andP=> [_ /andP [_ /andP [_ /andP [_ /andP [_ /andP [_ /andP [/eqP Hevk _]]]]]]].
    exact: Hevk.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_table memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memL IndCpadGame.table_addr =
      get_heap memR IndCpaDSim.table_addr.
  Proof.
    rewrite /sim_decrypt_reduction_heap_rel -!andbA.
    move/andP=> [_ /andP [_ /andP [_ /andP [_ /andP [_ /andP [_ /andP [_ /andP [/eqP Htable _]]]]]]]].
    exact: Htable.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_decrypt_count memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memL IndCpadGame.decrypt_count_addr =
      get_heap memR IndCpaDSim.decrypt_count_addr.
  Proof.
    rewrite /sim_decrypt_reduction_heap_rel -!andbA.
    move/andP=> [_ /andP [_ /andP [_ /andP [_ /andP [_ /andP [_ /andP [_ /andP [_ /eqP Hcount]]]]]]]].
    exact: Hcount.
  Qed.

  Arguments sim_decrypt_reduction_heap_rel_challenge_valid {memL memR}.
  Arguments sim_decrypt_reduction_heap_rel_ready {memL memR}.
  Arguments sim_decrypt_reduction_heap_rel_bit {memL memR}.
  Arguments sim_decrypt_reduction_heap_rel_pk_outer {memL memR}.
  Arguments sim_decrypt_reduction_heap_rel_evk_outer {memL memR}.
  Arguments sim_decrypt_reduction_heap_rel_pk_sim {memL memR}.
  Arguments sim_decrypt_reduction_heap_rel_evk_sim {memL memR}.
  Arguments sim_decrypt_reduction_heap_rel_table {memL memR}.
  Arguments sim_decrypt_reduction_heap_rel_decrypt_count {memL memR}.

  Lemma sim_decrypt_reduction_heap_rel_set_table memL memR table :
    sim_decrypt_reduction_heap_rel memL memR ->
    challenge_heap_valid
      (set_heap memL IndCpadGame.table_addr table) ->
    sim_decrypt_reduction_heap_rel
      (set_heap memL IndCpadGame.table_addr table)
      (set_heap memR IndCpaDSim.table_addr table).
  Proof.
    move=> Hrel Hvalid.
    rewrite /sim_decrypt_reduction_heap_rel Hvalid /=.
    have Hready := sim_decrypt_reduction_heap_rel_ready Hrel.
    have Hbit := sim_decrypt_reduction_heap_rel_bit Hrel.
    have Hpk_outer := sim_decrypt_reduction_heap_rel_pk_outer Hrel.
    have Hevk_outer := sim_decrypt_reduction_heap_rel_evk_outer Hrel.
    have Hpk_sim := sim_decrypt_reduction_heap_rel_pk_sim Hrel.
    have Hevk_sim := sim_decrypt_reduction_heap_rel_evk_sim Hrel.
    have Hcount := sim_decrypt_reduction_heap_rel_decrypt_count Hrel.
    repeat first [
      rewrite get_set_heap_eq
    | rewrite get_set_heap_neq; [| neq_loc_auto]
    ].
    by rewrite Hready -Hbit -Hpk_outer -Hevk_outer -Hpk_sim -Hevk_sim -Hcount !eqxx.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_set_decrypt_count memL memR n :
    sim_decrypt_reduction_heap_rel memL memR ->
    challenge_heap_valid
      (set_heap memL IndCpadGame.decrypt_count_addr n) ->
    sim_decrypt_reduction_heap_rel
      (set_heap memL IndCpadGame.decrypt_count_addr n)
      (set_heap memR IndCpaDSim.decrypt_count_addr n).
  Proof.
    move=> Hrel Hvalid.
    rewrite /sim_decrypt_reduction_heap_rel Hvalid /=.
    have Hready := sim_decrypt_reduction_heap_rel_ready Hrel.
    have Hbit := sim_decrypt_reduction_heap_rel_bit Hrel.
    have Hpk_outer := sim_decrypt_reduction_heap_rel_pk_outer Hrel.
    have Hevk_outer := sim_decrypt_reduction_heap_rel_evk_outer Hrel.
    have Hpk_sim := sim_decrypt_reduction_heap_rel_pk_sim Hrel.
    have Hevk_sim := sim_decrypt_reduction_heap_rel_evk_sim Hrel.
    have Htable := sim_decrypt_reduction_heap_rel_table Hrel.
    repeat first [
      rewrite get_set_heap_eq
    | rewrite get_set_heap_neq; [| neq_loc_auto]
    ].
    by rewrite Hready -Hbit -Hpk_outer -Hevk_outer -Hpk_sim -Hevk_sim -Htable !eqxx.
  Qed.

  Lemma challenge_heap_valid_depends_only_on_oracle_mem_spec :
    heap_pred_depends_only_on
      IndCpadGame.oracle_mem_spec challenge_heap_valid.
  Proof.
    rewrite /heap_pred_depends_only_on /heap_eq_on /challenge_heap_valid.
    move=> mem0 mem1 Heq.
    have -> : get_heap mem0 IndCpadGame.bit_addr =
              get_heap mem1 IndCpadGame.bit_addr
      by apply: Heq; fmap_solve.
    have -> : get_heap mem0 IndCpadGame.table_addr =
              get_heap mem1 IndCpadGame.table_addr
      by apply: Heq; fmap_solve.
    have -> : get_heap mem0 IndCpadGame.pk_addr =
              get_heap mem1 IndCpadGame.pk_addr
      by apply: Heq; fmap_solve.
    have -> : get_heap mem0 IndCpadGame.evk_addr =
              get_heap mem1 IndCpadGame.evk_addr
      by apply: Heq; fmap_solve.
    have -> : get_heap mem0 IndCpadGame.sk_addr =
              get_heap mem1 IndCpadGame.sk_addr
      by apply: Heq; fmap_solve.
    by [].
  Qed.

  Lemma table_valid_for_branch_nth sk b table i
      (i_in_range : (i < length table)%N) :
    table_valid_for_branch sk b table ->
    row_valid_for_branch sk b (nth_valid table i i_in_range).
  Proof.
    rewrite /table_valid_for_branch=> /allP Hall.
    apply: Hall.
    exact: nth_valid_in.
  Qed.

  Lemma table_valid_for_branch_rcons_encrypt
      pk evk sk b table m0 m1 c :
    good_keys pk evk sk ->
    table_valid_for_branch sk b table ->
    c \in dinsupp (encrypt pk (if b then m1 else m0)) ->
    table_valid_for_branch sk b (table ++ [:: (m0, m1, c)]).
  Proof.
    move=> Hkeys Htable Hc.
    rewrite /table_valid_for_branch in Htable *.
    rewrite all_cat Htable /= andbT.
    rewrite /row_valid_for_branch /selected_plaintext /=.
    exact: (encrypt_support_underlying pk evk sk
      (if b then m1 else m0) c Hkeys Hc).
  Qed.

  Lemma table_valid_for_branch_rcons_eval1
      pk evk sk b table gate r (r_in_range : (r < length table)%N) c' :
    good_keys pk evk sk ->
    table_valid_for_branch sk b table ->
    c' \in dinsupp
      (let '(_, _, c) := nth_valid table r r_in_range in
       eval1 evk gate c) ->
    table_valid_for_branch sk b
      (table ++
        [:: let '(m0, m1, _) := nth_valid table r r_in_range in
            (interpret_unary gate m0, interpret_unary gate m1, c')]).
  Proof.
    move=> Hkeys Htable Hc'.
    have Hrow :=
      table_valid_for_branch_nth sk b table r r_in_range Htable.
    case Hnth: (nth_valid table r r_in_range)=> [[m0 m1] c] /= in Hrow Hc' *.
    rewrite /table_valid_for_branch in Htable *.
    rewrite all_cat Htable /= andbT.
    rewrite /row_valid_for_branch /selected_plaintext /=.
    rewrite -[if b then interpret_unary gate m1 else interpret_unary gate m0]
      (fun_if (interpret_unary gate)).
    exact: (eval1_support_underlying pk evk sk gate c
      (if b then m1 else m0) c' Hkeys Hrow Hc').
  Qed.

  Lemma table_valid_for_branch_rcons_eval2
      pk evk sk b table gate ri rj
      (ri_in_range : (ri < length table)%N)
      (rj_in_range : (rj < length table)%N) c' :
    good_keys pk evk sk ->
    table_valid_for_branch sk b table ->
    c' \in dinsupp
      (let '(_, _, ci) := nth_valid table ri ri_in_range in
       let '(_, _, cj) := nth_valid table rj rj_in_range in
       eval2 evk gate ci cj) ->
    table_valid_for_branch sk b
      (table ++
        [:: let '(m0i, m1i, _) := nth_valid table ri ri_in_range in
            let '(m0j, m1j, _) := nth_valid table rj rj_in_range in
            (interpret_binary gate m0i m0j,
             interpret_binary gate m1i m1j, c')]).
  Proof.
    move=> Hkeys Htable Hc'.
    have Hrow_i :=
      table_valid_for_branch_nth sk b table ri ri_in_range Htable.
    have Hrow_j :=
      table_valid_for_branch_nth sk b table rj rj_in_range Htable.
    case Hnthi: (nth_valid table ri ri_in_range)=> [[m0i m1i] ci]
      /= in Hrow_i Hc' *.
    case Hnthj: (nth_valid table rj rj_in_range)=> [[m0j m1j] cj]
      /= in Hrow_j Hc' *.
    rewrite /table_valid_for_branch in Htable *.
    rewrite all_cat Htable /= andbT.
    rewrite /row_valid_for_branch /selected_plaintext /=.
    case: b Htable Hrow_i Hrow_j Hc'=>
      /= Htable Hrow_i Hrow_j Hc'.
    - exact: (eval2_support_underlying pk evk sk gate ci cj
        m1i m1j c' Hkeys Hrow_i Hrow_j Hc').
    - exact: (eval2_support_underlying pk evk sk gate ci cj
        m0i m0j c' Hkeys Hrow_i Hrow_j Hc').
  Qed.

  Lemma row_valid_for_branch_equal_messages_some sk b m c :
    row_valid_for_branch sk b (m, m, c) ->
    exists data error_bound,
      c = Some (data, error_bound) /\
      (metric (deterministic_dec sk c) m <= error_bound)%N.
  Proof.
    rewrite /row_valid_for_branch /selected_plaintext /=.
    case: b=> /= Hvalid;
      case Hc: c Hvalid=> [[data error_bound]|] Hvalid //=.
    - by exists data, error_bound.
    - by exists data, error_bound.
  Qed.

  Lemma challenge_heap_valid_set_decrypt_count mem n :
    challenge_heap_valid mem ->
    challenge_heap_valid
      (set_heap mem IndCpadGame.decrypt_count_addr n).
  Proof.
    rewrite /challenge_heap_valid.
    rewrite !get_set_heap_neq; try neq_loc_auto.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_set_decrypt_count_valid
      memL memR n :
    sim_decrypt_reduction_heap_rel memL memR ->
    sim_decrypt_reduction_heap_rel
      (set_heap memL IndCpadGame.decrypt_count_addr n)
      (set_heap memR IndCpaDSim.decrypt_count_addr n).
  Proof.
    move=> Hrel.
    apply: sim_decrypt_reduction_heap_rel_set_decrypt_count.
    - exact: Hrel.
    - apply: challenge_heap_valid_set_decrypt_count.
      exact: (sim_decrypt_reduction_heap_rel_challenge_valid Hrel).
  Qed.

  Lemma challenge_heap_valid_pk_initialized mem pk :
    challenge_heap_valid mem ->
    get_heap mem IndCpadGame.pk_addr = Some pk ->
    exists evk sk,
      [/\ get_heap mem IndCpadGame.evk_addr = Some evk,
          get_heap mem IndCpadGame.sk_addr = Some sk,
          good_keys pk evk sk &
          table_valid_for_branch sk
            (get_heap mem IndCpadGame.bit_addr)
            (get_heap mem IndCpadGame.table_addr)].
  Proof.
    rewrite /challenge_heap_valid=> Hinv Hpk.
    move: Hinv.
    rewrite Hpk.
    case Hevk: (get_heap mem IndCpadGame.evk_addr)=> [evk|] //.
    case Hsk: (get_heap mem IndCpadGame.sk_addr)=> [sk|] //.
    move=> /andP [Hkeys Htable].
    by exists evk, sk.
  Qed.

  Lemma challenge_heap_valid_evk_initialized mem evk :
    challenge_heap_valid mem ->
    get_heap mem IndCpadGame.evk_addr = Some evk ->
    exists pk sk,
      [/\ get_heap mem IndCpadGame.pk_addr = Some pk,
          get_heap mem IndCpadGame.sk_addr = Some sk,
          good_keys pk evk sk &
          table_valid_for_branch sk
            (get_heap mem IndCpadGame.bit_addr)
            (get_heap mem IndCpadGame.table_addr)].
  Proof.
    rewrite /challenge_heap_valid=> Hinv Hevk.
    move: Hinv.
    case Hpk: (get_heap mem IndCpadGame.pk_addr)=> [pk|];
      rewrite Hevk //.
    case Hsk: (get_heap mem IndCpadGame.sk_addr)=> [sk|] //.
    move=> /andP [Hkeys Htable].
    by exists pk, sk.
  Qed.

  Lemma challenge_heap_valid_sk_initialized mem sk :
    challenge_heap_valid mem ->
    get_heap mem IndCpadGame.sk_addr = Some sk ->
    exists pk evk,
      [/\ get_heap mem IndCpadGame.pk_addr = Some pk,
          get_heap mem IndCpadGame.evk_addr = Some evk,
          good_keys pk evk sk &
          table_valid_for_branch sk
            (get_heap mem IndCpadGame.bit_addr)
            (get_heap mem IndCpadGame.table_addr)].
  Proof.
    rewrite /challenge_heap_valid=> Hinv Hsk.
    move: Hinv.
    case Hpk: (get_heap mem IndCpadGame.pk_addr)=> [pk|];
      last first.
      case: (get_heap mem IndCpadGame.evk_addr)=> [evk|] //.
      by rewrite Hsk.
    case Hevk: (get_heap mem IndCpadGame.evk_addr)=> [evk|] //.
    rewrite Hsk.
    move=> /andP [Hkeys Htable].
    by exists pk, evk.
  Qed.

  Lemma challenge_heap_valid_set_table_encrypt
      mem pk evk sk m0 m1 c :
    challenge_heap_valid mem ->
    get_heap mem IndCpadGame.pk_addr = Some pk ->
    get_heap mem IndCpadGame.evk_addr = Some evk ->
    get_heap mem IndCpadGame.sk_addr = Some sk ->
    c \in dinsupp
      (encrypt pk
        (if get_heap mem IndCpadGame.bit_addr then m1 else m0)) ->
    challenge_heap_valid
      (set_heap mem IndCpadGame.table_addr
        (get_heap mem IndCpadGame.table_addr ++ [:: (m0, m1, c)])).
  Proof.
    move=> Hinv Hpk Hevk Hsk Hc.
    rewrite /challenge_heap_valid in Hinv *.
    move: Hinv.
    rewrite Hpk Hevk Hsk=> /andP [Hkeys Htable].
    rewrite get_set_heap_eq.
    rewrite !get_set_heap_neq; try neq_loc_auto.
    rewrite Hpk Hevk Hsk Hkeys /=.
    exact: (table_valid_for_branch_rcons_encrypt
      pk evk sk (get_heap mem IndCpadGame.bit_addr)
      (get_heap mem IndCpadGame.table_addr) m0 m1 c
      Hkeys Htable Hc).
  Qed.

  Lemma challenge_heap_valid_set_table_eval1
      mem pk evk sk gate r
      (r_in_range :
        (r < length (get_heap mem IndCpadGame.table_addr))%N) c' :
    challenge_heap_valid mem ->
    get_heap mem IndCpadGame.pk_addr = Some pk ->
    get_heap mem IndCpadGame.evk_addr = Some evk ->
    get_heap mem IndCpadGame.sk_addr = Some sk ->
    c' \in dinsupp
      (let '(_, _, c) :=
        nth_valid (get_heap mem IndCpadGame.table_addr) r r_in_range in
       eval1 evk gate c) ->
    challenge_heap_valid
      (set_heap mem IndCpadGame.table_addr
        (get_heap mem IndCpadGame.table_addr ++
          [:: let '(m0, m1, _) :=
                nth_valid (get_heap mem IndCpadGame.table_addr)
                  r r_in_range in
              (interpret_unary gate m0, interpret_unary gate m1, c')])).
  Proof.
    move=> Hinv Hpk Hevk Hsk Hc'.
    rewrite /challenge_heap_valid in Hinv *.
    move: Hinv.
    rewrite Hpk Hevk Hsk=> /andP [Hkeys Htable].
    rewrite get_set_heap_eq.
    rewrite !get_set_heap_neq; try neq_loc_auto.
    rewrite Hpk Hevk Hsk Hkeys /=.
    exact: (table_valid_for_branch_rcons_eval1
      pk evk sk (get_heap mem IndCpadGame.bit_addr)
      (get_heap mem IndCpadGame.table_addr) gate r r_in_range c'
      Hkeys Htable Hc').
  Qed.

  Lemma challenge_heap_valid_set_table_eval2
      mem pk evk sk gate ri rj
      (ri_in_range :
        (ri < length (get_heap mem IndCpadGame.table_addr))%N)
      (rj_in_range :
        (rj < length (get_heap mem IndCpadGame.table_addr))%N) c' :
    challenge_heap_valid mem ->
    get_heap mem IndCpadGame.pk_addr = Some pk ->
    get_heap mem IndCpadGame.evk_addr = Some evk ->
    get_heap mem IndCpadGame.sk_addr = Some sk ->
    c' \in dinsupp
      (let '(_, _, ci) :=
        nth_valid (get_heap mem IndCpadGame.table_addr) ri ri_in_range in
       let '(_, _, cj) :=
        nth_valid (get_heap mem IndCpadGame.table_addr) rj rj_in_range in
       eval2 evk gate ci cj) ->
    challenge_heap_valid
      (set_heap mem IndCpadGame.table_addr
        (get_heap mem IndCpadGame.table_addr ++
          [:: let '(m0i, m1i, _) :=
                nth_valid (get_heap mem IndCpadGame.table_addr)
                  ri ri_in_range in
              let '(m0j, m1j, _) :=
                nth_valid (get_heap mem IndCpadGame.table_addr)
                  rj rj_in_range in
              (interpret_binary gate m0i m0j,
               interpret_binary gate m1i m1j, c')])).
  Proof.
    move=> Hinv Hpk Hevk Hsk Hc'.
    rewrite /challenge_heap_valid in Hinv *.
    move: Hinv.
    rewrite Hpk Hevk Hsk=> /andP [Hkeys Htable].
    rewrite get_set_heap_eq.
    rewrite !get_set_heap_neq; try neq_loc_auto.
    rewrite Hpk Hevk Hsk Hkeys /=.
    exact: (table_valid_for_branch_rcons_eval2
      pk evk sk (get_heap mem IndCpadGame.bit_addr)
      (get_heap mem IndCpadGame.table_addr) gate ri rj
      ri_in_range rj_in_range c' Hkeys Htable Hc').
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_set_table_encrypt
      memL memR pk evk sk m0 m1 c :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memL IndCpadGame.pk_addr = Some pk ->
    get_heap memL IndCpadGame.evk_addr = Some evk ->
    get_heap memL IndCpadGame.sk_addr = Some sk ->
    c \in dinsupp
      (encrypt pk
        (if get_heap memL IndCpadGame.bit_addr then m1 else m0)) ->
    sim_decrypt_reduction_heap_rel
      (set_heap memL IndCpadGame.table_addr
        (get_heap memL IndCpadGame.table_addr ++ [:: (m0, m1, c)]))
      (set_heap memR IndCpaDSim.table_addr
        (get_heap memR IndCpaDSim.table_addr ++ [:: (m0, m1, c)])).
  Proof.
    move=> Hrel Hpk Hevk Hsk Hc.
    have Htable := sim_decrypt_reduction_heap_rel_table Hrel.
    rewrite -Htable.
    apply: sim_decrypt_reduction_heap_rel_set_table.
    - exact: Hrel.
    - exact: (challenge_heap_valid_set_table_encrypt
        memL pk evk sk m0 m1 c
        (sim_decrypt_reduction_heap_rel_challenge_valid Hrel)
        Hpk Hevk Hsk Hc).
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_set_table_encrypt_right
      memL memR pk evk sk m0 m1 c :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memR IndCpaSecurity.IndCpaGame.pk_addr = Some pk ->
    get_heap memL IndCpadGame.evk_addr = Some evk ->
    get_heap memL IndCpadGame.sk_addr = Some sk ->
    c \in dinsupp
      (encrypt pk
        (if get_heap memR IndCpaSecurity.IndCpaGame.bit_addr then m1 else m0)) ->
    sim_decrypt_reduction_heap_rel
      (set_heap memL IndCpadGame.table_addr
        (get_heap memL IndCpadGame.table_addr ++ [:: (m0, m1, c)]))
      (set_heap memR IndCpaDSim.table_addr
        (get_heap memR IndCpaDSim.table_addr ++ [:: (m0, m1, c)])).
  Proof.
    move=> Hrel HpkR Hevk Hsk Hc.
    have HpkL : get_heap memL IndCpadGame.pk_addr = Some pk.
      have Hpk := sim_decrypt_reduction_heap_rel_pk_outer Hrel.
      by rewrite Hpk HpkR.
    have HcL :
        c \in dinsupp
          (encrypt pk
            (if get_heap memL IndCpadGame.bit_addr then m1 else m0)).
      have Hbit := sim_decrypt_reduction_heap_rel_bit Hrel.
      by rewrite Hbit.
    exact: (sim_decrypt_reduction_heap_rel_set_table_encrypt
      memL memR pk evk sk m0 m1 c Hrel HpkL Hevk Hsk HcL).
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_set_table_eval1
      memL memR pk evk sk gate r
      (r_in_range :
        (r < length (get_heap memL IndCpadGame.table_addr))%N) c' :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memL IndCpadGame.pk_addr = Some pk ->
    get_heap memL IndCpadGame.evk_addr = Some evk ->
    get_heap memL IndCpadGame.sk_addr = Some sk ->
    c' \in dinsupp
      (let '(_, _, c) :=
        nth_valid (get_heap memL IndCpadGame.table_addr) r r_in_range in
       eval1 evk gate c) ->
    sim_decrypt_reduction_heap_rel
      (set_heap memL IndCpadGame.table_addr
        (get_heap memL IndCpadGame.table_addr ++
          [:: let '(m0, m1, _) :=
                nth_valid (get_heap memL IndCpadGame.table_addr)
                  r r_in_range in
              (interpret_unary gate m0, interpret_unary gate m1, c')]))
      (set_heap memR IndCpaDSim.table_addr
        (get_heap memL IndCpadGame.table_addr ++
          [:: let '(m0, m1, _) :=
                nth_valid (get_heap memL IndCpadGame.table_addr)
                  r r_in_range in
              (interpret_unary gate m0, interpret_unary gate m1, c')])).
  Proof.
    move=> Hrel Hpk Hevk Hsk Hc'.
    apply: sim_decrypt_reduction_heap_rel_set_table.
    - exact: Hrel.
    - exact: (challenge_heap_valid_set_table_eval1
        memL pk evk sk gate r r_in_range c'
        (sim_decrypt_reduction_heap_rel_challenge_valid Hrel)
        Hpk Hevk Hsk Hc').
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_set_table_eval2
      memL memR pk evk sk gate ri rj
      (ri_in_range :
        (ri < length (get_heap memL IndCpadGame.table_addr))%N)
      (rj_in_range :
        (rj < length (get_heap memL IndCpadGame.table_addr))%N) c' :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memL IndCpadGame.pk_addr = Some pk ->
    get_heap memL IndCpadGame.evk_addr = Some evk ->
    get_heap memL IndCpadGame.sk_addr = Some sk ->
    c' \in dinsupp
      (let '(_, _, ci) :=
        nth_valid (get_heap memL IndCpadGame.table_addr) ri ri_in_range in
       let '(_, _, cj) :=
        nth_valid (get_heap memL IndCpadGame.table_addr) rj rj_in_range in
       eval2 evk gate ci cj) ->
    sim_decrypt_reduction_heap_rel
      (set_heap memL IndCpadGame.table_addr
        (get_heap memL IndCpadGame.table_addr ++
          [:: let '(m0i, m1i, _) :=
                nth_valid (get_heap memL IndCpadGame.table_addr)
                  ri ri_in_range in
              let '(m0j, m1j, _) :=
                nth_valid (get_heap memL IndCpadGame.table_addr)
                  rj rj_in_range in
              (interpret_binary gate m0i m0j,
               interpret_binary gate m1i m1j, c')]))
      (set_heap memR IndCpaDSim.table_addr
        (get_heap memL IndCpadGame.table_addr ++
          [:: let '(m0i, m1i, _) :=
                nth_valid (get_heap memL IndCpadGame.table_addr)
                  ri ri_in_range in
              let '(m0j, m1j, _) :=
                nth_valid (get_heap memL IndCpadGame.table_addr)
                  rj rj_in_range in
              (interpret_binary gate m0i m0j,
               interpret_binary gate m1i m1j, c')])).
  Proof.
    move=> Hrel Hpk Hevk Hsk Hc'.
    apply: sim_decrypt_reduction_heap_rel_set_table.
    - exact: Hrel.
    - exact: (challenge_heap_valid_set_table_eval2
        memL pk evk sk gate ri rj ri_in_range rj_in_range c'
        (sim_decrypt_reduction_heap_rel_challenge_valid Hrel)
        Hpk Hevk Hsk Hc').
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_eval1_row
      memL memR r
      (rL : (r < length (get_heap memL IndCpadGame.table_addr))%N)
      (rR : (r < length (get_heap memR IndCpaDSim.table_addr))%N) :
    sim_decrypt_reduction_heap_rel memL memR ->
    nth_valid (get_heap memR IndCpaDSim.table_addr) r rR =
    nth_valid (get_heap memL IndCpadGame.table_addr) r rL.
  Proof.
    move=> Hrel.
    have Htable := sim_decrypt_reduction_heap_rel_table Hrel.
    move: rR.
    rewrite -Htable=> rR.
    exact: nth_valid_irrel.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_eval2_row_i
      memL memR ri
      (riL : (ri < length (get_heap memL IndCpadGame.table_addr))%N)
      (riR : (ri < length (get_heap memR IndCpaDSim.table_addr))%N) :
    sim_decrypt_reduction_heap_rel memL memR ->
    nth_valid (get_heap memR IndCpaDSim.table_addr) ri riR =
    nth_valid (get_heap memL IndCpadGame.table_addr) ri riL.
  Proof.
    exact: sim_decrypt_reduction_heap_rel_eval1_row.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_eval2_row_j
      memL memR rj
      (rjL : (rj < length (get_heap memL IndCpadGame.table_addr))%N)
      (rjR : (rj < length (get_heap memR IndCpaDSim.table_addr))%N) :
    sim_decrypt_reduction_heap_rel memL memR ->
    nth_valid (get_heap memR IndCpaDSim.table_addr) rj rjR =
    nth_valid (get_heap memL IndCpadGame.table_addr) rj rjL.
  Proof.
    exact: sim_decrypt_reduction_heap_rel_eval1_row.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_evk_from_sim memL memR evk :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memR IndCpaDSim.evk_addr = Some evk ->
    get_heap memL IndCpadGame.evk_addr = Some evk.
  Proof.
    move=> Hrel Hevk.
    have H := sim_decrypt_reduction_heap_rel_evk_sim Hrel.
    by rewrite H Hevk.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_pk_from_sim memL memR pk :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memR IndCpaDSim.pk_addr = Some pk ->
    get_heap memL IndCpadGame.pk_addr = Some pk.
  Proof.
    move=> Hrel Hpk.
    have H := sim_decrypt_reduction_heap_rel_pk_sim Hrel.
    by rewrite H Hpk.
  Qed.

  Arguments sim_decrypt_reduction_heap_rel_eval1_row {memL memR r}.
  Arguments sim_decrypt_reduction_heap_rel_eval2_row_i {memL memR ri}.
  Arguments sim_decrypt_reduction_heap_rel_eval2_row_j {memL memR rj}.
  Arguments sim_decrypt_reduction_heap_rel_evk_from_sim {memL memR evk}.
  Arguments sim_decrypt_reduction_heap_rel_pk_from_sim {memL memR pk}.

  Lemma sim_decrypt_reduction_heap_rel_set_table_eval1_right
      memL memR pk evk sk gate r
      (rL : (r < length (get_heap memL IndCpadGame.table_addr))%N)
      (rR : (r < length (get_heap memR IndCpaDSim.table_addr))%N) c' :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memL IndCpadGame.pk_addr = Some pk ->
    get_heap memR IndCpaDSim.evk_addr = Some evk ->
    get_heap memL IndCpadGame.sk_addr = Some sk ->
    c' \in dinsupp
      (let '(_, _, c) :=
        nth_valid (get_heap memR IndCpaDSim.table_addr) r rR in
       eval1 evk gate c) ->
    sim_decrypt_reduction_heap_rel
      (set_heap memL IndCpadGame.table_addr
        (get_heap memL IndCpadGame.table_addr ++
          [:: let '(m0, m1, _) :=
                nth_valid (get_heap memL IndCpadGame.table_addr) r rL in
              (interpret_unary gate m0, interpret_unary gate m1, c')]))
      (set_heap memR IndCpaDSim.table_addr
        (get_heap memR IndCpaDSim.table_addr ++
          [:: let '(m0, m1, _) :=
                nth_valid (get_heap memR IndCpaDSim.table_addr) r rR in
              (interpret_unary gate m0, interpret_unary gate m1, c')])).
  Proof.
    move=> Hrel Hpk HevkR Hsk Hc'.
    have Hevk := sim_decrypt_reduction_heap_rel_evk_from_sim Hrel HevkR.
    have Hrow := sim_decrypt_reduction_heap_rel_eval1_row rL rR Hrel.
    rewrite Hrow in Hc' *.
    have Hbase := sim_decrypt_reduction_heap_rel_set_table_eval1
      memL memR pk evk sk gate r rL c' Hrel Hpk Hevk Hsk Hc'.
    move: Hbase.
    have Htable := sim_decrypt_reduction_heap_rel_table Hrel.
    rewrite -Htable.
    by [].
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_set_table_eval2_right
      memL memR pk evk sk gate ri rj
      (riL : (ri < length (get_heap memL IndCpadGame.table_addr))%N)
      (rjL : (rj < length (get_heap memL IndCpadGame.table_addr))%N)
      (riR : (ri < length (get_heap memR IndCpaDSim.table_addr))%N)
      (rjR : (rj < length (get_heap memR IndCpaDSim.table_addr))%N) c' :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memL IndCpadGame.pk_addr = Some pk ->
    get_heap memR IndCpaDSim.evk_addr = Some evk ->
    get_heap memL IndCpadGame.sk_addr = Some sk ->
    c' \in dinsupp
      (let '(_, _, ci) :=
        nth_valid (get_heap memR IndCpaDSim.table_addr) ri riR in
       let '(_, _, cj) :=
        nth_valid (get_heap memR IndCpaDSim.table_addr) rj rjR in
       eval2 evk gate ci cj) ->
    sim_decrypt_reduction_heap_rel
      (set_heap memL IndCpadGame.table_addr
        (get_heap memL IndCpadGame.table_addr ++
          [:: let '(m0i, m1i, _) :=
                nth_valid (get_heap memL IndCpadGame.table_addr) ri riL in
              let '(m0j, m1j, _) :=
                nth_valid (get_heap memL IndCpadGame.table_addr) rj rjL in
              (interpret_binary gate m0i m0j,
               interpret_binary gate m1i m1j, c')]))
      (set_heap memR IndCpaDSim.table_addr
        (get_heap memR IndCpaDSim.table_addr ++
          [:: let '(m0i, m1i, _) :=
                nth_valid (get_heap memR IndCpaDSim.table_addr) ri riR in
              let '(m0j, m1j, _) :=
                nth_valid (get_heap memR IndCpaDSim.table_addr) rj rjR in
              (interpret_binary gate m0i m0j,
               interpret_binary gate m1i m1j, c')])).
  Proof.
    move=> Hrel Hpk HevkR Hsk Hc'.
    have Hevk := sim_decrypt_reduction_heap_rel_evk_from_sim Hrel HevkR.
    have Hrow_i := sim_decrypt_reduction_heap_rel_eval2_row_i riL riR Hrel.
    have Hrow_j := sim_decrypt_reduction_heap_rel_eval2_row_j rjL rjR Hrel.
    rewrite Hrow_i Hrow_j in Hc' *.
    have Hbase := sim_decrypt_reduction_heap_rel_set_table_eval2
      memL memR pk evk sk gate ri rj riL rjL c'
      Hrel Hpk Hevk Hsk Hc'.
    move: Hbase.
    have Htable := sim_decrypt_reduction_heap_rel_table Hrel.
    rewrite -Htable.
    by [].
  Qed.

End NoiseFloodingSecureOracleSetup.
