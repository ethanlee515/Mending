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

From Mending.Security.NoiseFloodingSecurity Require Import Prelude GameReduction.

Module NoiseFloodingSecure
  (Import Scheme : ApproxFheScheme)
  (Import Metric : ApproxFheMetric(Scheme))
  (Import Correctness : ApproxCorrectnessPerfect(Scheme)(Metric))
  (Import IndCpaSecurity : IsIndCpa(Scheme))
  (Import Params : NoiseFloodingParams).
  Include GameReduction.NoiseFloodingSecureGameReduction(Scheme)(Metric)(Correctness)(IndCpaSecurity)(Params).

  Definition game_initial_pre :
    pred ((chUnit * heap) * (chUnit * heap)) :=
    pred1 ((tt, empty_heap), (tt, empty_heap)).

  Lemma ind_cpad_reduction_factored_result_bridge_from_guess_adv
      (A : nom_package)
      (guessL guessR :
        (bool * (pk_t * evk_t))%type -> raw_code bool) :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    sim_decrypt_reduction_adv_continuation_witness A guessL guessR ->
    ⊨AE ⦃ game_initial_pre ⦄
      (fun _ : chUnit =>
        init ← ind_cpad_challenge_init_code tt ;;
        guessL init)
      ≈( 0 )
      (fun _ : chUnit =>
        init ← ind_cpa_reduction_challenge_init_code tt ;;
        guessR init)
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> Houter Hcont.
    split; first exact: lexx.
    move=> memL memR xL xR Hpre.
    rewrite /game_initial_pre in Hpre.
    move/eqP: Hpre=> Hpre.
    inversion Hpre; subst.
    pose d0 := ind_cpad_reduction_challenge_init_coupling.
    pose KL (ymem : (bool * (pk_t * evk_t))%type * heap) :=
      Pr_code (guessL ymem.1) ymem.2.
    pose KR (ymem : (bool * (pk_t * evk_t))%type * heap) :=
      Pr_code (guessR ymem.1) ymem.2.
    pose K :=
      sim_decrypt_reduction_adv_continuation_kernel A guessL guessR Hcont.
    pose finalD := \dlet_(xy <- d0) K xy.
    pose leftD : {distr (bool * heap) / R} :=
      Pr_code
        (init ← ind_cpad_challenge_init_code tt ;; guessL init)
        empty_heap.
    pose rightD : {distr (bool * heap) / R} :=
      Pr_code
        (init ← ind_cpa_reduction_challenge_init_code tt ;; guessR init)
        empty_heap.
    have Hfinal_coupling : coupling finalD (complete leftD)
        (complete rightD).
      have Hbind := coupling_bind_kernel d0
        (complete (Pr_code (ind_cpad_challenge_init_code tt) empty_heap))
        (complete
          (Pr_code (ind_cpa_reduction_challenge_init_code tt) empty_heap))
        K (complete_bind_kernel KL) (complete_bind_kernel KR)
        ind_cpad_reduction_challenge_init_coupling_margins
        (sim_decrypt_reduction_adv_continuation_kernel_margins
          A guessL guessR Hcont).
      have [HL HR] := coupling_margins Hbind.
      apply: coupling_of_margins; split.
      - move=> z.
        rewrite /finalD /leftD HL.
        rewrite (complete_bind
          (Pr_code (ind_cpad_challenge_init_code tt) empty_heap) KL z).
        rewrite /KL Pr_code_bind.
        by [].
      - move=> z.
        rewrite /finalD /rightD HR.
        rewrite (complete_bind
          (Pr_code (ind_cpa_reduction_challenge_init_code tt) empty_heap)
          KR z).
        rewrite /KR Pr_code_bind.
        by [].
    exists finalD.
    split; first exact: Hfinal_coupling.
    rewrite subr0.
    have Hfinal_weight : dweight finalD = 1.
      have [HfinalL _] := coupling_margins Hfinal_coupling.
      rewrite -(dmargin_dweight fst finalD).
      transitivity (dweight (complete leftD)).
      - apply: eq_psum=> z.
        by rewrite !mul1r HfinalL.
      - exact: complete_dweight.
    rewrite (pr_eq1_of_support finalD same_game_result_opt Hfinal_weight).
    - exact: lexx.
    move=> outs Houts.
    have [xy Hxy Hinner] := @dinsupp_dlet R _ _ _ _ _ Houts.
    have [b [pk [evk [sk [Hkeys Hxy_eq]]]]] :=
      ind_cpad_reduction_challenge_init_coupling_support_some xy Hxy.
    rewrite Hxy_eq in Hinner.
    have Hinit_adv :=
      same_result_sim_decrypt_reduction_adv_opt_initialized
        A b pk evk sk Houter Hkeys.
    have Hinit_pre :
        same_input_sim_decrypt_reduction_adv_pre A
          (((b, (pk, evk)), challenge_initialized_heap b pk evk sk),
           ((b, (pk, evk)), reduction_initialized_heap b pk evk)).
      exact: (same_result_sim_decrypt_reduction_adv_opt_some_pre
        A (b, (pk, evk)) (b, (pk, evk))
        (challenge_initialized_heap b pk evk sk)
        (reduction_initialized_heap b pk evk) Hinit_adv).
    have Hsupport :
        supports_same_result_sim_decrypt_reduction_adv_opt A
          (K
            (Some
              ((b, (pk, evk)), challenge_initialized_heap b pk evk sk),
             Some
              ((b, (pk, evk)), reduction_initialized_heap b pk evk))).
      rewrite /K.
      exact: (sim_decrypt_reduction_adv_continuation_kernel_support
        A guessL guessR Hcont
        (b, (pk, evk)) (b, (pk, evk))
        (challenge_initialized_heap b pk evk sk)
        (reduction_initialized_heap b pk evk) Hinit_pre).
    have Hresult :=
      same_result_sim_decrypt_reduction_adv_result_opt A outs
        (Hsupport outs Hinner).
    by move: Hresult; rewrite /same_result_opt /same_game_result_opt.
  Qed.

  Definition ind_cpad_compiled_real_game_code
      (A : nom_package) (max_queries : nat) (_ : chUnit) :
      raw_code bool :=
    code_link
      (compile_calls max_queries
        (X := nat) (Y := chOption message)
        (IndCpadGame.IndCpadOracle max_queries)
        IndCpadGame.oracle_decrypt
        (ind_cpad_open_game_code A tt))
      (IndCpadGame.IndCpadOracle max_queries).

  Definition ind_cpad_compiled_real_factored_open_game_code
      (A : nom_package) (max_queries : nat) (_ : chUnit) :
      raw_code bool :=
    code_link
      (compile_calls max_queries
        (X := nat) (Y := chOption message)
        (IndCpadGame.IndCpadOracle max_queries)
        IndCpadGame.oracle_decrypt
        (ind_cpad_factored_open_game_code A tt))
      (IndCpadGame.IndCpadOracle max_queries).

  Lemma ind_cpad_compiled_real_game_code_factored
      (A : nom_package) max_queries x :
    ind_cpad_compiled_real_game_code A max_queries x =
    ind_cpad_compiled_real_factored_open_game_code A max_queries x.
  Proof.
    rewrite /ind_cpad_compiled_real_game_code
      /ind_cpad_compiled_real_factored_open_game_code.
    by rewrite ind_cpad_open_game_code_factored.
  Qed.

  Lemma ind_cpad_compiled_real_factored_open_game_code_guess
      (A : nom_package) max_queries x :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    ind_cpad_compiled_real_factored_open_game_code A max_queries x =
    ind_cpad_factored_compiled_real_guess_game_code A max_queries x.
  Proof.
    move=> A_valid.
    case: x=> [].
    rewrite /ind_cpad_compiled_real_factored_open_game_code
      /ind_cpad_factored_compiled_real_guess_game_code.
    have Hfactored_valid :
        ValidCode (loc ((IndCpadGame.IndCpadChallenger ∘ A)%sep))
          IndCpadGame.IndCpadAdv_import
          (ind_cpad_factored_open_game_code A tt).
      rewrite -ind_cpad_open_game_code_factored.
      exact: (ind_cpad_open_game_code_valid A A_valid tt).
    rewrite (@compile_calls_correct_code_link max_queries
      nat (chOption message) bool
      (loc ((IndCpadGame.IndCpadChallenger ∘ A)%sep))
      IndCpadGame.oracle_mem_spec IndCpadGame.IndCpadAdv_import
      (IndCpadGame.IndCpadOracle max_queries)
      IndCpadGame.oracle_decrypt
      (ind_cpad_factored_open_game_code A tt)
      (IndCpadRealOracle_valid max_queries)
      ind_cpad_decrypt_in_adv_import
      Hfactored_valid).
    rewrite /ind_cpad_factored_open_game_code code_link_bind.
    rewrite (_ : code_link (ind_cpad_challenge_init_code tt)
        (IndCpadGame.IndCpadOracle max_queries) =
      ind_cpad_challenge_init_code tt).
    - f_equal.
      apply functional_extensionality=> init.
      rewrite /ind_cpad_compiled_real_guess_code.
      rewrite (@compile_calls_correct_code_link max_queries
        nat (chOption message) bool
        (loc (ind_cpad_moved_adversary A))
        IndCpadGame.oracle_mem_spec IndCpadGame.IndCpadAdv_import
        (IndCpadGame.IndCpadOracle max_queries)
        IndCpadGame.oracle_decrypt
        (ind_cpad_open_guess_code A init)
        (IndCpadRealOracle_valid max_queries)
        ind_cpad_decrypt_in_adv_import
        (ind_cpad_open_guess_code_valid A A_valid init)).
      by [].
    exact: ind_cpad_challenge_init_code_link_closed.
  Qed.

  Definition ind_cpad_linked_real_game_code
      (A : nom_package) (max_queries : nat) (_ : chUnit) :
      raw_code bool :=
    code_link
      (ind_cpad_open_game_code A tt)
      (IndCpadGame.IndCpadOracle max_queries).

  Definition ind_cpad_compiled_sim_decrypt_game_code
      (A : nom_package) (max_queries : nat) (_ : chUnit) :
      raw_code bool :=
    code_link
      (compile_calls max_queries
        (X := nat) (Y := chOption message)
        (IndCpadSimDecryptOracle max_queries)
        IndCpadGame.oracle_decrypt
        (ind_cpad_open_game_code A tt))
      (IndCpadGame.IndCpadOracle max_queries).

  Definition ind_cpad_compiled_sim_decrypt_factored_open_game_code
      (A : nom_package) (max_queries : nat) (_ : chUnit) :
      raw_code bool :=
    code_link
      (compile_calls max_queries
        (X := nat) (Y := chOption message)
        (IndCpadSimDecryptOracle max_queries)
        IndCpadGame.oracle_decrypt
        (ind_cpad_factored_open_game_code A tt))
      (IndCpadGame.IndCpadOracle max_queries).

  Lemma ind_cpad_compiled_sim_decrypt_game_code_factored
      (A : nom_package) max_queries x :
    ind_cpad_compiled_sim_decrypt_game_code A max_queries x =
    ind_cpad_compiled_sim_decrypt_factored_open_game_code A max_queries x.
  Proof.
    rewrite /ind_cpad_compiled_sim_decrypt_game_code
      /ind_cpad_compiled_sim_decrypt_factored_open_game_code.
    by rewrite ind_cpad_open_game_code_factored.
  Qed.

  Lemma ind_cpad_compiled_sim_decrypt_factored_open_game_code_guess
      (A : nom_package) max_queries x mem :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    Pr_code
      (ind_cpad_compiled_sim_decrypt_factored_open_game_code
        A max_queries x) mem =
    Pr_code
      (ind_cpad_factored_compiled_sim_decrypt_guess_game_code
        A max_queries x) mem.
  Proof.
    move=> A_valid.
    case: x=> [].
    rewrite /ind_cpad_compiled_sim_decrypt_factored_open_game_code
      /ind_cpad_factored_compiled_sim_decrypt_guess_game_code
      /ind_cpad_factored_open_game_code.
    have Hinit_valid :
        ValidCode IndCpadGame.oracle_mem_spec [interface]
          (ind_cpad_challenge_init_code tt).
      rewrite /ind_cpad_challenge_init_code.
      typeclasses eauto with ssprove_valid_db.
    rewrite (@Pr_code_codeLinkCompileCallsClosedPrefix max_queries
      nat (chOption message) (chProd chBool (chProd pk_t evk_t)) bool
      IndCpadGame.oracle_mem_spec
      (IndCpadSimDecryptOracle max_queries)
      (IndCpadGame.IndCpadOracle max_queries)
      IndCpadGame.oracle_decrypt
      (ind_cpad_challenge_init_code tt)
      (ind_cpad_open_guess_code A)
      mem
      Hinit_valid).
    by [].
  Qed.

  (* Same compiled code as [ind_cpad_compiled_sim_decrypt_game_code], but
     linked against the replacement oracle itself.  This should be an exact
     bridge to the uncompiled sim-decrypt game by [compile_calls_correct]. *)
  Definition ind_cpad_compiled_sim_decrypt_self_link_game_code
      (A : nom_package) (max_queries : nat) (_ : chUnit) :
      raw_code bool :=
    code_link
      (compile_calls max_queries
        (X := nat) (Y := chOption message)
        (IndCpadSimDecryptOracle max_queries)
        IndCpadGame.oracle_decrypt
      (ind_cpad_open_game_code A tt))
      (IndCpadSimDecryptOracle max_queries).

  Lemma ind_cpad_compiled_sim_decrypt_self_link_game_code_guess
      (A : nom_package) max_queries x mem :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    Pr_code
      (ind_cpad_compiled_sim_decrypt_self_link_game_code
        A max_queries x) mem =
    Pr_code
      (ind_cpad_factored_compiled_sim_decrypt_self_link_guess_game_code
        A max_queries x) mem.
  Proof.
    move=> A_valid.
    case: x=> [].
    rewrite /ind_cpad_compiled_sim_decrypt_self_link_game_code
      /ind_cpad_factored_compiled_sim_decrypt_self_link_guess_game_code.
    rewrite ind_cpad_open_game_code_factored
      /ind_cpad_factored_open_game_code.
    have Hinit_valid :
        ValidCode IndCpadGame.oracle_mem_spec [interface]
          (ind_cpad_challenge_init_code tt).
      rewrite /ind_cpad_challenge_init_code.
      typeclasses eauto with ssprove_valid_db.
    rewrite (@Pr_code_codeLinkCompileCallsClosedPrefix max_queries
      nat (chOption message) (chProd chBool (chProd pk_t evk_t)) bool
      IndCpadGame.oracle_mem_spec
      (IndCpadSimDecryptOracle max_queries)
      (IndCpadSimDecryptOracle max_queries)
      IndCpadGame.oracle_decrypt
      (ind_cpad_challenge_init_code tt)
      (ind_cpad_open_guess_code A)
      mem
      Hinit_valid).
    by [].
  Qed.

  (* Uncompiled first hybrid: real encrypt/eval code and simulated decrypt,
     before reshaping it into the existing IND-CPA reduction. *)
  Definition ind_cpad_linked_sim_decrypt_game_code
      (A : nom_package) (max_queries : nat) (_ : chUnit) :
      raw_code bool :=
    code_link
      (ind_cpad_open_game_code A tt)
      (IndCpadSimDecryptOracle max_queries).

  Definition ind_cpad_factored_sim_decrypt_game_code
      (A : nom_package) (max_queries : nat) (_ : chUnit) :
      raw_code bool :=
    init ← ind_cpad_challenge_init_code tt ;;
    code_link
      (ind_cpad_open_guess_code A init)
      (IndCpadSimDecryptOracle max_queries).

  Definition ind_cpad_sim_decrypt_game_package
      (A : nom_package) (max_queries : nat) : nom_package :=
    ((IndCpadGame.IndCpadChallenger ∘ A)%sep ∘
      IndCpadSimDecryptOracle max_queries)%share.

  Definition ind_cpad_sim_decrypt_game_code
      (A : nom_package) (max_queries : nat) (_ : chUnit) :
      raw_code bool :=
    resolve (ind_cpad_sim_decrypt_game_package A max_queries)
      (IndCpadGame.main, ('unit, 'bool)) tt.

  Lemma ind_cpad_compiled_real_linked_correct
      (A : nom_package) max_queries :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    forall x,
      ind_cpad_compiled_real_game_code A max_queries x =
      ind_cpad_linked_real_game_code A max_queries x.
  Proof.
    move=> A_valid x.
    rewrite /ind_cpad_compiled_real_game_code
      /ind_cpad_linked_real_game_code.
    rewrite (@compile_calls_correct_code_link max_queries
      nat (chOption message) bool
      (loc ((IndCpadGame.IndCpadChallenger ∘ A)%sep))
      IndCpadGame.oracle_mem_spec IndCpadGame.IndCpadAdv_import
      (IndCpadGame.IndCpadOracle max_queries)
      IndCpadGame.oracle_decrypt
      (ind_cpad_open_game_code A tt)
      (IndCpadRealOracle_valid max_queries)
      ind_cpad_decrypt_in_adv_import
      (ind_cpad_open_game_code_valid A A_valid tt)).
    by [].
  Qed.

  Lemma ind_cpad_compiled_sim_decrypt_self_link_correct
      (A : nom_package) max_queries :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    forall x,
      ind_cpad_compiled_sim_decrypt_self_link_game_code A max_queries x =
      ind_cpad_linked_sim_decrypt_game_code A max_queries x.
  Proof.
    move=> A_valid x.
    rewrite /ind_cpad_compiled_sim_decrypt_self_link_game_code
      /ind_cpad_linked_sim_decrypt_game_code.
    rewrite (@compile_calls_correct_code_link max_queries
      nat (chOption message) bool
      (loc ((IndCpadGame.IndCpadChallenger ∘ A)%sep))
      IndCpadGame.oracle_mem_spec IndCpadGame.IndCpadAdv_import
      (IndCpadSimDecryptOracle max_queries)
      IndCpadGame.oracle_decrypt
      (ind_cpad_open_game_code A tt)
      (IndCpadSimDecryptOracle_valid max_queries)
      ind_cpad_decrypt_in_adv_import
      (ind_cpad_open_game_code_valid A A_valid tt)).
    by [].
  Qed.

  Lemma ind_cpad_sim_decrypt_game_code_linked
      (A : nom_package) max_queries x :
    ind_cpad_sim_decrypt_game_code A max_queries x =
    ind_cpad_linked_sim_decrypt_game_code A max_queries x.
  Proof.
    rewrite /ind_cpad_sim_decrypt_game_code
      /ind_cpad_sim_decrypt_game_package
      /ind_cpad_linked_sim_decrypt_game_code
      /ind_cpad_open_game_code.
    by rewrite resolve_link.
  Qed.

  Lemma ind_cpad_linked_sim_decrypt_game_code_factored
      (A : nom_package) max_queries x :
    ind_cpad_linked_sim_decrypt_game_code A max_queries x =
    ind_cpad_factored_sim_decrypt_game_code A max_queries x.
  Proof.
    case: x=> [].
    rewrite /ind_cpad_linked_sim_decrypt_game_code
      /ind_cpad_factored_sim_decrypt_game_code.
    rewrite ind_cpad_open_game_code_factored.
    rewrite /ind_cpad_factored_open_game_code.
    rewrite code_link_bind.
    rewrite ind_cpad_challenge_init_code_link_closed.
    by [].
  Qed.

  Lemma ind_cpad_sim_decrypt_game_code_factored
      (A : nom_package) max_queries x :
    ind_cpad_sim_decrypt_game_code A max_queries x =
    ind_cpad_factored_sim_decrypt_game_code A max_queries x.
  Proof.
    rewrite ind_cpad_sim_decrypt_game_code_linked.
    exact: ind_cpad_linked_sim_decrypt_game_code_factored.
  Qed.

  Lemma ind_cpad_compiled_guess_decrypt_replacement_from_compile_ready_vector_bound
      (A : nom_package) max_queries :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    ⊨AE ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (ind_cpad_compiled_real_guess_code A max_queries)
      ≈( compile_security_error max_queries )
      (ind_cpad_compiled_sim_decrypt_guess_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> A_valid Hprefix_vector.
    rewrite /ind_cpad_compiled_real_guess_code
      /ind_cpad_compiled_sim_decrypt_guess_code
      /compile_security_error.
    rewrite /same_game_output_opt /same_input_invariant_pre.
    rewrite -tuple_sum_noise_flooding_vector_call_error.
    exact: (compileRule max_queries nat (chOption message)
      (chProd chBool (chProd pk_t evk_t)) bool
      IndCpadGame.oracle_mem_spec
      (loc (ind_cpad_moved_adversary A))
      IndCpadGame.oracle_mem_spec IndCpadGame.oracle_mem_spec
      IndCpadGame.IndCpadAdv_import
      (IndCpadGame.IndCpadOracle max_queries)
      (IndCpadSimDecryptOracle max_queries)
      IndCpadGame.oracle_decrypt
      (ind_cpad_open_guess_code A)
      (cat_tuple [tuple 0]
        (cat_tuple
          [tuple (dim%:R / (2 * gaussian_width_multiplier ^+ 2))] [tuple 0]))
      challenge_heap_valid
      (ind_cpad_open_guess_code_valid A A_valid)
      (IndCpadRealOracle_valid max_queries)
      (IndCpadSimDecryptOracle_valid max_queries)
      (ind_cpad_moved_adversary_separate A)
      challenge_heap_valid_depends_only_on_oracle_mem_spec
      (ind_cpad_real_oracle_preserves_challenge_heap_valid_except_decrypt
        max_queries)
      ind_cpad_decrypt_in_adv_import
      (ind_cpad_decrypt_resolve_pyth_from_metric_encoding_ready_vector_bound
        max_queries Hprefix_vector)).
  Qed.

  Definition ind_cpa_reduction (A : nom_package)
    (max_queries : nat) :=
    IndCpaDSim.IndCpaReduction A max_queries.

  Definition reduction_locs (A : nom_package)
    (max_queries : nat) : Locations :=
    IndCpaDSim.IndCpaReduction_locs A max_queries.

  Definition security_bound (A : nom_package) (max_queries : nat) :=
    let B := ind_cpa_reduction A max_queries in
    IndCpaSecurity.IndCpaGame.winning_probability B +
      security_loss dim max_queries gaussian_width_multiplier.

  Definition ind_cpad_game_code
    (A : nom_package) (max_queries : nat) (_ : chUnit) :
    raw_code bool :=
    resolve (IndCpadGame.IndCpadGame max_queries A)
      (IndCpadGame.main, ('unit, 'bool)) tt.

  Lemma ind_cpad_game_code_linked (A : nom_package) max_queries x :
    ind_cpad_game_code A max_queries x =
    ind_cpad_linked_real_game_code A max_queries x.
  Proof.
    rewrite /ind_cpad_game_code /ind_cpad_linked_real_game_code
      /ind_cpad_open_game_code /IndCpadGame.IndCpadGame.
    by rewrite resolve_link.
  Qed.

  Definition ind_cpa_reduction_game_code
    (A : nom_package) (max_queries : nat) (_ : chUnit) :
    raw_code bool :=
    resolve
      (IndCpaSecurity.IndCpaGame.IndCpaGame
        (ind_cpa_reduction A max_queries))
      (IndCpaSecurity.IndCpaGame.main, ('unit, 'bool)) tt.

  (* The same right endpoint split at the outer IND-CPA encryption oracle.
     These names make the intended item-5 chain explicit: first relate the
     simulated-decrypt IND-CPAD game to the reduction-shaped open game, then
     close it with the real IND-CPA oracle. *)
  Definition ind_cpa_reduction_open_game_code
    (A : nom_package) (max_queries : nat) (_ : chUnit) :
    raw_code bool :=
    resolve
      ((IndCpaSecurity.IndCpaGame.IndCpaChallenger ∘
        ind_cpa_reduction A max_queries)%sep)
      (IndCpaSecurity.IndCpaGame.main, ('unit, 'bool)) tt.

  Definition ind_cpa_reduction_unfresh_open_game_code
    (A : nom_package) (max_queries : nat) (_ : chUnit) :
    raw_code bool :=
    resolve
      ((IndCpaSecurity.IndCpaGame.IndCpaChallenger ∘
        ind_cpa_reduction A max_queries)%share)
      (IndCpaSecurity.IndCpaGame.main, ('unit, 'bool)) tt.

  Definition ind_cpa_reduction_unfresh_open_guess_code
      (A : nom_package) (max_queries : nat)
      (input : (bool * (pk_t * evk_t))%type) : raw_code bool :=
    let '(b, (pk, evk)) := input in
    b' ← resolve
      (ind_cpa_reduction A max_queries)
      (mkopsig IndCpaSecurity.IndCpaGame.adv_guess
        (chProd pk_t evk_t) chBool) (pk, evk) ;;
    ret (eq_op b' b).

  Definition ind_cpa_reduction_unfresh_linked_guess_code
      (A : nom_package) (max_queries : nat)
      (input : (bool * (pk_t * evk_t))%type) : raw_code bool :=
    code_link
      (ind_cpa_reduction_unfresh_open_guess_code A max_queries input)
      IndCpaSecurity.IndCpaGame.IndCpaOracle.

  Lemma ind_cpa_reduction_unfresh_linked_guess_codeE
      (A : nom_package) max_queries input :
    ind_cpa_reduction_unfresh_linked_guess_code A max_queries input =
    let '(b, (pk, evk)) := input in
    ready ← get IndCpaDSim.ready_addr ;;
    b' ← code_link
      (code_link
        (code_link
          (#assert (~~ ready) ;;
           #put IndCpaDSim.ready_addr := true ;;
           #put IndCpaDSim.pk_addr := Some pk ;;
           #put IndCpaDSim.evk_addr := Some evk ;;
           call [ IndCpadGame.guess ] :
             { pk_t × evk_t ~> 'bool } (pk, evk))
          (ind_cpa_reduction_moved_adversary A))
        (IndCpaDSim.IndCpadOracle max_queries))
      IndCpaSecurity.IndCpaGame.IndCpaOracle ;;
    ret (eq_op b' b).
  Proof.
    case: input=> b [pk evk].
    rewrite /ind_cpa_reduction_unfresh_linked_guess_code
      /ind_cpa_reduction_unfresh_open_guess_code
      /ind_cpa_reduction /IndCpaDSim.IndCpaReduction
      /IndCpaDSim.IndCpaSimTop.
    rewrite code_link_bind.
    rewrite resolve_link.
    rewrite sep_linkE.
    rewrite resolve_link.
    rewrite resolve_set /= coerce_kleisliE /=.
    by [].
  Qed.

  (* Continuation entered after [ind_cpa_reduction_challenge_init_code] has
     already installed the simulator keys and set [ready].  This bypasses the
     public IND-CPA adversary-entry shim, which is only correct before the
     simulator has been initialized. *)
  Definition ind_cpa_reduction_direct_guess_code
      (A : nom_package) (max_queries : nat)
      (input : (bool * (pk_t * evk_t))%type) : raw_code bool :=
    let '(b, (pk, evk)) := input in
    b' ← code_link
      (code_link
        (resolve
          (ind_cpa_reduction_moved_adversary A)
          (mkopsig IndCpadGame.guess (chProd pk_t evk_t) chBool)
          (pk, evk))
        (IndCpaDSim.IndCpadOracle max_queries))
      IndCpaSecurity.IndCpaGame.IndCpaOracle ;;
    ret (eq_op b' b).

  Lemma ind_cpa_reduction_direct_guess_code_renamed
      (A : nom_package) max_queries input :
    ind_cpa_reduction_direct_guess_code A max_queries input =
    let '(b, (pk, evk)) := input in
    b' ← code_link
      (code_link
        (Nominal.rename
          (sim_decrypt_reduction_moved_adversary_perm A)
          (resolve
            (ind_cpad_moved_adversary A)
            (mkopsig IndCpadGame.guess (chProd pk_t evk_t) chBool)
            (pk, evk)))
        (IndCpaDSim.IndCpadOracle max_queries))
      IndCpaSecurity.IndCpaGame.IndCpaOracle ;;
    ret (eq_op b' b).
  Proof.
    case: input=> b [pk evk].
    rewrite /ind_cpa_reduction_direct_guess_code.
    rewrite -ind_cpa_reduction_moved_resolve_rename.
    by [].
  Qed.

  Lemma ind_cpa_reduction_ready_false_top_link_prefix
      (A : nom_package) max_queries pk evk :
    code_link
      (code_link
        (code_link
          (#assert true ;;
           #put IndCpaDSim.ready_addr := true ;;
           #put IndCpaDSim.pk_addr := Some pk ;;
           #put IndCpaDSim.evk_addr := Some evk ;;
           call [ IndCpadGame.guess ] :
             { pk_t × evk_t ~> 'bool } (pk, evk))
          (ind_cpa_reduction_moved_adversary A))
        (IndCpaDSim.IndCpadOracle max_queries))
      IndCpaSecurity.IndCpaGame.IndCpaOracle =
    #put IndCpaDSim.ready_addr := true ;;
    #put IndCpaDSim.pk_addr := Some pk ;;
    #put IndCpaDSim.evk_addr := Some evk ;;
    code_link
      (code_link
        (resolve
          (ind_cpa_reduction_moved_adversary A)
          (mkopsig IndCpadGame.guess (chProd pk_t evk_t) chBool)
          (pk, evk))
        (IndCpaDSim.IndCpadOracle max_queries))
      IndCpaSecurity.IndCpaGame.IndCpaOracle.
  Proof.
    rewrite !code_link_assertD /= /assertD /=.
    ssprove_match_commut_gen.
    by rewrite !bind_ret.
  Qed.

  Lemma ind_cpa_reduction_unfresh_linked_guess_ready_falseE
      (A : nom_package) max_queries b pk evk :
    Pr_code
      (ind_cpa_reduction_unfresh_linked_guess_code
        A max_queries (b, (pk, evk)))
      (reduction_outer_initialized_heap b pk evk) =1
    Pr_code
      (ind_cpa_reduction_direct_guess_code A max_queries (b, (pk, evk)))
      (reduction_initialized_heap b pk evk).
  Proof.
    move=> out.
    rewrite ind_cpa_reduction_unfresh_linked_guess_codeE
      /ind_cpa_reduction_direct_guess_code.
    rewrite Pr_code_bind Pr_code_get.
    rewrite reduction_outer_initialized_heap_ready.
    rewrite ind_cpa_reduction_ready_false_top_link_prefix.
    rewrite !Pr_code_bind !Pr_code_put.
    by rewrite /reduction_outer_initialized_heap /reduction_initialized_heap.
  Qed.

  Lemma sim_decrypt_reduction_adv_continuation_witness_direct_guess_expanded
      (A : nom_package) max_queries :
    (forall pk evk,
      sim_decrypt_reduction_adv_continuation_witness A
        (fun _ : chUnit =>
          code_link
            (resolve
              (ind_cpad_moved_adversary A)
              (mkopsig IndCpadGame.guess (chProd pk_t evk_t) chBool)
              (pk, evk))
            (IndCpadSimDecryptOracle max_queries))
        (fun _ : chUnit =>
          code_link
            (code_link
              (Nominal.rename
                (sim_decrypt_reduction_moved_adversary_perm A)
                (resolve
                  (ind_cpad_moved_adversary A)
                  (mkopsig IndCpadGame.guess
                    (chProd pk_t evk_t) chBool)
                  (pk, evk)))
              (IndCpaDSim.IndCpadOracle max_queries))
            IndCpaSecurity.IndCpaGame.IndCpaOracle)) ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun init =>
        let '(b, (pk, evk)) := init in
        b' ← code_link
          (resolve
            (ind_cpad_moved_adversary A)
            (mkopsig IndCpadGame.guess (chProd pk_t evk_t) chBool)
            (pk, evk))
          (IndCpadSimDecryptOracle max_queries) ;;
        ret (eq_op b' b))
      (fun init =>
        let '(b, (pk, evk)) := init in
        b' ← code_link
          (code_link
            (Nominal.rename
              (sim_decrypt_reduction_moved_adversary_perm A)
              (resolve
                (ind_cpad_moved_adversary A)
                (mkopsig IndCpadGame.guess (chProd pk_t evk_t) chBool)
                (pk, evk)))
            (IndCpaDSim.IndCpadOracle max_queries))
          IndCpaSecurity.IndCpaGame.IndCpaOracle ;;
        ret (eq_op b' b)).
  Proof.
    move=> Hresolve.
    apply: sim_decrypt_reduction_adv_continuation_witness_same_input.
    move=> [b [pk evk]].
    apply: sim_decrypt_reduction_adv_continuation_witness_bind_input.
    - exact: Hresolve.
    - move=> b'.
      apply: sim_decrypt_reduction_adv_continuation_witness_ret.
      by [].
  Qed.

  Lemma sim_decrypt_reduction_adv_continuation_witness_moved_guess_resolve
      (A : nom_package) max_queries pk evk :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun _ : chUnit =>
        sim_decrypt_reduction_adv_left_link max_queries
          (resolve
            (ind_cpad_moved_adversary A)
            (mkopsig IndCpadGame.guess (chProd pk_t evk_t) chBool)
            (pk, evk)))
      (fun _ : chUnit =>
        sim_decrypt_reduction_adv_right_link A max_queries
          (resolve
            (ind_cpad_moved_adversary A)
            (mkopsig IndCpadGame.guess (chProd pk_t evk_t) chBool)
            (pk, evk))).
  Proof.
    move=> A_valid Houter.
    exact: (sim_decrypt_reduction_adv_continuation_witness_code_link_rename
      A max_queries
      (resolve
        (ind_cpad_moved_adversary A)
        (mkopsig IndCpadGame.guess (chProd pk_t evk_t) chBool)
        (pk, evk))
      Houter
      (ind_cpad_moved_guess_resolve_valid A pk evk A_valid)).
  Qed.

  Lemma sim_decrypt_reduction_adv_continuation_witness_direct_guess
      (A : nom_package) max_queries :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun init =>
        code_link
          (ind_cpad_open_guess_code A init)
          (IndCpadSimDecryptOracle max_queries))
      (ind_cpa_reduction_direct_guess_code A max_queries).
  Proof.
    move=> A_valid Houter.
    pose guessL (init : (bool * (pk_t * evk_t))%type) : raw_code bool :=
      let '(b, (pk, evk)) := init in
      b' ← code_link
        (resolve
          (ind_cpad_moved_adversary A)
          (mkopsig IndCpadGame.guess (chProd pk_t evk_t) chBool)
          (pk, evk))
        (IndCpadSimDecryptOracle max_queries) ;;
      ret (eq_op b' b).
    pose guessR (init : (bool * (pk_t * evk_t))%type) : raw_code bool :=
      let '(b, (pk, evk)) := init in
      b' ← code_link
        (code_link
          (Nominal.rename
            (sim_decrypt_reduction_moved_adversary_perm A)
            (resolve
              (ind_cpad_moved_adversary A)
              (mkopsig IndCpadGame.guess (chProd pk_t evk_t) chBool)
              (pk, evk)))
          (IndCpaDSim.IndCpadOracle max_queries))
        IndCpaSecurity.IndCpaGame.IndCpaOracle ;;
      ret (eq_op b' b).
    apply: (sim_decrypt_reduction_adv_continuation_witness_eq
      A guessL
      (fun init =>
        code_link
          (ind_cpad_open_guess_code A init)
          (IndCpadSimDecryptOracle max_queries))
      guessR
      (ind_cpa_reduction_direct_guess_code A max_queries)).
    - move=> [b [pk evk]].
      rewrite /guessL /ind_cpad_open_guess_code code_link_bind /=.
      by [].
    - move=> input.
      rewrite /guessR.
      symmetry.
      exact: ind_cpa_reduction_direct_guess_code_renamed.
    - rewrite /guessL /guessR.
      apply: sim_decrypt_reduction_adv_continuation_witness_direct_guess_expanded.
      move=> pk evk.
      exact: (sim_decrypt_reduction_adv_continuation_witness_moved_guess_resolve
        A max_queries pk evk A_valid Houter).
  Qed.

  Definition ind_cpa_reduction_direct_factored_game_code
      (A : nom_package) (max_queries : nat) (_ : chUnit) :
      raw_code bool :=
    init ← ind_cpa_reduction_challenge_init_code tt ;;
    ind_cpa_reduction_direct_guess_code A max_queries init.

  Definition ind_cpa_reduction_unfresh_factored_outer_open_game_code
      (A : nom_package) (max_queries : nat) (_ : chUnit) :
      raw_code bool :=
    init ← ind_cpa_reduction_outer_challenge_init_code tt ;;
    ind_cpa_reduction_unfresh_open_guess_code A max_queries init.

  Lemma ind_cpa_reduction_unfresh_open_game_code_factored_outer
      (A : nom_package) max_queries x :
    ind_cpa_reduction_unfresh_open_game_code A max_queries x =
    ind_cpa_reduction_unfresh_factored_outer_open_game_code
      A max_queries x.
  Proof.
    case: x=> [].
    rewrite /ind_cpa_reduction_unfresh_open_game_code
      /ind_cpa_reduction_unfresh_factored_outer_open_game_code
      /ind_cpa_reduction_outer_challenge_init_code
      /ind_cpa_reduction_unfresh_open_guess_code
      /IndCpaSecurity.IndCpaGame.IndCpaChallenger.
    rewrite resolve_link.
    rewrite resolve_set /= coerce_kleisliE.
    ssprove_match_commut_gen.
    case: a0=> [[pk evk] sk] /=.
    ssprove_match_commut_gen.
  Qed.

  Lemma ind_cpa_reduction_unfresh_open_game_code_rename
      (A : nom_package) max_queries x :
    let P := (IndCpaSecurity.IndCpaGame.IndCpaChallenger : nom_package) in
    let R := IndCpaDSim.IndCpaReduction A max_queries in
    fresh P R ∙
      ind_cpa_reduction_unfresh_open_game_code A max_queries x =
    ind_cpa_reduction_open_game_code A max_queries x.
  Proof.
    case: x=> [].
    set P := (IndCpaSecurity.IndCpaGame.IndCpaChallenger : nom_package).
    set R := IndCpaDSim.IndCpaReduction A max_queries.
    rewrite /ind_cpa_reduction_unfresh_open_game_code
      /ind_cpa_reduction_open_game_code /ind_cpa_reduction.
    change (fresh P R ∙
      resolve ((P ∘ R)%share)
        (IndCpaSecurity.IndCpaGame.main, ('unit, 'bool)) tt =
      resolve ((P ∘ R)%sep)
        (IndCpaSecurity.IndCpaGame.main, ('unit, 'bool)) tt).
    rewrite rename_resolve.
    have Hpkg : fresh P R ∙ ((P ∘ R)%share) = ((P ∘ R)%sep).
      rewrite sep_linkE /move.
      rewrite (equi2_use _ equi_share_link).
      rewrite /P /R.
      rewrite ind_cpa_reduction_sep_fresh_fixes_ind_cpa_challenger.
      by [].
    have Hraw :
        val (fresh P R ∙ ((P ∘ R)%share)) = val ((P ∘ R)%sep).
      by rewrite Hpkg.
    change (resolve (val (fresh P R ∙ ((P ∘ R)%share)))
        (IndCpaSecurity.IndCpaGame.main, ('unit, 'bool)) tt =
      resolve (val ((P ∘ R)%sep))
        (IndCpaSecurity.IndCpaGame.main, ('unit, 'bool)) tt).
    by rewrite Hraw.
  Qed.

  Definition ind_cpa_reduction_linked_game_code
    (A : nom_package) (max_queries : nat) (_ : chUnit) :
    raw_code bool :=
    code_link
      (ind_cpa_reduction_open_game_code A max_queries tt)
      IndCpaSecurity.IndCpaGame.IndCpaOracle.

  Definition ind_cpa_reduction_unfresh_linked_game_code
    (A : nom_package) (max_queries : nat) (_ : chUnit) :
    raw_code bool :=
    code_link
      (ind_cpa_reduction_unfresh_open_game_code A max_queries tt)
      IndCpaSecurity.IndCpaGame.IndCpaOracle.

  Definition ind_cpa_reduction_unfresh_factored_outer_linked_game_code
      (A : nom_package) (max_queries : nat) (_ : chUnit) :
      raw_code bool :=
    init ← ind_cpa_reduction_outer_challenge_init_code tt ;;
    code_link
      (ind_cpa_reduction_unfresh_open_guess_code A max_queries init)
      IndCpaSecurity.IndCpaGame.IndCpaOracle.

  Lemma ind_cpa_reduction_unfresh_factored_outer_linked_game_code_from_guess
      (A : nom_package) max_queries x :
    ind_cpa_reduction_unfresh_factored_outer_linked_game_code
      A max_queries x =
    (init ← ind_cpa_reduction_outer_challenge_init_code tt ;;
     ind_cpa_reduction_unfresh_linked_guess_code A max_queries init).
  Proof. by []. Qed.

  Lemma ind_cpa_reduction_direct_factored_to_unfresh_factored_outer_linked_Pr_codeE
      (A : nom_package) max_queries :
    Pr_code (ind_cpa_reduction_direct_factored_game_code A max_queries tt)
      empty_heap =1
    Pr_code (ind_cpa_reduction_unfresh_factored_outer_linked_game_code
      A max_queries tt) empty_heap.
  Proof.
    move=> out.
    transitivity
      ((\dlet_(b <- dflip (1 / 2))
        \dlet_(keys <- keygen)
          let '(pk, evk, _) := keys in
          Pr_code (ind_cpa_reduction_direct_guess_code
            A max_queries (b, (pk, evk)))
            (reduction_initialized_heap b pk evk)) out).
    - rewrite /ind_cpa_reduction_direct_factored_game_code.
      rewrite Pr_code_bind.
      rewrite /ind_cpa_reduction_challenge_init_code.
      rewrite Pr_code_sample __deprecated__dlet_dlet.
      apply: eq_in_dlet=> // b _ out_b.
      rewrite Pr_code_sample __deprecated__dlet_dlet.
      apply: eq_in_dlet=> // keys _ out_keys.
      case: keys=> [[pk evk] sk].
      by rewrite !Pr_code_put Pr_code_ret dlet_unit /reduction_initialized_heap.
    - symmetry.
      rewrite ind_cpa_reduction_unfresh_factored_outer_linked_game_code_from_guess.
      rewrite Pr_code_bind.
      rewrite /ind_cpa_reduction_outer_challenge_init_code.
      rewrite Pr_code_sample __deprecated__dlet_dlet.
      apply: eq_in_dlet=> // b _ out_b.
      rewrite Pr_code_sample __deprecated__dlet_dlet.
      apply: eq_in_dlet=> // keys _ out_keys.
      case: keys=> [[pk evk] sk].
      rewrite !Pr_code_put Pr_code_ret dlet_unit.
      exact: (ind_cpa_reduction_unfresh_linked_guess_ready_falseE
        A max_queries b pk evk out_keys).
  Qed.

  Lemma ind_cpa_reduction_unfresh_linked_game_code_factored_outer
      (A : nom_package) max_queries x :
    ind_cpa_reduction_unfresh_linked_game_code A max_queries x =
    ind_cpa_reduction_unfresh_factored_outer_linked_game_code
      A max_queries x.
  Proof.
    case: x=> [].
    rewrite /ind_cpa_reduction_unfresh_linked_game_code
      /ind_cpa_reduction_unfresh_factored_outer_linked_game_code.
    rewrite ind_cpa_reduction_unfresh_open_game_code_factored_outer.
    rewrite /ind_cpa_reduction_unfresh_factored_outer_open_game_code.
    rewrite code_link_bind.
    rewrite ind_cpa_reduction_outer_challenge_init_code_link_closed.
    by [].
  Qed.

  Lemma ind_cpa_reduction_unfresh_linked_game_code_alpha
      (A : nom_package) max_queries x :
    ind_cpa_reduction_unfresh_linked_game_code A max_queries x ≡
    ind_cpa_reduction_linked_game_code A max_queries x.
  Proof.
    case: x=> [].
    set P := (IndCpaSecurity.IndCpaGame.IndCpaChallenger : nom_package).
    set R := IndCpaDSim.IndCpaReduction A max_queries.
    exists (fresh P R).
    rewrite /ind_cpa_reduction_unfresh_linked_game_code
      /ind_cpa_reduction_linked_game_code.
    change (fresh P R ∙
      code_link (ind_cpa_reduction_unfresh_open_game_code A max_queries tt)
        IndCpaSecurity.IndCpaGame.IndCpaOracle =
      code_link (ind_cpa_reduction_open_game_code A max_queries tt)
        IndCpaSecurity.IndCpaGame.IndCpaOracle).
    rewrite code_link_rename.
    rewrite /P /R.
    rewrite ind_cpa_reduction_sep_fresh_fixes_ind_cpa_oracle.
    rewrite -/P -/R.
    rewrite ind_cpa_reduction_unfresh_open_game_code_rename.
    by [].
  Qed.

  Lemma ind_cpa_reduction_unfresh_factored_outer_to_linked_ae
      (A : nom_package) max_queries :
    ⊨AE ⦃ game_initial_pre ⦄
      (ind_cpa_reduction_unfresh_factored_outer_linked_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_unfresh_linked_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    apply: (additiveErrorConseqRule
      (ind_cpa_reduction_unfresh_factored_outer_linked_game_code A max_queries)
      (ind_cpa_reduction_unfresh_linked_game_code A max_queries)
      game_initial_pre game_initial_pre
      same_output_heap_opt same_game_output_opt
      0 0).
    - by [].
    - move=> outs.
      exact: same_output_heap_game_output_opt.
    - exact: lexx.
    apply: additiveErrorSameOutputTvdEqRule.
    - exact: lexx.
    - move=> memL memR xL xR Hpre.
      rewrite /game_initial_pre in Hpre.
      move/eqP: Hpre=> Hpre.
      inversion Hpre; subst.
      rewrite -ind_cpa_reduction_unfresh_linked_game_code_factored_outer.
      exact: total_variation_refl_le0.
  Qed.

  Lemma ind_cpa_reduction_game_code_linked
      (A : nom_package) max_queries x :
    ind_cpa_reduction_game_code A max_queries x =
    ind_cpa_reduction_linked_game_code A max_queries x.
  Proof.
    rewrite /ind_cpa_reduction_game_code
      /ind_cpa_reduction_linked_game_code
      /ind_cpa_reduction_open_game_code
      /IndCpaSecurity.IndCpaGame.IndCpaGame.
    by rewrite resolve_link.
  Qed.

  Lemma ind_cpa_reduction_linked_game_code_ae
      (A : nom_package) max_queries :
    ⊨AE ⦃ game_initial_pre ⦄
      (ind_cpa_reduction_linked_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    apply: (additiveErrorConseqRule
      (ind_cpa_reduction_linked_game_code A max_queries)
      (ind_cpa_reduction_game_code A max_queries)
      game_initial_pre game_initial_pre
      same_output_heap_opt same_game_output_opt
      0 0).
    - by [].
    - move=> outs.
      exact: same_output_heap_game_output_opt.
    - by [].
    apply: additiveErrorSameOutputTvdEqRule.
    - exact: lexx.
    - move=> memL memR xL xR Hpre.
      rewrite /game_initial_pre in Hpre.
      move/eqP: Hpre=> Hpre.
      inversion Hpre; subst.
      rewrite -ind_cpa_reduction_game_code_linked.
      exact: total_variation_refl_le0.
  Qed.

  Lemma ind_cpad_sim_decrypt_to_direct_reduction_from_guess_adv_ae
      (A : nom_package) max_queries :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun init =>
        code_link
          (ind_cpad_open_guess_code A init)
          (IndCpadSimDecryptOracle max_queries))
      (ind_cpa_reduction_direct_guess_code A max_queries) ->
    ⊨AE ⦃ game_initial_pre ⦄
      (ind_cpad_sim_decrypt_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_direct_factored_game_code A max_queries)
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> Houter Hcont.
    have Hbridge :=
      ind_cpad_reduction_factored_result_bridge_from_guess_adv
        A
        (fun init =>
          code_link
            (ind_cpad_open_guess_code A init)
            (IndCpadSimDecryptOracle max_queries))
        (ind_cpa_reduction_direct_guess_code A max_queries)
        Houter Hcont.
    split; first exact: Hbridge.1.
    move=> memL memR xL xR Hpre.
    have [d [Hd Hpost]] := Hbridge.2 memL memR xL xR Hpre.
    exists d.
    split; last exact: Hpost.
    move: Hd.
    rewrite (ind_cpad_sim_decrypt_game_code_factored A max_queries xL).
    rewrite /ind_cpad_factored_sim_decrypt_game_code.
    rewrite /ind_cpa_reduction_direct_factored_game_code.
    by [].
  Qed.

  Lemma ind_cpad_sim_decrypt_to_direct_reduction_ae
      (A : nom_package) max_queries :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    ⊨AE ⦃ game_initial_pre ⦄
      (ind_cpad_sim_decrypt_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_direct_factored_game_code A max_queries)
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> A_valid Houter.
    exact: (ind_cpad_sim_decrypt_to_direct_reduction_from_guess_adv_ae
      A max_queries Houter
      (sim_decrypt_reduction_adv_continuation_witness_direct_guess
        A max_queries A_valid Houter)).
  Qed.

  Lemma ind_cpad_sim_decrypt_to_direct_reduction_no_sep_ae
      (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    ⊨AE ⦃ game_initial_pre ⦄
      (ind_cpad_sim_decrypt_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_direct_factored_game_code A max_queries)
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> A_valid.
    exact: (ind_cpad_sim_decrypt_to_direct_reduction_ae
      A max_queries A_valid
      (ind_cpa_reduction_moved_adversary_outer_separate A)).
  Qed.

  Lemma ind_cpad_challenge_init_code_ae :
    ⊨AE_raw ⦃ game_initial_pre ⦄
      ind_cpad_challenge_init_code
      ≈( 0 )
      ind_cpad_challenge_init_code
    ⦃ same_input_invariant_pre challenge_heap_valid ⦄.
  Proof.
    apply: (additiveErrorRawConseqRule
      ind_cpad_challenge_init_code
      ind_cpad_challenge_init_code
      game_initial_pre game_initial_pre
      (fun outs =>
        let '((initL, memL), (initR, memR)) := outs in
        challenge_heap_valid memL && (initL == initR) && (memL == memR))
      (same_input_invariant_pre challenge_heap_valid)
      0 0).
    - by [].
    - case=> [[initL memL] [initR memR]] /=.
      move/andP=> [/andP [Hinv /eqP Hinit] /eqP Hmem].
      subst initR; subst memR.
      by rewrite /same_input_invariant_pre Hinv !eqxx.
    - by [].
    apply: (additiveErrorRawTvdEqPostTotalRule
      ind_cpad_challenge_init_code
      ind_cpad_challenge_init_code
      game_initial_pre
      (fun out => challenge_heap_valid out.2)
      0).
    - exact: lexx.
    - move=> memL memR xL xR Hpre.
      exact: (ind_cpad_challenge_init_code_dweight memL keygen_lossless).
    - move=> memL memR xL xR Hpre.
      exact: (ind_cpad_challenge_init_code_dweight memR keygen_lossless).
    - move=> memL memR xL xR.
      rewrite /game_initial_pre=> /eqP Hpre.
      inversion Hpre; subst.
      exact: total_variation_refl_le0.
    - move=> memL memR xL xR y.
      rewrite /game_initial_pre=> /eqP Hpre Hy.
      inversion Hpre; subst.
      have Hy' :
          y \in dinsupp
            (Pr_code (ind_cpad_challenge_init_code tt) empty_heap).
        exact: Hy.
      case: y Hy Hy'=> [init mem] Hy Hy'.
      exact: (ind_cpad_challenge_init_code_empty_valid (init, mem) Hy').
  Qed.

  Lemma ind_cpad_factored_compiled_guess_decrypt_replacement_ready_vector_bound
      (A : nom_package) max_queries :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    ⊨AE ⦃ game_initial_pre ⦄
      (ind_cpad_factored_compiled_real_guess_game_code A max_queries)
      ≈( compile_security_error max_queries )
      (ind_cpad_factored_compiled_sim_decrypt_guess_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> A_valid Hprefix_vector.
    have -> : compile_security_error max_queries =
        0 + compile_security_error max_queries by lra.
    exact: (additiveErrorSeqRule
      ind_cpad_challenge_init_code
      ind_cpad_challenge_init_code
      (ind_cpad_compiled_real_guess_code A max_queries)
      (ind_cpad_compiled_sim_decrypt_guess_code A max_queries)
      game_initial_pre
      (same_input_invariant_pre challenge_heap_valid)
      same_game_output_opt
      0 (compile_security_error max_queries)
      ind_cpad_challenge_init_code_ae
      (ind_cpad_compiled_guess_decrypt_replacement_from_compile_ready_vector_bound
        A max_queries A_valid Hprefix_vector)).
  Qed.

  Lemma ind_cpad_compiled_open_decrypt_replacement_from_guess_factoring_ready_vector_bound
      (A : nom_package) max_queries :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    ⊨AE ⦃ game_initial_pre ⦄
      (ind_cpad_compiled_real_game_code A max_queries)
      ≈( compile_security_error max_queries )
      (ind_cpad_compiled_sim_decrypt_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> A_valid Hprefix_vector.
    have Hfactored :=
      ind_cpad_factored_compiled_guess_decrypt_replacement_ready_vector_bound
        A max_queries A_valid Hprefix_vector.
    split; first exact: Hfactored.1.
    move=> memL memR xL xR Hpre.
    have [d [Hd Hpost]] := Hfactored.2 memL memR xL xR Hpre.
    exists d.
    split; last exact: Hpost.
    move: Hd.
    rewrite -(ind_cpad_compiled_real_factored_open_game_code_guess
      A max_queries xL A_valid).
    rewrite -(ind_cpad_compiled_sim_decrypt_factored_open_game_code_guess
      A max_queries xR memR A_valid).
    rewrite -(ind_cpad_compiled_real_game_code_factored
      A max_queries xL).
    rewrite -(ind_cpad_compiled_sim_decrypt_game_code_factored
      A max_queries xR).
    by [].
  Qed.

  Lemma ind_cpad_game_to_compiled_sim_decrypt_additive_error_ready_vector_bound
      (A : nom_package) max_queries :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    ⊨AE ⦃ game_initial_pre ⦄
      (ind_cpad_game_code A max_queries)
      ≈( compile_security_error max_queries )
      (ind_cpad_compiled_sim_decrypt_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> A_valid Hprefix_vector.
    have Hcompiled :=
      ind_cpad_compiled_open_decrypt_replacement_from_guess_factoring_ready_vector_bound
        A max_queries A_valid Hprefix_vector.
    split; first exact: Hcompiled.1.
    move=> memL memR xL xR Hpre.
    have [d [Hd Hpost]] := Hcompiled.2 memL memR xL xR Hpre.
    exists d.
    split; last exact: Hpost.
    move: Hd.
    rewrite (ind_cpad_compiled_real_linked_correct A max_queries A_valid xL).
    rewrite ind_cpad_game_code_linked.
    by [].
  Qed.

  Lemma ind_cpad_compiled_sim_decrypt_self_link_to_sim_decrypt_ae
      (A : nom_package) max_queries :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    ⊨AE ⦃ game_initial_pre ⦄
      (ind_cpad_compiled_sim_decrypt_self_link_game_code A max_queries)
      ≈( 0 )
      (ind_cpad_sim_decrypt_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> A_valid.
    apply: (additiveErrorConseqRule
      (ind_cpad_compiled_sim_decrypt_self_link_game_code A max_queries)
      (ind_cpad_sim_decrypt_game_code A max_queries)
      game_initial_pre game_initial_pre
      same_output_heap_opt same_game_output_opt
      0 0).
    - by [].
    - move=> outs.
      exact: same_output_heap_game_output_opt.
    - by [].
    apply: additiveErrorSameOutputTvdEqRule.
    - exact: lexx.
    - move=> memL memR xL xR Hpre.
      rewrite /game_initial_pre in Hpre.
      move/eqP: Hpre=> Hpre.
      inversion Hpre; subst.
      rewrite (ind_cpad_compiled_sim_decrypt_self_link_correct
        A max_queries A_valid tt).
      rewrite ind_cpad_sim_decrypt_game_code_linked.
      exact: total_variation_refl_le0.
  Qed.

  Lemma game_initial_pre_same_input memL memR xL xR :
    game_initial_pre ((xL, memL), (xR, memR)) ->
    xL = xR /\ memL = memR.
  Proof.
    rewrite /game_initial_pre=> /eqP Hpre.
    by inversion Hpre.
  Qed.

  Lemma additiveErrorSameGameOutputTriangleRule
      (progL progM progR : chUnit -> raw_code bool)
      (ε ε' : R) :
    ⊨AE ⦃ game_initial_pre ⦄
      progL ≈( ε ) progM
    ⦃ same_game_output_opt ⦄ ->
    ⊨AE ⦃ game_initial_pre ⦄
      progM ≈( ε' ) progR
    ⦃ same_game_output_opt ⦄ ->
    ⊨AE ⦃ game_initial_pre ⦄
      progL ≈( ε + ε' ) progR
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> HLM HMR.
    apply: (additiveErrorConseqRule
      progL progR
      game_initial_pre game_initial_pre
      same_output_heap_opt same_game_output_opt
      (ε + ε') (ε + ε')).
    - by [].
    - move=> outs.
      exact: same_output_heap_game_output_opt.
    - exact: lexx.
    apply: (additiveErrorSameOutputTriangleRule
      progL progM progR game_initial_pre ε ε'
      game_initial_pre_same_input).
    - apply: (additiveErrorConseqRule
        progL progM
        game_initial_pre game_initial_pre
        same_game_output_opt same_output_heap_opt
        ε ε).
      + by [].
      + move=> outs.
        exact: same_game_output_same_output_heap_opt.
      + exact: lexx.
      + exact: HLM.
    - apply: (additiveErrorConseqRule
        progM progR
        game_initial_pre game_initial_pre
        same_game_output_opt same_output_heap_opt
        ε' ε').
      + by [].
      + move=> outs.
        exact: same_game_output_same_output_heap_opt.
      + exact: lexx.
      + exact: HMR.
  Qed.

  Lemma additiveErrorSameGameResultTvdEqRule
      (progL progR : chUnit -> raw_code bool)
      (ε : R) :
    0 <= ε ->
    (forall memL memR xL xR,
      game_initial_pre ((xL, memL), (xR, memR)) ->
      total_variation
        (complete (dmargin fst (Pr_code (progL xL) memL)))
        (complete (dmargin fst (Pr_code (progR xR) memR))) <= ε) ->
    ⊨AE ⦃ game_initial_pre ⦄
      progL ≈( ε ) progR
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> Heps Htv.
    split; first exact: Heps.
    move=> memL memR xL xR Hpre.
    set outL := Pr_code (progL xL) memL.
    set outR := Pr_code (progR xR) memR.
    pose strip (out : option (bool * heap)) : option bool := omap fst out.
    have Htv_projected :
        total_variation
          (dmargin strip (complete outL))
          (dmargin strip (complete outR)) <= ε.
      rewrite (total_variation_ext
        (dmargin strip (complete outL))
        (complete (dmargin fst outL))
        (dmargin strip (complete outR))
        (complete (dmargin fst outR))).
      exact: (Htv memL memR xL xR Hpre).
      + move=> z.
        rewrite /strip.
        change (dmargin (omap fst) (complete outL) z =
          complete (dmargin fst outL) z).
        exact: dmargin_omap_complete.
      + move=> z.
        rewrite /strip.
        change (dmargin (omap fst) (complete outR) z =
          complete (dmargin fst outR) z).
        exact: dmargin_omap_complete.
    have [d [HdL [HdR Hprob]]] :=
      projected_total_variation_coupling strip
        (complete outL) (complete outR) ε
        (complete_dweight outL) (complete_dweight outR)
        Htv_projected.
    exists d.
    split.
    - apply: coupling_of_margins; split.
      + exact: HdL.
      + exact: HdR.
    - apply: (le_trans Hprob).
      apply: subset_pr=> xy Hxy.
      case: xy Hxy=> outL' outR'.
      by rewrite /same_game_result_opt /strip.
  Qed.

  Lemma additiveErrorSameGameResultAlphaRule
      (progL progR : chUnit -> raw_code bool) :
    (forall x, progL x ≡ progR x) ->
    ⊨AE ⦃ game_initial_pre ⦄
      progL
      ≈( 0 )
      progR
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> Halpha.
    apply: additiveErrorSameGameResultTvdEqRule.
    - exact: lexx.
    - move=> memL memR xL xR Hpre.
      rewrite /game_initial_pre in Hpre.
      move/eqP: Hpre=> Hpre.
      inversion Hpre; subst.
      have [π Hπ] := Halpha tt.
      apply: total_variation_eq_le0.
      apply: complete_ext=> out.
      rewrite -Hπ.
      symmetry.
      exact: (@dmargin_fst_Pr_code_rename_empty bool π (progL tt) out).
  Qed.

  Lemma ind_cpa_reduction_unfresh_linked_to_linked_ae
      (A : nom_package) max_queries :
    ⊨AE ⦃ game_initial_pre ⦄
      (ind_cpa_reduction_unfresh_linked_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_linked_game_code A max_queries)
    ⦃ same_game_result_opt ⦄.
  Proof.
    apply: additiveErrorSameGameResultAlphaRule.
    exact: ind_cpa_reduction_unfresh_linked_game_code_alpha.
  Qed.

  Lemma additiveErrorSameGameResultTvBound
    {inL_t inR_t : choice_type}
    (progL : inL_t -> raw_code bool)
    (progR : inR_t -> raw_code bool)
    (pre : pred ((inL_t * heap) * (inR_t * heap)))
    (ε : R) memL memR xL xR :
    ⊨AE ⦃ pre ⦄ progL ≈( ε ) progR ⦃ same_game_result_opt ⦄ ->
    pre ((xL, memL), (xR, memR)) ->
    total_variation (complete (dmargin fst (Pr_code (progL xL) memL)))
                    (complete (dmargin fst (Pr_code (progR xR) memR))) <= ε.
  Proof.
    move=> [_ Hae] Hpre.
    move: (Hae memL memR xL xR Hpre) => [d [Hd Hpost]].
    set outL := Pr_code (progL xL) memL.
    set outR := Pr_code (progR xR) memR.
    pose strip (out : option (bool * heap)) : option bool := omap fst out.
    pose project (xy : option (bool * heap) * option (bool * heap)) :=
      (strip xy.1, strip xy.2).
    pose d' := dmargin project d.
    have [HdL HdR] := coupling_margins Hd.
    have Hd'L :
        dmargin fst d' =1 complete (dmargin fst outL).
      move=> z.
      rewrite /d'.
      rewrite (dmargin_comp fst project d z).
      rewrite -(dmargin_comp strip fst d z).
      rewrite (dmargin_ext strip _ _ HdL z).
      rewrite /strip.
      exact: dmargin_omap_complete.
    have Hd'R :
        dmargin snd d' =1 complete (dmargin fst outR).
      move=> z.
      rewrite /d'.
      rewrite (dmargin_comp snd project d z).
      rewrite -(dmargin_comp strip snd d z).
      rewrite (dmargin_ext strip _ _ HdR z).
      rewrite /strip.
      exact: dmargin_omap_complete.
    have Hpost' :
        \P_[d'] (fun xy => eq_op xy.1 xy.2) >= 1 - ε.
      apply: (le_trans Hpost).
      rewrite /d' pr_dmargin.
      apply: subset_pr => xy Hxy.
      case: xy Hxy=> outL' outR' /= Hxy.
      move: Hxy.
      rewrite inE /same_game_result_opt /=.
      by [].
    apply: (exact_coupling_eq_pr_total_variation
      d' (complete (dmargin fst outL)) (complete (dmargin fst outR)) ε).
    - exact: complete_dweight.
    - exact: complete_dweight.
    - exact: Hd'L.
    - exact: Hd'R.
    - exact: Hpost'.
  Qed.

  Lemma additiveErrorSameGameResultTriangleRule
      (progL progM progR : chUnit -> raw_code bool)
      (ε ε' : R) :
    ⊨AE ⦃ game_initial_pre ⦄
      progL ≈( ε ) progM
    ⦃ same_game_result_opt ⦄ ->
    ⊨AE ⦃ game_initial_pre ⦄
      progM ≈( ε' ) progR
    ⦃ same_game_result_opt ⦄ ->
    ⊨AE ⦃ game_initial_pre ⦄
      progL ≈( ε + ε' ) progR
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> HLM HMR.
    apply: additiveErrorSameGameResultTvdEqRule.
    - have Heps := additiveErrorEpsNonneg _ _ _ _ _ HLM.
      have Heps' := additiveErrorEpsNonneg _ _ _ _ _ HMR.
      lra.
    - move=> memL memR xL xR Hpre.
      have [Hx Hmem] := game_initial_pre_same_input
        memL memR xL xR Hpre.
      subst xR; subst memR.
      have HtvLM :=
        additiveErrorSameGameResultTvBound
          progL progM game_initial_pre ε memL memL xL xL HLM Hpre.
      have HtvMR :=
        additiveErrorSameGameResultTvBound
          progM progR game_initial_pre ε' memL memL xL xL HMR Hpre.
      have Htri := total_variation_triangle
        (complete (dmargin fst (Pr_code (progL xL) memL)))
        (complete (dmargin fst (Pr_code (progM xL) memL)))
        (complete (dmargin fst (Pr_code (progR xL) memL))).
      apply: (le_trans Htri).
      lra.
  Qed.

  Lemma additiveErrorSameGameOutputToResult
      (progL progR : chUnit -> raw_code bool) ε :
    ⊨AE ⦃ game_initial_pre ⦄
      progL ≈( ε ) progR
    ⦃ same_game_output_opt ⦄ ->
    ⊨AE ⦃ game_initial_pre ⦄
      progL ≈( ε ) progR
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> Hae.
    apply: (additiveErrorConseqRule
      progL progR game_initial_pre game_initial_pre
      same_game_output_opt same_game_result_opt ε ε).
    - by [].
    - exact: same_game_output_result_opt.
    - exact: lexx.
    - exact: Hae.
  Qed.

  Lemma ind_cpa_reduction_direct_factored_to_unfresh_factored_outer_linked_ae
      (A : nom_package) max_queries :
    ⊨AE ⦃ game_initial_pre ⦄
      (ind_cpa_reduction_direct_factored_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_unfresh_factored_outer_linked_game_code A max_queries)
    ⦃ same_game_result_opt ⦄.
  Proof.
    apply: additiveErrorSameGameResultTvdEqRule.
    - exact: lexx.
    - move=> memL memR xL xR Hpre.
      rewrite /game_initial_pre in Hpre.
      move/eqP: Hpre=> Hpre.
      inversion Hpre; subst.
      apply: total_variation_eq_le0.
      apply: complete_distr_ext.
      apply: dmargin_ext.
      exact: ind_cpa_reduction_direct_factored_to_unfresh_factored_outer_linked_Pr_codeE.
  Qed.

  Lemma ind_cpad_compiled_sim_decrypt_mixed_to_self_link_ae
      (A : nom_package) max_queries :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    (* The compiled calls already use [IndCpadSimDecryptOracle].  The only
       difference between the two programs is the package used for residual
       uncompiled decrypt calls.  The intended proof is that, once the first
       [max_queries] selected decrypt calls have been compiled, any later
       decrypt call assert-fails on both the real and simulator packages
       because they share the same decrypt counter. *)
    ⊨AE ⦃ game_initial_pre ⦄
      (ind_cpad_compiled_sim_decrypt_game_code A max_queries)
      ≈( 0 )
      (ind_cpad_compiled_sim_decrypt_self_link_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> A_valid.
    apply: (additiveErrorConseqRule
      (ind_cpad_compiled_sim_decrypt_game_code A max_queries)
      (ind_cpad_compiled_sim_decrypt_self_link_game_code A max_queries)
      game_initial_pre game_initial_pre
      same_output_heap_opt same_game_output_opt
      0 0).
    - by [].
    - move=> outs.
      exact: same_output_heap_game_output_opt.
    - exact: lexx.
    apply: additiveErrorSameOutputTvdEqRule.
    - exact: lexx.
    - move=> memL memR xL xR Hpre.
      rewrite /game_initial_pre in Hpre.
      move/eqP: Hpre=> Hpre.
      inversion Hpre; subst.
      apply: total_variation_eq_le0=> z.
      apply: complete_distr_ext=> out.
      rewrite (ind_cpad_compiled_sim_decrypt_game_code_factored
        A max_queries tt).
      rewrite (ind_cpad_compiled_sim_decrypt_factored_open_game_code_guess
        A max_queries tt empty_heap A_valid).
      rewrite (ind_cpad_compiled_sim_decrypt_self_link_game_code_guess
        A max_queries tt empty_heap A_valid).
      rewrite /ind_cpad_factored_compiled_sim_decrypt_guess_game_code
        /ind_cpad_factored_compiled_sim_decrypt_self_link_guess_game_code.
      rewrite !Pr_code_bind.
      apply: eq_in_dlet.
      + move=> init_mem Hinit out'.
        case: init_mem Hinit=> init mem_init Hinit.
        rewrite /ind_cpad_compiled_sim_decrypt_guess_code
          /ind_cpad_compiled_sim_decrypt_self_link_guess_code.
        have Hbudget :
            (max_queries <=
              get_heap mem_init IndCpadGame.decrypt_count_addr +
                max_queries)%N.
          by rewrite addnC leq_addr.
        exact: (code_link_compile_calls_from_trace_real_sim_decrypt_budget_eq
          max_queries bool (loc (ind_cpad_moved_adversary A))
          (ind_cpad_open_guess_code A init)
          (ind_cpad_open_guess_code A init) [::] max_queries mem_init
          (ind_cpad_open_guess_code_valid A A_valid init)
          (ind_cpad_moved_adversary_separate A)
          (continue_from_trace_nil (ind_cpad_open_guess_code A init))
          Hbudget out').
      + by [].
  Qed.

  Lemma ind_cpad_sim_decrypt_to_ind_cpa_reduction_linked_ae
      (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    ⊨AE ⦃ game_initial_pre ⦄
      (ind_cpad_sim_decrypt_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_linked_game_code A max_queries)
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> A_valid.
    have Hdirect :=
      ind_cpad_sim_decrypt_to_direct_reduction_no_sep_ae
        A max_queries A_valid.
    have Hdirect_unfresh_factored :=
      ind_cpa_reduction_direct_factored_to_unfresh_factored_outer_linked_ae
        A max_queries.
    have Hunfresh_factored :=
      additiveErrorSameGameOutputToResult
        (ind_cpa_reduction_unfresh_factored_outer_linked_game_code
          A max_queries)
        (ind_cpa_reduction_unfresh_linked_game_code A max_queries)
        0
        (ind_cpa_reduction_unfresh_factored_outer_to_linked_ae
          A max_queries).
    have Hunfresh_linked :=
      ind_cpa_reduction_unfresh_linked_to_linked_ae A max_queries.
    have H1 :=
      additiveErrorSameGameResultTriangleRule
        (ind_cpad_sim_decrypt_game_code A max_queries)
        (ind_cpa_reduction_direct_factored_game_code A max_queries)
        (ind_cpa_reduction_unfresh_factored_outer_linked_game_code
          A max_queries)
        0 0 Hdirect Hdirect_unfresh_factored.
    have H2 :=
      additiveErrorSameGameResultTriangleRule
        (ind_cpad_sim_decrypt_game_code A max_queries)
        (ind_cpa_reduction_unfresh_factored_outer_linked_game_code
          A max_queries)
        (ind_cpa_reduction_unfresh_linked_game_code A max_queries)
        (0 + 0) 0 H1 Hunfresh_factored.
    have H3 :=
      additiveErrorSameGameResultTriangleRule
        (ind_cpad_sim_decrypt_game_code A max_queries)
        (ind_cpa_reduction_unfresh_linked_game_code A max_queries)
        (ind_cpa_reduction_linked_game_code A max_queries)
        ((0 + 0) + 0) 0 H2 Hunfresh_linked.
    apply: (additiveErrorConseqRule
      (ind_cpad_sim_decrypt_game_code A max_queries)
      (ind_cpa_reduction_linked_game_code A max_queries)
      game_initial_pre game_initial_pre
      same_game_result_opt same_game_result_opt
      (((0 + 0) + 0) + 0) 0).
    - by [].
    - by [].
    - lra.
    - exact: H3.
  Qed.

  Lemma ind_cpad_sim_decrypt_to_ind_cpa_reduction_ae
      (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    ⊨AE ⦃ game_initial_pre ⦄
      (ind_cpad_sim_decrypt_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_game_code A max_queries)
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> A_valid.
    have Hlinked :=
      ind_cpad_sim_decrypt_to_ind_cpa_reduction_linked_ae
        A max_queries A_valid.
    have Houter :=
      additiveErrorSameGameOutputToResult
        (ind_cpa_reduction_linked_game_code A max_queries)
        (ind_cpa_reduction_game_code A max_queries)
        0
        (ind_cpa_reduction_linked_game_code_ae A max_queries).
    have H :=
      additiveErrorSameGameResultTriangleRule
        (ind_cpad_sim_decrypt_game_code A max_queries)
        (ind_cpa_reduction_linked_game_code A max_queries)
        (ind_cpa_reduction_game_code A max_queries)
        0 0 Hlinked Houter.
    apply: (additiveErrorConseqRule
      (ind_cpad_sim_decrypt_game_code A max_queries)
      (ind_cpa_reduction_game_code A max_queries)
      game_initial_pre game_initial_pre
      same_game_result_opt same_game_result_opt
      (0 + 0) 0).
    - by [].
    - by [].
    - lra.
    - exact: H.
  Qed.

  (* The package-level reduction preserves the IND-CPA adversary interface. *)
  Lemma ind_cpa_reduction_valid (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    Package IndCpaSecurity.IndCpaGame.IndCpaAdv_import
      IndCpaSecurity.IndCpaGame.IndCpaAdv_export
      (ind_cpa_reduction A max_queries).
  Proof.
    move=> A_valid.
    rewrite /reduction_locs /ind_cpa_reduction.
    exact: (IndCpaDSim.IndCpaReduction_valid A max_queries A_valid).
  Qed.

  (* Converts a whole-game AE judgment into the sampled-game advantage bound. *)
  Lemma ind_cpa_reduction_bound_from_additive_error
    (A : nom_package) max_queries ε :
    ⊨AE ⦃ game_initial_pre ⦄
      (ind_cpad_game_code A max_queries)
      ≈( ε )
      (ind_cpa_reduction_game_code A max_queries)
    ⦃ same_game_result_opt ⦄ ->
    2 * ε <= security_loss dim max_queries gaussian_width_multiplier ->
    IndCpadGame.winning_probability max_queries A <=
    IndCpaSecurity.IndCpaGame.winning_probability
      (ind_cpa_reduction A max_queries) +
    security_loss dim max_queries gaussian_width_multiplier.
  Proof.
    move=> Hae Hloss.
    have Hpre : game_initial_pre ((tt, empty_heap), (tt, empty_heap)).
      by rewrite /game_initial_pre.
    have Htv :=
      additiveErrorSameGameResultTvBound
        _ _ _ _ empty_heap empty_heap tt tt Hae Hpre.
    have Hpoint :
      `|IndCpadGame.success_probability max_queries A -
        IndCpaSecurity.IndCpaGame.success_probability
          (ind_cpa_reduction A max_queries)| <= 2 * ε.
      apply: (@le_trans _ _
        (2 * total_variation
          (complete
            (dmargin fst
              (Pr_code (ind_cpad_game_code A max_queries tt) empty_heap)))
          (complete
            (dmargin fst
              (Pr_code
                (ind_cpa_reduction_game_code A max_queries tt) empty_heap))))).
        rewrite /IndCpadGame.success_probability
          /IndCpaSecurity.IndCpaGame.success_probability
          /IndCpadGame.game_out /IndCpaSecurity.IndCpaGame.game_out
          /ind_cpad_game_code /ind_cpa_reduction_game_code /Pr_op.
        exact: total_variation_complete_point_bound2.
      lra.
    rewrite /IndCpadGame.winning_probability
      /IndCpaSecurity.IndCpaGame.winning_probability.
    set pL := IndCpadGame.success_probability max_queries A.
    set pR := IndCpaSecurity.IndCpaGame.success_probability
      (ind_cpa_reduction A max_queries).
    have Htri : `|pL - 1 / 2| <= `|pL - pR| + `|pR - 1 / 2|.
      have H := ler_distD pR pL (1 / 2).
      exact: H.
    apply: (@le_trans _ _ (`|pL - pR| + `|pR - 1 / 2|)).
      exact: Htri.
    lra.
  Qed.

  (* The cryptographic core: compose the compile-rule decrypt replacement
     with the exact endpoint identifications.  The final endpoint uses the
     value-only postcondition because the IND-CPA reduction presentation need
     not share the same internal heap layout. *)
  Lemma ind_cpa_reduction_additive_error_from_compile_ready_vector_bound
    (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    ⊨AE ⦃ game_initial_pre ⦄
      (ind_cpad_game_code A max_queries)
      ≈( compile_security_error max_queries )
      (ind_cpa_reduction_game_code A max_queries)
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> A_valid Hprefix_vector.
    have Hleft :=
      ind_cpad_game_to_compiled_sim_decrypt_additive_error_ready_vector_bound
        A max_queries A_valid Hprefix_vector.
    have Hmixed :=
      ind_cpad_compiled_sim_decrypt_mixed_to_self_link_ae
        A max_queries A_valid.
    have Hself :=
      ind_cpad_compiled_sim_decrypt_self_link_to_sim_decrypt_ae
        A max_queries A_valid.
    have Hred :=
      ind_cpad_sim_decrypt_to_ind_cpa_reduction_ae
        A max_queries A_valid.
    have H1 := additiveErrorSameGameOutputTriangleRule
      (ind_cpad_game_code A max_queries)
      (ind_cpad_compiled_sim_decrypt_game_code A max_queries)
      (ind_cpad_compiled_sim_decrypt_self_link_game_code A max_queries)
      (compile_security_error max_queries) 0 Hleft Hmixed.
    have H2 := additiveErrorSameGameOutputTriangleRule
      (ind_cpad_game_code A max_queries)
      (ind_cpad_compiled_sim_decrypt_self_link_game_code A max_queries)
      (ind_cpad_sim_decrypt_game_code A max_queries)
      (compile_security_error max_queries + 0) 0 H1 Hself.
    have H2_result := additiveErrorSameGameOutputToResult
      (ind_cpad_game_code A max_queries)
      (ind_cpad_sim_decrypt_game_code A max_queries)
      (compile_security_error max_queries + 0 + 0) H2.
    have H3 := additiveErrorSameGameResultTriangleRule
      (ind_cpad_game_code A max_queries)
      (ind_cpad_sim_decrypt_game_code A max_queries)
      (ind_cpa_reduction_game_code A max_queries)
      (compile_security_error max_queries + 0 + 0) 0 H2_result Hred.
    apply: (additiveErrorConseqRule
      (ind_cpad_game_code A max_queries)
      (ind_cpa_reduction_game_code A max_queries)
      game_initial_pre game_initial_pre
      same_game_result_opt same_game_result_opt
      ((compile_security_error max_queries + 0 + 0) + 0)
      (compile_security_error max_queries)).
    - by [].
    - by [].
    - lra.
    - exact: H3.
  Qed.

  Lemma ind_cpa_reduction_additive_error_ready_vector_bound
      (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    ⊨AE ⦃ game_initial_pre ⦄
      (ind_cpad_game_code A max_queries)
      ≈( security_loss dim max_queries gaussian_width_multiplier / 2 )
      (ind_cpa_reduction_game_code A max_queries)
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> A_valid Hprefix_vector.
    rewrite security_loss_halfE.
    exact: (ind_cpa_reduction_additive_error_from_compile_ready_vector_bound
      A max_queries A_valid Hprefix_vector).
  Qed.

  Theorem ind_cpa_reduction_bound_ready_vector_bound
      (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    IndCpadGame.winning_probability max_queries A <=
    IndCpaSecurity.IndCpaGame.winning_probability
      (ind_cpa_reduction A max_queries) +
    security_loss dim max_queries gaussian_width_multiplier.
  Proof.
    move=> A_valid Hprefix_vector.
    have Hae := ind_cpa_reduction_additive_error_ready_vector_bound
      A max_queries A_valid Hprefix_vector.
    apply: (ind_cpa_reduction_bound_from_additive_error
      A max_queries _ Hae).
    lra.
  Qed.

  Theorem is_secure_ready_vector_bound (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    IndCpadGame.winning_probability max_queries A <=
    security_bound A max_queries.
  Proof.
    move=> A_valid Hprefix_vector.
    rewrite /security_bound.
    exact: (ind_cpa_reduction_bound_ready_vector_bound
      A max_queries A_valid Hprefix_vector).
  Qed.

  (* Main reduction theorem: IND-CPAD advantage is bounded by the advantage of
     the constructed IND-CPA adversary, plus the noise-flooding loss. *)
  Theorem is_secure (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    IndCpadGame.winning_probability max_queries A <=
    security_bound A max_queries.
  Proof.
    move=> A_valid.
    exact: (is_secure_ready_vector_bound
      A max_queries A_valid
      (ind_cpad_decrypt_prefix_code_readies_row_vector_bound
        max_queries)).
  Qed.
End NoiseFloodingSecure.
