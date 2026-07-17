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

From Mending.Security.NoiseFloodingSecurity Require Import Prelude DecryptCompiler.

Module NoiseFloodingSecureGameReduction
  (Import Scheme : ApproxFheScheme)
  (Import Metric : ApproxFheMetric(Scheme))
  (Import Correctness : ApproxCorrectnessPerfect(Scheme)(Metric))
  (Import IndCpaSecurity : IsIndCpa(Scheme))
  (Import Params : NoiseFloodingParams).
  Include DecryptCompiler.NoiseFloodingSecureDecryptCompiler(Scheme)(Metric)(Correctness)(IndCpaSecurity)(Params).

  Definition ind_cpad_open_game_code
      (A : nom_package) (_ : chUnit) : raw_code bool :=
    resolve ((IndCpadGame.IndCpadChallenger ∘ A)%sep)
      (IndCpadGame.main, ('unit, 'bool)) tt.

  Definition ind_cpad_moved_adversary (A : nom_package) : nom_package :=
    move (IndCpadGame.IndCpadChallenger : nom_package) A.

  Definition ind_cpa_reduction_moved_adversary
      (A : nom_package) : nom_package :=
    move (IndCpaDSim.IndCpaSimTop : nom_package) A.

  Definition sim_decrypt_reduction_moved_adversary_perm
      (A : nom_package) : {fperm atom} :=
    (fresh (IndCpaDSim.IndCpaSimTop : nom_package) A *
      (fresh (IndCpadGame.IndCpadChallenger : nom_package) A)^-1)%fperm.

  Lemma ind_cpa_reduction_moved_adversary_rename
      (A : nom_package) :
    ind_cpa_reduction_moved_adversary A =
      sim_decrypt_reduction_moved_adversary_perm A ∙
        ind_cpad_moved_adversary A.
  Proof.
    rewrite /ind_cpa_reduction_moved_adversary
      /sim_decrypt_reduction_moved_adversary_perm
      /ind_cpad_moved_adversary.
    exact: move_rename_between.
  Qed.

  Lemma ind_cpa_reduction_moved_adversary_loc_rename
      (A : nom_package) :
    loc (ind_cpa_reduction_moved_adversary A) =
      sim_decrypt_reduction_moved_adversary_perm A ∙
        loc (ind_cpad_moved_adversary A).
  Proof.
    by rewrite ind_cpa_reduction_moved_adversary_rename.
  Qed.

  Lemma ind_cpa_reduction_moved_resolve_rename
      (A : nom_package) (o : opsig) (x : src o) :
    resolve (ind_cpa_reduction_moved_adversary A) o x =
      sim_decrypt_reduction_moved_adversary_perm A ∙
        resolve (ind_cpad_moved_adversary A) o x.
  Proof.
    rewrite ind_cpa_reduction_moved_adversary_rename.
    symmetry.
    exact: resolve_rename.
  Qed.

  Definition sim_decrypt_reduction_adversary_heap_eq
      (A : nom_package) (memL memR : heap) : Prop :=
    heap_eq_on_renamed
      (sim_decrypt_reduction_moved_adversary_perm A)
      (loc (ind_cpad_moved_adversary A)) memL memR.

  Lemma sim_decrypt_reduction_adversary_heap_eq_get
      (A : nom_package) memL memR (l : Location) :
    sim_decrypt_reduction_adversary_heap_eq A memL memR ->
    fhas (loc (ind_cpad_moved_adversary A)) l ->
    get_heap memL l =
      get_heap memR
        (Nominal.rename
          (sim_decrypt_reduction_moved_adversary_perm A) l : Location).
  Proof.
    exact: heap_eq_on_renamed_get.
  Qed.

  Lemma sim_decrypt_reduction_adversary_heap_eq_set_heap_same
      (A : nom_package) memL memR (l : Location) (v : l) :
    sim_decrypt_reduction_adversary_heap_eq A memL memR ->
    sim_decrypt_reduction_adversary_heap_eq A
      (set_heap memL l v)
      (set_heap memR
        (Nominal.rename
          (sim_decrypt_reduction_moved_adversary_perm A) l : Location) v).
  Proof.
    exact: heap_eq_on_renamed_set_heap_same.
  Qed.

  Definition sim_decrypt_reduction_adv_heap_rel
      (A : nom_package) (memL memR : heap) : Prop :=
    sim_decrypt_reduction_heap_rel memL memR /\
    sim_decrypt_reduction_adversary_heap_eq A memL memR.

  Definition same_input_sim_decrypt_reduction_adv_pre
      (A : nom_package) {T : choice_type}
      (inps : (T * heap) * (T * heap)) : Prop :=
    let '((xL, memL), (xR, memR)) := inps in
    xL = xR /\ sim_decrypt_reduction_adv_heap_rel A memL memR.

  Definition same_result_sim_decrypt_reduction_adv_opt
      (A : nom_package) {out_t : choice_type}
      (outs : option (out_t * heap) * option (out_t * heap)) : Prop :=
    match outs with
    | (Some (outL, memL), Some (outR, memR)) =>
        outL = outR /\ sim_decrypt_reduction_adv_heap_rel A memL memR
    | (None, None) => True
    | _ => False
    end.

  Definition supports_same_result_sim_decrypt_reduction_adv_opt
      (A : nom_package) {out_t : choice_type}
      (d : {distr
        (option (out_t * heap) * option (out_t * heap)) / R}) : Prop :=
    forall outs,
      outs \in dinsupp d ->
      same_result_sim_decrypt_reduction_adv_opt A outs.

  Lemma same_result_sim_decrypt_reduction_adv_opt_project
      A {out_t : choice_type}
      (outs : option (out_t * heap) * option (out_t * heap)) :
    same_result_sim_decrypt_reduction_adv_opt A outs ->
    same_result_sim_decrypt_reduction_opt outs.
  Proof.
    case: outs=> outL outR.
    case: outL=> [[outL memL]|]; case: outR=> [[outR memR]|] //=.
    move=> [-> [Hrel _]].
    by rewrite eqxx Hrel.
  Qed.

  Lemma same_result_sim_decrypt_reduction_adv_result_opt
      A {out_t : choice_type}
      (outs : option (out_t * heap) * option (out_t * heap)) :
    same_result_sim_decrypt_reduction_adv_opt A outs -> same_result_opt outs.
  Proof.
    move=> Houts.
    exact: (same_result_sim_decrypt_reduction_result_opt outs
      (same_result_sim_decrypt_reduction_adv_opt_project A outs Houts)).
  Qed.

  Lemma sim_decrypt_reduction_adv_heap_rel_get
      (A : nom_package) memL memR (l : Location) :
    sim_decrypt_reduction_adv_heap_rel A memL memR ->
    fhas (loc (ind_cpad_moved_adversary A)) l ->
    get_heap memL l =
      get_heap memR
        (Nominal.rename
          (sim_decrypt_reduction_moved_adversary_perm A) l : Location).
  Proof.
    move=> [_ Hadv].
    exact: sim_decrypt_reduction_adversary_heap_eq_get.
  Qed.

  Lemma same_input_sim_decrypt_reduction_adv_pre_get
      (A : nom_package) {T : choice_type}
      (xL xR : T) memL memR (l : Location) :
    same_input_sim_decrypt_reduction_adv_pre A
      ((xL, memL), (xR, memR)) ->
    fhas (loc (ind_cpad_moved_adversary A)) l ->
    get_heap memL l =
      get_heap memR
        (Nominal.rename
          (sim_decrypt_reduction_moved_adversary_perm A) l : Location).
  Proof.
    move=> [_ Hrel].
    exact: sim_decrypt_reduction_adv_heap_rel_get.
  Qed.

  Lemma same_result_sim_decrypt_reduction_adv_opt_some_pre
      (A : nom_package) {T : choice_type}
      (outL outR : T) memL memR :
    same_result_sim_decrypt_reduction_adv_opt A
      (Some (outL, memL), Some (outR, memR)) ->
    same_input_sim_decrypt_reduction_adv_pre A
      ((outL, memL), (outR, memR)).
  Proof. by []. Qed.

  Definition ind_cpad_open_guess_code
      (A : nom_package) (input : (bool * (pk_t * evk_t))%type) :
      raw_code bool :=
    let '(b, (pk, evk)) := input in
    b' ← resolve (ind_cpad_moved_adversary A)
      (mkopsig IndCpadGame.guess (chProd pk_t evk_t) chBool) (pk, evk) ;;
    ret (eq_op b' b).

  Definition ind_cpad_challenge_init_code (_ : chUnit) :
      raw_code (bool * (pk_t * evk_t))%type :=
    b <$ ('bool; dflip (1 / 2)) ;;
    keys <$ (pk_t × evk_t × sk_t; keygen) ;;
    let '(pk, evk, sk) := keys in
    #put IndCpadGame.bit_addr := b ;;
    #put IndCpadGame.pk_addr := Some pk ;;
    #put IndCpadGame.evk_addr := Some evk ;;
    #put IndCpadGame.sk_addr := Some sk ;;
    ret (b, (pk, evk)).

  Definition ind_cpa_reduction_challenge_init_code (_ : chUnit) :
      raw_code (bool * (pk_t * evk_t))%type :=
    b <$ ('bool; dflip (1 / 2)) ;;
    keys <$ (pk_t × evk_t × sk_t; keygen) ;;
    let '(pk, evk, _) := keys in
    #put IndCpaSecurity.IndCpaGame.bit_addr := b ;;
    #put IndCpaSecurity.IndCpaGame.pk_addr := Some pk ;;
    #put IndCpaSecurity.IndCpaGame.evk_addr := Some evk ;;
    #put IndCpaDSim.ready_addr := true ;;
    #put IndCpaDSim.pk_addr := Some pk ;;
    #put IndCpaDSim.evk_addr := Some evk ;;
    ret (b, (pk, evk)).

  Definition ind_cpa_reduction_outer_challenge_init_code (_ : chUnit) :
      raw_code (bool * (pk_t * evk_t))%type :=
    b <$ ('bool; dflip (1 / 2)) ;;
    keys <$ (pk_t × evk_t × sk_t; keygen) ;;
    let '(pk, evk, _) := keys in
    #put IndCpaSecurity.IndCpaGame.bit_addr := b ;;
    #put IndCpaSecurity.IndCpaGame.pk_addr := Some pk ;;
    #put IndCpaSecurity.IndCpaGame.evk_addr := Some evk ;;
    ret (b, (pk, evk)).

  Definition ind_cpad_factored_open_game_code
      (A : nom_package) (_ : chUnit) : raw_code bool :=
    init ← ind_cpad_challenge_init_code tt ;;
    ind_cpad_open_guess_code A init.

  Definition ind_cpad_compiled_real_guess_code
      (A : nom_package) (max_queries : nat)
      (input : (bool * (pk_t * evk_t))%type) : raw_code bool :=
    code_link
      (compile_calls max_queries
        (X := nat) (Y := chOption message)
        (IndCpadGame.IndCpadOracle max_queries)
        IndCpadGame.oracle_decrypt
        (ind_cpad_open_guess_code A input))
      (IndCpadGame.IndCpadOracle max_queries).

  Definition ind_cpad_compiled_sim_decrypt_guess_code
      (A : nom_package) (max_queries : nat)
      (input : (bool * (pk_t * evk_t))%type) : raw_code bool :=
    code_link
      (compile_calls max_queries
        (X := nat) (Y := chOption message)
        (IndCpadSimDecryptOracle max_queries)
        IndCpadGame.oracle_decrypt
        (ind_cpad_open_guess_code A input))
      (IndCpadGame.IndCpadOracle max_queries).

  Definition ind_cpad_compiled_sim_decrypt_self_link_guess_code
      (A : nom_package) (max_queries : nat)
      (input : (bool * (pk_t * evk_t))%type) : raw_code bool :=
    code_link
      (compile_calls max_queries
        (X := nat) (Y := chOption message)
        (IndCpadSimDecryptOracle max_queries)
        IndCpadGame.oracle_decrypt
        (ind_cpad_open_guess_code A input))
      (IndCpadSimDecryptOracle max_queries).

  Definition ind_cpad_factored_compiled_real_guess_game_code
      (A : nom_package) (max_queries : nat) (_ : chUnit) :
      raw_code bool :=
    init ← ind_cpad_challenge_init_code tt ;;
    ind_cpad_compiled_real_guess_code A max_queries init.

  Definition ind_cpad_factored_compiled_sim_decrypt_guess_game_code
      (A : nom_package) (max_queries : nat) (_ : chUnit) :
      raw_code bool :=
    init ← ind_cpad_challenge_init_code tt ;;
    ind_cpad_compiled_sim_decrypt_guess_code A max_queries init.

  Definition ind_cpad_factored_compiled_sim_decrypt_self_link_guess_game_code
      (A : nom_package) (max_queries : nat) (_ : chUnit) :
      raw_code bool :=
    init ← ind_cpad_challenge_init_code tt ;;
    ind_cpad_compiled_sim_decrypt_self_link_guess_code A max_queries init.

  Lemma ind_cpad_challenge_init_code_link_closed P :
    code_link (ind_cpad_challenge_init_code tt) P =
    ind_cpad_challenge_init_code tt.
  Proof.
    rewrite /ind_cpad_challenge_init_code.
    ssprove_match_commut_gen.
    case: keys=> [[pk evk] sk] /=.
    ssprove_match_commut_gen.
  Qed.

  Lemma ind_cpa_reduction_outer_challenge_init_code_link_closed P :
    code_link (ind_cpa_reduction_outer_challenge_init_code tt) P =
    ind_cpa_reduction_outer_challenge_init_code tt.
  Proof.
    rewrite /ind_cpa_reduction_outer_challenge_init_code.
    ssprove_match_commut_gen.
    case: keys=> [[pk evk] sk] /=.
    ssprove_match_commut_gen.
  Qed.

  Lemma ind_cpad_guess_in_adv_export :
    fhas IndCpadGame.IndCpadAdv_export
      (mkopsig IndCpadGame.guess (chProd pk_t evk_t) chBool).
  Proof.
    rewrite /IndCpadGame.IndCpadAdv_export.
    fmap_solve.
  Qed.

  Lemma ind_cpad_open_guess_code_valid (A : nom_package) :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    forall x,
      ValidCode (loc (ind_cpad_moved_adversary A))
        IndCpadGame.IndCpadAdv_import
        (ind_cpad_open_guess_code A x).
  Proof.
    move=> A_valid x.
    case: x=> b [pk evk].
    rewrite /ind_cpad_open_guess_code /= /ind_cpad_moved_adversary.
    exact: (@moved_resolve_ret_valid
      IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export
      (IndCpadGame.IndCpadChallenger : nom_package) A
      bool
      (mkopsig IndCpadGame.guess (chProd pk_t evk_t) chBool)
      (pk, evk)
      (fun b' => eq_op b' b)
      A_valid ind_cpad_guess_in_adv_export).
  Qed.

  Lemma ind_cpad_moved_guess_resolve_valid (A : nom_package) pk evk :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    ValidCode (loc (ind_cpad_moved_adversary A))
      IndCpadGame.IndCpadAdv_import
      (resolve (ind_cpad_moved_adversary A)
        (mkopsig IndCpadGame.guess (chProd pk_t evk_t) chBool)
        (pk, evk)).
  Proof.
    move=> A_valid.
    apply: (@valid_resolve
      (loc (ind_cpad_moved_adversary A))
      IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export
      (ind_cpad_moved_adversary A)
      (mkopsig IndCpadGame.guess (chProd pk_t evk_t) chBool)
      (pk, evk)).
    exact: ind_cpad_guess_in_adv_export.
  Qed.

  Lemma ind_cpad_open_game_code_factored (A : nom_package) :
    forall x,
      ind_cpad_open_game_code A x =
      ind_cpad_factored_open_game_code A x.
  Proof.
    move=> [].
    rewrite /ind_cpad_open_game_code /ind_cpad_factored_open_game_code
      /ind_cpad_challenge_init_code /ind_cpad_open_guess_code
      /ind_cpad_moved_adversary /IndCpadGame.IndCpadChallenger.
    rewrite sep_linkE.
    rewrite resolve_link.
    rewrite resolve_set /= coerce_kleisliE.
    ssprove_match_commut_gen.
    case: a0=> [[pk evk] sk] /=.
    ssprove_match_commut_gen.
  Qed.

  Lemma ind_cpad_challenge_init_code_empty_valid out :
    out \in
      dinsupp (Pr_code (ind_cpad_challenge_init_code tt) empty_heap) ->
    let '(_, mem) := out in challenge_heap_valid mem.
  Proof.
    rewrite /ind_cpad_challenge_init_code.
    rewrite Pr_code_sample.
    move=> Hout.
    have [b Hb Hout_b] := @dinsupp_dlet R _ _ _ _ _ Hout.
    rewrite Pr_code_sample in Hout_b.
    have [keys Hkeys Hout_keys] := @dinsupp_dlet R _ _ _ _ _ Hout_b.
    case: keys Hkeys Hout_keys=> [[pk evk] sk] Hkeys.
    rewrite !Pr_code_put Pr_code_ret.
    move=> Hout_ret.
    have -> : out = ((b, (pk, evk)), challenge_initialized_heap b pk evk sk).
      exact: in_dunit Hout_ret.
    exact: (challenge_heap_valid_initialized b (pk, evk, sk) Hkeys).
  Qed.

  Lemma ind_cpad_challenge_init_code_dweight mem :
    dweight keygen = 1 ->
    dweight (Pr_code (ind_cpad_challenge_init_code tt) mem) = 1.
  Proof.
    move=> Hkeygen.
    rewrite /ind_cpad_challenge_init_code.
    rewrite Pr_code_sample.
    rewrite dweight_dlet.
    transitivity (@psum R _ (fun b : bool => dflip (1 / 2) b * 1)).
    - apply/eq_psum=> b.
      congr (_ * _).
      rewrite Pr_code_sample.
      rewrite dweight_dlet.
      transitivity (@psum R _ (fun keys : pk_t * evk_t * sk_t =>
        keygen keys * 1)).
      + apply/eq_psum=> keys.
        case: keys=> [[pk evk] sk].
        rewrite !Pr_code_put Pr_code_ret.
        by rewrite dunit_dweight mulr1.
      + transitivity (@psum R _ keygen).
          apply/eq_psum=> keys.
          by rewrite mulr1.
        by rewrite -pr_predT Hkeygen.
    - transitivity (@psum R _ (dflip (1 / 2) : {distr bool / R})).
        apply/eq_psum=> b.
        by rewrite mulr1.
      by rewrite -pr_predT dflip_dweight.
  Qed.

  Definition IndCpadMain_export :=
    [interface [IndCpadGame.main] : { 'unit ~> 'bool }].

  Lemma ind_cpad_open_game_code_valid (A : nom_package) :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    forall x,
      ValidCode (loc ((IndCpadGame.IndCpadChallenger ∘ A)%sep))
        IndCpadGame.IndCpadAdv_import
        (ind_cpad_open_game_code A x).
  Proof.
    move=> A_valid x.
    apply: (@valid_resolve
      (loc ((IndCpadGame.IndCpadChallenger ∘ A)%sep))
      IndCpadGame.IndCpadAdv_import IndCpadMain_export
      ((IndCpadGame.IndCpadChallenger ∘ A)%sep)
      (IndCpadGame.main, ('unit, 'bool)) tt).
    rewrite /IndCpadMain_export.
    fmap_solve.
  Qed.

  Lemma ind_cpad_moved_adversary_separate (A : nom_package) :
    fseparate IndCpadGame.oracle_mem_spec
      (loc (ind_cpad_moved_adversary A)).
  Proof.
    rewrite fseparate_disj /ind_cpad_moved_adversary.
    change (disj (IndCpadGame.IndCpadChallenger : nom_package)
      (move (IndCpadGame.IndCpadChallenger : nom_package) A)).
    exact: move_disj.
  Qed.

  Lemma ind_cpad_moved_adversary_separateC (A : nom_package) :
    fseparate (loc (ind_cpad_moved_adversary A))
      IndCpadGame.oracle_mem_spec.
  Proof.
    rewrite fseparate_disj /ind_cpad_moved_adversary.
    change (disj (move (IndCpadGame.IndCpadChallenger : nom_package) A)
      (IndCpadGame.IndCpadChallenger : nom_package)).
    by rewrite disjC; exact: move_disj.
  Qed.

  Lemma ind_cpa_reduction_moved_adversary_sim_separateC
      (A : nom_package) :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaDSim.oracle_mem_spec.
  Proof.
    rewrite fseparate_disj /ind_cpa_reduction_moved_adversary.
    change (disj (move (IndCpaDSim.IndCpaSimTop : nom_package) A)
      (IndCpaDSim.IndCpaSimTop : nom_package)).
    by rewrite disjC; exact: move_disj.
  Qed.

  Lemma ind_cpa_locs_support_lt103 a :
    a \in supp IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    (natize a < 103)%N.
  Proof.
    rewrite /IndCpaSecurity.IndCpaGame.IndCpa_locs /supp /=.
    move=> /imfsetP [n Hn ->].
    move/dommP: Hn=> [s Hs].
    have Hhas : fhas
        [fmap IndCpaSecurity.IndCpaGame.pk_addr;
              IndCpaSecurity.IndCpaGame.evk_addr;
              IndCpaSecurity.IndCpaGame.bit_addr] (n, s).
      exact: Hs.
    rewrite /IndCpaSecurity.IndCpaGame.pk_addr
      /IndCpaSecurity.IndCpaGame.evk_addr
      /IndCpaSecurity.IndCpaGame.bit_addr in Hhas.
    fmap_invert Hhas; rewrite atomizeK; lia.
  Qed.

  Lemma ind_cpa_challenger_offset_ge103 :
    (103 <= offset
      (supp (IndCpaSecurity.IndCpaGame.IndCpaChallenger : nom_package)))%N.
  Proof.
    change (103 <=
      offset (supp IndCpaSecurity.IndCpaGame.IndCpa_locs))%N.
    have Hhas : fhas IndCpaSecurity.IndCpaGame.IndCpa_locs
        IndCpaSecurity.IndCpaGame.bit_addr.
      rewrite /IndCpaSecurity.IndCpaGame.IndCpa_locs.
      fmap_solve.
    have Hsub := supp_Locations Hhas.
    have Hbit :
        atomize IndCpaSecurity.IndCpaGame.bit_addr.1 \in
          supp IndCpaSecurity.IndCpaGame.IndCpa_locs.
      apply: (fsubsetP Hsub).
      by rewrite /supp /= in_fset1.
    have Hlt := ltn_offset Hbit.
    rewrite /IndCpaSecurity.IndCpaGame.bit_addr /= in Hlt.
    lia.
  Qed.

  Lemma ind_cpa_sim_top_offset_gt_ind_cpa_locs :
    (103 <= offset (supp (IndCpaDSim.IndCpaSimTop : nom_package)))%N.
  Proof.
    change (103 <= offset (supp IndCpaDSim.oracle_mem_spec))%N.
    have Hhas : fhas IndCpaDSim.oracle_mem_spec IndCpaDSim.ready_addr.
      rewrite /IndCpaDSim.oracle_mem_spec.
      fmap_solve.
    have Hsub := supp_Locations Hhas.
    have Hready :
        atomize IndCpaDSim.ready_addr.1 \in
          supp IndCpaDSim.oracle_mem_spec.
      apply: (fsubsetP Hsub).
      by rewrite /supp /= in_fset1.
    have Hlt := ltn_offset Hready.
    rewrite /IndCpaDSim.ready_addr /= in Hlt.
    lia.
  Qed.

  Lemma ind_cpa_reduction_moved_adversary_outer_separate
      (A : nom_package) :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs.
  Proof.
    rewrite fseparate_disj /ind_cpa_reduction_moved_adversary /disj.
    apply/fdisjointP=> a Hmoved.
    apply/negP=> Houter.
    rewrite /move /= in Hmoved.
    rewrite -supp_equi in Hmoved.
    rewrite /rename /= in Hmoved.
    move/imfsetP: Hmoved=> [a0 Ha0 Ha].
    have Hoffset := ind_cpa_sim_top_offset_gt_ind_cpa_locs.
    have Houter_lt := ind_cpa_locs_support_lt103 a Houter.
    rewrite Ha /rename /= freshE // atomizeK in Houter_lt.
    lia.
  Qed.

  Lemma ind_cpa_reduction_sim_oracle_outer_separate :
    fseparate IndCpaDSim.oracle_mem_spec
      IndCpaSecurity.IndCpaGame.IndCpa_locs.
  Proof.
    rewrite /IndCpaDSim.oracle_mem_spec
      /IndCpaSecurity.IndCpaGame.IndCpa_locs.
    fmap_solve.
  Qed.

  Lemma ind_cpa_reduction_outer_separate
      (A : nom_package) max_queries :
    fseparate (loc (IndCpaDSim.IndCpaReduction A max_queries))
      IndCpaSecurity.IndCpaGame.IndCpa_locs.
  Proof.
    rewrite /IndCpaDSim.IndCpaReduction.
    rewrite sep_linkE /=.
    apply: fseparateUl.
    - apply: fseparateUl.
      + exact: ind_cpa_reduction_sim_oracle_outer_separate.
      + exact: ind_cpa_reduction_moved_adversary_outer_separate.
    - exact: ind_cpa_reduction_sim_oracle_outer_separate.
  Qed.

  Lemma fresh_fix_below_left_offset
      {X Y : nomType} (x : X) (y : Y) a :
    (natize a < offset (supp x))%N ->
    a \notin supp y ->
    fresh x y ∙ a = a.
  Proof.
    move=> Ha_lt Ha_y.
    rewrite /rename /=.
    apply/ffun.suppPn.
    apply/negP=> Ha_supp.
    rewrite /fresh in Ha_supp.
    have Hsub := supp_fperm
      (fun a0 : atom => atomize (offset (supp x) + natize a0))
      (supp y).
    have Ha_union := fsubsetP Hsub a Ha_supp.
    move/fsetUP: Ha_union=> [Hy|Him].
    - by rewrite Hy in Ha_y.
    - move/imfsetP: Him=> [b Hb Hba].
      exfalso.
      move: Ha_lt.
      rewrite Hba atomizeK.
      lia.
  Qed.

  Lemma ind_cpa_reduction_sep_fresh_fixes_ind_cpa_locs_atom
      (A : nom_package) max_queries a :
    a \in supp IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    fresh (IndCpaSecurity.IndCpaGame.IndCpaChallenger : nom_package)
      (IndCpaDSim.IndCpaReduction A max_queries) ∙ a = a.
  Proof.
    move=> Ha.
    apply: fresh_fix_below_left_offset.
    - have Ha_lt := ind_cpa_locs_support_lt103 a Ha.
      have Hoffset := ind_cpa_challenger_offset_ge103.
      lia.
    - apply/negP=> Hred.
      have Hsep := ind_cpa_reduction_outer_separate A max_queries.
      rewrite fseparate_disj in Hsep.
      move/fdisjointP: Hsep=> Hsep.
      move: (Hsep a Hred).
      by rewrite Ha.
  Qed.

  Lemma ind_cpa_reduction_sep_fresh_fixes_ind_cpa_challenger
      (A : nom_package) max_queries :
    fresh (IndCpaSecurity.IndCpaGame.IndCpaChallenger : nom_package)
      (IndCpaDSim.IndCpaReduction A max_queries) ∙
        (IndCpaSecurity.IndCpaGame.IndCpaChallenger : nom_package) =
    IndCpaSecurity.IndCpaGame.IndCpaChallenger.
  Proof.
    rewrite -[RHS]rename_id.
    apply: eq_in_supp=> a Ha.
    change (is_true
      (a \in supp IndCpaSecurity.IndCpaGame.IndCpa_locs)) in Ha.
    exact: (ind_cpa_reduction_sep_fresh_fixes_ind_cpa_locs_atom
      A max_queries a Ha).
  Qed.

  Lemma ind_cpa_reduction_sep_fresh_fixes_ind_cpa_oracle
      (A : nom_package) max_queries :
    fresh (IndCpaSecurity.IndCpaGame.IndCpaChallenger : nom_package)
      (IndCpaDSim.IndCpaReduction A max_queries) ∙
        (IndCpaSecurity.IndCpaGame.IndCpaOracle : raw_package) =
    (IndCpaSecurity.IndCpaGame.IndCpaOracle : raw_package).
  Proof.
    have Hvalid :
        ValidPackage IndCpaSecurity.IndCpaGame.IndCpa_locs
          [interface] IndCpaSecurity.IndCpaGame.IndCpaAdv_import
          IndCpaSecurity.IndCpaGame.IndCpaOracle.
      typeclasses eauto with ssprove_valid_db.
    have Hsupport :=
      @valid_support_package IndCpaSecurity.IndCpaGame.IndCpa_locs
        [interface] IndCpaSecurity.IndCpaGame.IndCpaAdv_import
        IndCpaSecurity.IndCpaGame.IndCpaOracle Hvalid.
    apply: Hsupport.
    move=> a Ha.
    exact: ind_cpa_reduction_sep_fresh_fixes_ind_cpa_locs_atom.
  Qed.

  Lemma sim_decrypt_reduction_adversary_heap_eq_oracle_outputs
      (A : nom_package) max_queries (o : opsig) (x : src o)
      memL memR (outL outR : tgt o * heap) :
    fhas IndCpadGame.IndCpadAdv_import o ->
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    sim_decrypt_reduction_adversary_heap_eq A memL memR ->
    outL \in dinsupp
      (Pr_code (resolve (IndCpadSimDecryptOracle max_queries) o x) memL) ->
    outR \in dinsupp
      (Pr_code
        (code_link
          (resolve (IndCpaDSim.IndCpadOracle max_queries) o x)
          IndCpaSecurity.IndCpaGame.IndCpaOracle)
        memR) ->
    sim_decrypt_reduction_adversary_heap_eq A outL.2 outR.2.
  Proof.
    move=> Ho Houter Hadv HoutL HoutR.
    have HL := ind_cpad_sim_decrypt_resolve_preserves_heap_eq_on
      max_queries (loc (ind_cpad_moved_adversary A)) o x memL outL
      (ind_cpad_moved_adversary_separateC A) Ho HoutL.
    have HR := ind_cpa_reduction_sim_outer_resolve_preserves_heap_eq_on
      max_queries (loc (ind_cpa_reduction_moved_adversary A)) o x memR outR
      (ind_cpa_reduction_moved_adversary_sim_separateC A)
      Houter Ho HoutR.
    rewrite /sim_decrypt_reduction_adversary_heap_eq
      /heap_eq_on_renamed in Hadv *.
    rewrite ind_cpa_reduction_moved_adversary_loc_rename in HR.
    have HLren := @heap_eq_on_rename
      (sim_decrypt_reduction_moved_adversary_perm A)
      (loc (ind_cpad_moved_adversary A)) memL outL.2 HL.
    pose K :=
      sim_decrypt_reduction_moved_adversary_perm A ∙
        loc (ind_cpad_moved_adversary A).
    have Hren_sym := @heap_eq_on_sym K
      (sim_decrypt_reduction_moved_adversary_perm A ∙ memL)
      (sim_decrypt_reduction_moved_adversary_perm A ∙ outL.2) HLren.
    have HleftR := @heap_eq_on_trans K
      (sim_decrypt_reduction_moved_adversary_perm A ∙ outL.2)
      (sim_decrypt_reduction_moved_adversary_perm A ∙ memL)
      memR Hren_sym Hadv.
    exact: (@heap_eq_on_trans K
      (sim_decrypt_reduction_moved_adversary_perm A ∙ outL.2)
      memR outR.2 HleftR HR).
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_set_adversary
      (A : nom_package) memL memR (l : Location) (v : l) :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    fhas (loc (ind_cpad_moved_adversary A)) l ->
    sim_decrypt_reduction_heap_rel memL memR ->
    sim_decrypt_reduction_heap_rel
      (set_heap memL l v)
      (set_heap memR
        (Nominal.rename
          (sim_decrypt_reduction_moved_adversary_perm A) l : Location) v).
  Proof.
    move=> Houter Hl Hrel.
    pose π := sim_decrypt_reduction_moved_adversary_perm A.
    pose lR := (Nominal.rename π l : Location).
    have HlR : fhas (loc (ind_cpa_reduction_moved_adversary A)) lR.
      rewrite /lR ind_cpa_reduction_moved_adversary_loc_rename.
      exact: fhas_rename.
    have Hleft_neq k :
        fhas IndCpadGame.oracle_mem_spec k -> k.1 != l.1.
      move=> Hk.
      have Hnotin := notin_has_separate IndCpadGame.oracle_mem_spec
        (loc (ind_cpad_moved_adversary A)) k Hk
        (ind_cpad_moved_adversary_separate A).
      have Hin := fhas_in (loc (ind_cpad_moved_adversary A)) l Hl.
      apply/negP=> /eqP Hkl.
      by rewrite Hkl Hin in Hnotin.
    have Hright_sim_neq k :
        fhas IndCpaDSim.oracle_mem_spec k -> k.1 != lR.1.
      move=> Hk.
      have Hnotin := notin_has_separate
        (loc (ind_cpa_reduction_moved_adversary A))
        IndCpaDSim.oracle_mem_spec lR HlR
        (ind_cpa_reduction_moved_adversary_sim_separateC A).
      have Hin := fhas_in IndCpaDSim.oracle_mem_spec k Hk.
      apply/negP=> /eqP Hkl.
      by rewrite -Hkl Hin in Hnotin.
    have Hright_outer_neq k :
        fhas IndCpaSecurity.IndCpaGame.IndCpa_locs k -> k.1 != lR.1.
      move=> Hk.
      have Hnotin := notin_has_separate
        (loc (ind_cpa_reduction_moved_adversary A))
        IndCpaSecurity.IndCpaGame.IndCpa_locs lR HlR Houter.
      have Hin := fhas_in IndCpaSecurity.IndCpaGame.IndCpa_locs k Hk.
      apply/negP=> /eqP Hkl.
      by rewrite -Hkl Hin in Hnotin.
    have Hvalid_eq :
        challenge_heap_valid memL =
        challenge_heap_valid (set_heap memL l v).
      apply: challenge_heap_valid_depends_only_on_oracle_mem_spec.
      exact: (heap_eq_on_set_heap_separate
        IndCpadGame.oracle_mem_spec
        (loc (ind_cpad_moved_adversary A)) memL l v
        (ind_cpad_moved_adversary_separate A) Hl).
    have Hready := sim_decrypt_reduction_heap_rel_ready Hrel.
    have Hbit := sim_decrypt_reduction_heap_rel_bit Hrel.
    have Hpk_outer := sim_decrypt_reduction_heap_rel_pk_outer Hrel.
    have Hevk_outer := sim_decrypt_reduction_heap_rel_evk_outer Hrel.
    have Hpk_sim := sim_decrypt_reduction_heap_rel_pk_sim Hrel.
    have Hevk_sim := sim_decrypt_reduction_heap_rel_evk_sim Hrel.
    have Htable := sim_decrypt_reduction_heap_rel_table Hrel.
    have Hcount := sim_decrypt_reduction_heap_rel_decrypt_count Hrel.
    rewrite /sim_decrypt_reduction_heap_rel -Hvalid_eq
      (sim_decrypt_reduction_heap_rel_challenge_valid Hrel) /=.
    repeat (rewrite get_set_heap_neq;
      [| first [
          apply Hleft_neq; fmap_solve
        | apply Hright_sim_neq; fmap_solve
        | apply Hright_outer_neq; fmap_solve
        ]]).
    by rewrite Hready -Hbit -Hpk_outer -Hevk_outer
      -Hpk_sim -Hevk_sim -Htable -Hcount !eqxx.
  Qed.

  Lemma sim_decrypt_reduction_adv_heap_rel_set_adversary
      (A : nom_package) memL memR (l : Location) (v : l) :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    fhas (loc (ind_cpad_moved_adversary A)) l ->
    sim_decrypt_reduction_adv_heap_rel A memL memR ->
    sim_decrypt_reduction_adv_heap_rel A
      (set_heap memL l v)
      (set_heap memR
        (Nominal.rename
          (sim_decrypt_reduction_moved_adversary_perm A) l : Location) v).
  Proof.
    move=> Houter Hl [Hrel Hadv].
    split.
    - exact: (sim_decrypt_reduction_heap_rel_set_adversary
        A memL memR l v Houter Hl Hrel).
    - exact: (sim_decrypt_reduction_adversary_heap_eq_set_heap_same
        A memL memR l v Hadv).
  Qed.

  Lemma sim_decrypt_reduction_adversary_heap_eq_initialized
      (A : nom_package) b pk evk sk :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    sim_decrypt_reduction_adversary_heap_eq A
      (challenge_initialized_heap b pk evk sk)
      (reduction_initialized_heap b pk evk).
  Proof.
    move=> Houter.
    pose π := sim_decrypt_reduction_moved_adversary_perm A.
    pose K := loc (ind_cpad_moved_adversary A).
    have Hleft :
        fseparate (π ∙ K : Locations)
          (π ∙ IndCpadGame.oracle_mem_spec : Locations).
      exact: (fseparate_rename π K IndCpadGame.oracle_mem_spec
        (ind_cpad_moved_adversary_separateC A)).
    have Hsim :
        fseparate (π ∙ K : Locations) IndCpaDSim.oracle_mem_spec.
      rewrite /π /K -ind_cpa_reduction_moved_adversary_loc_rename.
      exact: ind_cpa_reduction_moved_adversary_sim_separateC.
    have Houter' :
        fseparate (π ∙ K : Locations)
          IndCpaSecurity.IndCpaGame.IndCpa_locs.
      by rewrite /π /K -ind_cpa_reduction_moved_adversary_loc_rename.
    rewrite /sim_decrypt_reduction_adversary_heap_eq
      /challenge_initialized_heap /reduction_initialized_heap.
    apply: (heap_eq_on_renamed_set_heap_right_separate
      (sim_decrypt_reduction_moved_adversary_perm A)
      (loc (ind_cpad_moved_adversary A))
      IndCpaDSim.oracle_mem_spec); [exact: Hsim|fmap_solve|].
    apply: (heap_eq_on_renamed_set_heap_right_separate
      (sim_decrypt_reduction_moved_adversary_perm A)
      (loc (ind_cpad_moved_adversary A))
      IndCpaDSim.oracle_mem_spec); [exact: Hsim|fmap_solve|].
    apply: (heap_eq_on_renamed_set_heap_right_separate
      (sim_decrypt_reduction_moved_adversary_perm A)
      (loc (ind_cpad_moved_adversary A))
      IndCpaDSim.oracle_mem_spec); [exact: Hsim|fmap_solve|].
    apply: (heap_eq_on_renamed_set_heap_right_separate
      (sim_decrypt_reduction_moved_adversary_perm A)
      (loc (ind_cpad_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs);
      [exact: Houter'|fmap_solve|].
    apply: (heap_eq_on_renamed_set_heap_right_separate
      (sim_decrypt_reduction_moved_adversary_perm A)
      (loc (ind_cpad_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs);
      [exact: Houter'|fmap_solve|].
    apply: (heap_eq_on_renamed_set_heap_right_separate
      (sim_decrypt_reduction_moved_adversary_perm A)
      (loc (ind_cpad_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs);
      [exact: Houter'|fmap_solve|].
    apply: (heap_eq_on_renamed_set_heap_left_separate
      (sim_decrypt_reduction_moved_adversary_perm A)
      (loc (ind_cpad_moved_adversary A))
      IndCpadGame.oracle_mem_spec); [exact: Hleft|fmap_solve|].
    apply: (heap_eq_on_renamed_set_heap_left_separate
      (sim_decrypt_reduction_moved_adversary_perm A)
      (loc (ind_cpad_moved_adversary A))
      IndCpadGame.oracle_mem_spec); [exact: Hleft|fmap_solve|].
    apply: (heap_eq_on_renamed_set_heap_left_separate
      (sim_decrypt_reduction_moved_adversary_perm A)
      (loc (ind_cpad_moved_adversary A))
      IndCpadGame.oracle_mem_spec); [exact: Hleft|fmap_solve|].
    apply: (heap_eq_on_renamed_set_heap_left_separate
      (sim_decrypt_reduction_moved_adversary_perm A)
      (loc (ind_cpad_moved_adversary A))
      IndCpadGame.oracle_mem_spec); [exact: Hleft|fmap_solve|].
    rewrite /heap_eq_on_renamed rename_empty_heap.
    exact: heap_eq_on_refl.
  Qed.

  Lemma sim_decrypt_reduction_adv_heap_rel_initialized
      (A : nom_package) b pk evk sk :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    good_keys pk evk sk ->
    sim_decrypt_reduction_adv_heap_rel A
      (challenge_initialized_heap b pk evk sk)
      (reduction_initialized_heap b pk evk).
  Proof.
    move=> Houter Hkeys.
    split.
    - exact: (sim_decrypt_reduction_heap_rel_initialized b pk evk sk Hkeys).
    - exact: (sim_decrypt_reduction_adversary_heap_eq_initialized
        A b pk evk sk Houter).
  Qed.

  Lemma same_result_sim_decrypt_reduction_adv_opt_initialized
      (A : nom_package) b pk evk sk :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    (pk, evk, sk) \in dinsupp keygen ->
    same_result_sim_decrypt_reduction_adv_opt A
      (Some ((b, (pk, evk)), challenge_initialized_heap b pk evk sk),
       Some ((b, (pk, evk)), reduction_initialized_heap b pk evk)).
  Proof.
    move=> Houter Hkeys.
    split; first done.
    exact: (sim_decrypt_reduction_adv_heap_rel_initialized
      A b pk evk sk Houter (keygen_support_good (pk, evk, sk) Hkeys)).
  Qed.

  Definition ind_cpad_reduction_challenge_init_sample :
      {distr (bool * (pk_t * evk_t * sk_t)) / R} :=
    \dlet_(b <- dflip (1 / 2))
      \dlet_(keys <- keygen) dunit (b, keys).

  Definition ind_cpad_reduction_challenge_init_outL
      (sample : bool * (pk_t * evk_t * sk_t)) :
      (bool * (pk_t * evk_t))%type * heap :=
    let '(b, ((pk, evk), sk)) := sample in
    ((b, (pk, evk)), challenge_initialized_heap b pk evk sk).

  Definition ind_cpad_reduction_challenge_init_outR
      (sample : bool * (pk_t * evk_t * sk_t)) :
      (bool * (pk_t * evk_t))%type * heap :=
    let '(b, ((pk, evk), _)) := sample in
    ((b, (pk, evk)), reduction_initialized_heap b pk evk).

  Definition ind_cpad_reduction_challenge_init_coupling :
      {distr
        (option (((bool * (pk_t * evk_t))%type * heap)) *
         option (((bool * (pk_t * evk_t))%type * heap))) / R} :=
    shared_complete_sample_coupling
      ind_cpad_reduction_challenge_init_sample
      ind_cpad_reduction_challenge_init_outL
      ind_cpad_reduction_challenge_init_outR.

  Lemma ind_cpad_reduction_challenge_init_sample_weight :
    dweight ind_cpad_reduction_challenge_init_sample = 1.
  Proof.
    rewrite /ind_cpad_reduction_challenge_init_sample dweight_dlet.
    transitivity (@psum R _ (fun b : bool => dflip (1 / 2) b * 1)).
    - apply/eq_psum=> b.
      congr (_ * _).
      rewrite dweight_dlet.
      transitivity (@psum R _ (fun keys : pk_t * evk_t * sk_t =>
        keygen keys * 1)).
      + apply/eq_psum=> keys.
        by rewrite dunit_dweight mulr1.
      + transitivity (@psum R _ keygen).
          apply/eq_psum=> keys.
          by rewrite mulr1.
        by rewrite -pr_predT keygen_lossless.
    - transitivity (@psum R _ (dflip (1 / 2) : {distr bool / R})).
        apply/eq_psum=> b.
        by rewrite mulr1.
      by rewrite -pr_predT dflip_dweight.
  Qed.

  Lemma ind_cpad_reduction_challenge_init_sample_keygen b pk evk sk :
    (b, (pk, evk, sk)) \in
      dinsupp ind_cpad_reduction_challenge_init_sample ->
    (pk, evk, sk) \in dinsupp keygen.
  Proof.
    rewrite /ind_cpad_reduction_challenge_init_sample.
    move=> Hsample.
    have [b' Hb' Hafter_b] := @dinsupp_dlet R _ _ _ _ _ Hsample.
    have [keys' Hkeys' Hafter_keys] :=
      @dinsupp_dlet R _ _ _ _ _ Hafter_b.
    have Heq : (b, (pk, evk, sk)) = (b', keys').
      exact: in_dunit Hafter_keys.
    inversion Heq; subst keys'.
    exact: Hkeys'.
  Qed.

  Lemma ind_cpad_reduction_challenge_init_coupling_support_some outs :
    outs \in dinsupp ind_cpad_reduction_challenge_init_coupling ->
    exists b pk evk sk,
      (pk, evk, sk) \in dinsupp keygen /\
      outs =
        (Some
          (((b, (pk, evk)),
            challenge_initialized_heap b pk evk sk)),
         Some
          (((b, (pk, evk)),
            reduction_initialized_heap b pk evk))).
  Proof.
    rewrite /ind_cpad_reduction_challenge_init_coupling
      /shared_complete_sample_coupling.
    move=> Houts.
    have [os Hos Hinner] := @dinsupp_dlet R _ _ _ _ _ Houts.
    case: os Hos Hinner=> [sample|] Hos Hinner.
    - have Houts_eq : outs =
          (Some (ind_cpad_reduction_challenge_init_outL sample),
           Some (ind_cpad_reduction_challenge_init_outR sample)).
        exact: in_dunit Hinner.
      clear Hinner.
      case: sample Hos Houts_eq=> [b [[pk evk] sk]] Hsample Houts_eq.
      exists b, pk, evk, sk.
      split.
      + exact: (ind_cpad_reduction_challenge_init_sample_keygen
          b pk evk sk Hsample).
      + exact: Houts_eq.
    - move: Hos.
      rewrite in_dinsupp completeE /=.
      rewrite ind_cpad_reduction_challenge_init_sample_weight subrr eqxx.
      by [].
  Qed.

  Lemma ind_cpad_reduction_challenge_init_coupling_margins :
    coupling ind_cpad_reduction_challenge_init_coupling
      (complete (Pr_code (ind_cpad_challenge_init_code tt) empty_heap))
      (complete
        (Pr_code (ind_cpa_reduction_challenge_init_code tt) empty_heap)).
  Proof.
    rewrite /ind_cpad_reduction_challenge_init_coupling.
    have [HmarginL HmarginR] :=
      shared_complete_sample_coupling_margins
        ind_cpad_reduction_challenge_init_sample
        ind_cpad_reduction_challenge_init_outL
        ind_cpad_reduction_challenge_init_outR.
    apply: coupling_of_margins; split.
    - move=> z.
      rewrite HmarginL.
      apply: complete_distr_ext=> y.
      rewrite /ind_cpad_reduction_challenge_init_sample
        /ind_cpad_reduction_challenge_init_outL
        /ind_cpad_challenge_init_code.
      rewrite dmarginE Pr_code_sample.
      rewrite __deprecated__dlet_dlet.
      apply: eq_in_dlet=> // b _ y'.
      rewrite Pr_code_sample.
      rewrite __deprecated__dlet_dlet.
      apply: eq_in_dlet=> // keys _ y''.
      case: keys=> [[pk evk] sk].
      by rewrite dlet_unit /challenge_initialized_heap !Pr_code_put Pr_code_ret.
    - move=> z.
      rewrite HmarginR.
      apply: complete_distr_ext=> y.
      rewrite /ind_cpad_reduction_challenge_init_sample
        /ind_cpad_reduction_challenge_init_outR
        /ind_cpa_reduction_challenge_init_code.
      rewrite dmarginE Pr_code_sample.
      rewrite __deprecated__dlet_dlet.
      apply: eq_in_dlet=> // b _ y'.
      rewrite Pr_code_sample.
      rewrite __deprecated__dlet_dlet.
      apply: eq_in_dlet=> // keys _ y''.
      case: keys=> [[pk evk] sk].
      by rewrite dlet_unit /reduction_initialized_heap !Pr_code_put Pr_code_ret.
  Qed.

  Definition sim_decrypt_reduction_adv_continuation_witness
      (A : nom_package) {in_t out_t : choice_type}
      (contL contR : in_t -> raw_code out_t) : Prop :=
    forall memL memR xL xR,
      exists d,
        coupling d
          (complete (Pr_code (contL xL) memL))
          (complete (Pr_code (contR xR) memR)) /\
        (same_input_sim_decrypt_reduction_adv_pre A
            ((xL, memL), (xR, memR)) ->
         supports_same_result_sim_decrypt_reduction_adv_opt A d).

  Lemma sim_decrypt_reduction_adv_continuation_witness_eq
      (A : nom_package) {in_t out_t : choice_type}
      (contL contL' contR contR' : in_t -> raw_code out_t) :
    (forall x, contL x = contL' x) ->
    (forall x, contR x = contR' x) ->
    sim_decrypt_reduction_adv_continuation_witness A contL contR ->
    sim_decrypt_reduction_adv_continuation_witness A contL' contR'.
  Proof.
    move=> HL HR Hcont memL memR xL xR.
    rewrite -(HL xL) -(HR xR).
    exact: (Hcont memL memR xL xR).
  Qed.

  Definition sim_decrypt_reduction_adv_continuation_kernel
      (A : nom_package) {mid_t out_t : choice_type}
      (contL contR : mid_t -> raw_code out_t)
      (Hcont : sim_decrypt_reduction_adv_continuation_witness
        A contL contR)
      (xy : option (mid_t * heap) * option (mid_t * heap)) :
      {distr (option (out_t * heap) * option (out_t * heap)) / R} :=
    let KL ymem := Pr_code (contL ymem.1) ymem.2 in
    let KR ymem := Pr_code (contR ymem.1) ymem.2 in
    match xy with
    | (Some (yL, memL), Some (yR, memR)) =>
        proj1_sig
          (boolp.constructive_indefinite_description
            (Hcont memL memR yL yR))
    | _ => complete_bind_fallback_coupling KL KR xy
    end.

  Lemma sim_decrypt_reduction_adv_continuation_kernel_margins
      (A : nom_package) {mid_t out_t : choice_type}
      (contL contR : mid_t -> raw_code out_t)
      (Hcont : sim_decrypt_reduction_adv_continuation_witness
        A contL contR) xy :
    let KL ymem := Pr_code (contL ymem.1) ymem.2 in
    let KR ymem := Pr_code (contR ymem.1) ymem.2 in
    coupling
      (sim_decrypt_reduction_adv_continuation_kernel
        A contL contR Hcont xy)
      (complete_bind_kernel KL xy.1)
      (complete_bind_kernel KR xy.2).
  Proof.
    case: xy=> [[ymemL|] [ymemR|]] /=.
    - case: ymemL=> yL memL; case: ymemR=> yR memR /=.
      rewrite /sim_decrypt_reduction_adv_continuation_kernel /=.
      case: (boolp.constructive_indefinite_description
        (Hcont memL memR yL yR))=> d [Hd Hsupport] /=.
      exact: Hd.
    - case: ymemL=> yL memL.
      rewrite /sim_decrypt_reduction_adv_continuation_kernel /=.
      have [HdL HdR] :=
        complete_bind_fallback_coupling_margins
          (fun ymem : mid_t * heap => Pr_code (contL ymem.1) ymem.2)
          (fun ymem : mid_t * heap => Pr_code (contR ymem.1) ymem.2)
          (Some (yL, memL), None).
      apply: coupling_of_margins; split.
      + exact: HdL.
      + exact: HdR.
    - case: ymemR=> yR memR.
      rewrite /sim_decrypt_reduction_adv_continuation_kernel /=.
      have [HdL HdR] :=
        complete_bind_fallback_coupling_margins
          (fun ymem : mid_t * heap => Pr_code (contL ymem.1) ymem.2)
          (fun ymem : mid_t * heap => Pr_code (contR ymem.1) ymem.2)
          (None, Some (yR, memR)).
      apply: coupling_of_margins; split.
      + exact: HdL.
      + exact: HdR.
    - rewrite /sim_decrypt_reduction_adv_continuation_kernel /=.
      have [HdL HdR] :=
        complete_bind_fallback_coupling_margins
          (fun ymem : mid_t * heap => Pr_code (contL ymem.1) ymem.2)
          (fun ymem : mid_t * heap => Pr_code (contR ymem.1) ymem.2)
          (None, None).
      apply: coupling_of_margins; split.
      + exact: HdL.
      + exact: HdR.
  Qed.

  Lemma sim_decrypt_reduction_adv_continuation_kernel_support
      (A : nom_package) {mid_t out_t : choice_type}
      (contL contR : mid_t -> raw_code out_t)
      (Hcont : sim_decrypt_reduction_adv_continuation_witness
        A contL contR)
      (yL yR : mid_t) memL memR :
    same_input_sim_decrypt_reduction_adv_pre A
      ((yL, memL), (yR, memR)) ->
    supports_same_result_sim_decrypt_reduction_adv_opt A
      (sim_decrypt_reduction_adv_continuation_kernel A contL contR
        Hcont (Some (yL, memL), Some (yR, memR))).
  Proof.
    move=> Hpre.
    rewrite /sim_decrypt_reduction_adv_continuation_kernel /=.
    case: (boolp.constructive_indefinite_description
      (Hcont memL memR yL yR))=> d [Hd Hsupport] /=.
    exact: Hsupport Hpre.
  Qed.

  Lemma sim_decrypt_reduction_adv_continuation_witness_ret
      (A : nom_package) {in_t out_t : choice_type}
      (fL fR : in_t -> out_t) :
    (forall memL memR xL xR,
      same_input_sim_decrypt_reduction_adv_pre A
        ((xL, memL), (xR, memR)) ->
      fL xL = fR xR) ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun x => ret (fL x))
      (fun x => ret (fR x)).
  Proof.
    move=> Hf memL memR xL xR.
    pose d : {distr
        (option (out_t * heap) * option (out_t * heap)) / R} :=
      dunit
        (Some (fL xL, memL), Some (fR xR, memR)).
    exists d.
    split.
    - apply: coupling_of_margins; split.
      + move=> z.
        rewrite /d dmargin_dunit Pr_code_ret.
        case: z=> [[y mem]|] /=.
        * rewrite /complete_mass.
          by rewrite !dunit1E.
        * by rewrite /complete_mass dunit_dweight subrr dunit1E.
      + move=> z.
        rewrite /d dmargin_dunit Pr_code_ret.
        case: z=> [[y mem]|] /=.
        * rewrite /complete_mass.
          by rewrite !dunit1E.
        * by rewrite /complete_mass dunit_dweight subrr dunit1E.
    - move=> Hpre outs Houts.
      have -> :
          outs = (Some (fL xL, memL), Some (fR xR, memR)).
        exact: in_dunit Houts.
      have Hfx := Hf memL memR xL xR Hpre.
      case: Hpre=> _ Hrel.
      split.
      + exact: Hfx.
      + exact: Hrel.
  Qed.

  Lemma sim_decrypt_reduction_adv_continuation_witness_bind_input
      (A : nom_package) {in_t mid_t out_t : choice_type}
      (progL progR : in_t -> raw_code mid_t)
      (contL contR : mid_t -> in_t -> raw_code out_t) :
    sim_decrypt_reduction_adv_continuation_witness A progL progR ->
    (forall y,
      sim_decrypt_reduction_adv_continuation_witness A
        (contL y) (contR y)) ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun x => y ← progL x ;; contL y x)
      (fun x => y ← progR x ;; contR y x).
  Proof.
    move=> Hprog Hcont memL memR xL xR.
    have [d0 [Hd0 Hprog_support_if]] := Hprog memL memR xL xR.
    pose KL (ymem : mid_t * heap) :=
      Pr_code (contL ymem.1 xL) ymem.2.
    pose KR (ymem : mid_t * heap) :=
      Pr_code (contR ymem.1 xR) ymem.2.
    pose K (xy : option (mid_t * heap) * option (mid_t * heap)) :
        {distr (option (out_t * heap) * option (out_t * heap)) / R} :=
      match xy with
      | (Some (yL, memL'), Some (yR, memR')) =>
          if eq_op yL yR then
              proj1_sig
                (boolp.constructive_indefinite_description
                  (Hcont yL memL' memR' xL xR))
          else
              completed_fallback_coupling
                (Pr_code (contL yL xL) memL')
                (Pr_code (contR yR xR) memR')
      | _ => complete_bind_fallback_coupling KL KR xy
      end.
    have HK xy :
        coupling (K xy)
          (complete_bind_kernel KL xy.1)
          (complete_bind_kernel KR xy.2).
      case: xy=> [[ymemL|] [ymemR|]] /=.
      - case: ymemL=> yL memL'; case: ymemR=> yR memR'.
        rewrite /K /=.
        case Heq: (eq_op yL yR).
        + move/eqP: Heq=> Heq.
          subst yR.
          case: (boolp.constructive_indefinite_description
            (Hcont yL memL' memR' xL xR))=> d [Hd Hsupport] /=.
          exact: Hd.
        + have [HdL HdR] :=
            completed_fallback_coupling_margins
              (Pr_code (contL yL xL) memL')
              (Pr_code (contR yR xR) memR').
          apply: coupling_of_margins; split.
          * exact: HdL.
          * exact: HdR.
      - case: ymemL=> yL memL'.
        have [HdL HdR] :=
          complete_bind_fallback_coupling_margins KL KR
            (Some (yL, memL'), None).
        apply: coupling_of_margins; split.
        + exact: HdL.
        + exact: HdR.
      - case: ymemR=> yR memR'.
        have [HdL HdR] :=
          complete_bind_fallback_coupling_margins KL KR
            (None, Some (yR, memR')).
        apply: coupling_of_margins; split.
        + exact: HdL.
        + exact: HdR.
      - have [HdL HdR] :=
          complete_bind_fallback_coupling_margins KL KR (None, None).
        apply: coupling_of_margins; split.
        + exact: HdL.
        + exact: HdR.
    exists (\dlet_(xy <- d0) K xy).
    split.
    - have Hbind := coupling_bind_kernel d0
        (complete (Pr_code (progL xL) memL))
        (complete (Pr_code (progR xR) memR))
        K (complete_bind_kernel KL) (complete_bind_kernel KR)
        Hd0 HK.
      have [HL HR] := coupling_margins Hbind.
      apply: coupling_of_margins; split.
      + move=> z.
        rewrite HL.
        rewrite (complete_bind (Pr_code (progL xL) memL) KL z).
        rewrite /KL Pr_code_bind.
        by [].
      + move=> z.
        rewrite HR.
        rewrite (complete_bind (Pr_code (progR xR) memR) KR z).
        rewrite /KR Pr_code_bind.
        by [].
    - move=> Hpre outs Houts.
      have Hprog_support := Hprog_support_if Hpre.
      have [xy Hxy Hinner] := @dinsupp_dlet R _ _ _ _ _ Houts.
      have Hmid := Hprog_support xy Hxy.
      clear Hxy.
      case: xy Hmid Hinner=> [[ymemL|] [ymemR|]].
      + case: ymemL=> yL memL'.
        case: ymemR=> yR memR' Hmid Hinner.
        move: Hmid=> [Hy Hrel].
        subst yR.
        rewrite /K /= in Hinner.
        rewrite eqxx in Hinner.
        case: Hpre=> Hx _.
        have Hcont_pre :
            same_input_sim_decrypt_reduction_adv_pre A
              ((xL, memL'), (xR, memR')).
          split; first exact: Hx.
          exact: Hrel.
        set cid := boolp.constructive_indefinite_description
          (Hcont yL memL' memR' xL xR) in Hinner.
        have Hselected_support :
            supports_same_result_sim_decrypt_reduction_adv_opt A
              (proj1_sig cid).
          rewrite /cid.
          case: (boolp.constructive_indefinite_description
            (Hcont yL memL' memR' xL xR))=> d [Hd Hsupport] /=.
          exact: Hsupport Hcont_pre.
        exact: (Hselected_support outs Hinner).
      + case: ymemL=> yL memL' Hmid.
        by [].
      + case: ymemR=> yR memR' Hmid.
        by [].
      + move=> _ Hinner.
        have -> : outs = (None, None).
          rewrite /K /complete_bind_fallback_coupling
            /complete_bind_kernel /product_coupling in Hinner.
          rewrite !dlet_unit in Hinner.
          exact: in_dunit Hinner.
        by [].
  Qed.

  Lemma sim_decrypt_reduction_adv_continuation_witness_same_input
      (A : nom_package) {in_t out_t : choice_type}
      (progL progR : in_t -> raw_code out_t) :
    (forall x,
      sim_decrypt_reduction_adv_continuation_witness A
        (fun _ : chUnit => progL x)
        (fun _ : chUnit => progR x)) ->
    sim_decrypt_reduction_adv_continuation_witness A progL progR.
  Proof.
    move=> Hpoint memL memR xL xR.
    case Hx: (eq_op xL xR).
    - move/eqP: Hx=> Hx.
      subst xR.
      have [d [Hd Hsupport_if]] := Hpoint xL memL memR tt tt.
      exists d.
      split; first exact: Hd.
      move=> Hpre.
      apply: Hsupport_if.
      case: Hpre=> _ Hrel.
      by split.
    - pose d :=
        completed_fallback_coupling
          (Pr_code (progL xL) memL)
          (Pr_code (progR xR) memR).
      exists d.
      split.
      + have [HdL HdR] :=
          completed_fallback_coupling_margins
            (Pr_code (progL xL) memL)
            (Pr_code (progR xR) memR).
        apply: coupling_of_margins; split.
        * exact: HdL.
        * exact: HdR.
      + move=> Hpre.
        case: Hpre=> Hx_eq _.
        move: Hx.
        rewrite Hx_eq eqxx.
        by [].
  Qed.

  Lemma sim_decrypt_reduction_adv_continuation_witness_put_adversary
      (A : nom_package) {in_t out_t : choice_type}
      (l : Location) (v : l) (contL contR : in_t -> raw_code out_t) :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    fhas (loc (ind_cpad_moved_adversary A)) l ->
    sim_decrypt_reduction_adv_continuation_witness A contL contR ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun x => #put l := v ;; contL x)
      (fun x =>
        #put (Nominal.rename
          (sim_decrypt_reduction_moved_adversary_perm A) l : Location)
          := v ;;
        contR x).
  Proof.
    move=> Houter Hl Hcont memL memR xL xR.
    pose lR :=
      (Nominal.rename
        (sim_decrypt_reduction_moved_adversary_perm A) l : Location).
    have [d [Hd Hsupport_if]] :=
      Hcont (set_heap memL l v) (set_heap memR lR v) xL xR.
    exists d.
      split.
      - have [HL HR] := coupling_margins Hd.
        apply: coupling_of_margins; split.
        + move=> z.
          rewrite Pr_code_put.
          by rewrite HL.
        + move=> z.
          rewrite /lR Pr_code_put.
          by rewrite HR.
    - move=> Hpre.
      apply: Hsupport_if.
      case: Hpre=> Hx Hrel.
      split; first exact: Hx.
      rewrite /lR.
      exact: (sim_decrypt_reduction_adv_heap_rel_set_adversary
        A memL memR l v Houter Hl Hrel).
  Qed.

  Lemma sim_decrypt_reduction_adv_continuation_witness_get_adversary
      (A : nom_package) {in_t out_t : choice_type}
      (l : Location) (contL contR : l -> in_t -> raw_code out_t) :
    fhas (loc (ind_cpad_moved_adversary A)) l ->
    (forall v,
      sim_decrypt_reduction_adv_continuation_witness A
        (contL v) (contR v)) ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun x => v ← get l ;; contL v x)
      (fun x =>
        v ← get (Nominal.rename
          (sim_decrypt_reduction_moved_adversary_perm A) l : Location) ;;
        contR v x).
  Proof.
    move=> Hl Hcont memL memR xL xR.
    pose lR :=
      (Nominal.rename
        (sim_decrypt_reduction_moved_adversary_perm A) l : Location).
    pose vL := get_heap memL l.
    pose vR := get_heap memR lR.
    case Hpick: (eq_op (pickle vL) (pickle vR)).
    - have Hv : vL = vR.
        apply: (pcan_inj pickleK).
        exact/eqP.
      have [d [Hd Hsupport_if]] := Hcont vL memL memR xL xR.
      exists d.
      split.
      + have [HL HR] := coupling_margins Hd.
        apply: coupling_of_margins; split.
        * move=> z.
          rewrite Pr_code_get /vL.
          by rewrite HL.
        * move=> z.
          rewrite Pr_code_get /lR -/vR -Hv /vL.
          by rewrite HR.
      + exact: Hsupport_if.
    - pose d :=
        completed_fallback_coupling
          (Pr_code (contL vL xL) memL)
          (Pr_code (contR vR xR) memR).
      exists d.
      split.
      + have [HL HR] :=
          completed_fallback_coupling_margins
            (Pr_code (contL vL xL) memL)
            (Pr_code (contR vR xR) memR).
        apply: coupling_of_margins; split.
        * move=> z.
          rewrite /d.
          rewrite Pr_code_get /vL.
          exact: (HL z).
        * move=> z.
          rewrite /d.
          rewrite Pr_code_get /lR /vR.
          exact: (HR z).
      + move=> Hpre.
        have Hread :
            get_heap memL l = get_heap memR lR.
          rewrite /lR.
          exact: (same_input_sim_decrypt_reduction_adv_pre_get
            A xL xR memL memR l Hpre Hl).
        move: Hpick.
        rewrite /vL /vR Hread eqxx.
        by [].
  Qed.

  Lemma sim_decrypt_reduction_adv_continuation_witness_sample
      (A : nom_package) {in_t out_t : choice_type}
      (op : Op) (contL contR : Arit op -> in_t -> raw_code out_t) :
    (forall a,
      sim_decrypt_reduction_adv_continuation_witness A
        (contL a) (contR a)) ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun x => a ← sample op ;; contL a x)
      (fun x => a ← sample op ;; contR a x).
  Proof.
    move=> Hcont memL memR xL xR.
    pose D : {distr (Arit op) / R} := projT2 op.
    pose outL (a : Arit op) := (a, memL).
    pose outR (a : Arit op) := (a, memR).
    pose d0 := shared_complete_sample_coupling D outL outR.
    pose KL (ymem : Arit op * heap) :=
      Pr_code (contL ymem.1 xL) ymem.2.
    pose KR (ymem : Arit op * heap) :=
      Pr_code (contR ymem.1 xR) ymem.2.
    pose K (xy : option (Arit op * heap) * option (Arit op * heap)) :
        {distr (option (out_t * heap) * option (out_t * heap)) / R} :=
      match xy with
      | (Some (aL, memL'), Some (aR, memR')) =>
          match @idP (eq_op aL aR) with
          | ReflectT _ =>
              proj1_sig
                (boolp.constructive_indefinite_description
                  (Hcont aL memL' memR' xL xR))
          | ReflectF _ =>
              completed_fallback_coupling
                (Pr_code (contL aL xL) memL')
                (Pr_code (contR aR xR) memR')
          end
      | _ => complete_bind_fallback_coupling KL KR xy
      end.
    have Hd0 : coupling d0
        (complete (dmargin outL D))
        (complete (dmargin outR D)).
      have [HmarginL HmarginR] :=
        shared_complete_sample_coupling_margins D outL outR.
      apply: coupling_of_margins; split.
      + exact: HmarginL.
      + exact: HmarginR.
    have HK xy :
        coupling (K xy)
          (complete_bind_kernel KL xy.1)
          (complete_bind_kernel KR xy.2).
      case: xy=> [[ymemL|] [ymemR|]] /=.
      - case: ymemL=> aL memL'; case: ymemR=> aR memR'.
        rewrite /K /=.
        destruct (@idP (eq_op aL aR)) as [Heq|Hneq].
        + move/eqP: Heq=> Heq.
          subst aR.
          case: (boolp.constructive_indefinite_description
            (Hcont aL memL' memR' xL xR))=> d [Hd Hsupport] /=.
          exact: Hd.
        + have [HdL HdR] :=
            completed_fallback_coupling_margins
              (Pr_code (contL aL xL) memL')
              (Pr_code (contR aR xR) memR').
          apply: coupling_of_margins; split.
          * exact: HdL.
          * exact: HdR.
      - case: ymemL=> aL memL'.
        have [HdL HdR] :=
          complete_bind_fallback_coupling_margins KL KR
            (Some (aL, memL'), None).
        apply: coupling_of_margins; split.
        + exact: HdL.
        + exact: HdR.
      - case: ymemR=> aR memR'.
        have [HdL HdR] :=
          complete_bind_fallback_coupling_margins KL KR
            (None, Some (aR, memR')).
        apply: coupling_of_margins; split.
        + exact: HdL.
        + exact: HdR.
      - have [HdL HdR] :=
          complete_bind_fallback_coupling_margins KL KR (None, None).
        apply: coupling_of_margins; split.
        + exact: HdL.
        + exact: HdR.
    exists (\dlet_(xy <- d0) K xy).
    split.
    - have Hbind := coupling_bind_kernel d0
        (complete (dmargin outL D)) (complete (dmargin outR D))
        K (complete_bind_kernel KL) (complete_bind_kernel KR) Hd0 HK.
      have [HL HR] := coupling_margins Hbind.
      apply: coupling_of_margins; split.
      + move=> z.
        rewrite HL.
        rewrite (complete_bind (dmargin outL D) KL z).
        apply: complete_distr_ext=> y.
        rewrite /KL /outL /D Pr_code_sample dmarginE.
        rewrite __deprecated__dlet_dlet.
        apply: eq_in_dlet=> // a _ y'.
        by rewrite dlet_unit.
      + move=> z.
        rewrite HR.
        rewrite (complete_bind (dmargin outR D) KR z).
        apply: complete_distr_ext=> y.
        rewrite /KR /outR /D Pr_code_sample dmarginE.
        rewrite __deprecated__dlet_dlet.
        apply: eq_in_dlet=> // a _ y'.
        by rewrite dlet_unit.
    - move=> Hpre outs Houts.
      have [xy Hxy Hinner] := @dinsupp_dlet R _ _ _ _ _ Houts.
      rewrite /d0 /shared_complete_sample_coupling in Hxy.
      have [ox Hox Hxy_inner] := @dinsupp_dlet R _ _ _ _ _ Hxy.
      case: ox Hox Hxy_inner=> [a|] Hox Hxy_inner.
      + have Hxy_eq : xy = (Some (outL a), Some (outR a)).
          exact: in_dunit Hxy_inner.
        rewrite Hxy_eq in Hinner.
        rewrite /K /outL /outR /= in Hinner.
        destruct (@idP (eq_op a a)) as [Heq|Hneq].
        * case: (boolp.constructive_indefinite_description
            (Hcont a memL memR xL xR)) Hinner=>
            d [Hd Hsupport] Hinner /=.
          exact: (Hsupport Hpre outs Hinner).
        * by move: Hneq; rewrite eqxx.
      + have Hxy_eq : xy = (None, None).
          exact: in_dunit Hxy_inner.
        rewrite Hxy_eq in Hinner.
        have -> : outs = (None, None).
          rewrite /K /complete_bind_fallback_coupling
            /complete_bind_kernel /product_coupling in Hinner.
          rewrite !dlet_unit in Hinner.
          exact: in_dunit Hinner.
        by [].
  Qed.

  Lemma supports_same_result_sim_decrypt_reduction_adv_opt_oracle
      (A : nom_package) max_queries (o : opsig) (x : src o)
      memL memR
      (d : {distr
        (option (tgt o * heap) * option (tgt o * heap)) / R}) :
    fhas IndCpadGame.IndCpadAdv_import o ->
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    sim_decrypt_reduction_adv_heap_rel A memL memR ->
    coupling d
      (complete
        (Pr_code (resolve (IndCpadSimDecryptOracle max_queries) o x) memL))
      (complete
        (Pr_code
          (code_link
            (resolve (IndCpaDSim.IndCpadOracle max_queries) o x)
            IndCpaSecurity.IndCpaGame.IndCpaOracle)
          memR)) ->
    \P_[d] same_result_sim_decrypt_reduction_opt >= 1 ->
    supports_same_result_sim_decrypt_reduction_adv_opt A d.
  Proof.
    move=> Ho Houter [Hheap Hadv] Hd Hprob outs Houts.
    have [HdL HdR] := coupling_margins Hd.
    have Hdweight : dweight d = 1.
      rewrite -(dmargin_dweight fst d).
      transitivity (dweight (complete
        (Pr_code (resolve (IndCpadSimDecryptOracle max_queries) o x) memL))).
      - apply: eq_psum=> z.
        by rewrite !mul1r HdL.
      - exact: complete_dweight.
    have Hbool :
        same_result_sim_decrypt_reduction_opt outs.
      exact: (support_of_pr_ge1 d
        (@same_result_sim_decrypt_reduction_opt (tgt o))
        Hdweight Hprob outs Houts).
    case: outs Hbool Houts=> [outLopt outRopt].
    case: outLopt=> [[outL memL']|];
      case: outRopt=> [[outR memR']|] //=.
    - move=> /andP [/eqP Hout Hrel] Houts.
      split; first exact: Hout.
      split; first exact: Hrel.
      have HoutL :
          (outL, memL') \in
            dinsupp
              (Pr_code
                (resolve (IndCpadSimDecryptOracle max_queries) o x) memL).
        have Hfst :
            Some (outL, memL') \in dinsupp (dmargin fst d).
          exact: dmargin_dinsupp_image Houts.
        move: Hfst.
        by rewrite in_dinsupp HdL completeE /= -in_dinsupp.
      have HoutR :
          (outR, memR') \in
            dinsupp
              (Pr_code
                (code_link
                  (resolve (IndCpaDSim.IndCpadOracle max_queries) o x)
                  IndCpaSecurity.IndCpaGame.IndCpaOracle)
                memR).
        have Hsnd :
            Some (outR, memR') \in dinsupp (dmargin snd d).
          exact: dmargin_dinsupp_image Houts.
        move: Hsnd.
        by rewrite in_dinsupp HdR completeE /= -in_dinsupp.
      exact: (sim_decrypt_reduction_adversary_heap_eq_oracle_outputs
        A max_queries o x memL memR (outL, memL') (outR, memR')
        Ho Houter Hadv HoutL HoutR).
  Qed.

  Lemma sim_decrypt_reduction_adv_continuation_witness_oracle_prefix
      (A : nom_package) max_queries {in_t : choice_type}
      (o : opsig) (x : src o) :
    fhas IndCpadGame.IndCpadAdv_import o ->
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    ⊨AE ⦃ same_input_sim_decrypt_reduction_pre ⦄
      (fun x : src o =>
        resolve (IndCpadSimDecryptOracle max_queries) o x)
      ≈( 0 )
      (fun x : src o =>
        code_link
          (resolve (IndCpaDSim.IndCpadOracle max_queries) o x)
          IndCpaSecurity.IndCpaGame.IndCpaOracle)
    ⦃ same_result_sim_decrypt_reduction_opt ⦄ ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun _ : in_t =>
        resolve (IndCpadSimDecryptOracle max_queries) o x)
      (fun _ : in_t =>
        code_link
          (resolve (IndCpaDSim.IndCpadOracle max_queries) o x)
          IndCpaSecurity.IndCpaGame.IndCpaOracle).
  Proof.
    move=> Ho Houter Horacle memL memR xL xR.
    case Hrel_bool: (sim_decrypt_reduction_heap_rel memL memR).
    - have Hsame :
          same_input_sim_decrypt_reduction_pre
            ((x, memL), (x, memR)).
        by rewrite /same_input_sim_decrypt_reduction_pre /= eqxx Hrel_bool.
      have [d [Hd Hprob]] := Horacle.2 memL memR x x Hsame.
      rewrite subr0 in Hprob.
      exists d.
      split; first exact: Hd.
      move=> Hpre.
      case: Hpre=> _ Hrel.
      exact: (supports_same_result_sim_decrypt_reduction_adv_opt_oracle
        A max_queries o x memL memR d Ho Houter Hrel Hd Hprob).
    - pose d :=
        completed_fallback_coupling
          (Pr_code (resolve (IndCpadSimDecryptOracle max_queries) o x) memL)
          (Pr_code
            (code_link
              (resolve (IndCpaDSim.IndCpadOracle max_queries) o x)
              IndCpaSecurity.IndCpaGame.IndCpaOracle)
            memR).
      exists d.
      split.
      + have [HdL HdR] :=
          completed_fallback_coupling_margins
            (Pr_code
              (resolve (IndCpadSimDecryptOracle max_queries) o x) memL)
            (Pr_code
              (code_link
                (resolve (IndCpaDSim.IndCpadOracle max_queries) o x)
                IndCpaSecurity.IndCpaGame.IndCpaOracle)
              memR).
        apply: coupling_of_margins; split.
        * exact: HdL.
        * exact: HdR.
      + move=> Hpre.
        case: Hpre=> _ [Hrel _].
        move: Hrel_bool.
        by rewrite Hrel.
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_resolve_outer_link_rel_ae
      max_queries (o : opsig) :
    fhas IndCpadGame.IndCpadAdv_import o ->
    ⊨AE ⦃ same_input_sim_decrypt_reduction_pre ⦄
      (fun x : src o =>
        resolve (IndCpadSimDecryptOracle max_queries) o x)
      ≈( 0 )
      (fun x : src o =>
        code_link
          (resolve (IndCpaDSim.IndCpadOracle max_queries) o x)
          IndCpaSecurity.IndCpaGame.IndCpaOracle)
    ⦃ same_result_sim_decrypt_reduction_opt ⦄.
  Proof.
    move: o=> [f [S T]] Ho.
    destruct ((f == IndCpadGame.oracle_encrypt)%bool) eqn:Ho_encrypt.
    - have Hfid : f = IndCpadGame.oracle_encrypt :=
        ident_eqb_eq f IndCpadGame.oracle_encrypt Ho_encrypt.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_encrypt
            (chProd message message) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Ho.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      exact: (ind_cpad_sim_decrypt_reduction_encrypt_resolve_outer_link_rel_ae
        max_queries).
    destruct ((f == IndCpadGame.oracle_eval1)%bool) eqn:Ho_eval1.
    - have Hfid : f = IndCpadGame.oracle_eval1 :=
        ident_eqb_eq f IndCpadGame.oracle_eval1 Ho_eval1.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_eval1
            (chProd unary_gate nat) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Ho.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      exact: (ind_cpad_sim_decrypt_reduction_eval1_resolve_outer_link_rel_ae
        max_queries).
    destruct ((f == IndCpadGame.oracle_eval2)%bool) eqn:Ho_eval2.
    - have Hfid : f = IndCpadGame.oracle_eval2 :=
        ident_eqb_eq f IndCpadGame.oracle_eval2 Ho_eval2.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_eval2
            (chProd (chProd binary_gate nat) nat) ciphertext.
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Ho.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      exact: (ind_cpad_sim_decrypt_reduction_eval2_resolve_outer_link_rel_ae
        max_queries).
    destruct ((f == IndCpadGame.oracle_decrypt)%bool) eqn:Ho_decrypt.
    - have Hfid : f = IndCpadGame.oracle_decrypt :=
        ident_eqb_eq f IndCpadGame.oracle_decrypt Ho_decrypt.
      have Hop : (f, (S, T)) =
          mkopsig IndCpadGame.oracle_decrypt nat (chOption message).
        apply: (fhas_same_ident_opsig IndCpadGame.IndCpadAdv_import).
        + rewrite /IndCpadGame.IndCpadAdv_import.
          fmap_solve.
        + exact: Ho.
        + exact: Hfid.
      subst f.
      inversion Hop; subst S T.
      exact: (ind_cpad_sim_decrypt_reduction_decrypt_resolve_outer_link_rel_ae
        max_queries).
    exfalso.
    rewrite /IndCpadGame.IndCpadAdv_import in Ho.
    fmap_invert Ho.
    - by move: Ho_encrypt; rewrite eqxx.
    - by move: Ho_eval1; rewrite eqxx.
    - by move: Ho_eval2; rewrite eqxx.
    - by move: Ho_decrypt; rewrite eqxx.
  Qed.

  Definition sim_decrypt_reduction_adv_left_link
      max_queries {out_t : choice_type} (c : raw_code out_t) :
      raw_code out_t :=
    code_link c (IndCpadSimDecryptOracle max_queries).

  Definition sim_decrypt_reduction_adv_right_link
      (A : nom_package) max_queries {out_t : choice_type}
      (c : raw_code out_t) : raw_code out_t :=
    code_link
      (code_link
        (Nominal.rename (sim_decrypt_reduction_moved_adversary_perm A) c)
        (IndCpaDSim.IndCpadOracle max_queries))
      IndCpaSecurity.IndCpaGame.IndCpaOracle.

  Lemma sim_decrypt_reduction_adv_continuation_witness_code_link_rename_opr
      (A : nom_package) max_queries {out_t : choice_type}
      (o : opsig) (x : src o) (k : tgt o -> raw_code out_t) :
    fhas IndCpadGame.IndCpadAdv_import o ->
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    (forall y,
      sim_decrypt_reduction_adv_continuation_witness A
        (fun _ : chUnit =>
          sim_decrypt_reduction_adv_left_link max_queries (k y))
        (fun _ : chUnit =>
          sim_decrypt_reduction_adv_right_link A max_queries (k y))) ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun _ : chUnit =>
        sim_decrypt_reduction_adv_left_link max_queries (opr o x k))
      (fun _ : chUnit =>
        sim_decrypt_reduction_adv_right_link A max_queries (opr o x k)).
  Proof.
    rewrite /sim_decrypt_reduction_adv_left_link
      /sim_decrypt_reduction_adv_right_link.
    move=> Ho Houter Hk /=.
    rewrite code_link_bind.
    apply: sim_decrypt_reduction_adv_continuation_witness_bind_input.
    - exact: (sim_decrypt_reduction_adv_continuation_witness_oracle_prefix
        A max_queries (in_t := chUnit) o x Ho Houter
        (ind_cpad_sim_decrypt_reduction_resolve_outer_link_rel_ae
          max_queries o Ho)).
    - move=> y.
      exact: (Hk y).
  Qed.

  Lemma sim_decrypt_reduction_adv_continuation_witness_code_link_rename
      (A : nom_package) max_queries {out_t : choice_type}
      (c : raw_code out_t) :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    ValidCode (loc (ind_cpad_moved_adversary A))
      IndCpadGame.IndCpadAdv_import c ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun _ : chUnit =>
        sim_decrypt_reduction_adv_left_link max_queries c)
      (fun _ : chUnit =>
        sim_decrypt_reduction_adv_right_link A max_queries c).
  Proof.
    move=> Houter.
    elim: c=> [a|o x k IH|l k IH|l v k IH|op k IH] Hvalid.
    - rewrite /sim_decrypt_reduction_adv_left_link
        /sim_decrypt_reduction_adv_right_link /=.
      apply: sim_decrypt_reduction_adv_continuation_witness_ret.
      by [].
    - have [Ho Hk] := @inversion_valid_opr
        (loc (ind_cpad_moved_adversary A))
        IndCpadGame.IndCpadAdv_import out_t o x k
        (valid_code_from_class
          (loc (ind_cpad_moved_adversary A))
          IndCpadGame.IndCpadAdv_import out_t (opr o x k) Hvalid).
      apply: sim_decrypt_reduction_adv_continuation_witness_code_link_rename_opr.
      + exact: Ho.
      + exact: Houter.
      + move=> y.
        exact: (IH y (Hk y)).
    - have [Hl Hk] := @inversion_valid_getr
        (loc (ind_cpad_moved_adversary A))
        IndCpadGame.IndCpadAdv_import out_t l k
        (valid_code_from_class
          (loc (ind_cpad_moved_adversary A))
          IndCpadGame.IndCpadAdv_import out_t (getr l k) Hvalid).
      rewrite /sim_decrypt_reduction_adv_left_link
        /sim_decrypt_reduction_adv_right_link /=.
      apply: sim_decrypt_reduction_adv_continuation_witness_get_adversary.
      + exact: Hl.
      + move=> y.
        exact: (IH y (Hk y)).
    - have [Hl Hk] := @inversion_valid_putr
        (loc (ind_cpad_moved_adversary A))
        IndCpadGame.IndCpadAdv_import out_t l v k
        (valid_code_from_class
          (loc (ind_cpad_moved_adversary A))
          IndCpadGame.IndCpadAdv_import out_t (putr l v k) Hvalid).
      rewrite /sim_decrypt_reduction_adv_left_link
        /sim_decrypt_reduction_adv_right_link /=.
      apply: sim_decrypt_reduction_adv_continuation_witness_put_adversary.
      + exact: Houter.
      + exact: Hl.
      + exact: (IH Hk).
    - have Hk := @inversion_valid_sampler
        (loc (ind_cpad_moved_adversary A))
        IndCpadGame.IndCpadAdv_import out_t op k
        (valid_code_from_class
          (loc (ind_cpad_moved_adversary A))
          IndCpadGame.IndCpadAdv_import out_t (sampler op k) Hvalid).
      rewrite /sim_decrypt_reduction_adv_left_link
        /sim_decrypt_reduction_adv_right_link /=.
      apply: sim_decrypt_reduction_adv_continuation_witness_sample.
      move=> y.
      exact: (IH y (Hk y)).
  Qed.

End NoiseFloodingSecureGameReduction.
