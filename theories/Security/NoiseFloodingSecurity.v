From Stdlib Require Import Utf8 Unicode.Utf8 BinInt.
From extructures Require Import ord fset fmap.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot all_order all_algebra reals distr realsum lra.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
From SSProve Require Import NominalPrelude.
From Mending.Schemes Require Import ApproxFHE Indcpa Indcpad.
From Mending.Constructions Require Import NoiseFlooding.
From Mending.Security Require Import IndcpadSimulator.
From Mending.Schemes.Utils Require Import IntVec.
From Mending.ProgramLogics Require Import Ae.
From Mending.ProgramLogics Require Import Pyth.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras TupleExtras.

Import PackageNotation.
Import GRing.Theory Num.Theory Order.Theory Order.POrderTheory.

Local Open Scope package_scope.
Local Open Scope ring_scope.
Local Open Scope AeNotations.
Local Open Scope PythNotations.

(* TODO fill with actual value *)
Definition global_epsilon (max_queries : nat) (gaussian_width_multiplier : R) : R.
Admitted.

(* Glue code *)
Module Type NoiseFloodingIsIndCpad
  (Scheme : ApproxFheScheme)
  (Metric : ApproxFheMetric(Scheme))
  (Params : NoiseFloodingParams).
  Module NF := NoiseFlooding(Scheme)(Metric)(Params).
  Include IsIndCpad(NF).
End NoiseFloodingIsIndCpad.

(* Main theorem *)
Module NoiseFloodingSecure
  (Import Scheme : ApproxFheScheme)
  (Import Metric : ApproxFheMetric(Scheme))
  (Import Correctness : ApproxCorrectness(Scheme)(Metric))
  (Import IndCpaSecurity : IsIndCpa(Scheme))
  (Import Params : NoiseFloodingParams)
  : NoiseFloodingIsIndCpad(Scheme)(Metric)(Params).
  Module NF := NoiseFlooding(Scheme)(Metric)(Params).
  Definition security_loss (max_queries : nat) :=
    global_epsilon max_queries gaussian_width_multiplier.
  Definition security_bound (max_queries : nat) :=
    IndCpaSecurity.security_bound + security_loss max_queries.

  Lemma security_loss_nonnegative max_queries :
    0 <= security_loss max_queries.
  Admitted.

  Module IndCpadGame := IndCpad NF.
  Module IndCpaDSim := IndCpadSimulator(Scheme)(Metric)(Params).

  Notation " 'adv_keys " := (pk_t × evk_t) (in custom pack_type at level 2).
  Notation " 'message_pair " := (message × message) (in custom pack_type at level 2).
  Notation " 'ciphertext " := ciphertext (in custom pack_type at level 2).

  Definition ind_cpa_reduction (A : nom_package)
    (max_queries : nat) :=
    IndCpaDSim.IndCpaReduction A max_queries.

  Definition reduction_locs (A : nom_package)
    (max_queries : nat) : Locations :=
    IndCpaDSim.IndCpaReduction_locs A max_queries.

  Definition ind_cpad_game_code
    (A : nom_package) (max_queries : nat) (_ : chUnit) :
    raw_code bool :=
    resolve (IndCpadGame.IndCpadGame max_queries A)
      (IndCpadGame.main, ('unit, 'bool)) tt.

  Definition ind_cpa_reduction_game_code
    (A : nom_package) (max_queries : nat) (_ : chUnit) :
    raw_code bool :=
    resolve
      (IndCpaSecurity.IndCpaGame.IndCpaGame
        (ind_cpa_reduction A max_queries))
      (IndCpaSecurity.IndCpaGame.main, ('unit, 'bool)) tt.

  Definition game_initial_pre :
    pred ((chUnit * heap) * (chUnit * heap)) :=
    pred1 ((tt, empty_heap), (tt, empty_heap)).

  Definition same_game_output (outs : (bool * heap) * (bool * heap)) : bool :=
    eq_op outs.1.1 outs.2.1.

  Definition same_game_output_and_heap
    (outs : (bool * heap) * (bool * heap)) : bool :=
    let '((y1, m1), (y2, m2)) := outs in
    andb (eq_op y1 y2) (eq_op m1 m2).

  (* A singleton event is controlled by twice our TV convention
     (`total_variation` is defined as one half of the L1 distance). *)
  Lemma total_variation_point_bound2
    {T : choiceType} (P Q : {distr T / R}) (x : T) :
    `|P x - Q x| <= 2 * total_variation P Q.
  Proof.
    rewrite /total_variation.
    have Hsummable : summable (fun y => P y - Q y).
      apply: summableD; first exact: summable_mu.
      by apply: summableN; exact: summable_mu.
    have Hpoint :=
      gerfinseq_psum (S := fun y => P y - Q y) (r := [:: x])
        _ Hsummable.
    rewrite big_seq1 in Hpoint.
    rewrite -(psum_abs (fun y => P y - Q y)) in Hpoint.
    have Hpsum_sum :
      psum (fun y => `|P y - Q y|) =
      sum (fun y => `|P y - Q y|).
      by apply: psum_sum => y; exact: normr_ge0.
    rewrite Hpsum_sum in Hpoint.
    apply: (@le_trans _ _ (sum (fun y => `|P y - Q y|))).
      exact: Hpoint.
    lra.
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
    ⦃ same_game_output ⦄ ->
    2 * ε <= security_loss max_queries ->
    IndCpadGame.winning_probability max_queries A <=
    IndCpaSecurity.IndCpaGame.winning_probability
      (ind_cpa_reduction A max_queries) +
    security_loss max_queries.
  Proof.
    move=> Hae Hloss.
    have Hpre : game_initial_pre ((tt, empty_heap), (tt, empty_heap)).
      by rewrite /game_initial_pre.
    have Htv :=
      additiveErrorTvBound _ _ _ _ empty_heap empty_heap tt tt Hae Hpre.
    have Hpoint :
      `|IndCpadGame.success_probability max_queries A -
        IndCpaSecurity.IndCpaGame.success_probability
          (ind_cpa_reduction A max_queries)| <= 2 * ε.
      apply: (@le_trans _ _
        (2 * total_variation
          (dmargin fst (Pr_code (ind_cpad_game_code A max_queries tt) empty_heap))
          (dmargin fst
            (Pr_code (ind_cpa_reduction_game_code A max_queries tt) empty_heap)))).
        rewrite /IndCpadGame.success_probability
          /IndCpaSecurity.IndCpaGame.success_probability
          /IndCpadGame.game_out /IndCpaSecurity.IndCpaGame.game_out
          /ind_cpad_game_code /ind_cpa_reduction_game_code /Pr_op.
        exact: total_variation_point_bound2.
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

  (* Applies Micciancio-Walter to turn a Pythagorean judgment into AE. *)
  Lemma ind_cpa_reduction_additive_error_from_pyth
    {ℓ : nat} (A : nom_package) max_queries
    (s : (ℓ.+1).-tuple R) ε :
    pythagorean_tv_bound s <= ε ->
    ⊨Pyth ⦃ game_initial_pre ⦄
      (ind_cpad_game_code A max_queries)
      ≈( s )
      (ind_cpa_reduction_game_code A max_queries)
    ⦃ fun _ : bool * heap => true ⦄ ->
    ⊨AE ⦃ game_initial_pre ⦄
      (ind_cpad_game_code A max_queries)
      ≈( ε )
      (ind_cpa_reduction_game_code A max_queries)
    ⦃ same_game_output ⦄.
  Proof.
    move=> Hbound Hpyth.
    have Hmw :
      ⊨AE ⦃ game_initial_pre ⦄
        (ind_cpad_game_code A max_queries)
        ≈( pythagorean_tv_bound s )
        (ind_cpa_reduction_game_code A max_queries)
      ⦃ same_game_output_and_heap ⦄.
      exact: (MicciancioWalterRule _ _ _ _ _ Hpyth).
    apply: (additiveErrorConseqRule
      (ind_cpad_game_code A max_queries)
      (ind_cpa_reduction_game_code A max_queries)
      game_initial_pre game_initial_pre
      same_game_output_and_heap same_game_output
      (pythagorean_tv_bound s) ε).
    - by [].
    - move=> [[y1 m1] [y2 m2]] /=.
      move=> H.
      by move/andP: H => [Hy _].
    - exact: Hbound.
    - exact: Hmw.
  Qed.

  (* The cryptographic core: prove the reduction games satisfy a Pyth judgment. *)
  Lemma ind_cpa_reduction_pyth
    {ℓ : nat} (A : nom_package) max_queries
    (s : (ℓ.+1).-tuple R) :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    pythagorean_tv_bound s <= security_loss max_queries / 2 ->
    ⊨Pyth ⦃ game_initial_pre ⦄
      (ind_cpad_game_code A max_queries)
      ≈( s )
      (ind_cpa_reduction_game_code A max_queries)
    ⦃ fun _ : bool * heap => true ⦄.
  Admitted.

  (* Chooses the Pyth budget and packages the result as the AE obligation. *)
  Lemma ind_cpa_reduction_additive_error
    (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    ⊨AE ⦃ game_initial_pre ⦄
      (ind_cpad_game_code A max_queries)
      ≈( security_loss max_queries / 2 )
      (ind_cpa_reduction_game_code A max_queries)
    ⦃ same_game_output ⦄.
  Proof.
    move=> A_valid.
    apply: (ind_cpa_reduction_additive_error_from_pyth
      A max_queries [tuple 0]).
    - rewrite /pythagorean_tv_bound /tuple_sum /=.
      rewrite big_ord_recl big_ord0 /= add0r mul0r sqrtr0.
      have := security_loss_nonnegative max_queries.
      lra.
    - have Hbound : pythagorean_tv_bound [tuple 0] <=
          security_loss max_queries / 2.
        rewrite /pythagorean_tv_bound /tuple_sum /=.
        rewrite big_ord_recl big_ord0 /= add0r mul0r sqrtr0.
        have := security_loss_nonnegative max_queries.
        lra.
      exact: (@ind_cpa_reduction_pyth 0 A max_queries [tuple 0]
        A_valid Hbound).
  Qed.

  (* The main reduction theorem composes AE-to-bound with the core AE judgment. *)
  Theorem ind_cpa_reduction_bound (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    IndCpadGame.winning_probability max_queries A <=
    IndCpaSecurity.IndCpaGame.winning_probability
      (ind_cpa_reduction A max_queries) +
    security_loss max_queries.
  Proof.
    move=> A_valid.
    have Hae := ind_cpa_reduction_additive_error A max_queries A_valid.
    apply: (ind_cpa_reduction_bound_from_additive_error
      A max_queries _ Hae).
    lra.
  Qed.

  (* IND-CPAD security follows by applying IND-CPA security to the reduction. *)
  Theorem is_secure (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    IndCpadGame.winning_probability max_queries A <= security_bound max_queries.
  Proof.
    move=> A_valid.
    rewrite /security_bound /security_loss.
    apply: (le_trans (ind_cpa_reduction_bound A max_queries A_valid)).
    rewrite lerD2r.
    exact: (IndCpaSecurity.is_secure
      (ind_cpa_reduction A max_queries)
      (ind_cpa_reduction_valid A max_queries A_valid)).
  Qed.
End NoiseFloodingSecure.
