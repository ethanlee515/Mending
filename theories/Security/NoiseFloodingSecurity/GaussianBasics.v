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

From Mending.Security.NoiseFloodingSecurity Require Import Prelude.

Module NoiseFloodingSecureGaussianBasics
  (Import Scheme : ApproxFheScheme)
  (Import Metric : ApproxFheMetric(Scheme))
  (Import Correctness : ApproxCorrectnessPerfect(Scheme)(Metric))
  (Import IndCpaSecurity : IsIndCpa(Scheme))
  (Import Params : NoiseFloodingParams).
  Module NF := NoiseFlooding(Scheme)(Metric)(Params).
  Definition security_loss (max_queries : nat) :=
    global_epsilon dim max_queries gaussian_width_multiplier.
  Definition security_bound (max_queries : nat) :=
    IndCpaSecurity.security_bound + security_loss max_queries.
  Definition compile_security_error (max_queries : nat) :=
    Num.sqrt
      ((max_queries%:R *
        noise_flooding_per_query_epsilon dim gaussian_width_multiplier) / 2).

  Lemma security_loss_nonnegative max_queries :
    0 <= security_loss max_queries.
  Proof.
    rewrite /security_loss /global_epsilon.
    apply: mulr_ge0; first lra.
    exact: Num.Theory.sqrtr_ge0.
  Qed.

  Lemma security_loss_halfE max_queries :
    security_loss max_queries / 2 = compile_security_error max_queries.
  Proof.
    rewrite /security_loss /global_epsilon /compile_security_error.
    lra.
  Qed.

  Lemma noise_flooding_dg_stdev_pos error_bound :
    0 < noise_flooding_dg_stdev gaussian_width_multiplier error_bound.
  Proof.
    rewrite /noise_flooding_dg_stdev.
    apply: mulr_gt0; last exact: gt0_gaussian_width_multiplier.
    rewrite ltr0z.
    lia.
  Qed.

  Lemma noise_flooding_per_query_epsilon_nonnegative :
    0 <= noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
  Proof.
    rewrite /noise_flooding_per_query_epsilon.
    apply: divr_ge0; first exact: ler0n.
    apply: mulr_ge0; first lra.
    apply: exprn_ge0.
    exact: ltW gt0_gaussian_width_multiplier.
  Qed.

  Lemma compile_security_error_nonnegative max_queries :
    0 <= compile_security_error max_queries.
  Proof.
    exact: Num.Theory.sqrtr_ge0.
  Qed.

  Lemma noise_flooding_scalar_kl_budget
      error_bound (delta : R) :
    delta ^+ 2 <= error_bound%:R ^+ 2 ->
    delta ^+ 2 /
      (2 * (noise_flooding_dg_stdev
        gaussian_width_multiplier error_bound) ^+ 2) <=
    1 / (2 * gaussian_width_multiplier ^+ 2).
  Proof.
    move=> Hdelta.
    rewrite /noise_flooding_dg_stdev.
    set e : R := error_bound%:R.
    set a : R := (error_bound * error_bound + 1)%:~R.
    set g := gaussian_width_multiplier.
    have Hg : 0 < g by rewrite /g; exact: gt0_gaussian_width_multiplier.
    have He_ge0 : 0 <= e by rewrite /e ler0n.
    have He_le_a : e <= a.
      rewrite /e /a.
      change (error_bound%:R <=
        (error_bound * error_bound + 1)%:R :> R).
      rewrite ler_nat.
      nia.
    have Ha_ge1 : 1 <= a.
      rewrite /a.
      change ((1%N)%:R <= (error_bound * error_bound + 1)%:R :> R).
      rewrite ler_nat.
      nia.
    have Ha_pos : 0 < a by lra.
    have Hdelta_a : delta ^+ 2 <= a ^+ 2.
      apply: (le_trans Hdelta).
      rewrite !expr2.
      nra.
    rewrite ler_pdivrMr.
    - apply: (le_trans Hdelta_a).
      rewrite !expr2.
      have -> :
          1 / (2 * (g * g)) * (2 * (a * g * (a * g))) = a * a.
        field.
        nra.
      exact: lexx.
    apply: mulr_gt0; first lra.
    by rewrite expr2 mulr_gt0 // mulr_gt0.
  Qed.

  Lemma int_abs_le_square_bound (z : int) (n : nat) :
    (absz z <= n)%N ->
    (z%:~R : R) ^+ 2 <= n%:R ^+ 2.
  Proof.
    move=> Hzn.
    have HabsR : `|z%:~R : R| <= n%:R.
      rewrite -intr_norm -natr_absz.
      by rewrite ler_nat.
    have Hz2 : (z%:~R : R) ^+ 2 = `|z%:~R : R| ^+ 2.
      rewrite -normrX.
      rewrite ger0_norm //.
      exact: sqr_ge0.
    rewrite Hz2.
    rewrite !expr2.
    have Habs_nonneg : 0 <= `|z%:~R : R| := normr_ge0 _.
    have Hn_nonneg : 0 <= n%:R :> R by exact: ler0n.
    nra.
  Qed.

  Lemma noise_flooding_coordinate_kl_budget
      error_bound (centerL centerR : dim.-tuple int) (i : 'I_dim) :
    (ivec_dist centerL centerR <= error_bound)%N ->
    ((tnth centerR i - tnth centerL i)%:~R : R) ^+ 2 /
      (2 * (noise_flooding_dg_stdev
        gaussian_width_multiplier error_bound) ^+ 2) <=
    1 / (2 * gaussian_width_multiplier ^+ 2).
  Proof.
    move=> Hdist.
    apply: noise_flooding_scalar_kl_budget.
    rewrite -[tnth centerR i - tnth centerL i]opprB rmorphN sqrrN.
    apply: int_abs_le_square_bound.
    exact: (leq_trans (ivec_dist_tnth_le centerL centerR i) Hdist).
  Qed.

  Lemma noise_flooding_coordinate_kl
      error_bound (centerL centerR : dim.-tuple int) (i : 'I_dim) :
    (ivec_dist centerL centerR <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    finite_kl
      (discrete_gaussian (tnth centerL i) stdev)
      (discrete_gaussian (tnth centerR i) stdev) /\
    δ_KL
      (discrete_gaussian (tnth centerL i) stdev)
      (discrete_gaussian (tnth centerR i) stdev) <=
    1 / (2 * gaussian_width_multiplier ^+ 2).
  Proof.
    move=> Hdist stdev.
    split.
    - apply: finite_kl_discrete_gaussian.
      exact: noise_flooding_dg_stdev_pos.
    rewrite kl_discrete_gaussian; first
      exact: noise_flooding_coordinate_kl_budget.
    exact: noise_flooding_dg_stdev_pos.
  Qed.

  Lemma noise_flooding_coordinate_epsilon_nonnegative :
    0 <= 1 / (2 * gaussian_width_multiplier ^+ 2).
  Proof.
    apply: divr_ge0; first lra.
    apply: mulr_ge0; first lra.
    apply: exprn_ge0.
    exact: ltW gt0_gaussian_width_multiplier.
  Qed.

  Lemma noise_flooding_coordinate_epsilon_sum :
    \sum_(i < dim) (1 / (2 * gaussian_width_multiplier ^+ 2)) =
    noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
  Proof.
    rewrite /noise_flooding_per_query_epsilon.
    rewrite big_const_ord iter_addr_0 mulr_natl.
    field.
    have Hg : 0 < gaussian_width_multiplier :=
      gt0_gaussian_width_multiplier.
    nra.
  Qed.

  Lemma n_dg_shifted_singleton_pyth_trace (c : int) s :
    n_dg_shifted [tuple c] s =1
      dmargin (@singleton_pyth_trace int) (discrete_gaussian c s).
  Proof.
    move=> y.
    have Hcenter : [tuple c] = [tuple of c :: [tuple]] :> 1.-tuple int.
      by apply: val_inj.
    rewrite Hcenter.
    rewrite (n_dg_shifted_cons_cat c [tuple] s y).
    rewrite dmarginE.
    apply: eq_in_dlet=> // x _ z.
    rewrite /= dlet_unit.
    have -> : cat_tuple [tuple x] [tuple] = singleton_pyth_trace x.
      by apply: val_inj.
    by [].
  Qed.

  Lemma n_dg_shifted_pythDist
      {n : nat} (centerL centerR : n.-tuple int)
      (stdev eps : R) :
    0 <= eps ->
    0 < stdev ->
    (forall i : 'I_n,
      finite_kl
        (discrete_gaussian (tnth centerL i) stdev)
        (discrete_gaussian (tnth centerR i) stdev) /\
      δ_KL
        (discrete_gaussian (tnth centerL i) stdev)
        (discrete_gaussian (tnth centerR i) stdev) <= eps) ->
    pythDist
      (n_dg_shifted centerL stdev)
      (n_dg_shifted centerR stdev)
      [tuple eps | i < n].
  Proof.
    elim: n centerL centerR=> [|n IH] centerL centerR Heps Hstdev Hcoord.
    - rewrite [centerL](tuple0 centerL) [centerR](tuple0 centerR) /=.
      apply: pythDist_refl.
      + by move=> i; case: i.
      exact: dunit_dweight.
    case: n IH centerL centerR Hcoord=> [IH0|n IH] centerL centerR Hcoord.
    - pose cL := thead centerL.
      pose cR := thead centerR.
      have HcenterL : centerL = [tuple cL].
        apply: eq_from_tnth=> i.
        rewrite [i]ord1 /cL /thead.
        by rewrite tnth0.
      have HcenterR : centerR = [tuple cR].
        apply: eq_from_tnth=> i.
        rewrite [i]ord1 /cR /thead.
        by rewrite tnth0.
      have [Hfin Hkl] :
          finite_kl (discrete_gaussian cL stdev)
            (discrete_gaussian cR stdev) /\
          δ_KL (discrete_gaussian cL stdev)
            (discrete_gaussian cR stdev) <= eps.
        exact: (Hcoord ord0).
      rewrite (mktuple_const_1 eps).
      apply: (pythDist_ext
        (dmargin (@singleton_pyth_trace int) (discrete_gaussian cL stdev))
        (n_dg_shifted centerL stdev)
        (dmargin (@singleton_pyth_trace int) (discrete_gaussian cR stdev))
        (n_dg_shifted centerR stdev)
        [tuple eps]).
      + move=> y; symmetry.
        rewrite HcenterL.
        exact: n_dg_shifted_singleton_pyth_trace.
      + move=> y; symmetry.
        rewrite HcenterR.
        exact: n_dg_shifted_singleton_pyth_trace.
      apply: pythDist_kl_singleton.
      + exact: Heps.
      + exact: Hfin.
      + by rewrite discrete_gaussian_mass1.
      + by rewrite discrete_gaussian_mass1.
      exact: Hkl.
    pose cL := thead centerL.
    pose tailL := behead_tuple centerL.
    pose cR := thead centerR.
    pose tailR := behead_tuple centerR.
    have HcenterL : centerL = [tuple of cL :: tailL].
      by rewrite (tuple_eta centerL).
    have HcenterR : centerR = [tuple of cR :: tailR].
      by rewrite (tuple_eta centerR).
    have HtailL i : tnth centerL (lift ord0 i) = tnth tailL i.
      by rewrite HcenterL tnthS.
    have HtailR i : tnth centerR (lift ord0 i) = tnth tailR i.
      by rewrite HcenterR tnthS.
    have [Hfin_head Hkl_head] :
        finite_kl (discrete_gaussian cL stdev)
          (discrete_gaussian cR stdev) /\
        δ_KL (discrete_gaussian cL stdev)
          (discrete_gaussian cR stdev) <= eps.
      exact: (Hcoord ord0).
    have Hhead :
        pythDist
          (dmargin (@singleton_pyth_trace int)
            (discrete_gaussian cL stdev))
          (dmargin (@singleton_pyth_trace int)
            (discrete_gaussian cR stdev))
          [tuple eps].
      apply: pythDist_kl_singleton.
      + exact: Heps.
      + exact: Hfin_head.
      + by rewrite discrete_gaussian_mass1.
      + by rewrite discrete_gaussian_mass1.
      exact: Hkl_head.
    have Htail :
        pythDist
          (n_dg_shifted tailL stdev)
          (n_dg_shifted tailR stdev)
          [tuple eps | i < n.+1].
      apply: IH=> // i.
      move: (Hcoord (lift ord0 i)).
      by rewrite HtailL HtailR.
    rewrite HcenterL HcenterR.
    rewrite -cat_tuple_singleton_const.
    apply: (pythDist_ext
      (\dlet_(omega0 <-
          dmargin (@singleton_pyth_trace int)
            (discrete_gaussian cL stdev))
       \dlet_(omega1 <- n_dg_shifted tailL stdev)
         dunit (cat_tuple omega0 omega1))
      (n_dg_shifted [tuple of cL :: tailL] stdev)
      (\dlet_(omega0 <-
          dmargin (@singleton_pyth_trace int)
            (discrete_gaussian cR stdev))
       \dlet_(omega1 <- n_dg_shifted tailR stdev)
         dunit (cat_tuple omega0 omega1))
      (n_dg_shifted [tuple of cR :: tailR] stdev)
      (cat_tuple [tuple eps] [tuple eps | i < n.+1])).
    - move=> y.
      rewrite (n_dg_shifted_cons_cat cL tailL stdev y).
      rewrite dmarginE __deprecated__dlet_dlet.
      apply: eq_in_dlet=> // x _ z.
      by rewrite dlet_unit /singleton_pyth_trace.
    - move=> y.
      rewrite (n_dg_shifted_cons_cat cR tailR stdev y).
      rewrite dmarginE __deprecated__dlet_dlet.
      apply: eq_in_dlet=> // x _ z.
      by rewrite dlet_unit /singleton_pyth_trace.
    exact: (pythDist_dlet_cat_const
      _ _ _ _ _ _ Hhead Htail).
  Qed.

  Lemma noise_flooding_vector_pythDist
      error_bound (centerL centerR : dim.-tuple int) :
    (ivec_dist centerL centerR <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    pythDist
      (n_dg_shifted centerL stdev)
      (n_dg_shifted centerR stdev)
      [tuple 1 / (2 * gaussian_width_multiplier ^+ 2) | i < dim].
  Proof.
    move=> Hdist stdev.
    apply: n_dg_shifted_pythDist.
    - exact: noise_flooding_coordinate_epsilon_nonnegative.
    - exact: noise_flooding_dg_stdev_pos.
    move=> i.
    exact: (noise_flooding_coordinate_kl error_bound centerL centerR i Hdist).
  Qed.

  Lemma noise_flooding_vector_kl_bound
      error_bound (centerL centerR : dim.-tuple int) :
    (ivec_dist centerL centerR <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    finite_kl
      (n_dg_shifted centerL stdev)
      (n_dg_shifted centerR stdev) /\
    δ_KL
      (n_dg_shifted centerL stdev)
      (n_dg_shifted centerR stdev) <=
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
  Proof.
    move=> Hdist stdev.
    have Hpyth :
        pythDist
          (n_dg_shifted centerL stdev)
          (n_dg_shifted centerR stdev)
          [tuple 1 / (2 * gaussian_width_multiplier ^+ 2) | i < dim].
      exact: (noise_flooding_vector_pythDist
        error_bound centerL centerR Hdist).
    split.
    - exact: (pythDist_finite_kl _ _ _ Hpyth).
    have Hbound := pythDist_kl_bound _ _ _ Hpyth.
    rewrite (eq_bigr
      (fun _ : 'I_dim =>
        1 / (2 * gaussian_width_multiplier ^+ 2)) _ ) in Hbound.
    - by rewrite noise_flooding_coordinate_epsilon_sum in Hbound.
    - move=> i _.
      by rewrite tnth_mktuple.
  Qed.

  Lemma shifted_tuple_gaussian_n_dg_shiftedE
      (center : dim.-tuple int) (stdev : R) :
    Metric.shifted_tuple_gaussian center stdev =1
    n_dg_shifted center stdev.
  Proof.
    move=> y.
    rewrite /Metric.shifted_tuple_gaussian
      /Metric.centered_tuple_gaussian /n_dg.
    exact: n_dg_shiftedE.
  Qed.

  Lemma inverse_isometry_shift_n_dg
      (centerL centerR : message) stdev :
    dmargin (fun v => inverse_isometry centerR v) (n_dg dim stdev) =1
    dmargin
      (fun v => inverse_isometry centerL
        (ivec_add v (isometry centerL centerR)))
      (n_dg dim stdev).
  Proof.
    move=> y.
    apply: dmargin_fun_ext=> v.
    exact: inverse_isometry_shift.
  Qed.

  Lemma inverse_isometry_shifted_gaussian_one_chart
      (centerL centerR : message) stdev :
    dmargin (fun v => inverse_isometry centerR v) (n_dg dim stdev) =1
    dmargin (fun v => inverse_isometry centerL v)
      (n_dg_shifted (isometry centerL centerR) stdev).
  Proof.
    move=> y.
    rewrite -(dmargin_ext
      (fun v => inverse_isometry centerL v)
      (dmargin (fun noise => ivec_add noise (isometry centerL centerR))
        (n_dg dim stdev))
      (n_dg_shifted (isometry centerL centerR) stdev)
      (n_dg_shiftedE (isometry centerL centerR) stdev) y).
    rewrite (dmargin_comp
      (fun v => inverse_isometry centerL v)
      (fun noise => ivec_add noise (isometry centerL centerR))
      (n_dg dim stdev) y).
    apply: dmargin_fun_ext=> v.
    exact: inverse_isometry_shift.
  Qed.

  Lemma n_dg_shifted_ivec_zeroE {n : nat} stdev :
    n_dg_shifted (ivec_zero : n.-tuple int) stdev =1
    n_dg n stdev.
  Proof.
    move=> y.
    rewrite -(n_dg_shiftedE (ivec_zero : n.-tuple int) stdev y).
    rewrite (dmargin_fun_ext
      (fun noise : n.-tuple int => ivec_add noise ivec_zero)
      (fun noise : n.-tuple int => noise)
      (n_dg n stdev) _ y); last
      exact: ivec_add0r.
    have Hid : injective (fun noise : n.-tuple int => noise) by [].
    exact: (dmargin_injectiveE
      (fun noise : n.-tuple int => noise) (n_dg n stdev) Hid y).
  Qed.

  Lemma noise_flooding_vector_pythDist_one_chart
      error_bound (centerL centerR : message) :
    (metric centerL centerR <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    pythDist
      (n_dg dim stdev)
      (n_dg_shifted (isometry centerL centerR) stdev)
      [tuple 1 / (2 * gaussian_width_multiplier ^+ 2) | i < dim].
  Proof.
    move=> Hmetric stdev.
    apply: (pythDist_ext
      (n_dg_shifted (ivec_zero : dim.-tuple int) stdev)
      (n_dg dim stdev)
      (n_dg_shifted (isometry centerL centerR) stdev)
      (n_dg_shifted (isometry centerL centerR) stdev)
      [tuple 1 / (2 * gaussian_width_multiplier ^+ 2) | i < dim]).
    - exact: n_dg_shifted_ivec_zeroE.
    - by [].
    apply: (noise_flooding_vector_pythDist
      error_bound (ivec_zero : dim.-tuple int)
      (isometry centerL centerR)).
    by rewrite -metric_chartE.
  Qed.

  Lemma noise_flooding_vector_kl_bound_one_chart
      error_bound (centerL centerR : message) :
    (metric centerL centerR <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    finite_kl
      (n_dg dim stdev)
      (n_dg_shifted (isometry centerL centerR) stdev) /\
    δ_KL
      (n_dg dim stdev)
      (n_dg_shifted (isometry centerL centerR) stdev) <=
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
  Proof.
    move=> Hmetric stdev.
    have Hpyth :
        pythDist
          (n_dg dim stdev)
          (n_dg_shifted (isometry centerL centerR) stdev)
          [tuple 1 / (2 * gaussian_width_multiplier ^+ 2) | i < dim].
      exact: (noise_flooding_vector_pythDist_one_chart
        error_bound centerL centerR Hmetric).
    split.
    - exact: (pythDist_finite_kl _ _ _ Hpyth).
    have Hbound := pythDist_kl_bound _ _ _ Hpyth.
    rewrite (eq_bigr
      (fun _ : 'I_dim =>
        1 / (2 * gaussian_width_multiplier ^+ 2)) _ ) in Hbound.
    - by rewrite noise_flooding_coordinate_epsilon_sum in Hbound.
    - move=> i _.
      by rewrite tnth_mktuple.
  Qed.

  Lemma scheme_decrypt_deterministic_dec_dunit sk c :
    decrypt sk c =1 dunit (deterministic_dec sk c).
  Proof.
    apply: pr_pred1_eq1_dunit.
    exact: deterministic_dec_correct.
  Qed.

  Lemma noise_flooding_decrypt_some_shifted
      sk data error_bound :
    let c : ciphertext := Some (data, error_bound) in
    NF.decrypt sk c =1
      dmargin
        (fun v => inverse_isometry (deterministic_dec sk c) v)
        (n_dg_shifted
          (isometry (deterministic_dec sk c) (deterministic_dec sk c))
          (noise_flooding_dg_stdev gaussian_width_multiplier error_bound)).
  Proof.
    move=> c y.
    rewrite /NF.decrypt /=.
    set stdev := noise_flooding_dg_stdev gaussian_width_multiplier error_bound.
    set center := deterministic_dec sk c.
    set center_vec := isometry center center.
    transitivity
      ((\dlet_(m <- dunit center)
        \dlet_(noise <- n_dg dim stdev)
          dunit (inverse_isometry m (ivec_add noise (isometry m m)))) y).
    - apply: eq_in_dlet.
      + by move=> m _ z.
      + exact: scheme_decrypt_deterministic_dec_dunit.
    rewrite dlet_unit.
    transitivity
      ((dmargin (fun v => inverse_isometry center v)
        (dmargin (fun noise => ivec_add noise center_vec)
          (n_dg dim stdev))) y).
    - rewrite !dmarginE __deprecated__dlet_dlet.
      apply: eq_in_dlet=> // noise _ z.
      by rewrite dlet_unit.
    apply: dmargin_ext.
    exact: n_dg_shiftedE.
  Qed.

  Module IndCpadGame := IndCpad NF.
  Module IndCpaDSim := IndCpadSimulator(Scheme)(Metric)(Params).

  Definition simulator_successful_decrypt_distribution
      (m : message) (error_bound : nat) : distr R message :=
    dmargin
      (fun noise =>
        inverse_isometry m
          (ivec_add (IndCpaDSim.toIntVec noise) (isometry m m)))
      (discrete_gaussians (IndCpaDSim.zeroChVec dim)
        (noise_flooding_dg_stdev gaussian_width_multiplier error_bound)).

  Lemma simulator_decrypt_noise_shifted m error_bound :
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    simulator_successful_decrypt_distribution m error_bound =1
    dmargin
      (fun v => inverse_isometry m v)
      (n_dg_shifted (isometry m m) stdev).
  Proof.
    move=> stdev y.
    set center_vec := isometry m m.
    transitivity
      ((dmargin
        (fun noise_vec : dim.-tuple int =>
          inverse_isometry m (ivec_add noise_vec center_vec))
        (dmargin (@IndCpaDSim.toIntVec dim)
          (discrete_gaussians (IndCpaDSim.zeroChVec dim) stdev))) y).
    - rewrite !dmarginE __deprecated__dlet_dlet.
      apply: eq_in_dlet=> // noise _ z.
      by rewrite dlet_unit.
    transitivity
      ((dmargin
        (fun noise_vec : dim.-tuple int =>
          inverse_isometry m (ivec_add noise_vec center_vec))
        (n_dg dim stdev)) y).
    - apply: dmargin_ext.
      exact: IndCpaDSim.dmargin_toIntVec_discrete_gaussians_zero.
    transitivity
      ((dmargin (fun v => inverse_isometry m v)
        (dmargin (fun noise_vec => ivec_add noise_vec center_vec)
          (n_dg dim stdev))) y).
    - rewrite !dmarginE __deprecated__dlet_dlet.
      apply: eq_in_dlet=> // noise_vec _ z.
      by rewrite dlet_unit.
    apply: dmargin_ext.
    exact: n_dg_shiftedE.
  Qed.

  Lemma noise_flooding_decrypt_some_centered
      sk data error_bound :
    let c : ciphertext := Some (data, error_bound) in
    NF.decrypt sk c =1
      dmargin
        (fun v => inverse_isometry (deterministic_dec sk c) v)
        (n_dg dim
          (noise_flooding_dg_stdev
            gaussian_width_multiplier error_bound)).
  Proof.
    move=> c y.
    rewrite (noise_flooding_decrypt_some_shifted sk data error_bound y).
    rewrite (isometry_center0 (deterministic_dec sk c)).
    apply: dmargin_ext.
    exact: n_dg_shifted_ivec_zeroE.
  Qed.

  Lemma simulator_decrypt_noise_centered m error_bound :
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    simulator_successful_decrypt_distribution m error_bound =1
    dmargin (fun v => inverse_isometry m v) (n_dg dim stdev).
  Proof.
    move=> stdev y.
    rewrite (simulator_decrypt_noise_shifted m error_bound y).
    rewrite (isometry_center0 m).
    apply: dmargin_ext.
    exact: n_dg_shifted_ivec_zeroE.
  Qed.

  Lemma simulator_decrypt_noise_one_chart
      (centerL centerR : message) error_bound :
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    simulator_successful_decrypt_distribution centerR error_bound =1
    dmargin (fun v => inverse_isometry centerL v)
      (n_dg_shifted (isometry centerL centerR) stdev).
  Proof.
    move=> stdev y.
    rewrite (simulator_decrypt_noise_centered centerR error_bound y).
    exact: (inverse_isometry_shifted_gaussian_one_chart
      centerL centerR stdev y).
  Qed.

  Lemma simulator_successful_decrypt_distribution_mass1 m error_bound :
    dweight (simulator_successful_decrypt_distribution m error_bound) = 1.
  Proof.
    rewrite (pr_ext
      (simulator_successful_decrypt_distribution m error_bound)
      (dmargin (fun v => inverse_isometry m v)
        (n_dg_shifted (isometry m m)
          (noise_flooding_dg_stdev
            gaussian_width_multiplier error_bound)))
      predT); last
      exact: simulator_decrypt_noise_shifted.
    rewrite dmargin_dweight.
    apply: n_dg_shifted_mass1.
    exact: noise_flooding_dg_stdev_pos.
  Qed.

  Lemma sampleRaw_ret_someE
      {T : choice_type} (D : {distr T / R}) mem :
    Pr_code
      (x ← sampleRaw D ;;
       ret (Some x))
      mem =1
    dmargin (fun x => (Some x, mem)) D.
  Proof.
    move=> out.
    rewrite Pr_code_bind.
    transitivity
      ((\dlet_(x_mem <- dmargin (fun x => (x, mem)) D)
          Pr_code (ret (Some x_mem.1)) x_mem.2) out).
    - apply: eq_in_dlet=> //.
      exact: sampleRawE.
    rewrite dmarginE __deprecated__dlet_dlet.
    apply: eq_in_dlet=> // x _ out'.
    by rewrite dlet_unit Pr_code_ret.
  Qed.

  Lemma sampleRaw_ext
      {T : choice_type} (D E : {distr T / R}) mem :
    D =1 E ->
    Pr_code (sampleRaw D) mem =1 Pr_code (sampleRaw E) mem.
  Proof.
    move=> HDE out.
    rewrite !sampleRawE.
    apply: dmargin_ext=> y.
    exact: HDE.
  Qed.

  Lemma sampleRaw_bind_retE
      {T U : choice_type} (D : {distr T / R}) (f : T -> U) mem :
    Pr_code
      (x ← sampleRaw D ;;
       ret (f x))
      mem =1
    Pr_code (sampleRaw (dmargin f D)) mem.
  Proof.
    move=> out.
    rewrite Pr_code_bind.
    transitivity
      ((\dlet_(x_mem <- Pr_code (sampleRaw D) mem)
        dunit (f x_mem.1, x_mem.2)) out).
    - apply: eq_in_dlet=> // x_mem _ out'.
      by rewrite Pr_code_ret.
    transitivity
      ((\dlet_(x_mem <- dmargin (fun x => (x, mem)) D)
        dunit (f x_mem.1, x_mem.2)) out).
    - apply: eq_in_dlet=> //.
      exact: sampleRawE.
    transitivity
      ((dmargin
        (fun x_mem : T * heap => (f x_mem.1, x_mem.2))
        (dmargin (fun x => (x, mem)) D)) out).
    - by rewrite dmarginE.
    rewrite (dmargin_comp
      (fun x_mem : T * heap => (f x_mem.1, x_mem.2))
      (fun x : T => (x, mem)) D out).
    rewrite sampleRawE.
    symmetry.
    exact: (dmargin_comp (fun y : U => (y, mem)) f D out).
  Qed.

  Lemma sampleRaw_dmargin_someE
      {T : choice_type} (D : {distr T / R}) mem :
    Pr_code (sampleRaw (dmargin (@Some T) D)) mem =1
    Pr_code
      (x ← sampleRaw D ;;
       ret (Some x))
      mem.
  Proof.
    move=> out.
    rewrite sampleRawE sampleRaw_ret_someE.
    exact: (dmargin_comp
      (fun y => (y, mem)) (@Some T) D out).
  Qed.

  Lemma noise_flooding_decrypt_some_codeE sk c mem :
    Pr_code
      (m <$ (message; NF.decrypt sk c) ;;
       ret (Some m))
      mem =1
    Pr_code
      (m' ← sampleRaw (NF.decrypt sk c) ;;
       ret (Some m'))
      mem.
  Proof.
    move=> out.
    by rewrite Pr_code_sample.
  Qed.

  Lemma simulator_successful_decrypt_some_codeE
      m error_bound mem :
    Pr_code
      (noise <$ (chVec chInt dim;
        discrete_gaussians (IndCpaDSim.zeroChVec dim)
          (noise_flooding_dg_stdev
            gaussian_width_multiplier error_bound)) ;;
       let res :=
         inverse_isometry m
           (ivec_add (IndCpaDSim.toIntVec noise) (isometry m m)) in
       ret (Some res))
      mem =1
    Pr_code
      (m' ← sampleRaw
        (simulator_successful_decrypt_distribution m error_bound) ;;
       ret (Some m'))
      mem.
  Proof.
    move=> out.
    rewrite Pr_code_sample.
    transitivity
      ((dmargin
        (fun noise =>
          (Some
            (inverse_isometry m
              (ivec_add (IndCpaDSim.toIntVec noise) (isometry m m))),
           mem))
        (discrete_gaussians (IndCpaDSim.zeroChVec dim)
          (noise_flooding_dg_stdev
            gaussian_width_multiplier error_bound))) out).
    - rewrite dmarginE.
      apply: eq_in_dlet=> // noise _ out'.
      by rewrite Pr_code_ret.
    rewrite (sampleRaw_ret_someE
      (simulator_successful_decrypt_distribution m error_bound) mem out).
    rewrite /simulator_successful_decrypt_distribution.
    symmetry.
    exact: (dmargin_comp
      (fun x => (Some x, mem))
      (fun noise =>
        inverse_isometry m
          (ivec_add (IndCpaDSim.toIntVec noise) (isometry m m)))
      (discrete_gaussians (IndCpaDSim.zeroChVec dim)
        (noise_flooding_dg_stdev
          gaussian_width_multiplier error_bound)) out).
  Qed.

  Lemma noise_flooding_decrypt_centered_codeE
      sk data error_bound mem :
    let c : ciphertext := Some (data, error_bound) in
    Pr_code
      (noise <$ (chVec chInt dim;
        discrete_gaussians (IndCpaDSim.zeroChVec dim)
          (noise_flooding_dg_stdev
            gaussian_width_multiplier error_bound)) ;;
       ret (inverse_isometry (deterministic_dec sk c)
         (IndCpaDSim.toIntVec noise)))
      mem =1
    Pr_code (sampleRaw (NF.decrypt sk c)) mem.
  Proof.
    move=> c out.
    set stdev := noise_flooding_dg_stdev
      gaussian_width_multiplier error_bound.
    set center := deterministic_dec sk c.
    rewrite Pr_code_sample.
    transitivity
      ((dmargin
        (fun noise =>
          (inverse_isometry center
            (IndCpaDSim.toIntVec noise), mem))
        (discrete_gaussians (IndCpaDSim.zeroChVec dim) stdev)) out).
    - rewrite dmarginE.
      apply: eq_in_dlet=> // noise _ out'.
      by rewrite Pr_code_ret.
    transitivity
      ((dmargin
        (fun v => (inverse_isometry center v, mem))
        (n_dg dim stdev)) out).
    - rewrite -(dmargin_comp
        (fun v => (inverse_isometry center v, mem))
        (@IndCpaDSim.toIntVec dim)
        (discrete_gaussians (IndCpaDSim.zeroChVec dim) stdev) out).
      apply: dmargin_ext.
      exact: IndCpaDSim.dmargin_toIntVec_discrete_gaussians_zero.
    rewrite sampleRawE.
    rewrite -(dmargin_comp
      (fun y => (y, mem))
      (fun v => inverse_isometry center v)
      (n_dg dim stdev) out).
    apply: dmargin_ext=> y.
    symmetry.
    rewrite /center /stdev.
    exact: noise_flooding_decrypt_some_centered.
  Qed.

  Lemma simulator_one_chart_codeE
      (centerL centerR : message) error_bound mem :
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    Pr_code
      (noise <$ (chVec chInt dim;
        discrete_gaussians (IndCpaDSim.zeroChVec dim) stdev) ;;
       ret (inverse_isometry centerL
         (ivec_add (IndCpaDSim.toIntVec noise)
           (isometry centerL centerR))))
      mem =1
    Pr_code
      (sampleRaw
        (simulator_successful_decrypt_distribution
          centerR error_bound))
      mem.
  Proof.
    move=> stdev out.
    set shift := isometry centerL centerR.
    rewrite Pr_code_sample.
    transitivity
      ((dmargin
        (fun noise =>
          (inverse_isometry centerL
            (ivec_add (IndCpaDSim.toIntVec noise) shift), mem))
        (discrete_gaussians (IndCpaDSim.zeroChVec dim) stdev)) out).
    - rewrite dmarginE.
      apply: eq_in_dlet=> // noise _ out'.
      by rewrite Pr_code_ret.
    transitivity
      ((dmargin
        (fun v =>
          (inverse_isometry centerL (ivec_add v shift), mem))
        (n_dg dim stdev)) out).
    - rewrite -(dmargin_comp
        (fun v =>
          (inverse_isometry centerL (ivec_add v shift), mem))
        (@IndCpaDSim.toIntVec dim)
        (discrete_gaussians (IndCpaDSim.zeroChVec dim) stdev) out).
      apply: dmargin_ext.
      exact: IndCpaDSim.dmargin_toIntVec_discrete_gaussians_zero.
    transitivity
      ((dmargin
        (fun y => (y, mem))
        (dmargin (fun v => inverse_isometry centerL v)
          (n_dg_shifted shift stdev))) out).
    - rewrite (dmargin_comp
        (fun y => (y, mem))
        (fun v => inverse_isometry centerL v)
        (n_dg_shifted shift stdev) out).
      rewrite -(dmargin_ext
        (fun v => (inverse_isometry centerL v, mem))
        (dmargin (fun noise => ivec_add noise shift)
          (n_dg dim stdev))
        (n_dg_shifted shift stdev)
        (n_dg_shiftedE shift stdev) out).
      rewrite (dmargin_comp
        (fun v => (inverse_isometry centerL v, mem))
        (fun noise => ivec_add noise shift)
        (n_dg dim stdev) out).
      by [].
    rewrite sampleRawE.
    apply: dmargin_ext=> y.
    symmetry.
    rewrite /shift.
    exact: simulator_decrypt_noise_one_chart.
  Qed.

  Lemma complete_output_heap_ext
      {out_t : choice_type} (D E : {distr (out_t * heap) / R}) :
    D =1 E ->
    complete_output_heap D =1 complete_output_heap E.
  Proof.
    move=> HDE out.
    rewrite /complete_output_heap.
    apply: complete_ext=> packed.
    exact: (dmargin_ext (@pack_output_heap out_t) D E HDE packed).
  Qed.

  Lemma pythJudgment_ext_true
      {ell : nat} {inL_t inR_t out_t : choice_type}
      (progL progL' : inL_t -> raw_code out_t)
      (progR progR' : inR_t -> raw_code out_t)
      (pre : pred ((inL_t * heap) * (inR_t * heap)))
      (s : (ell.+1).-tuple R) :
    (forall x mem, Pr_code (progL x) mem =1 Pr_code (progL' x) mem) ->
    (forall x mem, Pr_code (progR x) mem =1 Pr_code (progR' x) mem) ->
    ⊨Pyth ⦃ pre ⦄ progL ≈( s ) progR
      ⦃ fun _ : out_t * heap => true ⦄ ->
    ⊨Pyth ⦃ pre ⦄ progL' ≈( s ) progR'
      ⦃ fun _ : out_t * heap => true ⦄.
  Proof.
    move=> HextL HextR [Hs Hpyth].
    split; first exact: Hs.
    move=> memL memR xL xR Hpre.
    have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
      Hpyth memL memR xL xR Hpre.
    exists P, Q.
    split; first exact: Hdist.
    split.
    - move=> z.
      rewrite (HmarginL z).
      exact: (complete_output_heap_ext
        (Pr_code (progL xL) memL)
        (Pr_code (progL' xL) memL)
        (HextL xL memL) z).
    split.
    - move=> z.
      rewrite (HmarginR z).
      exact: (complete_output_heap_ext
        (Pr_code (progR xR) memR)
        (Pr_code (progR' xR) memR)
        (HextR xR memR) z).
    split; by move=> y Hy.
  Qed.

  Fixpoint toChIntVec {n : nat} : n.-tuple int -> chVec chInt n :=
    match n with
    | 0 => fun _ => tt
    | S n' => fun v =>
      (Z_of_int (thead v), toChIntVec (behead_tuple v))
    end.

  Lemma toIntVec_toChIntVec {n : nat} (v : n.-tuple int) :
    IndCpaDSim.toIntVec (toChIntVec v) = v.
  Proof.
    elim: n v=> [|n IH] v.
    - by rewrite [v](tuple0 v).
    rewrite /= IH Z_of_intK.
    by rewrite [RHS](tuple_eta v).
  Qed.

  Lemma toChIntVec_injective {n : nat} :
    injective (@toChIntVec n).
  Proof.
    move=> x y Hxy.
    by rewrite -(toIntVec_toChIntVec x) Hxy toIntVec_toChIntVec.
  Qed.

  Lemma noise_flooding_ch_vector_kl_bound_one_chart
      error_bound (centerL centerR : message) :
    (metric centerL centerR <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    finite_kl
      (dmargin (@toChIntVec dim) (n_dg dim stdev))
      (dmargin (@toChIntVec dim)
        (n_dg_shifted (isometry centerL centerR) stdev)) /\
    δ_KL
      (dmargin (@toChIntVec dim) (n_dg dim stdev))
      (dmargin (@toChIntVec dim)
        (n_dg_shifted (isometry centerL centerR) stdev)) <=
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
  Proof.
    move=> Hmetric stdev.
    have [Hfin Hkl] :=
      noise_flooding_vector_kl_bound_one_chart
        error_bound centerL centerR Hmetric.
    split.
    - exact: (finite_kl_dmargin_injective
        (@toChIntVec dim) _ _ toChIntVec_injective Hfin).
    rewrite (kl_dmargin_injective
      (@toChIntVec dim) _ _ toChIntVec_injective Hfin).
    exact: Hkl.
  Qed.

  Lemma noise_flooding_ch_vector_sample_pyth_one_chart
      error_bound (centerL centerR : message) :
    (metric centerL centerR <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    ⊨Pyth1 ⦃ fun inps =>
      let '((_, memL), (_, memR)) := inps in eq_op memL memR ⦄
      (fun _ : chUnit =>
        sampleRaw (dmargin (@toChIntVec dim) (n_dg dim stdev)))
      ≈( noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier )
      (fun _ : chUnit =>
        sampleRaw (dmargin (@toChIntVec dim)
          (n_dg_shifted (isometry centerL centerR) stdev)))
    ⦃ fun _ : chVec chInt dim * heap => true ⦄.
  Proof.
    move=> Hmetric stdev.
    have [Hfin Hkl] :=
      noise_flooding_ch_vector_kl_bound_one_chart
        error_bound centerL centerR Hmetric.
    apply: (klSampRule
      (fun _ : chUnit =>
        dmargin (@toChIntVec dim) (n_dg dim stdev))
      (fun _ : chUnit =>
        dmargin (@toChIntVec dim)
          (n_dg_shifted (isometry centerL centerR) stdev))
      (fun inps =>
        let '((_, memL), (_, memR)) := inps in eq_op memL memR)
      (fun _ : chVec chInt dim * heap => true)
      (noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier)).
    - exact: noise_flooding_per_query_epsilon_nonnegative.
    - by move=> memL memR [] [] /eqP.
    - by move=> [] [].
    - move=> [].
      rewrite dmargin_dweight.
      apply: n_dg_mass1.
      exact: noise_flooding_dg_stdev_pos.
    - move=> [].
      rewrite dmargin_dweight.
      apply: n_dg_shifted_mass1.
      exact: noise_flooding_dg_stdev_pos.
    - by move=> memL memR [] [] Hpre.
    - by move=> memL memR [] [] y Hpre Hy.
    - by move=> memL memR [] [] y Hpre Hy.
  Qed.

  Lemma noise_flooding_successful_decrypt_some_target_pyth_one_chart
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    (metric (deterministic_dec sk c) m <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    ⊨Pyth ⦃ fun inps =>
      let '((_, memL), (_, memR)) := inps in eq_op memL memR ⦄
      (fun _ : chUnit =>
        noise ← sampleRaw
          (dmargin (@toChIntVec dim) (n_dg dim stdev)) ;;
        ret (Some
          (inverse_isometry (deterministic_dec sk c) (IndCpaDSim.toIntVec noise))))
      ≈( cat_tuple
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] [tuple 0] )
      (fun _ : chUnit =>
        noise ← sampleRaw
          (dmargin (@toChIntVec dim)
            (n_dg_shifted (isometry (deterministic_dec sk c) m) stdev)) ;;
        ret (Some
          (inverse_isometry (deterministic_dec sk c) (IndCpaDSim.toIntVec noise))))
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    move=> c Hmetric stdev.
    set centerL := deterministic_dec sk c.
    apply: (pythAeSeqRule
      (fun _ : chUnit =>
        sampleRaw (dmargin (@toChIntVec dim) (n_dg dim stdev)))
      (fun _ : chUnit =>
        sampleRaw (dmargin (@toChIntVec dim)
          (n_dg_shifted (isometry centerL m) stdev)))
      (fun noise : chVec chInt dim =>
        ret (Some (inverse_isometry centerL
          (IndCpaDSim.toIntVec noise))))
      (fun inps =>
        let '((_, memL), (_, memR)) := inps in eq_op memL memR)
      (fun _ : chVec chInt dim * heap => true)
      (fun _ : chOption message * heap => true)
      [tuple noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier]).
    - rewrite /centerL /stdev.
      exact: (noise_flooding_ch_vector_sample_pyth_one_chart
        error_bound (deterministic_dec sk c) m Hmetric).
    - apply: hoareRetRule.
      by [].
  Qed.

  Lemma noise_flooding_decrypt_pushed_centered_some_codeE
      sk data error_bound mem :
    let c : ciphertext := Some (data, error_bound) in
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    Pr_code
      (noise ← sampleRaw
        (dmargin (@toChIntVec dim) (n_dg dim stdev)) ;;
       ret (Some
        (inverse_isometry (deterministic_dec sk c) (IndCpaDSim.toIntVec noise))))
      mem =1
    Pr_code
      (m' ← sampleRaw (NF.decrypt sk c) ;;
       ret (Some m'))
      mem.
  Proof.
    move=> c stdev out.
    set center := deterministic_dec sk c.
    rewrite (sampleRaw_bind_retE
      (dmargin (@toChIntVec dim) (n_dg dim stdev))
      (fun noise => Some
        (inverse_isometry center (IndCpaDSim.toIntVec noise)))
      mem out).
    rewrite sampleRawE.
    rewrite (dmargin_comp
      (fun y => (y, mem))
      (fun noise => Some
        (inverse_isometry center (IndCpaDSim.toIntVec noise)))
      (dmargin (@toChIntVec dim) (n_dg dim stdev)) out).
    rewrite (dmargin_comp
      (fun noise => (Some
        (inverse_isometry center (IndCpaDSim.toIntVec noise)), mem))
      (@toChIntVec dim) (n_dg dim stdev) out).
    transitivity
      ((dmargin
        (fun v => (Some (inverse_isometry center v), mem))
        (n_dg dim stdev)) out).
    - apply: dmargin_fun_ext=> v.
      by rewrite toIntVec_toChIntVec.
    rewrite (sampleRaw_ret_someE (NF.decrypt sk c) mem out).
    rewrite -(dmargin_comp
      (fun y => (Some y, mem))
      (fun v => inverse_isometry center v)
      (n_dg dim stdev) out).
    apply: dmargin_ext=> y.
    symmetry.
    rewrite /center /stdev.
    exact: noise_flooding_decrypt_some_centered.
  Qed.

  Lemma simulator_pushed_one_chart_some_codeE
      (centerL centerR : message) error_bound mem :
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    Pr_code
      (noise ← sampleRaw
        (dmargin (@toChIntVec dim)
          (n_dg_shifted (isometry centerL centerR) stdev)) ;;
       ret (Some
        (inverse_isometry centerL (IndCpaDSim.toIntVec noise))))
      mem =1
    Pr_code
      (m' ← sampleRaw
        (simulator_successful_decrypt_distribution
          centerR error_bound) ;;
       ret (Some m'))
      mem.
  Proof.
    move=> stdev out.
    set shift := isometry centerL centerR.
    rewrite (sampleRaw_bind_retE
      (dmargin (@toChIntVec dim)
        (n_dg_shifted shift stdev))
      (fun noise => Some
        (inverse_isometry centerL (IndCpaDSim.toIntVec noise)))
      mem out).
    rewrite sampleRawE.
    rewrite (dmargin_comp
      (fun y => (y, mem))
      (fun noise => Some
        (inverse_isometry centerL (IndCpaDSim.toIntVec noise)))
      (dmargin (@toChIntVec dim)
        (n_dg_shifted shift stdev)) out).
    rewrite (dmargin_comp
      (fun noise => (Some
        (inverse_isometry centerL (IndCpaDSim.toIntVec noise)), mem))
      (@toChIntVec dim) (n_dg_shifted shift stdev) out).
    transitivity
      ((dmargin
        (fun v => (Some (inverse_isometry centerL v), mem))
        (n_dg_shifted shift stdev)) out).
    - apply: dmargin_fun_ext=> v.
      by rewrite toIntVec_toChIntVec.
    rewrite (sampleRaw_ret_someE
      (simulator_successful_decrypt_distribution
        centerR error_bound) mem out).
    rewrite -(dmargin_comp
      (fun y => (Some y, mem))
      (fun v => inverse_isometry centerL v)
      (n_dg_shifted shift stdev) out).
    apply: dmargin_ext=> y.
    symmetry.
    rewrite /shift.
    exact: simulator_decrypt_noise_one_chart.
  Qed.

  Lemma noise_flooding_successful_decrypt_some_pyth_one_chart
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    (metric (deterministic_dec sk c) m <= error_bound)%N ->
    ⊨Pyth ⦃ fun inps =>
      let '((_, memL), (_, memR)) := inps in eq_op memL memR ⦄
      (fun _ : chUnit =>
        m' ← sampleRaw (NF.decrypt sk c) ;;
        ret (Some m'))
      ≈( cat_tuple
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] [tuple 0] )
      (fun _ : chUnit =>
        m' ← sampleRaw
          (simulator_successful_decrypt_distribution m error_bound) ;;
        ret (Some m'))
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    move=> c Hmetric.
    set stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound.
    apply: (pythJudgment_ext_true
      (fun _ : chUnit =>
        noise ← sampleRaw
          (dmargin (@toChIntVec dim) (n_dg dim stdev)) ;;
        ret (Some
          (inverse_isometry (deterministic_dec sk c) (IndCpaDSim.toIntVec noise))))
      (fun _ : chUnit =>
        m' ← sampleRaw (NF.decrypt sk c) ;;
        ret (Some m'))
      (fun _ : chUnit =>
        noise ← sampleRaw
          (dmargin (@toChIntVec dim)
            (n_dg_shifted (isometry (deterministic_dec sk c) m) stdev)) ;;
        ret (Some
          (inverse_isometry (deterministic_dec sk c) (IndCpaDSim.toIntVec noise))))
      (fun _ : chUnit =>
        m' ← sampleRaw
          (simulator_successful_decrypt_distribution m error_bound) ;;
        ret (Some m'))
      (fun inps =>
        let '((_, memL), (_, memR)) := inps in eq_op memL memR)
      (cat_tuple
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] [tuple 0])).
    - move=> [] mem.
      rewrite /stdev.
      exact: noise_flooding_decrypt_pushed_centered_some_codeE.
    - move=> [] mem.
      rewrite /stdev.
      exact: (simulator_pushed_one_chart_some_codeE
        (deterministic_dec sk c) m error_bound mem).
    rewrite /stdev.
    exact: (noise_flooding_successful_decrypt_some_target_pyth_one_chart
      sk data error_bound m Hmetric).
  Qed.

  Lemma noise_flooding_successful_decrypt_code_pyth_one_chart
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    (metric (deterministic_dec sk c) m <= error_bound)%N ->
    ⊨Pyth ⦃ fun inps =>
      let '((_, memL), (_, memR)) := inps in eq_op memL memR ⦄
      (fun _ : chUnit =>
        m' <$ (message; NF.decrypt sk c) ;;
        ret (Some m'))
      ≈( cat_tuple
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] [tuple 0] )
      (fun _ : chUnit =>
        noise <$ (chVec chInt dim;
          discrete_gaussians (IndCpaDSim.zeroChVec dim)
            (noise_flooding_dg_stdev
              gaussian_width_multiplier error_bound)) ;;
        let res :=
          inverse_isometry m
            (ivec_add (IndCpaDSim.toIntVec noise) (isometry m m)) in
        ret (Some res))
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    move=> c Hmetric.
    have Hpyth :=
      noise_flooding_successful_decrypt_some_pyth_one_chart
        sk data error_bound m Hmetric.
    move: Hpyth=> [Hs Hpyth].
    split; first exact: Hs.
    move=> memL memR [] [] Hpre.
    have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
      Hpyth memL memR tt tt Hpre.
    exists P, Q.
    split; first exact: Hdist.
    split.
    - move=> out.
      rewrite (HmarginL out).
      symmetry.
      apply: complete_output_heap_ext=> out'.
      exact: (noise_flooding_decrypt_some_codeE
        sk c memL out').
    split.
    - move=> out.
      rewrite (HmarginR out).
      symmetry.
      apply: complete_output_heap_ext=> out'.
      exact: (simulator_successful_decrypt_some_codeE
        m error_bound memR out').
    split.
    - move=> y Hy.
      by [].
    - move=> y Hy.
      by [].
  Qed.

  Lemma noise_flooding_successful_decrypt_code_pyth
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    (metric (deterministic_dec sk c) m <= error_bound)%N ->
    ⊨Pyth ⦃ fun inps =>
      let '((_, memL), (_, memR)) := inps in eq_op memL memR ⦄
      (fun _ : chUnit =>
        m' <$ (message; NF.decrypt sk c) ;;
        ret (Some m'))
      ≈( cat_tuple
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] [tuple 0] )
      (fun _ : chUnit =>
        noise <$ (chVec chInt dim;
          discrete_gaussians (IndCpaDSim.zeroChVec dim)
            (noise_flooding_dg_stdev
              gaussian_width_multiplier error_bound)) ;;
        let res :=
          inverse_isometry m
            (ivec_add (IndCpaDSim.toIntVec noise) (isometry m m)) in
        ret (Some res))
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    move=> c Hmetric.
    exact: (noise_flooding_successful_decrypt_code_pyth_one_chart
      sk data error_bound m Hmetric).
  Qed.

End NoiseFloodingSecureGaussianBasics.
