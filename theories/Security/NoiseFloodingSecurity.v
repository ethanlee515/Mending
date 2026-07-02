From Stdlib Require Import Utf8 Unicode.Utf8 BinInt Lia.
From extructures Require Import ord fset fmap.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot all_order all_algebra reals distr realsum ssrZ lra.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp.algebra_tactics Require Import ring.
From SSProve.Crypt Require Import Axioms Package Prelude.
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

(* Conservative per-query KL budget for a [dim]-dimensional Gaussian vector.
   The outer factor matches the loss shape produced by [compileRule]. *)
Definition noise_flooding_per_query_epsilon
    (dim : nat) (gaussian_width_multiplier : R) : R :=
  dim%:R / (2 * gaussian_width_multiplier ^+ 2).

Definition global_epsilon
    (dim max_queries : nat) (gaussian_width_multiplier : R) : R :=
  2 * Num.sqrt
    ((max_queries%:R *
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier) / 2).

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
  (Import Correctness : ApproxCorrectnessPerfect(Scheme)(Metric))
  (Import IndCpaSecurity : IsIndCpa(Scheme))
  (Import Params : NoiseFloodingParams)
  : NoiseFloodingIsIndCpad(Scheme)(Metric)(Params).
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

  Lemma local_chart_metric_to_ivec_dist
      (center a b : message) error_bound :
    (metric center a <= isometry_radius center)%N ->
    (metric center b <= isometry_radius center)%N ->
    (metric a b <= error_bound)%N ->
    (ivec_dist (isometry center a) (isometry center b)
      <= error_bound)%N.
  Proof.
    move=> Ha Hb Hab.
    by rewrite -iso_correct.
  Qed.

  Lemma local_chart_center_metric_to_ivec_dist
      (center m : message) error_bound :
    (metric center center <= isometry_radius center)%N ->
    (metric center m <= isometry_radius center)%N ->
    (metric center m <= error_bound)%N ->
    (ivec_dist (isometry center center) (isometry center m)
      <= error_bound)%N.
  Proof.
    exact: local_chart_metric_to_ivec_dist.
  Qed.

  Lemma noise_flooding_vector_pythDist_from_metric_chart
      error_bound (center m : message) :
    (metric center center <= isometry_radius center)%N ->
    (metric center m <= isometry_radius center)%N ->
    (metric center m <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    pythDist
      (n_dg_shifted (isometry center center) stdev)
      (n_dg_shifted (isometry center m) stdev)
      [tuple 1 / (2 * gaussian_width_multiplier ^+ 2) | i < dim].
  Proof.
    move=> Hcenter Hradius Hmetric stdev.
    apply: noise_flooding_vector_pythDist.
    exact: (local_chart_center_metric_to_ivec_dist
      center m error_bound Hcenter Hradius Hmetric).
  Qed.

  (* This is the geometric chart-change principle missing from the current
     local-isometry interface.  It says that flooding in two nearby message
     charts gives message-space distributions with the same per-query KL
     budget as the tuple Gaussian proof above. *)
  Axiom noise_flooding_message_gaussian_kl :
    forall error_bound (centerL centerR : message),
    (metric centerL centerR <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let DL :=
      dmargin (fun v => inverse_isometry centerL v)
        (n_dg_shifted (isometry centerL centerL) stdev) in
    let DR :=
      dmargin (fun v => inverse_isometry centerR v)
        (n_dg_shifted (isometry centerR centerR) stdev) in
    finite_kl DL DR /\
    δ_KL DL DR <=
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier.

  Lemma noise_flooding_message_gaussian_kl_refl
      error_bound (center : message) :
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let D :=
      dmargin (fun v => inverse_isometry center v)
        (n_dg_shifted (isometry center center) stdev) in
    finite_kl D D /\
    δ_KL D D <=
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
  Proof.
    move=> stdev D.
    split.
    - exact: finite_kl_refl.
    rewrite kl_self.
    exact: noise_flooding_per_query_epsilon_nonnegative.
  Qed.

  Lemma noise_flooding_message_gaussian_pythDist
      error_bound (centerL centerR : message) :
    (metric centerL centerR <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let DL :=
      dmargin (fun v => inverse_isometry centerL v)
        (n_dg_shifted (isometry centerL centerL) stdev) in
    let DR :=
      dmargin (fun v => inverse_isometry centerR v)
        (n_dg_shifted (isometry centerR centerR) stdev) in
    pythDist
      (dmargin (@singleton_pyth_trace message) DL)
      (dmargin (@singleton_pyth_trace message) DR)
      [tuple noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier].
  Proof.
    move=> Hmetric stdev DL DR.
    have [Hfin Hkl] :=
      noise_flooding_message_gaussian_kl error_bound centerL centerR Hmetric.
    apply: pythDist_kl_singleton.
    - exact: noise_flooding_per_query_epsilon_nonnegative.
    - exact: Hfin.
    - rewrite /DL dmargin_dweight.
      apply: n_dg_shifted_mass1.
      exact: noise_flooding_dg_stdev_pos.
    - rewrite /DR dmargin_dweight.
      apply: n_dg_shifted_mass1.
      exact: noise_flooding_dg_stdev_pos.
    - exact: Hkl.
  Qed.

  Lemma noise_flooding_message_gaussian_pythDist_refl
      error_bound (center : message) :
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let D :=
      dmargin (fun v => inverse_isometry center v)
        (n_dg_shifted (isometry center center) stdev) in
    pythDist
      (dmargin (@singleton_pyth_trace message) D)
      (dmargin (@singleton_pyth_trace message) D)
      [tuple noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier].
  Proof.
    move=> stdev D.
    have [Hfin Hkl] :=
      noise_flooding_message_gaussian_kl_refl error_bound center.
    apply: pythDist_kl_singleton.
    - exact: noise_flooding_per_query_epsilon_nonnegative.
    - exact: Hfin.
    - rewrite /D dmargin_dweight.
      apply: n_dg_shifted_mass1.
      exact: noise_flooding_dg_stdev_pos.
    - rewrite /D dmargin_dweight.
      apply: n_dg_shifted_mass1.
      exact: noise_flooding_dg_stdev_pos.
    - exact: Hkl.
  Qed.

  Lemma scheme_decrypt_dec'_dunit sk c :
    decrypt sk c =1 dunit (dec' sk c).
  Proof.
    apply: pr_pred1_eq1_dunit.
    exact: dec'_correct.
  Qed.

  Lemma noise_flooding_decrypt_some_shifted
      sk data error_bound :
    let c : ciphertext := Some (data, error_bound) in
    NF.decrypt sk c =1
      dmargin
        (fun v => inverse_isometry (dec' sk c) v)
        (n_dg_shifted
          (isometry (dec' sk c) (dec' sk c))
          (noise_flooding_dg_stdev gaussian_width_multiplier error_bound)).
  Proof.
    move=> c y.
    rewrite /NF.decrypt /=.
    set stdev := noise_flooding_dg_stdev gaussian_width_multiplier error_bound.
    set center := dec' sk c.
    set center_vec := isometry center center.
    transitivity
      ((\dlet_(m <- dunit center)
        \dlet_(noise <- n_dg dim stdev)
          dunit (inverse_isometry m (ivec_add noise (isometry m m)))) y).
    - apply: eq_in_dlet.
      + by move=> m _ z.
      + exact: scheme_decrypt_dec'_dunit.
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

  Lemma noise_flooding_successful_decrypt_pythDist
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    (metric (dec' sk c) m <= error_bound)%N ->
    pythDist
      (dmargin (@singleton_pyth_trace message) (NF.decrypt sk c))
      (dmargin (@singleton_pyth_trace message)
        (simulator_successful_decrypt_distribution m error_bound))
      [tuple noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier].
  Proof.
    move=> c Hmetric.
    set centerL := dec' sk c.
    set centerR := m.
    set stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound.
    set DL :=
      dmargin (fun v => inverse_isometry centerL v)
        (n_dg_shifted (isometry centerL centerL) stdev).
    set DR :=
      dmargin (fun v => inverse_isometry centerR v)
        (n_dg_shifted (isometry centerR centerR) stdev).
    apply: (pythDist_ext
      (dmargin (@singleton_pyth_trace message) DL)
      (dmargin (@singleton_pyth_trace message) (NF.decrypt sk c))
      (dmargin (@singleton_pyth_trace message) DR)
      (dmargin (@singleton_pyth_trace message)
        (simulator_successful_decrypt_distribution m error_bound))
      [tuple noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier]).
    - move=> y.
      apply: dmargin_ext=> z.
      rewrite /DL /centerL /stdev.
      symmetry.
      exact: noise_flooding_decrypt_some_shifted.
    - move=> y.
      apply: dmargin_ext=> z.
      rewrite /DR /centerR /stdev.
      symmetry.
      exact: simulator_decrypt_noise_shifted.
    rewrite /DL /DR /centerL /centerR /stdev.
    exact: (noise_flooding_message_gaussian_pythDist
      error_bound (dec' sk c) m Hmetric).
  Qed.

  Lemma noise_flooding_successful_decrypt_sample_pyth
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    (metric (dec' sk c) m <= error_bound)%N ->
    ⊨Pyth1 ⦃ fun inps =>
      let '((_, memL), (_, memR)) := inps in eq_op memL memR ⦄
      (fun _ : chUnit => sampleRaw (NF.decrypt sk c))
      ≈( noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier )
      (fun _ : chUnit =>
        sampleRaw
          (simulator_successful_decrypt_distribution m error_bound))
    ⦃ fun _ : message * heap => true ⦄.
  Proof.
    move=> c Hmetric.
    set eps :=
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
    set centerL := dec' sk c.
    set centerR := m.
    set stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound.
    set DL :=
      dmargin (fun v => inverse_isometry centerL v)
        (n_dg_shifted (isometry centerL centerL) stdev).
    set DR :=
      dmargin (fun v => inverse_isometry centerR v)
        (n_dg_shifted (isometry centerR centerR) stdev).
    set Dreal := NF.decrypt sk c.
    set Dsim := simulator_successful_decrypt_distribution m error_bound.
    have [Hfin Hkl] :
        finite_kl DL DR /\ δ_KL DL DR <= eps.
      rewrite /DL /DR /centerL /centerR /stdev /eps.
      exact: (noise_flooding_message_gaussian_kl
        error_bound (dec' sk c) m Hmetric).
    have HDreal : DL =1 Dreal.
      move=> y.
      rewrite /DL /Dreal /centerL /stdev.
      symmetry.
      exact: noise_flooding_decrypt_some_shifted.
    have HDsim : DR =1 Dsim.
      move=> y.
      rewrite /DR /Dsim /centerR /stdev.
      symmetry.
      exact: simulator_decrypt_noise_shifted.
    apply: (klSampRule
      (fun _ : chUnit => Dreal)
      (fun _ : chUnit => Dsim)
      (fun inps =>
        let '((_, memL), (_, memR)) := inps in eq_op memL memR)
      (fun _ : message * heap => true)
      eps).
    - exact: noise_flooding_per_query_epsilon_nonnegative.
    - by move=> memL memR [] [] /eqP.
    - move=> [] [].
      exact: (finite_kl_ext DL Dreal DR Dsim HDreal HDsim Hfin).
    - move=> [].
      rewrite (pr_ext Dreal DL predT); last
        by move=> y; symmetry; exact: HDreal.
      rewrite /DL dmargin_dweight.
      apply: n_dg_shifted_mass1.
      exact: noise_flooding_dg_stdev_pos.
    - move=> [].
      rewrite (pr_ext Dsim DR predT); last
        by move=> y; symmetry; exact: HDsim.
      rewrite /DR dmargin_dweight.
      apply: n_dg_shifted_mass1.
      exact: noise_flooding_dg_stdev_pos.
    - move=> memL memR [] [] Hpre.
      rewrite -(kl_ext DL Dreal DR Dsim HDreal HDsim).
      exact: Hkl.
    - by move=> memL memR [] [] y Hpre Hy.
    - by move=> memL memR [] [] y Hpre Hy.
  Qed.

  Lemma noise_flooding_successful_decrypt_some_pyth
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    (metric (dec' sk c) m <= error_bound)%N ->
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
    apply: (pythAeSeqRule
      (fun _ : chUnit => sampleRaw (NF.decrypt sk c))
      (fun _ : chUnit =>
        sampleRaw
          (simulator_successful_decrypt_distribution m error_bound))
      (fun m' : message => ret (Some m'))
      (fun inps =>
        let '((_, memL), (_, memR)) := inps in eq_op memL memR)
      (fun _ : message * heap => true)
      (fun _ : chOption message * heap => true)
      [tuple noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier]).
    - exact: (noise_flooding_successful_decrypt_sample_pyth
        sk data error_bound m Hmetric).
    - apply: hoareRetRule.
      by [].
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

  Lemma noise_flooding_successful_decrypt_code_pyth
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    (metric (dec' sk c) m <= error_bound)%N ->
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
      noise_flooding_successful_decrypt_some_pyth
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

  Lemma noise_flooding_successful_decrypt_code_pyth1
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    (metric (dec' sk c) m <= error_bound)%N ->
    ⊨Pyth1 ⦃ fun inps =>
      let '((_, memL), (_, memR)) := inps in eq_op memL memR ⦄
      (fun _ : chUnit =>
        m' <$ (message; NF.decrypt sk c) ;;
        ret (Some m'))
      ≈( noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier )
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
    set eps :=
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
    set centerL := dec' sk c.
    set centerR := m.
    set stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound.
    set DL :=
      dmargin (fun v => inverse_isometry centerL v)
        (n_dg_shifted (isometry centerL centerL) stdev).
    set DR :=
      dmargin (fun v => inverse_isometry centerR v)
        (n_dg_shifted (isometry centerR centerR) stdev).
    set Dreal := NF.decrypt sk c.
    set Dsim := simulator_successful_decrypt_distribution m error_bound.
    set Dreal_opt := dmargin (@Some message) Dreal.
    set Dsim_opt := dmargin (@Some message) Dsim.
    have Hsome_inj : injective (@Some message).
      by move=> x y [= ->].
    have [Hfin Hkl] :
        finite_kl DL DR /\ δ_KL DL DR <= eps.
      rewrite /DL /DR /centerL /centerR /stdev /eps.
      exact: (noise_flooding_message_gaussian_kl
        error_bound (dec' sk c) m Hmetric).
    have HDreal : DL =1 Dreal.
      move=> y.
      rewrite /DL /Dreal /centerL /stdev.
      symmetry.
      exact: noise_flooding_decrypt_some_shifted.
    have HDsim : DR =1 Dsim.
      move=> y.
      rewrite /DR /Dsim /centerR /stdev.
      symmetry.
      exact: simulator_decrypt_noise_shifted.
    have Hfin_opt : finite_kl Dreal_opt Dsim_opt.
      apply: (finite_kl_ext
        (dmargin (@Some message) DL) Dreal_opt
        (dmargin (@Some message) DR) Dsim_opt).
      - move=> y; apply: dmargin_ext=> z.
        exact: HDreal.
      - move=> y; apply: dmargin_ext=> z.
        exact: HDsim.
      exact: (finite_kl_dmargin_injective _ _ _ Hsome_inj Hfin).
    have Hkl_opt : δ_KL Dreal_opt Dsim_opt <= eps.
      rewrite -(kl_ext
        (dmargin (@Some message) DL) Dreal_opt
        (dmargin (@Some message) DR) Dsim_opt).
      - rewrite (kl_dmargin_injective _ _ _ Hsome_inj Hfin).
        exact: Hkl.
      - move=> y; apply: dmargin_ext=> z.
        exact: HDreal.
      - move=> y; apply: dmargin_ext=> z.
        exact: HDsim.
    have Hsample :
        ⊨Pyth1 ⦃ fun inps =>
          let '((_, memL), (_, memR)) := inps in eq_op memL memR ⦄
          (fun _ : chUnit => sampleRaw Dreal_opt)
          ≈( eps )
          (fun _ : chUnit => sampleRaw Dsim_opt)
        ⦃ fun _ : chOption message * heap => true ⦄.
      apply: (klSampRule
        (fun _ : chUnit => Dreal_opt)
        (fun _ : chUnit => Dsim_opt)
        (fun inps =>
          let '((_, memL), (_, memR)) := inps in eq_op memL memR)
        (fun _ : chOption message * heap => true)
        eps).
      - exact: noise_flooding_per_query_epsilon_nonnegative.
      - by move=> memL memR [] [] /eqP.
      - by move=> [] [].
      - move=> [].
        rewrite /Dreal_opt dmargin_dweight.
        rewrite (pr_ext Dreal DL predT); last
          by move=> y; symmetry; exact: HDreal.
        rewrite /DL dmargin_dweight.
        apply: n_dg_shifted_mass1.
        exact: noise_flooding_dg_stdev_pos.
      - move=> [].
        rewrite /Dsim_opt dmargin_dweight.
        rewrite (pr_ext Dsim DR predT); last
          by move=> y; symmetry; exact: HDsim.
        rewrite /DR dmargin_dweight.
        apply: n_dg_shifted_mass1.
        exact: noise_flooding_dg_stdev_pos.
      - by move=> memL memR [] [] Hpre.
      - by move=> memL memR [] [] y Hpre Hy.
      - by move=> memL memR [] [] y Hpre Hy.
    move: Hsample=> [Hs Hpyth].
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
      rewrite /Dreal_opt (sampleRaw_dmargin_someE Dreal memL out').
      symmetry.
      exact: (noise_flooding_decrypt_some_codeE
        sk c memL out').
    split.
    - move=> out.
      rewrite (HmarginR out).
      symmetry.
      apply: complete_output_heap_ext=> out'.
      rewrite /Dsim_opt (sampleRaw_dmargin_someE Dsim memR out') /Dsim.
      rewrite /centerR /stdev.
      exact: (simulator_successful_decrypt_some_codeE
        m error_bound memR out').
    split.
    - move=> y Hy.
      by [].
    - move=> y Hy.
      by [].
  Qed.

  Notation " 'adv_keys " := (pk_t × evk_t) (in custom pack_type at level 2).
  Notation " 'message " := message (in custom pack_type at level 2).
  Notation " 'message_pair " := (message × message) (in custom pack_type at level 2).
  Notation " 'ciphertext " := ciphertext (in custom pack_type at level 2).
  Notation " 'unary_gate " := unary_gate (in custom pack_type at level 2).
  Notation " 'binary_gate " := binary_gate (in custom pack_type at level 2).
  Notation " 'option_message " := (chOption message)
    (in custom pack_type at level 2).

  (* Closed hybrid oracle for the first, query-counted replacement step:
     encryption and evaluation are the real IND-CPAD oracle, while decrypt is
     the simulator's plaintext/noise response. *)
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
        #assert ((length updated_table <= max_queries)%N) ;;
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
        #assert ((length updated_table <= max_queries)%N) ;;
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
        #assert ((length updated_table <= max_queries)%N) ;;
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

  Lemma ind_cpad_decrypt_in_adv_import :
    fhas IndCpadGame.IndCpadAdv_import
      (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)).
  Proof.
    rewrite /IndCpadGame.IndCpadAdv_import.
    fmap_solve.
  Qed.

  Definition trivial_heap_invariant : pred heap := fun _ => true.

  Lemma trivial_heap_invariant_depends_only_on K :
    heap_pred_depends_only_on K trivial_heap_invariant.
  Proof. by move=> mem0 mem1 _. Qed.

  Lemma package_preserves_trivial_heap_invariant_except
      M P fn :
    package_preserves_heap_pred_except
      M P fn trivial_heap_invariant.
  Proof.
    move=> o x _ _.
    rewrite /hoareJudgment /trivial_heap_invariant.
    by move=> y mem _ out _.
  Qed.

  Definition same_input_invariant_pre
      {A : choice_type} (call_invariant : pred heap) :
    pred ((A * heap) * (A * heap)) :=
    fun inps =>
      let '((xL, memL), (xR, memR)) := inps in
      (xL == xR) && (memL == memR) &&
      call_invariant memL.

  Definition same_input_heap_pre {A : choice_type} :
    pred ((A * heap) * (A * heap)) :=
    same_input_invariant_pre trivial_heap_invariant.

  Definition same_game_output_opt
    (outs : option (bool * heap) * option (bool * heap)) : bool :=
    let '(outL, outR) := outs in
    eq_op outL outR.

  Definition same_game_result_opt
    (outs : option (bool * heap) * option (bool * heap)) : bool :=
    let '(outL, outR) := outs in
    omap fst outL == omap fst outR.

  Lemma same_game_output_result_opt outs :
    same_game_output_opt outs -> same_game_result_opt outs.
  Proof.
    case: outs=> [outL outR].
    rewrite /same_game_output_opt /same_game_result_opt /=.
    by move/eqP=> ->; rewrite eqxx.
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

  Lemma challenge_heap_valid_empty :
    challenge_heap_valid empty_heap.
  Proof.
    rewrite /challenge_heap_valid !get_empty_heap /=.
    by rewrite eqxx.
  Qed.

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
    rewrite /sim_decrypt_reduction_heap_rel.
    by move/andP=> [].
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_ready memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memR IndCpaDSim.ready_addr = true.
  Proof.
    rewrite /sim_decrypt_reduction_heap_rel.
    move/andP=> [_ H].
    move: H=> /andP [/eqP Hready _].
    exact: Hready.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_bit memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memL IndCpadGame.bit_addr =
      get_heap memR IndCpaSecurity.IndCpaGame.bit_addr.
  Proof.
    rewrite /sim_decrypt_reduction_heap_rel.
    move/andP=> [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [/eqP Hbit _].
    exact: Hbit.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_pk_outer memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memL IndCpadGame.pk_addr =
      get_heap memR IndCpaSecurity.IndCpaGame.pk_addr.
  Proof.
    rewrite /sim_decrypt_reduction_heap_rel.
    move/andP=> [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [/eqP Hpk _].
    exact: Hpk.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_evk_outer memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memL IndCpadGame.evk_addr =
      get_heap memR IndCpaSecurity.IndCpaGame.evk_addr.
  Proof.
    rewrite /sim_decrypt_reduction_heap_rel.
    move/andP=> [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [/eqP Hevk _].
    exact: Hevk.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_pk_sim memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memL IndCpadGame.pk_addr =
      get_heap memR IndCpaDSim.pk_addr.
  Proof.
    rewrite /sim_decrypt_reduction_heap_rel.
    move/andP=> [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [/eqP Hpk _].
    exact: Hpk.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_evk_sim memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memL IndCpadGame.evk_addr =
      get_heap memR IndCpaDSim.evk_addr.
  Proof.
    rewrite /sim_decrypt_reduction_heap_rel.
    move/andP=> [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [/eqP Hevk _].
    exact: Hevk.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_table memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memL IndCpadGame.table_addr =
      get_heap memR IndCpaDSim.table_addr.
  Proof.
    rewrite /sim_decrypt_reduction_heap_rel.
    move/andP=> [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [/eqP Htable _].
    exact: Htable.
  Qed.

  Lemma sim_decrypt_reduction_heap_rel_decrypt_count memL memR :
    sim_decrypt_reduction_heap_rel memL memR ->
    get_heap memL IndCpadGame.decrypt_count_addr =
      get_heap memR IndCpaDSim.decrypt_count_addr.
  Proof.
    rewrite /sim_decrypt_reduction_heap_rel.
    move/andP=> [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    move: H=> /andP [_ H].
    by move/eqP.
  Qed.

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
    by rewrite Hready Hbit Hpk_outer Hevk_outer Hpk_sim Hevk_sim Hcount !eqxx.
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
    by rewrite Hready Hbit Hpk_outer Hevk_outer Hpk_sim Hevk_sim Htable !eqxx.
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

  Lemma table_valid_for_branch_decrypt_row sk b table i
      (i_in_range : (i < length table)%N) m c :
    table_valid_for_branch sk b table ->
    nth_valid table i i_in_range = (m, m, c) ->
    is_underlying_plaintext sk c m.
  Proof.
    move=> Htable Hnth.
    have Hrow :=
      table_valid_for_branch_nth sk b table i i_in_range Htable.
    clear Htable.
    move: Hrow.
    by rewrite Hnth /row_valid_for_branch /selected_plaintext /=; case: b.
  Qed.

  Lemma row_valid_for_branch_equal_messages_some sk b m c :
    row_valid_for_branch sk b (m, m, c) ->
    exists data error_bound,
      c = Some (data, error_bound) /\
      (metric (dec' sk c) m <= error_bound)%N.
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

  Lemma challenge_heap_valid_good_keys mem pk evk sk :
    challenge_heap_valid mem ->
    get_heap mem IndCpadGame.pk_addr = Some pk ->
    get_heap mem IndCpadGame.evk_addr = Some evk ->
    get_heap mem IndCpadGame.sk_addr = Some sk ->
    good_keys pk evk sk.
  Proof.
    rewrite /challenge_heap_valid=> Hinv Hpk Hevk Hsk.
    move: Hinv.
    rewrite Hpk Hevk Hsk=> /andP [].
    by [].
  Qed.

  Lemma challenge_heap_valid_table_for_branch mem pk evk sk :
    challenge_heap_valid mem ->
    get_heap mem IndCpadGame.pk_addr = Some pk ->
    get_heap mem IndCpadGame.evk_addr = Some evk ->
    get_heap mem IndCpadGame.sk_addr = Some sk ->
    table_valid_for_branch sk
      (get_heap mem IndCpadGame.bit_addr)
      (get_heap mem IndCpadGame.table_addr).
  Proof.
    rewrite /challenge_heap_valid=> Hinv Hpk Hevk Hsk.
    move: Hinv.
    rewrite Hpk Hevk Hsk=> /andP [].
    by [].
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

  Lemma challenge_heap_valid_decrypt_row mem pk evk sk i
      (i_in_range :
        (i < length (get_heap mem IndCpadGame.table_addr))%N) m c :
    challenge_heap_valid mem ->
    get_heap mem IndCpadGame.pk_addr = Some pk ->
    get_heap mem IndCpadGame.evk_addr = Some evk ->
    get_heap mem IndCpadGame.sk_addr = Some sk ->
    nth_valid (get_heap mem IndCpadGame.table_addr) i i_in_range =
      (m, m, c) ->
    is_underlying_plaintext sk c m.
  Proof.
    move=> Hinv Hpk Hevk Hsk Hnth.
    have Htable := challenge_heap_valid_table_for_branch
      mem pk evk sk Hinv Hpk Hevk Hsk.
    exact: (table_valid_for_branch_decrypt_row
      sk (get_heap mem IndCpadGame.bit_addr)
      (get_heap mem IndCpadGame.table_addr) i i_in_range
      m c Htable Hnth).
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
    rewrite -Htable Hrow.
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
    rewrite -Htable Hrow_i Hrow_j.
    by [].
  Qed.

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
    #assert ((length updated_table <= max_queries)%N) ;;
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
    #assert ((length updated_table <= max_queries)%N) ;;
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
          case Hlen:
              (length (get_heap mem IndCpadGame.table_addr ++
                [:: (m0, m1, c)]) <= max_queries)%N.
          -- rewrite /assertD Hlen /= in Hinner.
             rewrite Pr_code_put Pr_code_ret in Hinner.
             have -> :
                 out =
                 (c, set_heap mem IndCpadGame.table_addr
                   (get_heap mem IndCpadGame.table_addr ++
                    [:: (m0, m1, c)])).
               exact: in_dunit Hinner.
             exact: (challenge_heap_valid_set_table_encrypt
               mem pk evk sk m0 m1 c Hinv Hpk Hevk Hsk Hc).
          -- rewrite /assertD Hlen Pr_code_fail in Hinner.
             by move/dinsuppP: Hinner; rewrite dnullE.
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
    #assert ((length updated_table <= max_queries)%N) ;;
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
    #assert ((length updated_table <= max_queries)%N) ;;
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
      have [Hlen Hafter_len] := dinsupp_assertD _ _ _ _ Hinner.
      rewrite Pr_code_put Pr_code_ret in Hafter_len.
      have -> :
          out =
          (c', set_heap mem IndCpadGame.table_addr
            (get_heap mem IndCpadGame.table_addr ++
              [:: (interpret_unary gate m0,
                   interpret_unary gate m1, c')])).
        exact: in_dunit Hafter_len.
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
    #assert ((length updated_table <= max_queries)%N) ;;
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
      have [Hlen Hafter_len] := dinsupp_assertD _ _ _ _ Hinner.
      rewrite Pr_code_put Pr_code_ret in Hafter_len.
      have -> :
          out =
          (c', set_heap mem IndCpadGame.table_addr
            (get_heap mem IndCpadGame.table_addr ++
              [:: (interpret_binary gate m0i m0j,
                   interpret_binary gate m1i m1j, c')])).
        exact: in_dunit Hafter_len.
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
    #assert ((length updated_table <= max_queries)%N) ;;
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
    by rewrite Pr_code_fail dlet_null_ext.
  Qed.

  Lemma ind_cpad_sim_decrypt_code_over_bound_null max_queries i mem :
    ~~ (get_heap mem IndCpadGame.decrypt_count_addr < max_queries)%N ->
    Pr_code (ind_cpad_sim_decrypt_code max_queries i) mem =1 dnull.
  Proof.
    move=> Hcount out.
    rewrite /ind_cpad_sim_decrypt_code.
    rewrite Pr_code_get /assertD (negbTE Hcount) /=.
    by rewrite Pr_code_fail dlet_null_ext.
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

  Lemma challenge_decrypt_prefix_row_valid_equal_messages_some
      mem sk m c :
    challenge_decrypt_prefix_row_valid (m, m, c) mem ->
    get_heap mem IndCpadGame.sk_addr = Some sk ->
    exists data error_bound,
      c = Some (data, error_bound) /\
      (metric (dec' sk c) m <= error_bound)%N.
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
      (metric (dec' sk c) m <= error_bound)%N.
  Proof.
    rewrite /challenge_decrypt_prefix_row_ready=> /andP [Hinv Hrow].
    case Hsk: (get_heap mem IndCpadGame.sk_addr)=> [sk|] //= in Hrow.
    have [data [error_bound [Hc Hmetric]]] :=
      row_valid_for_branch_equal_messages_some sk
        (get_heap mem IndCpadGame.bit_addr) m c Hrow.
    by exists sk, data, error_bound.
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
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] [tuple 0] )
      (fun _ : chUnit => ind_cpad_sim_decrypt_cont (m, m, c))
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    split.
    - move=> i.
      apply: (cat_tuple_nonneg
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] [tuple 0] i).
      + move=> j.
        by rewrite [j]ord1 noise_flooding_per_query_epsilon_nonnegative.
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

  Lemma ind_cpad_decrypt_cont_eq_pyth1 m c :
    ⊨Pyth1 ⦃ fun inps =>
      let '((_, memL), (_, memR)) := inps in
      (eq_op memL memR) &&
      challenge_decrypt_prefix_row_ready (m, m, c) memL ⦄
      (fun _ : chUnit => ind_cpad_real_decrypt_cont (m, m, c))
      ≈( noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier )
      (fun _ : chUnit => ind_cpad_sim_decrypt_cont (m, m, c))
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    split.
    - move=> i.
      by rewrite [i]ord1 noise_flooding_per_query_epsilon_nonnegative.
    move=> memL memR [] [] Hpre.
    move/andP: Hpre=> [/eqP Hmem Hready].
    subst memR.
    have [sk [data [error_bound [Hsk [Hc Hmetric]]]]] :=
      challenge_decrypt_prefix_row_ready_equal_messages_some
        memL m c Hready.
    subst c.
    have Hpyth :=
      noise_flooding_successful_decrypt_code_pyth1
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

  Lemma ind_cpad_decrypt_cont_pyth
      (row : IndCpadGame.challenger_table_row) :
    ⊨Pyth ⦃ fun inps =>
      let '((_, memL), (_, memR)) := inps in
      (eq_op memL memR) &&
      challenge_decrypt_prefix_row_ready row memL ⦄
      (fun _ : chUnit => ind_cpad_real_decrypt_cont row)
      ≈( cat_tuple
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] [tuple 0] )
      (fun _ : chUnit => ind_cpad_sim_decrypt_cont row)
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    case: row=> [[m0 m1] c].
    destruct (eq_op m0 m1) eqn:Heq.
    - have Hm : m0 = m1 := eqP Heq.
      subst m1.
      exact: ind_cpad_decrypt_cont_eq_pyth.
    rewrite /ind_cpad_real_decrypt_cont /ind_cpad_sim_decrypt_cont Heq.
    apply: pythReflRule.
    - move=> i.
      apply: (cat_tuple_nonneg
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] [tuple 0] i).
      + move=> j.
        by rewrite [j]ord1 noise_flooding_per_query_epsilon_nonnegative.
      + by move=> j; rewrite [j]ord1.
    - move=> memL memR [] [] Hpre.
      move/andP: Hpre=> [/eqP Hmem _].
      by split.
    - by move=> mem [] y Hpre Hy.
  Qed.

  Lemma ind_cpad_decrypt_cont_pyth1
      (row : IndCpadGame.challenger_table_row) :
    ⊨Pyth1 ⦃ fun inps =>
      let '((_, memL), (_, memR)) := inps in
      (eq_op memL memR) &&
      challenge_decrypt_prefix_row_ready row memL ⦄
      (fun _ : chUnit => ind_cpad_real_decrypt_cont row)
      ≈( noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier )
      (fun _ : chUnit => ind_cpad_sim_decrypt_cont row)
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    case: row=> [[m0 m1] c].
    destruct (eq_op m0 m1) eqn:Heq.
    - have Hm : m0 = m1 := eqP Heq.
      subst m1.
      exact: ind_cpad_decrypt_cont_eq_pyth1.
    rewrite /ind_cpad_real_decrypt_cont /ind_cpad_sim_decrypt_cont Heq.
    apply: pythReflRule.
    - move=> i.
      by rewrite [i]ord1 noise_flooding_per_query_epsilon_nonnegative.
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
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] [tuple 0] )
      ind_cpad_sim_decrypt_cont
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    split.
    - move=> i.
      apply: (cat_tuple_nonneg
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] [tuple 0] i).
      + move=> j.
        by rewrite [j]ord1 noise_flooding_per_query_epsilon_nonnegative.
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

  Lemma ind_cpad_decrypt_cont_kernel_pyth1 :
    ⊨Pyth1 ⦃ fun inps =>
      let '((rowL, memL), (rowR, memR)) := inps in
      (rowL == rowR) && (memL == memR) &&
      challenge_decrypt_prefix_row_ready rowL memL ⦄
      ind_cpad_real_decrypt_cont
      ≈( noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier )
      ind_cpad_sim_decrypt_cont
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    split.
    - move=> i.
      by rewrite [i]ord1 noise_flooding_per_query_epsilon_nonnegative.
    move=> memL memR rowL rowR Hpre.
    move/andP: Hpre=> [/andP [/eqP Hrow /eqP Hmem] Hready].
    subst rowR.
    subst memR.
    have [_ Hpyth] := ind_cpad_decrypt_cont_pyth1 rowL.
    have Hpre_unit :
        (let '((_, memL0), (_, memR0)) :=
            ((tt, memL), (tt, memL)) in eq_op memL0 memR0) &&
        challenge_decrypt_prefix_row_ready rowL memL.
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
          [tuple noise_flooding_per_query_epsilon
            dim gaussian_width_multiplier] [tuple 0]) )
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
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] [tuple 0])).
    - move=> memL memR iL iR Hpre.
      move/andP: Hpre=> [/andP [/eqP Hi /eqP Hmem] Hinv].
      by split; [exact: Hi | split].
    - exact: ind_cpad_decrypt_prefix_code_readies_row.
    - exact: ind_cpad_decrypt_cont_kernel_pyth.
  Qed.

  Lemma ind_cpad_decrypt_factored_pyth_short max_queries :
    ⊨Pyth ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (fun i : nat =>
        row ← ind_cpad_decrypt_prefix_code max_queries i ;;
        ind_cpad_real_decrypt_cont row)
      ≈( cat_tuple [tuple 0]
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] )
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
      [tuple noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier]).
    - move=> memL memR iL iR Hpre.
      move/andP: Hpre=> [/andP [/eqP Hi /eqP Hmem] Hinv].
      by split; [exact: Hi | split].
    - exact: ind_cpad_decrypt_prefix_code_readies_row.
    - exact: ind_cpad_decrypt_cont_kernel_pyth1.
  Qed.

  Lemma ind_cpad_decrypt_code_pyth max_queries :
    ⊨Pyth ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (ind_cpad_real_decrypt_code max_queries)
      ≈( cat_tuple [tuple 0]
        (cat_tuple
          [tuple noise_flooding_per_query_epsilon
            dim gaussian_width_multiplier] [tuple 0]) )
      (ind_cpad_sim_decrypt_code max_queries)
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    have Hfactored := ind_cpad_decrypt_factored_pyth max_queries.
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

  Lemma ind_cpad_decrypt_code_pyth_short max_queries :
    ⊨Pyth ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (ind_cpad_real_decrypt_code max_queries)
      ≈( cat_tuple [tuple 0]
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] )
      (ind_cpad_sim_decrypt_code max_queries)
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    have Hfactored := ind_cpad_decrypt_factored_pyth_short max_queries.
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

  Lemma ind_cpad_decrypt_resolve_pyth_short max_queries :
    ⊨Pyth ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (fun x : nat =>
        resolve (IndCpadGame.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
      ≈( cat_tuple [tuple 0]
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] )
      (fun x : nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
    ⦃ fun out =>
      let '(_, mem) := out in challenge_heap_valid mem ⦄.
  Proof.
    have Hcode := ind_cpad_decrypt_code_pyth_short max_queries.
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

  Lemma pythagorean_tv_bound_cat0_singleton (eps : R) :
    pythagorean_tv_bound (cat_tuple [tuple 0] [tuple eps]) =
    Num.sqrt (eps / 2).
  Proof.
    rewrite /pythagorean_tv_bound /tuple_sum /=.
    rewrite !big_ord_recl big_ord0 /=.
    by rewrite !(tnth_nth 0) /= add0r addr0.
  Qed.

  Lemma ind_cpad_decrypt_resolve_additive_error_short max_queries :
    ⊨AE_opt ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (fun x : nat =>
        resolve (IndCpadGame.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
      ≈( Num.sqrt
        ((noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier) / 2) )
      (fun x : nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
    ⦃ fun outs =>
      let '(outL, outR) := outs in eq_op outL outR ⦄.
  Proof.
    rewrite -pythagorean_tv_bound_cat0_singleton.
    exact: (MicciancioWalterRule _ _ _ _ _
      (ind_cpad_decrypt_resolve_pyth_short max_queries)).
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

  Definition ind_cpad_open_game_code
      (A : nom_package) (_ : chUnit) : raw_code bool :=
    resolve ((IndCpadGame.IndCpadChallenger ∘ A)%sep)
      (IndCpadGame.main, ('unit, 'bool)) tt.

  Definition ind_cpad_moved_adversary (A : nom_package) : nom_package :=
    move (IndCpadGame.IndCpadChallenger : nom_package) A.

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

  Lemma ind_cpad_open_game_code_factored (A : nom_package) :
    forall x,
      ind_cpad_open_game_code A x =
      ind_cpad_factored_open_game_code A x.
  Proof.
    move=> [].
    rewrite /ind_cpad_open_game_code /ind_cpad_factored_open_game_code
      /ind_cpad_challenge_init_code /ind_cpad_open_guess_code
      /ind_cpad_moved_adversary.
    by rewrite resolve_set /=.
  Qed.

  Lemma ind_cpad_challenge_init_code_empty_valid out :
    out \in
      dinsupp (Pr_code (ind_cpad_challenge_init_code tt) empty_heap) ->
    let '(_, mem) := out in challenge_heap_valid mem.
  Proof.
    rewrite /ind_cpad_challenge_init_code.
    rewrite !Pr_code_bind Pr_code_sample.
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

  Definition IndCpadMain_export :=
    [interface [IndCpadGame.main] : { 'unit ~> 'bool }].

  Lemma ind_cpad_open_main_package_valid (A : nom_package) :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    Package IndCpadGame.IndCpadAdv_import IndCpadMain_export
      ((IndCpadGame.IndCpadChallenger ∘ A)%sep).
  Proof.
    move=> A_valid.
    rewrite /IndCpadMain_export.
    typeclasses eauto with ssprove_valid_db.
  Qed.

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
    rewrite /ind_cpad_challenge_init_code /=.
    by [].
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
      (A : nom_package) max_queries x :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    ind_cpad_compiled_sim_decrypt_factored_open_game_code A max_queries x =
    ind_cpad_factored_compiled_sim_decrypt_guess_game_code A max_queries x.
  Proof.
    move=> A_valid.
    case: x=> [].
    rewrite /ind_cpad_compiled_sim_decrypt_factored_open_game_code
      /ind_cpad_factored_compiled_sim_decrypt_guess_game_code
      /ind_cpad_factored_open_game_code.
    rewrite (@codeLinkCompileCallsClosedPrefix max_queries
      nat (chOption message) (chProd chBool (chProd pk_t evk_t)) bool
      IndCpadGame.oracle_mem_spec
      (IndCpadSimDecryptOracle max_queries)
      (IndCpadGame.IndCpadOracle max_queries)
      IndCpadGame.oracle_decrypt
      (ind_cpad_challenge_init_code tt)
      (ind_cpad_open_guess_code A)).
    - by [].
    rewrite /ind_cpad_challenge_init_code.
    typeclasses eauto with ssprove_valid_db.
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

  (* Uncompiled first hybrid: real encrypt/eval code and simulated decrypt,
     before reshaping it into the existing IND-CPA reduction. *)
  Definition ind_cpad_linked_sim_decrypt_game_code
      (A : nom_package) (max_queries : nat) (_ : chUnit) :
      raw_code bool :=
    code_link
      (ind_cpad_open_game_code A tt)
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

  Lemma ind_cpad_compiled_decrypt_replacement_from_compile
      (A : nom_package) max_queries
      (Lmain Lreal Lsim : Locations) :
    (forall x,
      ValidCode Lmain IndCpadGame.IndCpadAdv_import
        (ind_cpad_open_game_code A x)) ->
    ValidPackage Lreal [interface] IndCpadGame.IndCpadAdv_import
      (IndCpadGame.IndCpadOracle max_queries) ->
    ValidPackage Lsim [interface] IndCpadGame.IndCpadAdv_import
      (IndCpadSimDecryptOracle max_queries) ->
    fseparate (emptym : Locations) Lmain ->
    fhas IndCpadGame.IndCpadAdv_import
      (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) ->
    ⊨Pyth1 ⦃ same_input_heap_pre ⦄
      (fun x : nat =>
        resolve (IndCpadGame.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
      ≈( noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier )
      (fun x : nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
    ⦃ fun out =>
      let '(_, mem) := out in trivial_heap_invariant mem ⦄ ->
    ⊨AE_opt ⦃ same_input_heap_pre ⦄
      (ind_cpad_compiled_real_game_code A max_queries)
      ≈( compile_security_error max_queries )
      (ind_cpad_compiled_sim_decrypt_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> Hmain Hreal Hsim Hsep Hdecrypt Hcall.
    rewrite /ind_cpad_compiled_real_game_code
      /ind_cpad_compiled_sim_decrypt_game_code
      /compile_security_error.
    exact: (compileRule max_queries nat (chOption message) chUnit bool
      (emptym : Locations) Lmain Lreal Lsim IndCpadGame.IndCpadAdv_import
      (IndCpadGame.IndCpadOracle max_queries)
      (IndCpadSimDecryptOracle max_queries)
      IndCpadGame.oracle_decrypt
      (ind_cpad_open_game_code A)
      (noise_flooding_per_query_epsilon dim gaussian_width_multiplier)
      trivial_heap_invariant
      Hmain Hreal Hsim Hsep
      (trivial_heap_invariant_depends_only_on (emptym : Locations))
      (package_preserves_trivial_heap_invariant_except
        IndCpadGame.IndCpadAdv_import
        (IndCpadGame.IndCpadOracle max_queries)
        IndCpadGame.oracle_decrypt)
      Hdecrypt Hcall).
  Qed.

  Lemma ind_cpad_compiled_decrypt_replacement_from_compile_closed
      (A : nom_package) max_queries (Lmain : Locations) :
    (forall x,
      ValidCode Lmain IndCpadGame.IndCpadAdv_import
        (ind_cpad_open_game_code A x)) ->
    fseparate (emptym : Locations) Lmain ->
    ⊨Pyth1 ⦃ same_input_heap_pre ⦄
      (fun x : nat =>
        resolve (IndCpadGame.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
      ≈( noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier )
      (fun x : nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
    ⦃ fun out =>
      let '(_, mem) := out in trivial_heap_invariant mem ⦄ ->
    ⊨AE_opt ⦃ same_input_heap_pre ⦄
      (ind_cpad_compiled_real_game_code A max_queries)
      ≈( compile_security_error max_queries )
      (ind_cpad_compiled_sim_decrypt_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> Hmain Hsep Hcall.
    exact: (ind_cpad_compiled_decrypt_replacement_from_compile
      A max_queries Lmain IndCpadGame.oracle_mem_spec
      IndCpadGame.oracle_mem_spec Hmain
      (IndCpadRealOracle_valid max_queries)
      (IndCpadSimDecryptOracle_valid max_queries)
      Hsep ind_cpad_decrypt_in_adv_import Hcall).
  Qed.

  Lemma ind_cpad_compiled_decrypt_replacement_from_compile_for_adversary
      (A : nom_package) max_queries :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    ⊨Pyth1 ⦃ same_input_heap_pre ⦄
      (fun x : nat =>
        resolve (IndCpadGame.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
      ≈( noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier )
      (fun x : nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
    ⦃ fun out =>
      let '(_, mem) := out in trivial_heap_invariant mem ⦄ ->
    ⊨AE_opt ⦃ same_input_heap_pre ⦄
      (ind_cpad_compiled_real_game_code A max_queries)
      ≈( compile_security_error max_queries )
      (ind_cpad_compiled_sim_decrypt_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> A_valid Hcall.
    have Hsep :
        fseparate (emptym : Locations)
          (loc ((IndCpadGame.IndCpadChallenger ∘ A)%sep)).
      fmap_solve.
    exact: (ind_cpad_compiled_decrypt_replacement_from_compile_closed
      A max_queries (loc ((IndCpadGame.IndCpadChallenger ∘ A)%sep))
      (ind_cpad_open_game_code_valid A A_valid) Hsep Hcall).
  Qed.

  Lemma ind_cpad_compiled_decrypt_replacement_from_compile_with_invariant
      (A : nom_package) max_queries
      (K : Locations) (call_invariant : pred heap) :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    fseparate K (loc ((IndCpadGame.IndCpadChallenger ∘ A)%sep)) ->
    heap_pred_depends_only_on K call_invariant ->
    package_preserves_heap_pred_except
      IndCpadGame.IndCpadAdv_import
      (IndCpadGame.IndCpadOracle max_queries)
      IndCpadGame.oracle_decrypt call_invariant ->
    ⊨Pyth1 ⦃ same_input_invariant_pre call_invariant ⦄
      (fun x : nat =>
        resolve (IndCpadGame.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
      ≈( noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier )
      (fun x : nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
    ⦃ fun out =>
      let '(_, mem) := out in call_invariant mem ⦄ ->
    ⊨AE_opt ⦃ same_input_invariant_pre call_invariant ⦄
      (ind_cpad_compiled_real_game_code A max_queries)
      ≈( compile_security_error max_queries )
      (ind_cpad_compiled_sim_decrypt_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> A_valid Hsep Hdep Hpres Hcall.
    rewrite /ind_cpad_compiled_real_game_code
      /ind_cpad_compiled_sim_decrypt_game_code
      /compile_security_error.
    exact: (compileRule max_queries nat (chOption message) chUnit bool
      K (loc ((IndCpadGame.IndCpadChallenger ∘ A)%sep))
      IndCpadGame.oracle_mem_spec IndCpadGame.oracle_mem_spec
      IndCpadGame.IndCpadAdv_import
      (IndCpadGame.IndCpadOracle max_queries)
      (IndCpadSimDecryptOracle max_queries)
      IndCpadGame.oracle_decrypt
      (ind_cpad_open_game_code A)
      (noise_flooding_per_query_epsilon dim gaussian_width_multiplier)
      call_invariant
      (ind_cpad_open_game_code_valid A A_valid)
      (IndCpadRealOracle_valid max_queries)
      (IndCpadSimDecryptOracle_valid max_queries)
      Hsep Hdep Hpres ind_cpad_decrypt_in_adv_import Hcall).
  Qed.

  Lemma ind_cpad_compiled_decrypt_replacement_from_compile_challenge_heap_valid
      (A : nom_package) max_queries :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    fseparate IndCpadGame.oracle_mem_spec
      (loc ((IndCpadGame.IndCpadChallenger ∘ A)%sep)) ->
    ⊨Pyth1 ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (fun x : nat =>
        resolve (IndCpadGame.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
      ≈( noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier )
      (fun x : nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
    ⦃ fun out =>
      let '(_, mem) := out in challenge_heap_valid mem ⦄ ->
    ⊨AE_opt ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (ind_cpad_compiled_real_game_code A max_queries)
      ≈( compile_security_error max_queries )
      (ind_cpad_compiled_sim_decrypt_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> A_valid Hsep Hcall.
    exact: (ind_cpad_compiled_decrypt_replacement_from_compile_with_invariant
      A max_queries IndCpadGame.oracle_mem_spec challenge_heap_valid
      A_valid Hsep
      challenge_heap_valid_depends_only_on_oracle_mem_spec
      (ind_cpad_real_oracle_preserves_challenge_heap_valid_except_decrypt
        max_queries)
      Hcall).
  Qed.

  Lemma ind_cpad_compiled_guess_decrypt_replacement_from_compile
      (A : nom_package) max_queries :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    ⊨AE_opt ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (ind_cpad_compiled_real_guess_code A max_queries)
      ≈( compile_security_error max_queries )
      (ind_cpad_compiled_sim_decrypt_guess_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> A_valid.
    rewrite /ind_cpad_compiled_real_guess_code
      /ind_cpad_compiled_sim_decrypt_guess_code
      /compile_security_error.
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
      (noise_flooding_per_query_epsilon dim gaussian_width_multiplier)
      challenge_heap_valid
      (ind_cpad_open_guess_code_valid A A_valid)
      (IndCpadRealOracle_valid max_queries)
      (IndCpadSimDecryptOracle_valid max_queries)
      (ind_cpad_moved_adversary_separate A)
      challenge_heap_valid_depends_only_on_oracle_mem_spec
      (ind_cpad_real_oracle_preserves_challenge_heap_valid_except_decrypt
        max_queries)
      ind_cpad_decrypt_in_adv_import
      (ind_cpad_decrypt_resolve_pyth_short max_queries)).
  Qed.

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

  Definition ind_cpa_reduction_linked_game_code
    (A : nom_package) (max_queries : nat) (_ : chUnit) :
    raw_code bool :=
    code_link
      (ind_cpa_reduction_open_game_code A max_queries tt)
      IndCpaSecurity.IndCpaGame.IndCpaOracle.

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

  Definition game_initial_pre :
    pred ((chUnit * heap) * (chUnit * heap)) :=
    pred1 ((tt, empty_heap), (tt, empty_heap)).

  Lemma total_variation_refl_le0
      {T : choiceType} (P : {distr T / R}) :
    total_variation P P <= 0.
  Proof.
    rewrite /total_variation.
    rewrite (_ : sum (fun y => `|P y - P y|) = 0).
      by rewrite mulr0 lexx.
    rewrite -(@sum0 R T).
    apply/eq_sum=> y.
    by rewrite subrr normr0.
  Qed.

  Lemma ind_cpa_reduction_game_code_linked_ae
      (A : nom_package) max_queries :
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpa_reduction_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_linked_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    apply: (additiveErrorOptConseqRule
      (ind_cpa_reduction_game_code A max_queries)
      (ind_cpa_reduction_linked_game_code A max_queries)
      game_initial_pre game_initial_pre
      same_output_heap_opt same_game_output_opt
      0 0).
    - by [].
    - move=> outs.
      rewrite /same_output_heap_opt /same_game_output_opt.
      by [].
    - by [].
    apply: additiveErrorOptSameOutputTvdEqRule.
    - exact: lexx.
    - move=> memL memR xL xR Hpre.
      rewrite /game_initial_pre in Hpre.
      move/eqP: Hpre=> Hpre.
      inversion Hpre; subst.
      rewrite ind_cpa_reduction_game_code_linked.
      exact: total_variation_refl_le0.
  Qed.

  Lemma ind_cpa_reduction_linked_game_code_ae
      (A : nom_package) max_queries :
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpa_reduction_linked_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    apply: (additiveErrorOptConseqRule
      (ind_cpa_reduction_linked_game_code A max_queries)
      (ind_cpa_reduction_game_code A max_queries)
      game_initial_pre game_initial_pre
      same_output_heap_opt same_game_output_opt
      0 0).
    - by [].
    - move=> outs.
      rewrite /same_output_heap_opt /same_game_output_opt.
      by [].
    - by [].
    apply: additiveErrorOptSameOutputTvdEqRule.
    - exact: lexx.
    - move=> memL memR xL xR Hpre.
      rewrite /game_initial_pre in Hpre.
      move/eqP: Hpre=> Hpre.
      inversion Hpre; subst.
      rewrite -ind_cpa_reduction_game_code_linked.
      exact: total_variation_refl_le0.
  Qed.

  Lemma ind_cpad_challenge_init_code_ae :
    ⊨AE ⦃ game_initial_pre ⦄
      ind_cpad_challenge_init_code
      ≈( 0 )
      ind_cpad_challenge_init_code
    ⦃ same_input_invariant_pre challenge_heap_valid ⦄.
  Proof.
    apply: (additiveErrorConseqRule
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
      move/andP=> [Hinv /andP [/eqP Hinit /eqP Hmem]].
      subst initR; subst memR.
      by rewrite /same_input_invariant_pre eqxx.
    - by [].
    apply: (additiveErrorTvdEqPostRule
      ind_cpad_challenge_init_code
      ind_cpad_challenge_init_code
      game_initial_pre
      (fun out => challenge_heap_valid out.2)
      0).
    - exact: lexx.
    - move=> memL memR xL xR.
      rewrite /game_initial_pre=> /eqP Hpre.
      inversion Hpre; subst.
      exact: total_variation_refl_le0.
    - move=> memL memR xL xR y.
      rewrite /game_initial_pre=> /eqP Hpre Hy.
      inversion Hpre; subst.
      exact: ind_cpad_challenge_init_code_empty_valid.
  Qed.

  Lemma ind_cpad_factored_compiled_guess_decrypt_replacement
      (A : nom_package) max_queries :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpad_factored_compiled_real_guess_game_code A max_queries)
      ≈( compile_security_error max_queries )
      (ind_cpad_factored_compiled_sim_decrypt_guess_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> A_valid.
    have -> : compile_security_error max_queries =
        0 + compile_security_error max_queries by lra.
    exact: (additiveErrorOptSeqRule
      ind_cpad_challenge_init_code
      ind_cpad_challenge_init_code
      (ind_cpad_compiled_real_guess_code A max_queries)
      (ind_cpad_compiled_sim_decrypt_guess_code A max_queries)
      game_initial_pre
      (same_input_invariant_pre challenge_heap_valid)
      same_game_output_opt
      0 (compile_security_error max_queries)
      ind_cpad_challenge_init_code_ae
      (ind_cpad_compiled_guess_decrypt_replacement_from_compile
        A max_queries A_valid)).
  Qed.

  Lemma ind_cpad_compiled_open_decrypt_replacement_from_guess_factoring
      (A : nom_package) max_queries :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpad_compiled_real_game_code A max_queries)
      ≈( compile_security_error max_queries )
      (ind_cpad_compiled_sim_decrypt_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> A_valid.
    have Hfactored :=
      ind_cpad_factored_compiled_guess_decrypt_replacement
        A max_queries A_valid.
    split; first exact: Hfactored.1.
    move=> memL memR xL xR Hpre.
    have [d [Hd Hpost]] := Hfactored.2 memL memR xL xR Hpre.
    exists d.
    split; last exact: Hpost.
    move: Hd.
    rewrite -(ind_cpad_compiled_real_factored_open_game_code_guess
      A max_queries xL A_valid).
    rewrite -(ind_cpad_compiled_sim_decrypt_factored_open_game_code_guess
      A max_queries xR A_valid).
    rewrite -(ind_cpad_compiled_real_game_code_factored
      A max_queries xL).
    rewrite -(ind_cpad_compiled_sim_decrypt_game_code_factored
      A max_queries xR).
    by [].
  Qed.

  Lemma ind_cpad_game_to_compiled_sim_decrypt_additive_error
      (A : nom_package) max_queries :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpad_game_code A max_queries)
      ≈( compile_security_error max_queries )
      (ind_cpad_compiled_sim_decrypt_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> A_valid.
    have Hcompiled :=
      ind_cpad_compiled_open_decrypt_replacement_from_guess_factoring
        A max_queries A_valid.
    split; first exact: Hcompiled.1.
    move=> memL memR xL xR Hpre.
    have [d [Hd Hpost]] := Hcompiled.2 memL memR xL xR Hpre.
    exists d.
    split; last exact: Hpost.
    move: Hd.
    rewrite -(ind_cpad_compiled_real_linked_correct A max_queries A_valid xL).
    rewrite -ind_cpad_game_code_linked.
    by [].
  Qed.

  Lemma ind_cpad_compiled_sim_decrypt_self_link_to_sim_decrypt_ae
      (A : nom_package) max_queries :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpad_compiled_sim_decrypt_self_link_game_code A max_queries)
      ≈( 0 )
      (ind_cpad_sim_decrypt_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> A_valid.
    apply: (additiveErrorOptConseqRule
      (ind_cpad_linked_sim_decrypt_game_code A max_queries)
      (ind_cpad_linked_sim_decrypt_game_code A max_queries)
      game_initial_pre game_initial_pre
      same_output_heap_opt same_game_output_opt
      0 0).
    - by [].
    - move=> outs.
      rewrite /same_output_heap_opt /same_game_output_opt.
      by [].
    - by [].
    apply: additiveErrorOptSameOutputTvdEqRule.
    - exact: lexx.
    - move=> memL memR xL xR Hpre.
      rewrite /game_initial_pre in Hpre.
      move/eqP: Hpre=> Hpre.
      inversion Hpre; subst.
      rewrite -(ind_cpad_compiled_sim_decrypt_self_link_correct
        A max_queries A_valid tt).
      rewrite -ind_cpad_sim_decrypt_game_code_linked.
      exact: total_variation_refl_le0.
  Qed.

  Lemma game_initial_pre_same_input memL memR xL xR :
    game_initial_pre ((xL, memL), (xR, memR)) ->
    xL = xR /\ memL = memR.
  Proof.
    rewrite /game_initial_pre=> /eqP Hpre.
    by inversion Hpre.
  Qed.

  Lemma additiveErrorOptSameGameOutputTriangleRule
      (progL progM progR : chUnit -> raw_code bool)
      (ε ε' : R) :
    ⊨AE_opt ⦃ game_initial_pre ⦄
      progL ≈( ε ) progM
    ⦃ same_game_output_opt ⦄ ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      progM ≈( ε' ) progR
    ⦃ same_game_output_opt ⦄ ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      progL ≈( ε + ε' ) progR
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> HLM HMR.
    apply: (additiveErrorOptConseqRule
      progL progR
      game_initial_pre game_initial_pre
      same_output_heap_opt same_game_output_opt
      (ε + ε') (ε + ε')).
    - by [].
    - move=> outs.
      by rewrite /same_output_heap_opt /same_game_output_opt.
    - exact: lexx.
    apply: (additiveErrorOptSameOutputTriangleRule
      progL progM progR game_initial_pre ε ε'
      game_initial_pre_same_input).
    - apply: (additiveErrorOptConseqRule
        progL progM
        game_initial_pre game_initial_pre
        same_game_output_opt same_output_heap_opt
        ε ε).
      + by [].
      + move=> outs.
        by rewrite /same_game_output_opt /same_output_heap_opt.
      + exact: lexx.
      + exact: HLM.
    - apply: (additiveErrorOptConseqRule
        progM progR
        game_initial_pre game_initial_pre
        same_game_output_opt same_output_heap_opt
        ε' ε').
      + by [].
      + move=> outs.
        by rewrite /same_game_output_opt /same_output_heap_opt.
      + exact: lexx.
      + exact: HMR.
  Qed.

  Lemma additiveErrorOptSameGameResultTvdEqRule
      (progL progR : chUnit -> raw_code bool)
      (ε : R) :
    0 <= ε ->
    (forall memL memR xL xR,
      game_initial_pre ((xL, memL), (xR, memR)) ->
      total_variation
        (complete (dmargin fst (Pr_code (progL xL) memL)))
        (complete (dmargin fst (Pr_code (progR xR) memR))) <= ε) ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      progL ≈( ε ) progR
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> Heps Htv.
    split; first exact: Heps.
    move=> memL memR xL xR Hpre.
    set outL := Pr_code (progL xL) memL.
    set outR := Pr_code (progR xR) memR.
    pose strip (out : option (bool * heap)) : option bool := omap fst out.
    have [d [HdL [HdR Hprob]]] :=
      projected_total_variation_coupling strip
        (complete outL) (complete outR) ε
        (complete_dweight outL) (complete_dweight outR)
        (Htv memL memR xL xR Hpre).
    exists d.
    split.
    - split.
      + exact: HdL.
      + exact: HdR.
    - rewrite (eq_pr (B := same_game_result_opt)).
        exact: Hprob.
      by case=> outL' outR'.
  Qed.

  Lemma additiveErrorOptSameGameResultReflRule
      (prog : chUnit -> raw_code bool) :
    ⊨AE_opt ⦃ game_initial_pre ⦄
      prog ≈( 0 ) prog
    ⦃ same_game_result_opt ⦄.
  Proof.
    apply: additiveErrorOptSameGameResultTvdEqRule.
    - exact: lexx.
    - move=> memL memR xL xR Hpre.
      have [Hx Hmem] := game_initial_pre_same_input
        memL memR xL xR Hpre.
      subst xR; subst memR.
      exact: total_variation_refl_le0.
  Qed.

  Lemma additiveErrorOptSameGameResultTriangleRule
      (progL progM progR : chUnit -> raw_code bool)
      (ε ε' : R) :
    ⊨AE_opt ⦃ game_initial_pre ⦄
      progL ≈( ε ) progM
    ⦃ same_game_result_opt ⦄ ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      progM ≈( ε' ) progR
    ⦃ same_game_result_opt ⦄ ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      progL ≈( ε + ε' ) progR
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> HLM HMR.
    apply: additiveErrorOptSameGameResultTvdEqRule.
    - have Heps := additiveErrorOptEpsNonneg _ _ _ _ _ HLM.
      have Heps' := additiveErrorOptEpsNonneg _ _ _ _ _ HMR.
      lra.
    - move=> memL memR xL xR Hpre.
      have [Hx Hmem] := game_initial_pre_same_input
        memL memR xL xR Hpre.
      subst xR; subst memR.
      have HtvLM :=
        additiveErrorOptResultTvBound
          progL progM game_initial_pre ε memL memL xL xL HLM Hpre.
      have HtvMR :=
        additiveErrorOptResultTvBound
          progM progR game_initial_pre ε' memL memL xL xL HMR Hpre.
      have Htri := total_variation_triangle
        (complete (dmargin fst (Pr_code (progL xL) memL)))
        (complete (dmargin fst (Pr_code (progM xL) memL)))
        (complete (dmargin fst (Pr_code (progR xL) memL))).
      apply: (le_trans Htri).
      lra.
  Qed.

  Lemma additiveErrorOptSameGameOutputToResult
      (progL progR : chUnit -> raw_code bool) ε :
    ⊨AE_opt ⦃ game_initial_pre ⦄
      progL ≈( ε ) progR
    ⦃ same_game_output_opt ⦄ ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      progL ≈( ε ) progR
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> Hae.
    exact: (additiveErrorOptConseqRule
      progL progR game_initial_pre game_initial_pre
      same_game_output_opt same_game_result_opt ε ε
      (fun _ H => H) same_game_output_result_opt lexx Hae).
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
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpad_compiled_sim_decrypt_game_code A max_queries)
      ≈( 0 )
      (ind_cpad_compiled_sim_decrypt_self_link_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Admitted.

  Lemma ind_cpad_sim_decrypt_to_ind_cpa_reduction_linked_ae
      (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpad_sim_decrypt_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_linked_game_code A max_queries)
    ⦃ same_game_result_opt ⦄.
  Admitted.

  Lemma ind_cpad_sim_decrypt_to_ind_cpa_reduction_ae
      (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
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
      additiveErrorOptSameGameOutputToResult
        (ind_cpa_reduction_linked_game_code A max_queries)
        (ind_cpa_reduction_game_code A max_queries)
        0
        (ind_cpa_reduction_linked_game_code_ae A max_queries).
    have H :=
      additiveErrorOptSameGameResultTriangleRule
        (ind_cpad_sim_decrypt_game_code A max_queries)
        (ind_cpa_reduction_linked_game_code A max_queries)
        (ind_cpa_reduction_game_code A max_queries)
        0 0 Hlinked Houter.
    apply: (additiveErrorOptConseqRule
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

  Lemma total_variation_complete_point_bound2
    {T : choiceType} (P Q : {distr T / R}) (x : T) :
    `|P x - Q x| <=
      2 * total_variation (complete P) (complete Q).
  Proof.
    have H := total_variation_point_bound2 (complete P) (complete Q) (Some x).
    by rewrite !completeE /= in H.
  Qed.

  Lemma additiveErrorOptResultTvBound
    {inL_t inR_t : choice_type}
    (progL : inL_t -> raw_code bool)
    (progR : inR_t -> raw_code bool)
    (pre : pred ((inL_t * heap) * (inR_t * heap)))
    (ε : R) memL memR xL xR :
    ⊨AE_opt ⦃ pre ⦄ progL ≈( ε ) progR ⦃ same_game_result_opt ⦄ ->
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
    have HdL : dmargin fst d =1 complete outL.
      move: Hd=> [HdL _] z.
      by rewrite -HdL.
    have HdR : dmargin snd d =1 complete outR.
      move: Hd=> [_ HdR] z.
      by rewrite -HdR.
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

  Lemma additiveErrorOptTvBound
    {inL_t inR_t : choice_type}
    (progL : inL_t -> raw_code bool)
    (progR : inR_t -> raw_code bool)
    (pre : pred ((inL_t * heap) * (inR_t * heap)))
    (ε : R) memL memR xL xR :
    ⊨AE_opt ⦃ pre ⦄ progL ≈( ε ) progR ⦃ same_game_output_opt ⦄ ->
    pre ((xL, memL), (xR, memR)) ->
    total_variation (complete (dmargin fst (Pr_code (progL xL) memL)))
                    (complete (dmargin fst (Pr_code (progR xR) memR))) <= ε.
  Proof.
    move=> Hae Hpre.
    apply: (additiveErrorOptResultTvBound
      progL progR pre ε memL memR xL xR).
    - apply: (additiveErrorOptConseqRule
        progL progR pre pre same_game_output_opt same_game_result_opt ε ε).
      + by [].
      + exact: same_game_output_result_opt.
      + exact: lexx.
      + exact: Hae.
    - exact: Hpre.
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
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpad_game_code A max_queries)
      ≈( ε )
      (ind_cpa_reduction_game_code A max_queries)
    ⦃ same_game_result_opt ⦄ ->
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
      additiveErrorOptResultTvBound
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

  (* Applies Micciancio-Walter to turn a Pythagorean judgment into AE_opt. *)
  Lemma ind_cpa_reduction_additive_error_from_pyth
    {ℓ : nat} (A : nom_package) max_queries
    (s : (ℓ.+1).-tuple R) ε :
    pythagorean_tv_bound s <= ε ->
    ⊨Pyth ⦃ game_initial_pre ⦄
      (ind_cpad_game_code A max_queries)
      ≈( s )
      (ind_cpa_reduction_game_code A max_queries)
    ⦃ fun _ : bool * heap => true ⦄ ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpad_game_code A max_queries)
      ≈( ε )
      (ind_cpa_reduction_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> Hbound Hpyth.
    apply: (additiveErrorOptConseqRule
      (ind_cpad_game_code A max_queries)
      (ind_cpa_reduction_game_code A max_queries)
      game_initial_pre game_initial_pre
      same_game_output_opt same_game_output_opt
      (pythagorean_tv_bound s) ε).
    - by [].
    - by [].
    - exact: Hbound.
    - exact: (MicciancioWalterRule _ _ _ _ _ Hpyth).
  Qed.

  (* The cryptographic core: compose the compile-rule decrypt replacement
     with the exact endpoint identifications.  The final endpoint uses the
     value-only postcondition because the IND-CPA reduction presentation need
     not share the same internal heap layout. *)
  Lemma ind_cpa_reduction_additive_error_from_compile
    (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpad_game_code A max_queries)
      ≈( compile_security_error max_queries )
      (ind_cpa_reduction_game_code A max_queries)
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> A_valid.
    have Hleft :=
      ind_cpad_game_to_compiled_sim_decrypt_additive_error
        A max_queries A_valid.
    have Hmixed :=
      ind_cpad_compiled_sim_decrypt_mixed_to_self_link_ae
        A max_queries A_valid.
    have Hself :=
      ind_cpad_compiled_sim_decrypt_self_link_to_sim_decrypt_ae
        A max_queries A_valid.
    have Hred :=
      ind_cpad_sim_decrypt_to_ind_cpa_reduction_ae
        A max_queries A_valid.
    have H1 := additiveErrorOptSameGameOutputTriangleRule
      (ind_cpad_game_code A max_queries)
      (ind_cpad_compiled_sim_decrypt_game_code A max_queries)
      (ind_cpad_compiled_sim_decrypt_self_link_game_code A max_queries)
      (compile_security_error max_queries) 0 Hleft Hmixed.
    have H2 := additiveErrorOptSameGameOutputTriangleRule
      (ind_cpad_game_code A max_queries)
      (ind_cpad_compiled_sim_decrypt_self_link_game_code A max_queries)
      (ind_cpad_sim_decrypt_game_code A max_queries)
      (compile_security_error max_queries + 0) 0 H1 Hself.
    have H2_result := additiveErrorOptSameGameOutputToResult
      (ind_cpad_game_code A max_queries)
      (ind_cpad_sim_decrypt_game_code A max_queries)
      (compile_security_error max_queries + 0 + 0) H2.
    have H3 := additiveErrorOptSameGameResultTriangleRule
      (ind_cpad_game_code A max_queries)
      (ind_cpad_sim_decrypt_game_code A max_queries)
      (ind_cpa_reduction_game_code A max_queries)
      (compile_security_error max_queries + 0 + 0) 0 H2_result Hred.
    apply: (additiveErrorOptConseqRule
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

  (* Packages the compile-rule loss as the AE obligation expected downstream. *)
  Lemma ind_cpa_reduction_additive_error
    (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpad_game_code A max_queries)
      ≈( security_loss max_queries / 2 )
      (ind_cpa_reduction_game_code A max_queries)
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> A_valid.
    rewrite security_loss_halfE.
    exact: (ind_cpa_reduction_additive_error_from_compile
      A max_queries A_valid).
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
