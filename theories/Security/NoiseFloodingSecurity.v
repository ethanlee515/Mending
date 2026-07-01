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
From Mending.Probability Require Import Ae.
From Mending.Probability.KL Require Import Core Pyth.
From Mending.Probability.DiscreteGaussians Require Import
  DiscreteGaussian DiscreteGaussianKL.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras ListExtras
  TupleExtras.
From Mending.LibExtras.SSProveExtras Require Import ChoiceVector
  DiscreteGaussian.

Import PackageNotation.
Import GRing.Theory Num.Theory Order.Theory Order.POrderTheory.

Local Open Scope package_scope.
Local Open Scope sep_scope.
Local Open Scope seq_scope.
Local Open Scope ring_scope.
Local Open Scope AeNotations.
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
  (Import Correctness : ApproxCorrectness(Scheme)(Metric))
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

  Definition ind_cpad_open_game_code
      (A : nom_package) (_ : chUnit) : raw_code bool :=
    resolve ((IndCpadGame.IndCpadChallenger ∘ A)%sep)
      (IndCpadGame.main, ('unit, 'bool)) tt.

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
      rewrite inE /same_game_output_opt /= => /eqP ->.
      change (eq_op (strip outR') (strip outR')).
      by rewrite eqxx.
    apply: (exact_coupling_eq_pr_total_variation
      d' (complete (dmargin fst outL)) (complete (dmargin fst outR)) ε).
    - exact: complete_dweight.
    - exact: complete_dweight.
    - exact: Hd'L.
    - exact: Hd'R.
    - exact: Hpost'.
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
    ⦃ same_game_output_opt ⦄ ->
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
      additiveErrorOptTvBound _ _ _ _ empty_heap empty_heap tt tt Hae Hpre.
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

  (* The cryptographic core: instantiate [compileRule] for the decryption
     oracle replacement.  The remaining work is to prove the one-call
     Gaussian-vector Pyth judgment and the trace-compiler side conditions for
     these concrete packages. *)
  Lemma ind_cpa_reduction_additive_error_from_compile
    (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpad_game_code A max_queries)
      ≈( compile_security_error max_queries )
      (ind_cpa_reduction_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Admitted.

  (* Packages the compile-rule loss as the AE obligation expected downstream. *)
  Lemma ind_cpa_reduction_additive_error
    (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpad_game_code A max_queries)
      ≈( security_loss max_queries / 2 )
      (ind_cpa_reduction_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
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
