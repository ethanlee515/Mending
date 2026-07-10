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

  (* Legacy route: this certificate was used by an older two-chart/finite-
     encoding proof shape.  It is no longer used by the public security
     theorem.  Under origin-centered charts, the meaningful comparison is the
     one-chart vector bound through metric_chartE, not a comparison between
     isometry centerL centerL and isometry centerR centerR. *)
  Definition chart_center_dist_le_metric_cert : Prop :=
    forall (centerL centerR : message),
      (ivec_dist (isometry centerL centerL) (isometry centerR centerR)
        <= metric centerL centerR)%N.

  Record finite_message_encoding_cert := {
    finite_message_encoding_dim : nat;
    finite_message_encode : message -> 'I_finite_message_encoding_dim;
    finite_message_encode_injective : injective finite_message_encode
  }.

  (* Legacy route: finite_common_inverse_isometry_encoding tries to use one
     common pushed-forward message encoding for two origin-centered charts.
     That is not the current noise-flooding argument and should not be used for
     new work.  The current route compares integer-vector Gaussians in one
     chart, then applies the deterministic continuation operationally. *)
  Record finite_encoding_cert := {
    finite_encoding_dim : nat;
    finite_encode_message : message -> 'I_finite_encoding_dim;
    finite_encode_message_injective : injective finite_encode_message;
    finite_common_inverse_isometry_encoding :
      message -> message -> dim.-tuple int -> 'I_finite_encoding_dim;
    finite_common_inverse_isometry_encoding_left :
      forall (centerL centerR : message) (stdev : R),
      dmargin (finite_common_inverse_isometry_encoding centerL centerR)
        (Metric.shifted_tuple_gaussian (isometry centerL centerL) stdev) =1
      dmargin (fun v => finite_encode_message (inverse_isometry centerL v))
        (Metric.shifted_tuple_gaussian (isometry centerL centerL) stdev);
    finite_common_inverse_isometry_encoding_right :
      forall (centerL centerR : message) (stdev : R),
      dmargin (finite_common_inverse_isometry_encoding centerL centerR)
        (Metric.shifted_tuple_gaussian (isometry centerR centerR) stdev) =1
      dmargin (fun v => finite_encode_message (inverse_isometry centerR v))
        (Metric.shifted_tuple_gaussian (isometry centerR centerR) stdev)
  }.

  Definition finite_message_encoding_of_legacy
      (Henc : finite_encoding_cert) : finite_message_encoding_cert :=
    {|
      finite_message_encoding_dim := finite_encoding_dim Henc;
      finite_message_encode := finite_encode_message Henc;
      finite_message_encode_injective :=
        finite_encode_message_injective Henc
    |}.

  Lemma common_inverse_isometry_encoding_left_n_dg_shifted
      (Henc : finite_encoding_cert)
      (centerL centerR : message) (stdev : R) :
    dmargin (finite_common_inverse_isometry_encoding Henc centerL centerR)
      (n_dg_shifted (isometry centerL centerL) stdev) =1
    dmargin (fun v => finite_encode_message Henc (inverse_isometry centerL v))
      (n_dg_shifted (isometry centerL centerL) stdev).
  Proof.
    move=> y.
    rewrite -(dmargin_ext
      (finite_common_inverse_isometry_encoding Henc centerL centerR)
      (Metric.shifted_tuple_gaussian (isometry centerL centerL) stdev)
      (n_dg_shifted (isometry centerL centerL) stdev)
      (shifted_tuple_gaussian_n_dg_shiftedE
        (isometry centerL centerL) stdev) y).
    rewrite (finite_common_inverse_isometry_encoding_left Henc
      centerL centerR stdev y).
    exact: (dmargin_ext
      (fun v => finite_encode_message Henc (inverse_isometry centerL v))
      (Metric.shifted_tuple_gaussian (isometry centerL centerL) stdev)
      (n_dg_shifted (isometry centerL centerL) stdev)
      (shifted_tuple_gaussian_n_dg_shiftedE
        (isometry centerL centerL) stdev) y).
  Qed.

  Lemma common_inverse_isometry_encoding_right_n_dg_shifted
      (Henc : finite_encoding_cert)
      (centerL centerR : message) (stdev : R) :
    dmargin (finite_common_inverse_isometry_encoding Henc centerL centerR)
      (n_dg_shifted (isometry centerR centerR) stdev) =1
    dmargin (fun v => finite_encode_message Henc (inverse_isometry centerR v))
      (n_dg_shifted (isometry centerR centerR) stdev).
  Proof.
    move=> y.
    rewrite -(dmargin_ext
      (finite_common_inverse_isometry_encoding Henc centerL centerR)
      (Metric.shifted_tuple_gaussian (isometry centerR centerR) stdev)
      (n_dg_shifted (isometry centerR centerR) stdev)
      (shifted_tuple_gaussian_n_dg_shiftedE
        (isometry centerR centerR) stdev) y).
    rewrite (finite_common_inverse_isometry_encoding_right Henc
      centerL centerR stdev y).
    exact: (dmargin_ext
      (fun v => finite_encode_message Henc (inverse_isometry centerR v))
      (Metric.shifted_tuple_gaussian (isometry centerR centerR) stdev)
      (n_dg_shifted (isometry centerR centerR) stdev)
      (shifted_tuple_gaussian_n_dg_shiftedE
        (isometry centerR centerR) stdev) y).
  Qed.

  Lemma shifted_tuple_gaussian_dinsupp
      (center y : dim.-tuple int) stdev :
    0 < stdev ->
    y \in dinsupp (Metric.shifted_tuple_gaussian center stdev).
  Proof.
    move=> Hs.
    rewrite in_dinsupp shifted_tuple_gaussian_n_dg_shiftedE.
    by rewrite -in_dinsupp n_dg_shifted_dinsupp.
  Qed.

  Lemma noise_flooding_message_gaussian_kl_from_finite_encoding_vector_bound
      {m : nat} (enc : message -> 'I_m)
      (common : dim.-tuple int -> 'I_m)
      error_bound (centerL centerR : message) :
    injective enc ->
    (ivec_dist (isometry centerL centerL) (isometry centerR centerR)
      <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry centerL centerL) stdev in
    let Q :=
      n_dg_shifted (isometry centerR centerR) stdev in
    dmargin common P =1
      dmargin (fun v => enc (inverse_isometry centerL v)) P ->
    dmargin common Q =1
      dmargin (fun v => enc (inverse_isometry centerR v)) Q ->
    let DL :=
      dmargin (fun v => inverse_isometry centerL v) P in
    let DR :=
      dmargin (fun v => inverse_isometry centerR v) Q in
    finite_kl DL DR /\
      δ_KL DL DR <=
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
  Proof.
    move=> Henc Hvecdist stdev P Q HcommonL HcommonR DL DR.
    have [Hvecfin Hveckl] : finite_kl P Q /\
        δ_KL P Q <=
          noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
      rewrite /P /Q /stdev.
      exact: (noise_flooding_vector_kl_bound
        error_bound (isometry centerL centerL)
        (isometry centerR centerR) Hvecdist).
    exact: (kl_dmargin_finite_encoding_common_bound_comp
      enc common
      (fun v => inverse_isometry centerL v)
      (fun v => inverse_isometry centerR v)
      P Q
        (noise_flooding_per_query_epsilon dim gaussian_width_multiplier)
      Henc Hvecfin Hveckl HcommonL HcommonR).
  Qed.

  Lemma noise_flooding_message_gaussian_kl_from_finite_encoding_vector_bound_eq
      {m : nat} (enc : message -> 'I_m)
      (common : dim.-tuple int -> 'I_m)
      error_bound (centerL centerR : message) :
    injective enc ->
    (ivec_dist (isometry centerL centerL) (isometry centerR centerR)
      <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry centerL centerL) stdev in
    let Q :=
      n_dg_shifted (isometry centerR centerR) stdev in
    (forall v, common v = enc (inverse_isometry centerL v)) ->
    (forall v, common v = enc (inverse_isometry centerR v)) ->
    let DL :=
      dmargin (fun v => inverse_isometry centerL v) P in
    let DR :=
      dmargin (fun v => inverse_isometry centerR v) Q in
    finite_kl DL DR /\
      δ_KL DL DR <=
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
  Proof.
    move=> Henc Hvecdist stdev P Q HcommonL HcommonR DL DR.
    have [Hvecfin Hveckl] : finite_kl P Q /\
        δ_KL P Q <=
          noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
      rewrite /P /Q /stdev.
      exact: (noise_flooding_vector_kl_bound
        error_bound (isometry centerL centerL)
        (isometry centerR centerR) Hvecdist).
    exact: (kl_dmargin_finite_encoding_common_bound_comp_eq
      enc common
      (fun v => inverse_isometry centerL v)
      (fun v => inverse_isometry centerR v)
      P Q
        (noise_flooding_per_query_epsilon dim gaussian_width_multiplier)
      Henc Hvecfin Hveckl HcommonL HcommonR).
  Qed.

  Lemma noise_flooding_message_gaussian_kl_from_finite_encoding_vector_bound_eq_in
      {m : nat} (enc : message -> 'I_m)
      (common : dim.-tuple int -> 'I_m)
      error_bound (centerL centerR : message) :
    injective enc ->
    (ivec_dist (isometry centerL centerL) (isometry centerR centerR)
      <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry centerL centerL) stdev in
    let Q :=
      n_dg_shifted (isometry centerR centerR) stdev in
    (forall v, v \in dinsupp P ->
      common v = enc (inverse_isometry centerL v)) ->
    (forall v, v \in dinsupp Q ->
      common v = enc (inverse_isometry centerR v)) ->
    let DL :=
      dmargin (fun v => inverse_isometry centerL v) P in
    let DR :=
      dmargin (fun v => inverse_isometry centerR v) Q in
    finite_kl DL DR /\
      δ_KL DL DR <=
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
  Proof.
    move=> Henc Hvecdist stdev P Q HcommonL HcommonR DL DR.
    have [Hvecfin Hveckl] : finite_kl P Q /\
        δ_KL P Q <=
          noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
      rewrite /P /Q /stdev.
      exact: (noise_flooding_vector_kl_bound
        error_bound (isometry centerL centerL)
        (isometry centerR centerR) Hvecdist).
    exact: (kl_dmargin_finite_encoding_common_bound_comp_eq_in
      enc common
      (fun v => inverse_isometry centerL v)
      (fun v => inverse_isometry centerR v)
      P Q
        (noise_flooding_per_query_epsilon dim gaussian_width_multiplier)
      Henc Hvecfin Hveckl HcommonL HcommonR).
  Qed.

  Lemma noise_flooding_message_gaussian_kl_from_finite_encoding
      {m : nat} (enc : message -> 'I_m)
      (common : dim.-tuple int -> 'I_m)
      error_bound (centerL centerR : message) :
    chart_center_dist_le_metric_cert ->
    injective enc ->
    (metric centerL centerR <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry centerL centerL) stdev in
    let Q :=
      n_dg_shifted (isometry centerR centerR) stdev in
    dmargin common P =1
      dmargin (fun v => enc (inverse_isometry centerL v)) P ->
    dmargin common Q =1
      dmargin (fun v => enc (inverse_isometry centerR v)) Q ->
    let DL :=
      dmargin (fun v => inverse_isometry centerL v) P in
    let DR :=
      dmargin (fun v => inverse_isometry centerR v) Q in
    finite_kl DL DR /\
      δ_KL DL DR <=
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
  Proof.
    move=> Hchart Henc Hmetric stdev P Q HcommonL HcommonR DL DR.
    exact: (noise_flooding_message_gaussian_kl_from_finite_encoding_vector_bound
      enc common error_bound centerL centerR Henc
      (leq_trans (Hchart centerL centerR) Hmetric)
      HcommonL HcommonR).
  Qed.

  Lemma noise_flooding_message_gaussian_kl_from_finite_encoding_eq
      {m : nat} (enc : message -> 'I_m)
      (common : dim.-tuple int -> 'I_m)
      error_bound (centerL centerR : message) :
    chart_center_dist_le_metric_cert ->
    injective enc ->
    (metric centerL centerR <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry centerL centerL) stdev in
    let Q :=
      n_dg_shifted (isometry centerR centerR) stdev in
    (forall v, common v = enc (inverse_isometry centerL v)) ->
    (forall v, common v = enc (inverse_isometry centerR v)) ->
    let DL :=
      dmargin (fun v => inverse_isometry centerL v) P in
    let DR :=
      dmargin (fun v => inverse_isometry centerR v) Q in
    finite_kl DL DR /\
      δ_KL DL DR <=
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
  Proof.
    move=> Hchart Henc Hmetric stdev P Q HcommonL HcommonR DL DR.
    exact: (noise_flooding_message_gaussian_kl_from_finite_encoding_vector_bound_eq
      enc common error_bound centerL centerR Henc
      (leq_trans (Hchart centerL centerR) Hmetric)
      HcommonL HcommonR).
  Qed.

  Lemma noise_flooding_message_gaussian_kl_from_finite_encoding_eq_in
      {m : nat} (enc : message -> 'I_m)
      (common : dim.-tuple int -> 'I_m)
      error_bound (centerL centerR : message) :
    chart_center_dist_le_metric_cert ->
    injective enc ->
    (metric centerL centerR <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry centerL centerL) stdev in
    let Q :=
      n_dg_shifted (isometry centerR centerR) stdev in
    (forall v, v \in dinsupp P ->
      common v = enc (inverse_isometry centerL v)) ->
    (forall v, v \in dinsupp Q ->
      common v = enc (inverse_isometry centerR v)) ->
    let DL :=
      dmargin (fun v => inverse_isometry centerL v) P in
    let DR :=
      dmargin (fun v => inverse_isometry centerR v) Q in
    finite_kl DL DR /\
      δ_KL DL DR <=
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
  Proof.
    move=> Hchart Henc Hmetric stdev P Q HcommonL HcommonR DL DR.
    exact: (noise_flooding_message_gaussian_kl_from_finite_encoding_vector_bound_eq_in
      enc common error_bound centerL centerR Henc
      (leq_trans (Hchart centerL centerR) Hmetric)
      HcommonL HcommonR).
  Qed.

  Lemma noise_flooding_message_gaussian_kl_from_finite_encoding_same_chart_center
      {m : nat} (enc : message -> 'I_m)
      (common : dim.-tuple int -> 'I_m)
      error_bound (centerL centerR : message) :
    injective enc ->
    isometry centerL centerL = isometry centerR centerR ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry centerL centerL) stdev in
    let Q :=
      n_dg_shifted (isometry centerR centerR) stdev in
    dmargin common P =1
      dmargin (fun v => enc (inverse_isometry centerL v)) P ->
    dmargin common Q =1
      dmargin (fun v => enc (inverse_isometry centerR v)) Q ->
    let DL :=
      dmargin (fun v => inverse_isometry centerL v) P in
    let DR :=
      dmargin (fun v => inverse_isometry centerR v) Q in
    finite_kl DL DR /\
      δ_KL DL DR <=
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
  Proof.
    move=> Henc Hcenter stdev P Q HcommonL HcommonR DL DR.
    apply: (noise_flooding_message_gaussian_kl_from_finite_encoding_vector_bound
      enc common error_bound centerL centerR Henc _ HcommonL HcommonR).
    by rewrite Hcenter ivec_dist_refl.
  Qed.

  Lemma noise_flooding_message_gaussian_kl_from_finite_encoding_same_chart_center_eq
      {m : nat} (enc : message -> 'I_m)
      (common : dim.-tuple int -> 'I_m)
      error_bound (centerL centerR : message) :
    injective enc ->
    isometry centerL centerL = isometry centerR centerR ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry centerL centerL) stdev in
    let Q :=
      n_dg_shifted (isometry centerR centerR) stdev in
    (forall v, common v = enc (inverse_isometry centerL v)) ->
    (forall v, common v = enc (inverse_isometry centerR v)) ->
    let DL :=
      dmargin (fun v => inverse_isometry centerL v) P in
    let DR :=
      dmargin (fun v => inverse_isometry centerR v) Q in
    finite_kl DL DR /\
      δ_KL DL DR <=
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
  Proof.
    move=> Henc Hcenter stdev P Q HcommonL HcommonR DL DR.
    apply: (noise_flooding_message_gaussian_kl_from_finite_encoding_vector_bound_eq
      enc common error_bound centerL centerR Henc _ HcommonL HcommonR).
    by rewrite Hcenter ivec_dist_refl.
  Qed.

  Lemma noise_flooding_message_gaussian_kl_from_finite_encoding_same_chart_center_eq_in
      {m : nat} (enc : message -> 'I_m)
      (common : dim.-tuple int -> 'I_m)
      error_bound (centerL centerR : message) :
    injective enc ->
    isometry centerL centerL = isometry centerR centerR ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry centerL centerL) stdev in
    let Q :=
      n_dg_shifted (isometry centerR centerR) stdev in
    (forall v, v \in dinsupp P ->
      common v = enc (inverse_isometry centerL v)) ->
    (forall v, v \in dinsupp Q ->
      common v = enc (inverse_isometry centerR v)) ->
    let DL :=
      dmargin (fun v => inverse_isometry centerL v) P in
    let DR :=
      dmargin (fun v => inverse_isometry centerR v) Q in
    finite_kl DL DR /\
      δ_KL DL DR <=
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
  Proof.
    move=> Henc Hcenter stdev P Q HcommonL HcommonR DL DR.
    apply: (noise_flooding_message_gaussian_kl_from_finite_encoding_vector_bound_eq_in
      enc common error_bound centerL centerR Henc _ HcommonL HcommonR).
    by rewrite Hcenter ivec_dist_refl.
  Qed.

  Lemma noise_flooding_message_gaussian_pythDist_from_finite_encoding_vector_bound
      {m : nat} (enc : message -> 'I_m)
      (common : dim.-tuple int -> 'I_m)
      error_bound (centerL centerR : message) :
    injective enc ->
    (ivec_dist (isometry centerL centerL) (isometry centerR centerR)
      <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry centerL centerL) stdev in
    let Q :=
      n_dg_shifted (isometry centerR centerR) stdev in
    dmargin common P =1
      dmargin (fun v => enc (inverse_isometry centerL v)) P ->
    dmargin common Q =1
      dmargin (fun v => enc (inverse_isometry centerR v)) Q ->
    let DL :=
      dmargin (fun v => inverse_isometry centerL v) P in
    let DR :=
      dmargin (fun v => inverse_isometry centerR v) Q in
    pythDist
      (dmargin (@singleton_pyth_trace message) DL)
      (dmargin (@singleton_pyth_trace message) DR)
      [tuple noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier].
  Proof.
    move=> Henc Hvecdist stdev P Q HcommonL HcommonR DL DR.
    have [Hfin Hkl] :=
      noise_flooding_message_gaussian_kl_from_finite_encoding_vector_bound
        enc common error_bound centerL centerR Henc Hvecdist
        HcommonL HcommonR.
    apply: pythDist_kl_singleton.
    - exact: noise_flooding_per_query_epsilon_nonnegative.
    - exact: Hfin.
    - rewrite /DL /P dmargin_dweight.
      apply: n_dg_shifted_mass1.
      exact: noise_flooding_dg_stdev_pos.
    - rewrite /DR /Q dmargin_dweight.
      apply: n_dg_shifted_mass1.
      exact: noise_flooding_dg_stdev_pos.
    - exact: Hkl.
  Qed.

  Lemma noise_flooding_message_gaussian_pythDist_from_finite_encoding_same_chart_center
      {m : nat} (enc : message -> 'I_m)
      (common : dim.-tuple int -> 'I_m)
      error_bound (centerL centerR : message) :
    injective enc ->
    isometry centerL centerL = isometry centerR centerR ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry centerL centerL) stdev in
    let Q :=
      n_dg_shifted (isometry centerR centerR) stdev in
    dmargin common P =1
      dmargin (fun v => enc (inverse_isometry centerL v)) P ->
    dmargin common Q =1
      dmargin (fun v => enc (inverse_isometry centerR v)) Q ->
    let DL :=
      dmargin (fun v => inverse_isometry centerL v) P in
    let DR :=
      dmargin (fun v => inverse_isometry centerR v) Q in
    pythDist
      (dmargin (@singleton_pyth_trace message) DL)
      (dmargin (@singleton_pyth_trace message) DR)
      [tuple noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier].
  Proof.
    move=> Henc Hcenter stdev P Q HcommonL HcommonR DL DR.
    apply: (noise_flooding_message_gaussian_pythDist_from_finite_encoding_vector_bound
      enc common error_bound centerL centerR Henc _ HcommonL HcommonR).
    by rewrite Hcenter ivec_dist_refl.
  Qed.

  Lemma noise_flooding_message_gaussian_kl_one_chart_from_finite_encoding
      (Henc : finite_message_encoding_cert)
      error_bound (centerL centerR : message) :
    (metric centerL centerR <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let DL :=
      dmargin (fun v => inverse_isometry centerL v)
        (n_dg dim stdev) in
    let DR :=
      dmargin (fun v => inverse_isometry centerL v)
        (n_dg_shifted (isometry centerL centerR) stdev) in
    finite_kl DL DR /\
    δ_KL DL DR <=
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
  Proof.
    move=> Hmetric stdev DL DR.
    have [Hvecfin Hveckl] :=
      noise_flooding_vector_kl_bound_one_chart
        error_bound centerL centerR Hmetric.
    rewrite /DL /DR /stdev.
    apply: (kl_dmargin_finite_encoding_common_bound_comp_eq
      (finite_message_encode Henc)
      (fun v => finite_message_encode Henc (inverse_isometry centerL v))
      (fun v => inverse_isometry centerL v)
      (fun v => inverse_isometry centerL v)
      (n_dg dim
        (noise_flooding_dg_stdev
          gaussian_width_multiplier error_bound))
      (n_dg_shifted (isometry centerL centerR)
        (noise_flooding_dg_stdev
          gaussian_width_multiplier error_bound))
      (noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier)
      (finite_message_encode_injective Henc)
      Hvecfin Hveckl).
    - by [].
    - by [].
  Qed.

  Lemma noise_flooding_message_gaussian_kl :
    finite_encoding_cert ->
    chart_center_dist_le_metric_cert ->
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
  Proof.
    move=> Henc Hchart error_bound centerL centerR Hmetric stdev DL DR.
    exact: (noise_flooding_message_gaussian_kl_from_finite_encoding
      (finite_encode_message Henc)
      (finite_common_inverse_isometry_encoding Henc centerL centerR)
      error_bound centerL centerR Hchart
      (finite_encode_message_injective Henc) Hmetric
      (common_inverse_isometry_encoding_left_n_dg_shifted
        Henc centerL centerR stdev)
      (common_inverse_isometry_encoding_right_n_dg_shifted
        Henc centerL centerR stdev)).
  Qed.

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
    finite_encoding_cert ->
    chart_center_dist_le_metric_cert ->
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
    move=> Henc Hchart Hmetric stdev DL DR.
    have [Hfin Hkl] :=
      noise_flooding_message_gaussian_kl
        Henc Hchart error_bound centerL centerR Hmetric.
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

  Lemma noise_flooding_decrypt_some_centered
      sk data error_bound :
    let c : ciphertext := Some (data, error_bound) in
    NF.decrypt sk c =1
      dmargin
        (fun v => inverse_isometry (dec' sk c) v)
        (n_dg dim
          (noise_flooding_dg_stdev
            gaussian_width_multiplier error_bound)).
  Proof.
    move=> c y.
    rewrite (noise_flooding_decrypt_some_shifted sk data error_bound y).
    rewrite (isometry_center0 (dec' sk c)).
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

  Lemma noise_flooding_successful_decrypt_pythDist
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    finite_encoding_cert ->
    chart_center_dist_le_metric_cert ->
    (metric (dec' sk c) m <= error_bound)%N ->
    pythDist
      (dmargin (@singleton_pyth_trace message) (NF.decrypt sk c))
      (dmargin (@singleton_pyth_trace message)
        (simulator_successful_decrypt_distribution m error_bound))
      [tuple noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier].
  Proof.
    move=> c Henc Hchart Hmetric.
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
      error_bound (dec' sk c) m Henc Hchart Hmetric).
  Qed.

  Lemma noise_flooding_successful_decrypt_pythDist_from_finite_encoding_vector_bound
      {enc_dim : nat} (enc : message -> 'I_enc_dim)
      (common : dim.-tuple int -> 'I_enc_dim)
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    injective enc ->
    (ivec_dist (isometry (dec' sk c) (dec' sk c)) (isometry m m)
      <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry (dec' sk c) (dec' sk c)) stdev in
    let Q :=
      n_dg_shifted (isometry m m) stdev in
    dmargin common P =1
      dmargin (fun v => enc (inverse_isometry (dec' sk c) v)) P ->
    dmargin common Q =1
      dmargin (fun v => enc (inverse_isometry m v)) Q ->
    pythDist
      (dmargin (@singleton_pyth_trace message) (NF.decrypt sk c))
      (dmargin (@singleton_pyth_trace message)
        (simulator_successful_decrypt_distribution m error_bound))
      [tuple noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier].
  Proof.
    move=> c Henc Hvecdist stdev P Q HcommonL HcommonR.
    set centerL := dec' sk c.
    set centerR := m.
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
    exact: (noise_flooding_message_gaussian_pythDist_from_finite_encoding_vector_bound
      enc common error_bound (dec' sk c) m Henc Hvecdist
      HcommonL HcommonR).
  Qed.

  Lemma noise_flooding_successful_decrypt_pythDist_from_finite_encoding_same_chart_center
      {enc_dim : nat} (enc : message -> 'I_enc_dim)
      (common : dim.-tuple int -> 'I_enc_dim)
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    injective enc ->
    isometry (dec' sk c) (dec' sk c) = isometry m m ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry (dec' sk c) (dec' sk c)) stdev in
    let Q :=
      n_dg_shifted (isometry m m) stdev in
    dmargin common P =1
      dmargin (fun v => enc (inverse_isometry (dec' sk c) v)) P ->
    dmargin common Q =1
      dmargin (fun v => enc (inverse_isometry m v)) Q ->
    pythDist
      (dmargin (@singleton_pyth_trace message) (NF.decrypt sk c))
      (dmargin (@singleton_pyth_trace message)
        (simulator_successful_decrypt_distribution m error_bound))
      [tuple noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier].
  Proof.
    move=> c Henc Hcenter stdev P Q HcommonL HcommonR.
    apply: (noise_flooding_successful_decrypt_pythDist_from_finite_encoding_vector_bound
      enc common sk data error_bound m Henc _ HcommonL HcommonR).
    by rewrite Hcenter ivec_dist_refl.
  Qed.

  Lemma noise_flooding_successful_decrypt_sample_pyth
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    finite_encoding_cert ->
    chart_center_dist_le_metric_cert ->
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
    move=> c Henc Hchart Hmetric.
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
        Henc Hchart error_bound (dec' sk c) m Hmetric).
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

  Lemma noise_flooding_successful_decrypt_sample_pyth_from_finite_encoding_vector_bound
      {enc_dim : nat} (enc : message -> 'I_enc_dim)
      (common : dim.-tuple int -> 'I_enc_dim)
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    injective enc ->
    (ivec_dist (isometry (dec' sk c) (dec' sk c)) (isometry m m)
      <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry (dec' sk c) (dec' sk c)) stdev in
    let Q :=
      n_dg_shifted (isometry m m) stdev in
    dmargin common P =1
      dmargin (fun v => enc (inverse_isometry (dec' sk c) v)) P ->
    dmargin common Q =1
      dmargin (fun v => enc (inverse_isometry m v)) Q ->
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
    move=> c Henc Hvecdist stdev P Q HcommonL HcommonR.
    set eps :=
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
    set centerL := dec' sk c.
    set centerR := m.
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
      exact: (noise_flooding_message_gaussian_kl_from_finite_encoding_vector_bound
        enc common error_bound (dec' sk c) m Henc Hvecdist
        HcommonL HcommonR).
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

  Lemma noise_flooding_successful_decrypt_sample_pyth_from_finite_encoding_same_chart_center
      {enc_dim : nat} (enc : message -> 'I_enc_dim)
      (common : dim.-tuple int -> 'I_enc_dim)
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    injective enc ->
    isometry (dec' sk c) (dec' sk c) = isometry m m ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry (dec' sk c) (dec' sk c)) stdev in
    let Q :=
      n_dg_shifted (isometry m m) stdev in
    dmargin common P =1
      dmargin (fun v => enc (inverse_isometry (dec' sk c) v)) P ->
    dmargin common Q =1
      dmargin (fun v => enc (inverse_isometry m v)) Q ->
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
    move=> c Henc Hcenter stdev P Q HcommonL HcommonR.
    apply: (noise_flooding_successful_decrypt_sample_pyth_from_finite_encoding_vector_bound
      enc common sk data error_bound m Henc _ HcommonL HcommonR).
    by rewrite Hcenter ivec_dist_refl.
  Qed.

  Lemma noise_flooding_successful_decrypt_some_pyth
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    finite_encoding_cert ->
    chart_center_dist_le_metric_cert ->
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
    move=> c Henc Hchart Hmetric.
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
        sk data error_bound m Henc Hchart Hmetric).
    - apply: hoareRetRule.
      by [].
  Qed.

  Lemma noise_flooding_successful_decrypt_some_pyth_from_finite_encoding_vector_bound
      {enc_dim : nat} (enc : message -> 'I_enc_dim)
      (common : dim.-tuple int -> 'I_enc_dim)
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    injective enc ->
    (ivec_dist (isometry (dec' sk c) (dec' sk c)) (isometry m m)
      <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry (dec' sk c) (dec' sk c)) stdev in
    let Q :=
      n_dg_shifted (isometry m m) stdev in
    dmargin common P =1
      dmargin (fun v => enc (inverse_isometry (dec' sk c) v)) P ->
    dmargin common Q =1
      dmargin (fun v => enc (inverse_isometry m v)) Q ->
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
    move=> c Henc Hvecdist stdev P Q HcommonL HcommonR.
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
    - exact: (noise_flooding_successful_decrypt_sample_pyth_from_finite_encoding_vector_bound
        enc common sk data error_bound m Henc Hvecdist HcommonL HcommonR).
    - apply: hoareRetRule.
      by [].
  Qed.

  Lemma noise_flooding_successful_decrypt_some_pyth_from_finite_encoding_same_chart_center
      {enc_dim : nat} (enc : message -> 'I_enc_dim)
      (common : dim.-tuple int -> 'I_enc_dim)
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    injective enc ->
    isometry (dec' sk c) (dec' sk c) = isometry m m ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry (dec' sk c) (dec' sk c)) stdev in
    let Q :=
      n_dg_shifted (isometry m m) stdev in
    dmargin common P =1
      dmargin (fun v => enc (inverse_isometry (dec' sk c) v)) P ->
    dmargin common Q =1
      dmargin (fun v => enc (inverse_isometry m v)) Q ->
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
    move=> c Henc Hcenter stdev P Q HcommonL HcommonR.
    apply: (noise_flooding_successful_decrypt_some_pyth_from_finite_encoding_vector_bound
      enc common sk data error_bound m Henc _ HcommonL HcommonR).
    by rewrite Hcenter ivec_dist_refl.
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
       ret (inverse_isometry (dec' sk c)
         (IndCpaDSim.toIntVec noise)))
      mem =1
    Pr_code (sampleRaw (NF.decrypt sk c)) mem.
  Proof.
    move=> c out.
    set stdev := noise_flooding_dg_stdev
      gaussian_width_multiplier error_bound.
    set center := dec' sk c.
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
    (metric (dec' sk c) m <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    ⊨Pyth ⦃ fun inps =>
      let '((_, memL), (_, memR)) := inps in eq_op memL memR ⦄
      (fun _ : chUnit =>
        noise ← sampleRaw
          (dmargin (@toChIntVec dim) (n_dg dim stdev)) ;;
        ret (Some
          (inverse_isometry (dec' sk c) (IndCpaDSim.toIntVec noise))))
      ≈( cat_tuple
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] [tuple 0] )
      (fun _ : chUnit =>
        noise ← sampleRaw
          (dmargin (@toChIntVec dim)
            (n_dg_shifted (isometry (dec' sk c) m) stdev)) ;;
        ret (Some
          (inverse_isometry (dec' sk c) (IndCpaDSim.toIntVec noise))))
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    move=> c Hmetric stdev.
    set centerL := dec' sk c.
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
        error_bound (dec' sk c) m Hmetric).
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
        (inverse_isometry (dec' sk c) (IndCpaDSim.toIntVec noise))))
      mem =1
    Pr_code
      (m' ← sampleRaw (NF.decrypt sk c) ;;
       ret (Some m'))
      mem.
  Proof.
    move=> c stdev out.
    set center := dec' sk c.
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
    set stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound.
    apply: (pythJudgment_ext_true
      (fun _ : chUnit =>
        noise ← sampleRaw
          (dmargin (@toChIntVec dim) (n_dg dim stdev)) ;;
        ret (Some
          (inverse_isometry (dec' sk c) (IndCpaDSim.toIntVec noise))))
      (fun _ : chUnit =>
        m' ← sampleRaw (NF.decrypt sk c) ;;
        ret (Some m'))
      (fun _ : chUnit =>
        noise ← sampleRaw
          (dmargin (@toChIntVec dim)
            (n_dg_shifted (isometry (dec' sk c) m) stdev)) ;;
        ret (Some
          (inverse_isometry (dec' sk c) (IndCpaDSim.toIntVec noise))))
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
        (dec' sk c) m error_bound mem).
    rewrite /stdev.
    exact: (noise_flooding_successful_decrypt_some_target_pyth_one_chart
      sk data error_bound m Hmetric).
  Qed.

  Lemma noise_flooding_successful_decrypt_code_pyth_one_chart
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
    exact: (noise_flooding_successful_decrypt_code_pyth_one_chart
      sk data error_bound m Hmetric).
  Qed.

  Lemma noise_flooding_successful_decrypt_code_pyth_from_finite_encoding_vector_bound
      {enc_dim : nat} (enc : message -> 'I_enc_dim)
      (common : dim.-tuple int -> 'I_enc_dim)
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    injective enc ->
    (ivec_dist (isometry (dec' sk c) (dec' sk c)) (isometry m m)
      <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry (dec' sk c) (dec' sk c)) stdev in
    let Q :=
      n_dg_shifted (isometry m m) stdev in
    dmargin common P =1
      dmargin (fun v => enc (inverse_isometry (dec' sk c) v)) P ->
    dmargin common Q =1
      dmargin (fun v => enc (inverse_isometry m v)) Q ->
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
    move=> c Henc Hvecdist stdev P Q HcommonL HcommonR.
    have Hpyth :=
      noise_flooding_successful_decrypt_some_pyth_from_finite_encoding_vector_bound
        enc common sk data error_bound m Henc Hvecdist
        HcommonL HcommonR.
    move: Hpyth=> [Hs Hpyth].
    split; first exact: Hs.
    move=> memL memR [] [] Hpre.
    have [P0 [Q0 [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
      Hpyth memL memR tt tt Hpre.
    exists P0, Q0.
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

  Lemma noise_flooding_successful_decrypt_code_pyth_from_finite_encoding_same_chart_center
      {enc_dim : nat} (enc : message -> 'I_enc_dim)
      (common : dim.-tuple int -> 'I_enc_dim)
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    injective enc ->
    isometry (dec' sk c) (dec' sk c) = isometry m m ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry (dec' sk c) (dec' sk c)) stdev in
    let Q :=
      n_dg_shifted (isometry m m) stdev in
    dmargin common P =1
      dmargin (fun v => enc (inverse_isometry (dec' sk c) v)) P ->
    dmargin common Q =1
      dmargin (fun v => enc (inverse_isometry m v)) Q ->
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
    move=> c Henc Hcenter stdev P Q HcommonL HcommonR.
    apply: (noise_flooding_successful_decrypt_code_pyth_from_finite_encoding_vector_bound
      enc common sk data error_bound m Henc _ HcommonL HcommonR).
    by rewrite Hcenter ivec_dist_refl.
  Qed.

  Lemma noise_flooding_successful_decrypt_code_pyth_from_metric_encoding_vector_bound
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    finite_encoding_cert ->
    (ivec_dist (isometry (dec' sk c) (dec' sk c)) (isometry m m)
      <= error_bound)%N ->
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
    move=> c Henc Hvecdist.
    set centerL := dec' sk c.
    set centerR := m.
    set stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound.
    apply: (noise_flooding_successful_decrypt_code_pyth_from_finite_encoding_vector_bound
      (finite_encode_message Henc)
      (finite_common_inverse_isometry_encoding Henc centerL centerR)
      sk data error_bound m
      (finite_encode_message_injective Henc) Hvecdist).
    - exact: (common_inverse_isometry_encoding_left_n_dg_shifted
        Henc centerL centerR stdev).
    - exact: (common_inverse_isometry_encoding_right_n_dg_shifted
        Henc centerL centerR stdev).
  Qed.

  Lemma noise_flooding_successful_decrypt_code_pyth_from_metric_encoding_same_chart_center
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    finite_encoding_cert ->
    isometry (dec' sk c) (dec' sk c) = isometry m m ->
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
    move=> c Henc Hcenter.
    apply: (noise_flooding_successful_decrypt_code_pyth_from_metric_encoding_vector_bound
      sk data error_bound m Henc).
    by rewrite Hcenter ivec_dist_refl.
  Qed.

  Lemma noise_flooding_successful_decrypt_code_pyth1_from_finite_encoding_vector_bound
      {enc_dim : nat} (enc : message -> 'I_enc_dim)
      (common : dim.-tuple int -> 'I_enc_dim)
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    injective enc ->
    (ivec_dist (isometry (dec' sk c) (dec' sk c)) (isometry m m)
      <= error_bound)%N ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry (dec' sk c) (dec' sk c)) stdev in
    let Q :=
      n_dg_shifted (isometry m m) stdev in
    dmargin common P =1
      dmargin (fun v => enc (inverse_isometry (dec' sk c) v)) P ->
    dmargin common Q =1
      dmargin (fun v => enc (inverse_isometry m v)) Q ->
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
    move=> c Henc Hvecdist stdev P Q HcommonL HcommonR.
    set eps :=
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
    set centerL := dec' sk c.
    set centerR := m.
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
      exact: (noise_flooding_message_gaussian_kl_from_finite_encoding_vector_bound
        enc common error_bound (dec' sk c) m Henc Hvecdist
        HcommonL HcommonR).
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
    have [P0 [Q0 [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
      Hpyth memL memR tt tt Hpre.
    exists P0, Q0.
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

  Lemma noise_flooding_successful_decrypt_code_pyth1_from_finite_encoding_same_chart_center
      {enc_dim : nat} (enc : message -> 'I_enc_dim)
      (common : dim.-tuple int -> 'I_enc_dim)
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    injective enc ->
    isometry (dec' sk c) (dec' sk c) = isometry m m ->
    let stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
    let P :=
      n_dg_shifted (isometry (dec' sk c) (dec' sk c)) stdev in
    let Q :=
      n_dg_shifted (isometry m m) stdev in
    dmargin common P =1
      dmargin (fun v => enc (inverse_isometry (dec' sk c) v)) P ->
    dmargin common Q =1
      dmargin (fun v => enc (inverse_isometry m v)) Q ->
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
    move=> c Henc Hcenter stdev P Q HcommonL HcommonR.
    apply: (noise_flooding_successful_decrypt_code_pyth1_from_finite_encoding_vector_bound
      enc common sk data error_bound m Henc _ HcommonL HcommonR).
    by rewrite Hcenter ivec_dist_refl.
  Qed.

  Lemma noise_flooding_successful_decrypt_code_pyth1_from_metric_encoding_vector_bound
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    finite_encoding_cert ->
    (ivec_dist (isometry (dec' sk c) (dec' sk c)) (isometry m m)
      <= error_bound)%N ->
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
    move=> c Henc Hvecdist.
    set centerL := dec' sk c.
    set centerR := m.
    set stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound.
    apply: (noise_flooding_successful_decrypt_code_pyth1_from_finite_encoding_vector_bound
      (finite_encode_message Henc)
      (finite_common_inverse_isometry_encoding Henc centerL centerR)
      sk data error_bound m
      (finite_encode_message_injective Henc) Hvecdist).
    - exact: (common_inverse_isometry_encoding_left_n_dg_shifted
        Henc centerL centerR stdev).
    - exact: (common_inverse_isometry_encoding_right_n_dg_shifted
        Henc centerL centerR stdev).
  Qed.

  Lemma noise_flooding_successful_decrypt_code_pyth1_from_metric_encoding_same_chart_center
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    finite_encoding_cert ->
    isometry (dec' sk c) (dec' sk c) = isometry m m ->
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
    move=> c Henc Hcenter.
    apply: (noise_flooding_successful_decrypt_code_pyth1_from_metric_encoding_vector_bound
      sk data error_bound m Henc).
    by rewrite Hcenter ivec_dist_refl.
  Qed.

  Lemma noise_flooding_successful_decrypt_code_pyth1_one_chart
      sk data error_bound (m : message) :
    let c : ciphertext := Some (data, error_bound) in
    finite_message_encoding_cert ->
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
    move=> c Henc Hmetric.
    set eps :=
      noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
    set centerL := dec' sk c.
    set stdev :=
      noise_flooding_dg_stdev gaussian_width_multiplier error_bound.
    set DL :=
      dmargin (fun v => inverse_isometry centerL v)
        (n_dg dim stdev).
    set DR :=
      dmargin (fun v => inverse_isometry centerL v)
        (n_dg_shifted (isometry centerL m) stdev).
    set Dreal := NF.decrypt sk c.
    set Dsim := simulator_successful_decrypt_distribution m error_bound.
    set Dreal_opt := dmargin (@Some message) Dreal.
    set Dsim_opt := dmargin (@Some message) Dsim.
    have Hsome_inj : injective (@Some message).
      by move=> x y [= ->].
    have [Hfin Hkl] :
        finite_kl DL DR /\ δ_KL DL DR <= eps.
      rewrite /DL /DR /centerL /stdev /eps.
      exact: (noise_flooding_message_gaussian_kl_one_chart_from_finite_encoding
        Henc error_bound (dec' sk c) m Hmetric).
    have HDreal : DL =1 Dreal.
      move=> y.
      rewrite /DL /Dreal /centerL /stdev.
      symmetry.
      exact: noise_flooding_decrypt_some_centered.
    have HDsim : DR =1 Dsim.
      move=> y.
      rewrite /DR /Dsim /centerL /stdev.
      symmetry.
      exact: simulator_decrypt_noise_one_chart.
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
        apply: n_dg_mass1.
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
      rewrite /stdev.
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
    finite_encoding_cert ->
    chart_center_dist_le_metric_cert ->
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
    move=> c Henc _ Hmetric.
    exact: (noise_flooding_successful_decrypt_code_pyth1_one_chart
      sk data error_bound m (finite_message_encoding_of_legacy Henc)
      Hmetric).
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

  Lemma ind_cpad_encrypt_in_adv_import :
    fhas IndCpadGame.IndCpadAdv_import
      (mkopsig IndCpadGame.oracle_encrypt
        (chProd message message) ciphertext).
  Proof.
    rewrite /IndCpadGame.IndCpadAdv_import.
    fmap_solve.
  Qed.

  Lemma ind_cpad_eval1_in_adv_import :
    fhas IndCpadGame.IndCpadAdv_import
      (mkopsig IndCpadGame.oracle_eval1
        (chProd unary_gate nat) ciphertext).
  Proof.
    rewrite /IndCpadGame.IndCpadAdv_import.
    fmap_solve.
  Qed.

  Lemma ind_cpad_eval2_in_adv_import :
    fhas IndCpadGame.IndCpadAdv_import
      (mkopsig IndCpadGame.oracle_eval2
        (chProd (chProd binary_gate nat) nat) ciphertext).
  Proof.
    rewrite /IndCpadGame.IndCpadAdv_import.
    fmap_solve.
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

  Lemma pyth1_current_refl_witness
      {out_t : choice_type} (eps : R)
      (outL outR : {distr (out_t * heap) / R})
      (post : pred (out_t * heap)) :
    0 <= eps ->
    outL =1 outR ->
    (forall y, y \in dinsupp outL -> post y) ->
    (forall y, y \in dinsupp outR -> post y) ->
    exists
      (P Q : {distr (1.-tuple (option (nat * heap))) / R}),
      pythDist P Q [tuple eps] /\
      dmargin (fun omega => tnth omega ord_max) P
        =1 complete_output_heap outL /\
      dmargin (fun omega => tnth omega ord_max) Q
        =1 complete_output_heap outR /\
      (forall y, y \in dinsupp outL -> post y) /\
      (forall y, y \in dinsupp outR -> post y).
  Proof.
    move=> Heps Hout HpostL HpostR.
    pose lift_final (z : option (nat * heap)) :
        1.-tuple (option (nat * heap)) := [tuple z].
    pose P := dmargin lift_final (complete_output_heap outL).
    exists P, P.
    split.
      apply: pythDist_refl.
      - by move=> i; rewrite [i]ord1.
      - rewrite /P dmargin_dweight.
        exact: complete_dweight.
    split.
    - move=> z.
      rewrite /P __deprecated__dmargin_dlet.
      rewrite -(dlet_dunit_id (complete_output_heap outL) z).
      apply: eq_in_dlet=> // y _ z'.
      by rewrite dmargin_dunit /lift_final [ord_max]ord1 tnth0.
    split.
    - move=> z.
      rewrite -(@complete_output_heap_ext out_t outL outR Hout z).
      rewrite /P __deprecated__dmargin_dlet.
      rewrite -(dlet_dunit_id (complete_output_heap outL) z).
      apply: eq_in_dlet=> // y _ z'.
      by rewrite dmargin_dunit /lift_final [ord_max]ord1 tnth0.
    by split.
  Qed.

  Lemma bool_eq_true_is_true (b : bool) :
    b = true -> b.
  Proof. by move=> ->. Qed.

  Lemma nth_valid_eq_true_irrel {A} (lst : seq A) n
      (Htrue : (n < length lst)%N = true)
      (H : (n < length lst)%N) :
    nth_valid lst n (bool_eq_true_is_true _ Htrue) =
    nth_valid lst n H.
  Proof.
    exact: nth_valid_irrel.
  Qed.

  Lemma dmargin_fst_assertD_ext
      {out_t : choice_type} (b : bool)
      (kL kR : b = true -> raw_code out_t) memL memR :
    (forall Hb,
      dmargin fst (Pr_code (kL Hb) memL) =1
      dmargin fst (Pr_code (kR Hb) memR)) ->
    dmargin fst (Pr_code (@assertD out_t b kL) memL) =1
    dmargin fst (Pr_code (@assertD out_t b kR) memR).
  Proof.
    case: b kL kR=> kL kR Hcont out;
      rewrite !dmarginE /assertD /=.
    - exact: (Hcont erefl out).
    - by rewrite !Pr_code_fail !dlet_null_ext.
  Qed.

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

  Lemma Pr_code_assertD_false_ext
      {out_t : choice_type} (b : bool)
      (k : b = true -> raw_code out_t) mem :
    b = false ->
    Pr_code (@assertD out_t b k) mem =1 dnull.
  Proof.
    case: b k=> k Hb out.
    - discriminate Hb.
    - by rewrite /assertD /= Pr_code_fail.
  Qed.

  Lemma dmargin_fst_assertD_ext_eq
      {out_t : choice_type} (bL bR : bool)
      (kL : bL = true -> raw_code out_t)
      (kR : bR = true -> raw_code out_t) memL memR :
    bL = bR ->
    (forall HbL HbR,
      dmargin fst (Pr_code (kL HbL) memL) =1
      dmargin fst (Pr_code (kR HbR) memR)) ->
    dmargin fst (Pr_code (@assertD out_t bL kL) memL) =1
    dmargin fst (Pr_code (@assertD out_t bR kR) memR).
  Proof.
    case: bL kL=> kL; case: bR kR=> kR Hguard Hcont out;
      rewrite !dmarginE /assertD /= in Hguard *.
    - exact: (Hcont erefl erefl out).
    - discriminate Hguard.
    - discriminate Hguard.
    - by rewrite !Pr_code_fail !dlet_null_ext.
  Qed.

  Lemma dinsupp_assertD_intro
      {out_t : choice_type} (b : bool)
      (cont : b = true -> raw_code out_t) mem out
      (Hb : b = true) :
    out \in dinsupp (Pr_code (cont Hb) mem) ->
    out \in dinsupp (Pr_code (@assertD out_t b cont) mem).
  Proof.
    case: b cont Hb=> cont Hb Hsupp.
    - rewrite /assertD /=.
      move: Hsupp.
      rewrite (eq_irrelevance Hb erefl).
      by [].
    - by [].
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
        clean_coupling d
          (complete (Pr_code (kL HbL) memL))
          (complete (Pr_code (kR HbR) memR)) /\
        \P_[d] post >= 1 - ε) ->
    post (None, None) ->
    exists d,
      clean_coupling d
        (complete (Pr_code (@assertD outL_t b kL) memL))
        (complete (Pr_code (@assertD outR_t b kR) memR)) /\
      \P_[d] post >= 1 - ε.
  Proof.
    case: b kL kR=> kL kR Heps Hcont Hnone.
    - have [d [Hd Hprob]] := Hcont erefl erefl.
      exists d.
      split; last exact: Hprob.
      move: Hd=> [HdL HdR].
      split.
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
      + split.
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

  Lemma shared_sample_relation_coupling
      {sample_t outL_t outR_t : choice_type}
      (D : {distr sample_t / R})
      (outL : sample_t -> outL_t * heap)
      (outR : sample_t -> outR_t * heap)
      (progL : raw_code outL_t) (progR : raw_code outR_t)
      memL memR
      (post : pred (option (outL_t * heap) * option (outR_t * heap))) :
    dmargin outL D =1 Pr_code progL memL ->
    dmargin outR D =1 Pr_code progR memR ->
    (forall x, x \in dinsupp D -> post (Some (outL x), Some (outR x))) ->
    post (None, None) ->
    exists d,
      clean_coupling d (complete (Pr_code progL memL))
        (complete (Pr_code progR memR)) /\
      \P_[d] post >= 1.
  Proof.
    move=> Hleft Hright Hpost Hnone.
    exists (shared_complete_sample_coupling D outL outR).
    split.
    - have [HmarginL HmarginR] :=
        shared_complete_sample_coupling_margins D outL outR.
      split.
      + move=> z.
        rewrite HmarginL.
        exact: (complete_distr_ext _ _ Hleft z).
      + move=> z.
        rewrite HmarginR.
        exact: (complete_distr_ext _ _ Hright z).
    - exact: (shared_complete_sample_coupling_pr_ge1 D outL outR post
        Hpost Hnone).
  Qed.

  Lemma additiveErrorOptSameResultTvdEqRule
      {inL_t inR_t out_t : choice_type}
      (progL : inL_t -> raw_code out_t)
      (progR : inR_t -> raw_code out_t)
      (pre : pred ((inL_t * heap) * (inR_t * heap)))
      (ε : R) :
    0 <= ε ->
    (forall memL memR xL xR,
      pre ((xL, memL), (xR, memR)) ->
      total_variation
        (complete (dmargin fst (Pr_code (progL xL) memL)))
        (complete (dmargin fst (Pr_code (progR xR) memR))) <= ε) ->
    ⊨AE_opt ⦃ pre ⦄
      progL ≈( ε ) progR
    ⦃ same_result_opt ⦄.
  Proof.
    move=> Heps Htv.
    split; first exact: Heps.
    move=> memL memR xL xR Hpre.
    set outL := Pr_code (progL xL) memL.
    set outR := Pr_code (progR xR) memR.
    pose strip (out : option (out_t * heap)) : option out_t :=
      omap fst out.
    have Htv_projected :
        total_variation
          (dmargin strip (complete outL))
          (dmargin strip (complete outR)) <= ε.
      rewrite (total_variation_ext
        (dmargin strip (complete outL))
        (complete (dmargin fst outL))
        (dmargin strip (complete outR))
        (complete (dmargin fst outR))).
      exact: Htv.
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
    - split.
      + exact: HdL.
      + exact: HdR.
    - apply: (le_trans Hprob).
      apply: subset_pr=> xy Hxy.
      case: xy Hxy=> outL' outR'.
      by rewrite /same_result_opt /strip.
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

  Lemma additiveErrorOptSeqSameResultSimDecryptReductionRule
      {inL_t inR_t mid_t out_t : choice_type}
      (progL : inL_t -> raw_code mid_t)
      (progR : inR_t -> raw_code mid_t)
      (contL contR : mid_t -> raw_code out_t)
      (pre : pred ((inL_t * heap) * (inR_t * heap))) :
    ⊨AE_opt ⦃ pre ⦄
      progL
      ≈( 0 )
      progR
    ⦃ same_result_sim_decrypt_reduction_opt ⦄ ->
    ⊨AE_opt ⦃ same_input_sim_decrypt_reduction_pre ⦄
      contL
      ≈( 0 )
      contR
    ⦃ same_result_sim_decrypt_reduction_opt ⦄ ->
    ⊨AE_opt ⦃ pre ⦄
      (fun xL => yL ← progL xL ;; contL yL)
      ≈( 0 )
      (fun xR => yR ← progR xR ;; contR yR)
    ⦃ same_result_sim_decrypt_reduction_opt ⦄.
  Proof.
    move=> Hprefix Hcont.
    split; first exact: lexx.
    move=> memL memR xL xR Hpre.
    have [d0 [Hd0 Hmidprob]] := Hprefix.2 memL memR xL xR Hpre.
    pose mid := (@same_input_sim_decrypt_reduction_pre mid_t).
    pose post := (@same_result_sim_decrypt_reduction_opt out_t).
    pose KL (ymem : mid_t * heap) := Pr_code (contL ymem.1) ymem.2.
    pose KR (ymem : mid_t * heap) := Pr_code (contR ymem.1) ymem.2.
    pose K := additiveErrorOptSeqKernel contL contR mid post 0 Hcont.2.
    exists (\dlet_(xy <- d0) K xy).
    split.
    - have Hbind := coupling_bind_kernel d0
        (complete (Pr_code (progL xL) memL))
        (complete (Pr_code (progR xR) memR))
        K (complete_bind_kernel KL) (complete_bind_kernel KR)
        Hd0
        (additiveErrorOptSeqKernel_margins
          contL contR mid post 0 Hcont.2).
      move: Hbind=> [HL HR].
      split.
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
    - have Hprob :
          \P_[\dlet_(xy <- d0) K xy] post >= 1 - (0 + 0).
        apply: (pr_dlet_lower_bound_good d0 K
          (@same_result_sim_decrypt_reduction_opt mid_t) post 0 0).
        + exact: lexx.
        + exact: lexx.
        + exact: Hmidprob.
        + move=> xy Hxy.
          case: xy Hxy=> [[ymemL|] [ymemR|]] /=.
          * case: ymemL=> yL memL'.
            case: ymemR=> yR memR' /= Hmid.
            have Hgood :
                additiveErrorOptSeqGood mid
                  (Some (yL, memL'), Some (yR, memR')).
              by rewrite /additiveErrorOptSeqGood /mid
                /same_input_sim_decrypt_reduction_pre.
            exact: (additiveErrorOptSeqKernel_event
              contL contR mid post 0 Hcont.2 _ Hgood).
          * by case: ymemL.
          * by case: ymemR.
          * have HKnone :
                K (None, None) =1 dunit (None, None).
              move=> z.
              rewrite /K /additiveErrorOptSeqKernel
                /complete_bind_fallback_coupling /complete_bind_kernel
                /product_coupling.
              by rewrite !dlet_unit.
            rewrite (pr_ext _ _ post HKnone).
            rewrite pr_dunit /post /same_result_sim_decrypt_reduction_opt /=.
            by rewrite lerBlDr lerDl.
      by rewrite addr0 in Hprob.
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

  Lemma reduction_initialized_heap_bit b pk evk :
    get_heap (reduction_initialized_heap b pk evk)
      IndCpaSecurity.IndCpaGame.bit_addr = b.
  Proof.
    rewrite /reduction_initialized_heap.
    repeat first [
      rewrite get_set_heap_eq
    | rewrite get_set_heap_neq; [| neq_loc_auto]
    | rewrite get_empty_heap
    ].
    by [].
  Qed.

  Lemma reduction_initialized_heap_pk_outer b pk evk :
    get_heap (reduction_initialized_heap b pk evk)
      IndCpaSecurity.IndCpaGame.pk_addr = Some pk.
  Proof.
    rewrite /reduction_initialized_heap.
    repeat first [
      rewrite get_set_heap_eq
    | rewrite get_set_heap_neq; [| neq_loc_auto]
    | rewrite get_empty_heap
    ].
    by [].
  Qed.

  Lemma reduction_initialized_heap_evk_outer b pk evk :
    get_heap (reduction_initialized_heap b pk evk)
      IndCpaSecurity.IndCpaGame.evk_addr = Some evk.
  Proof.
    rewrite /reduction_initialized_heap.
    repeat first [
      rewrite get_set_heap_eq
    | rewrite get_set_heap_neq; [| neq_loc_auto]
    | rewrite get_empty_heap
    ].
    by [].
  Qed.

  Lemma reduction_initialized_heap_ready b pk evk :
    get_heap (reduction_initialized_heap b pk evk)
      IndCpaDSim.ready_addr = true.
  Proof.
    rewrite /reduction_initialized_heap.
    repeat first [
      rewrite get_set_heap_eq
    | rewrite get_set_heap_neq; [| neq_loc_auto]
    | rewrite get_empty_heap
    ].
    by [].
  Qed.

  Lemma reduction_initialized_heap_pk_sim b pk evk :
    get_heap (reduction_initialized_heap b pk evk)
      IndCpaDSim.pk_addr = Some pk.
  Proof.
    rewrite /reduction_initialized_heap.
    repeat first [
      rewrite get_set_heap_eq
    | rewrite get_set_heap_neq; [| neq_loc_auto]
    | rewrite get_empty_heap
    ].
    by [].
  Qed.

  Lemma reduction_initialized_heap_evk_sim b pk evk :
    get_heap (reduction_initialized_heap b pk evk)
      IndCpaDSim.evk_addr = Some evk.
  Proof.
    rewrite /reduction_initialized_heap.
    repeat first [
      rewrite get_set_heap_eq
    | rewrite get_set_heap_neq; [| neq_loc_auto]
    | rewrite get_empty_heap
    ].
    by [].
  Qed.

  Lemma reduction_initialized_heap_table b pk evk :
    get_heap (reduction_initialized_heap b pk evk)
      IndCpaDSim.table_addr = [::].
  Proof.
    rewrite /reduction_initialized_heap.
    repeat first [
      rewrite get_set_heap_eq
    | rewrite get_set_heap_neq; [| neq_loc_auto]
    | rewrite get_empty_heap
    ].
    by [].
  Qed.

  Lemma reduction_initialized_heap_decrypt_count b pk evk :
    get_heap (reduction_initialized_heap b pk evk)
      IndCpaDSim.decrypt_count_addr = 0.
  Proof.
    rewrite /reduction_initialized_heap.
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
    ⊨AE_opt ⦃ same_input_decrypt_over_bound_pre max_queries ⦄
      (fun i : nat =>
        resolve (IndCpadGame.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) i)
    ≈( 0 )
      (fun i : nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) i)
    ⦃ same_result_opt ⦄.
  Proof.
    apply: additiveErrorOptSameResultTvdEqRule.
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
    ⊨AE_opt ⦃ same_input_decrypt_over_bound_pre max_queries ⦄
      (fun i : nat =>
        resolve (IndCpadGame.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) i)
    ≈( 0 )
      (fun i : nat =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) i)
    ⦃ same_output_heap_opt ⦄.
  Proof.
    apply: additiveErrorOptSameOutputTvdEqRule.
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
          (ivec_dist ivec_zero (isometry (dec' sk c) m0)
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

  Lemma challenge_decrypt_prefix_row_ready_vector_bound_equal_messages_some
      mem m c :
    challenge_decrypt_prefix_row_ready_vector_bound (m, m, c) mem ->
    exists sk data error_bound,
      get_heap mem IndCpadGame.sk_addr = Some sk /\
      c = Some (data, error_bound) /\
      (ivec_dist ivec_zero (isometry (dec' sk c) m)
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
    finite_encoding_cert ->
    chart_center_dist_le_metric_cert ->
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
    move=> Henc Hchart.
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
        sk data error_bound m Henc Hchart Hmetric.
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

  Lemma ind_cpad_decrypt_cont_eq_pyth_from_finite_encoding_vector_bound
      {enc_dim : nat} (enc : message -> 'I_enc_dim)
      (common : dim.-tuple int -> 'I_enc_dim) m c :
    injective enc ->
    (forall (sk : sk_t) (data : encryption) (error_bound : nat),
      c = Some (data, error_bound) ->
      (ivec_dist (isometry (dec' sk c) (dec' sk c)) (isometry m m)
        <= error_bound)%N) ->
    (forall (sk : sk_t) (data : encryption) (error_bound : nat),
      c = Some (data, error_bound) ->
      let stdev :=
        noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
      let P :=
        n_dg_shifted (isometry (dec' sk c) (dec' sk c)) stdev in
      dmargin common P =1
        dmargin (fun v => enc (inverse_isometry (dec' sk c) v)) P) ->
    (forall (sk : sk_t) (data : encryption) (error_bound : nat),
      c = Some (data, error_bound) ->
      let stdev :=
        noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
      let Q := n_dg_shifted (isometry m m) stdev in
      dmargin common Q =1
        dmargin (fun v => enc (inverse_isometry m v)) Q) ->
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
    move=> Henc Hvecdist HcommonL HcommonR.
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
      noise_flooding_successful_decrypt_code_pyth_from_finite_encoding_vector_bound
        enc common sk data error_bound m Henc
        (Hvecdist sk data error_bound erefl)
        (HcommonL sk data error_bound erefl)
        (HcommonR sk data error_bound erefl).
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

  Lemma ind_cpad_decrypt_cont_eq_pyth_from_finite_encoding_same_chart_center
      {enc_dim : nat} (enc : message -> 'I_enc_dim)
      (common : dim.-tuple int -> 'I_enc_dim) m c :
    injective enc ->
    (forall (sk : sk_t) (data : encryption) (error_bound : nat),
      c = Some (data, error_bound) ->
      isometry (dec' sk c) (dec' sk c) = isometry m m) ->
    (forall (sk : sk_t) (data : encryption) (error_bound : nat),
      c = Some (data, error_bound) ->
      let stdev :=
        noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
      let P :=
        n_dg_shifted (isometry (dec' sk c) (dec' sk c)) stdev in
      dmargin common P =1
        dmargin (fun v => enc (inverse_isometry (dec' sk c) v)) P) ->
    (forall (sk : sk_t) (data : encryption) (error_bound : nat),
      c = Some (data, error_bound) ->
      let stdev :=
        noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
      let Q := n_dg_shifted (isometry m m) stdev in
      dmargin common Q =1
        dmargin (fun v => enc (inverse_isometry m v)) Q) ->
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
    move=> Henc Hcenter HcommonL HcommonR.
    apply: (ind_cpad_decrypt_cont_eq_pyth_from_finite_encoding_vector_bound
      enc common m c Henc _ HcommonL HcommonR).
    move=> sk data error_bound Hc.
    by rewrite (Hcenter sk data error_bound Hc) ivec_dist_refl.
  Qed.

  Lemma ind_cpad_decrypt_cont_eq_pyth1_from_finite_encoding_vector_bound
      {enc_dim : nat} (enc : message -> 'I_enc_dim)
      (common : dim.-tuple int -> 'I_enc_dim) m c :
    injective enc ->
    (forall (sk : sk_t) (data : encryption) (error_bound : nat),
      c = Some (data, error_bound) ->
      (ivec_dist (isometry (dec' sk c) (dec' sk c)) (isometry m m)
        <= error_bound)%N) ->
    (forall (sk : sk_t) (data : encryption) (error_bound : nat),
      c = Some (data, error_bound) ->
      let stdev :=
        noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
      let P :=
        n_dg_shifted (isometry (dec' sk c) (dec' sk c)) stdev in
      dmargin common P =1
        dmargin (fun v => enc (inverse_isometry (dec' sk c) v)) P) ->
    (forall (sk : sk_t) (data : encryption) (error_bound : nat),
      c = Some (data, error_bound) ->
      let stdev :=
        noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
      let Q := n_dg_shifted (isometry m m) stdev in
      dmargin common Q =1
        dmargin (fun v => enc (inverse_isometry m v)) Q) ->
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
    move=> Henc Hvecdist HcommonL HcommonR.
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
      noise_flooding_successful_decrypt_code_pyth1_from_finite_encoding_vector_bound
        enc common sk data error_bound m Henc
        (Hvecdist sk data error_bound erefl)
        (HcommonL sk data error_bound erefl)
        (HcommonR sk data error_bound erefl).
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

  Lemma ind_cpad_decrypt_cont_eq_pyth1_from_finite_encoding_same_chart_center
      {enc_dim : nat} (enc : message -> 'I_enc_dim)
      (common : dim.-tuple int -> 'I_enc_dim) m c :
    injective enc ->
    (forall (sk : sk_t) (data : encryption) (error_bound : nat),
      c = Some (data, error_bound) ->
      isometry (dec' sk c) (dec' sk c) = isometry m m) ->
    (forall (sk : sk_t) (data : encryption) (error_bound : nat),
      c = Some (data, error_bound) ->
      let stdev :=
        noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
      let P :=
        n_dg_shifted (isometry (dec' sk c) (dec' sk c)) stdev in
      dmargin common P =1
        dmargin (fun v => enc (inverse_isometry (dec' sk c) v)) P) ->
    (forall (sk : sk_t) (data : encryption) (error_bound : nat),
      c = Some (data, error_bound) ->
      let stdev :=
        noise_flooding_dg_stdev gaussian_width_multiplier error_bound in
      let Q := n_dg_shifted (isometry m m) stdev in
      dmargin common Q =1
        dmargin (fun v => enc (inverse_isometry m v)) Q) ->
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
    move=> Henc Hcenter HcommonL HcommonR.
    apply: (ind_cpad_decrypt_cont_eq_pyth1_from_finite_encoding_vector_bound
      enc common m c Henc _ HcommonL HcommonR).
    move=> sk data error_bound Hc.
    by rewrite (Hcenter sk data error_bound Hc) ivec_dist_refl.
  Qed.

  Lemma ind_cpad_decrypt_cont_eq_pyth_from_metric_encoding_vector_bound m c :
    finite_encoding_cert ->
    (forall (sk : sk_t) (data : encryption) (error_bound : nat),
      c = Some (data, error_bound) ->
      (ivec_dist (isometry (dec' sk c) (dec' sk c)) (isometry m m)
        <= error_bound)%N) ->
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
    move=> Henc Hvecdist.
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
      noise_flooding_successful_decrypt_code_pyth_from_metric_encoding_vector_bound
        sk data error_bound m
        Henc
        (Hvecdist sk data error_bound erefl).
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

  Lemma ind_cpad_decrypt_cont_eq_pyth_from_metric_encoding_same_chart_center m c :
    finite_encoding_cert ->
    (forall (sk : sk_t) (data : encryption) (error_bound : nat),
      c = Some (data, error_bound) ->
      isometry (dec' sk c) (dec' sk c) = isometry m m) ->
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
    move=> Henc Hcenter.
    apply: (ind_cpad_decrypt_cont_eq_pyth_from_metric_encoding_vector_bound
      m c Henc).
    move=> sk data error_bound Hc.
    by rewrite (Hcenter sk data error_bound Hc) ivec_dist_refl.
  Qed.

  Lemma ind_cpad_decrypt_cont_eq_pyth1_from_metric_encoding_vector_bound m c :
    finite_encoding_cert ->
    (forall (sk : sk_t) (data : encryption) (error_bound : nat),
      c = Some (data, error_bound) ->
      (ivec_dist (isometry (dec' sk c) (dec' sk c)) (isometry m m)
        <= error_bound)%N) ->
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
    move=> Henc Hvecdist.
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
      noise_flooding_successful_decrypt_code_pyth1_from_metric_encoding_vector_bound
        sk data error_bound m
        Henc
        (Hvecdist sk data error_bound erefl).
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

  Lemma ind_cpad_decrypt_cont_eq_pyth1_from_metric_encoding_same_chart_center m c :
    finite_encoding_cert ->
    (forall (sk : sk_t) (data : encryption) (error_bound : nat),
      c = Some (data, error_bound) ->
      isometry (dec' sk c) (dec' sk c) = isometry m m) ->
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
    move=> Henc Hcenter.
    apply: (ind_cpad_decrypt_cont_eq_pyth1_from_metric_encoding_vector_bound
      m c Henc).
    move=> sk data error_bound Hc.
    by rewrite (Hcenter sk data error_bound Hc) ivec_dist_refl.
  Qed.

  Lemma ind_cpad_decrypt_cont_eq_pyth_from_metric_encoding_ready_vector_bound
      m c :
    ⊨Pyth ⦃ fun inps =>
      let '((_, memL), (_, memR)) := inps in
      (eq_op memL memR) &&
      challenge_decrypt_prefix_row_ready_vector_bound (m, m, c) memL ⦄
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

  Lemma ind_cpad_decrypt_cont_eq_pyth1_from_metric_encoding_ready_vector_bound
      m c :
    finite_message_encoding_cert ->
    ⊨Pyth1 ⦃ fun inps =>
      let '((_, memL), (_, memR)) := inps in
      (eq_op memL memR) &&
      challenge_decrypt_prefix_row_ready_vector_bound (m, m, c) memL ⦄
      (fun _ : chUnit => ind_cpad_real_decrypt_cont (m, m, c))
      ≈( noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier )
      (fun _ : chUnit => ind_cpad_sim_decrypt_cont (m, m, c))
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    move=> Henc.
    split.
    - move=> i.
      by rewrite [i]ord1 noise_flooding_per_query_epsilon_nonnegative.
    move=> memL memR [] [] Hpre.
    move/andP: Hpre=> [/eqP Hmem Hready].
    subst memR.
    move/andP: Hready=> [Hready _].
    have [sk [data [error_bound [Hsk [Hc Hmetric]]]]] :=
      challenge_decrypt_prefix_row_ready_equal_messages_some
        memL m c Hready.
    subst c.
    have Hpyth :=
      noise_flooding_successful_decrypt_code_pyth1_one_chart
        sk data error_bound m Henc Hmetric.
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
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] [tuple 0] )
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

  Lemma ind_cpad_decrypt_cont_pyth1_from_metric_encoding_ready_vector_bound
      (row : IndCpadGame.challenger_table_row) :
    finite_message_encoding_cert ->
    ⊨Pyth1 ⦃ fun inps =>
      let '((_, memL), (_, memR)) := inps in
      (eq_op memL memR) &&
      challenge_decrypt_prefix_row_ready_vector_bound row memL ⦄
      (fun _ : chUnit => ind_cpad_real_decrypt_cont row)
      ≈( noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier )
      (fun _ : chUnit => ind_cpad_sim_decrypt_cont row)
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    move=> Henc.
    case: row=> [[m0 m1] c].
    destruct (eq_op m0 m1) eqn:Heq.
    - have Hm : m0 = m1 := eqP Heq.
      subst m1.
      exact: (ind_cpad_decrypt_cont_eq_pyth1_from_metric_encoding_ready_vector_bound
        m0 c Henc).
    rewrite /ind_cpad_real_decrypt_cont /ind_cpad_sim_decrypt_cont Heq.
    apply: pythReflRule.
    - move=> i.
      by rewrite [i]ord1 noise_flooding_per_query_epsilon_nonnegative.
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
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] [tuple 0] )
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
    finite_encoding_cert ->
    chart_center_dist_le_metric_cert ->
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
    move=> Henc Hchart.
    case: row=> [[m0 m1] c].
    destruct (eq_op m0 m1) eqn:Heq.
    - have Hm : m0 = m1 := eqP Heq.
      subst m1.
      exact: (ind_cpad_decrypt_cont_eq_pyth1 m0 c Henc Hchart).
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
    finite_encoding_cert ->
    chart_center_dist_le_metric_cert ->
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
    move=> Henc Hchart.
    split.
    - move=> i.
      by rewrite [i]ord1 noise_flooding_per_query_epsilon_nonnegative.
    move=> memL memR rowL rowR Hpre.
    move/andP: Hpre=> [/andP [/eqP Hrow /eqP Hmem] Hready].
    subst rowR.
    subst memR.
    have [_ Hpyth] := ind_cpad_decrypt_cont_pyth1 rowL Henc Hchart.
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

  Lemma ind_cpad_decrypt_cont_kernel_pyth1_from_metric_encoding_ready_vector_bound :
    finite_message_encoding_cert ->
    ⊨Pyth1 ⦃ fun inps =>
      let '((rowL, memL), (rowR, memR)) := inps in
      (rowL == rowR) && (memL == memR) &&
      challenge_decrypt_prefix_row_ready_vector_bound rowL memL ⦄
      ind_cpad_real_decrypt_cont
      ≈( noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier )
      ind_cpad_sim_decrypt_cont
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    move=> Henc.
    split.
    - move=> i.
      by rewrite [i]ord1 noise_flooding_per_query_epsilon_nonnegative.
    move=> memL memR rowL rowR Hpre.
    move/andP: Hpre=> [/andP [/eqP Hrow /eqP Hmem] Hready].
    subst rowR.
    subst memR.
    have [_ Hpyth] :=
      ind_cpad_decrypt_cont_pyth1_from_metric_encoding_ready_vector_bound
        rowL Henc.
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
    finite_encoding_cert ->
    chart_center_dist_le_metric_cert ->
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
    move=> Henc Hchart.
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
    - exact: (ind_cpad_decrypt_cont_kernel_pyth1 Henc Hchart).
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
          [tuple noise_flooding_per_query_epsilon
            dim gaussian_width_multiplier] [tuple 0]) )
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
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] [tuple 0])).
    - move=> memL memR iL iR Hpre.
      move/andP: Hpre=> [/andP [/eqP Hi /eqP Hmem] Hinv].
      by split; [exact: Hi | split].
    - exact: Hprefix_vector.
    - exact: ind_cpad_decrypt_cont_kernel_pyth_from_metric_encoding_ready_vector_bound.
  Qed.

  Lemma ind_cpad_decrypt_factored_pyth_short_from_metric_encoding_ready_vector_bound
      max_queries :
    finite_message_encoding_cert ->
    decrypt_prefix_ready_vector_bound_cert max_queries ->
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
    move=> Henc Hprefix_vector.
    apply: (pythHoareSeqRule
      (ind_cpad_decrypt_prefix_code max_queries)
      ind_cpad_real_decrypt_cont
      ind_cpad_sim_decrypt_cont
      (fun in_mem => challenge_heap_valid in_mem.2)
      (same_input_invariant_pre challenge_heap_valid)
      (fun out_mem =>
        challenge_decrypt_prefix_row_ready_vector_bound out_mem.1 out_mem.2)
      (fun _ : chOption message * heap => true)
      [tuple noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier]).
    - move=> memL memR iL iR Hpre.
      move/andP: Hpre=> [/andP [/eqP Hi /eqP Hmem] Hinv].
      by split; [exact: Hi | split].
    - exact: Hprefix_vector.
    - exact: (ind_cpad_decrypt_cont_kernel_pyth1_from_metric_encoding_ready_vector_bound
        Henc).
  Qed.

  Lemma ind_cpad_decrypt_factored_pyth_from_metric_encoding
      max_queries :
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
    exact: (ind_cpad_decrypt_factored_pyth_from_metric_encoding_ready_vector_bound
      max_queries
      (ind_cpad_decrypt_prefix_code_readies_row_vector_bound
        max_queries)).
  Qed.

  Lemma ind_cpad_decrypt_factored_pyth_short_from_metric_encoding
      max_queries :
    finite_message_encoding_cert ->
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
    move=> Henc.
    exact: (ind_cpad_decrypt_factored_pyth_short_from_metric_encoding_ready_vector_bound
      max_queries Henc
      (ind_cpad_decrypt_prefix_code_readies_row_vector_bound
        max_queries)).
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

  Lemma ind_cpad_decrypt_code_pyth_short max_queries :
    finite_encoding_cert ->
    chart_center_dist_le_metric_cert ->
    ⊨Pyth ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (ind_cpad_real_decrypt_code max_queries)
      ≈( cat_tuple [tuple 0]
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] )
      (ind_cpad_sim_decrypt_code max_queries)
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    move=> Henc Hchart.
    have Hfactored := ind_cpad_decrypt_factored_pyth_short
      max_queries Henc Hchart.
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
          [tuple noise_flooding_per_query_epsilon
            dim gaussian_width_multiplier] [tuple 0]) )
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

  Lemma ind_cpad_decrypt_code_pyth_short_from_metric_encoding_ready_vector_bound
      max_queries :
    finite_message_encoding_cert ->
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    ⊨Pyth ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (ind_cpad_real_decrypt_code max_queries)
      ≈( cat_tuple [tuple 0]
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] )
      (ind_cpad_sim_decrypt_code max_queries)
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    move=> Henc Hprefix_vector.
    have Hfactored :=
      ind_cpad_decrypt_factored_pyth_short_from_metric_encoding_ready_vector_bound
        max_queries Henc Hprefix_vector.
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
          [tuple noise_flooding_per_query_epsilon
            dim gaussian_width_multiplier] [tuple 0]) )
      (ind_cpad_sim_decrypt_code max_queries)
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    exact: (ind_cpad_decrypt_code_pyth_from_metric_encoding_ready_vector_bound
      max_queries
      (ind_cpad_decrypt_prefix_code_readies_row_vector_bound
        max_queries)).
  Qed.

  Lemma ind_cpad_decrypt_code_pyth_short_from_metric_encoding
      max_queries :
    finite_message_encoding_cert ->
    ⊨Pyth ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (ind_cpad_real_decrypt_code max_queries)
      ≈( cat_tuple [tuple 0]
        [tuple noise_flooding_per_query_epsilon
          dim gaussian_width_multiplier] )
      (ind_cpad_sim_decrypt_code max_queries)
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    move=> Henc.
    exact: (ind_cpad_decrypt_code_pyth_short_from_metric_encoding_ready_vector_bound
      max_queries Henc
      (ind_cpad_decrypt_prefix_code_readies_row_vector_bound
        max_queries)).
  Qed.

  Lemma ind_cpad_decrypt_code_pyth1_from_metric_encoding_ready_vector_bound
      max_queries :
    finite_message_encoding_cert ->
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    ⊨Pyth1 ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (ind_cpad_real_decrypt_code max_queries)
      ≈( noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier )
      (ind_cpad_sim_decrypt_code max_queries)
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    move=> Henc Hprefix_vector.
    split.
    - move=> i.
      by rewrite [i]ord1 noise_flooding_per_query_epsilon_nonnegative.
    move=> memL memR iL iR Hpre.
    move/andP: Hpre=> [/andP [/eqP Hi /eqP Hmem] Hinv].
    subst iL.
    subst memL.
    rewrite /ind_cpad_real_decrypt_code /ind_cpad_sim_decrypt_code.
    rewrite !Pr_code_get.
    case Hcount:
        (get_heap memR IndCpadGame.decrypt_count_addr < max_queries)%N.
    - rewrite /assertD /= !Pr_code_put !Pr_code_get.
      set mem1 := set_heap memR IndCpadGame.decrypt_count_addr
        (get_heap memR IndCpadGame.decrypt_count_addr).+1.
      rewrite /assertD.
      destruct (@idP
        (iR < length (get_heap mem1 IndCpadGame.table_addr))%N)
        as [i_in_range|i_not_in_range].
      + simpl.
        case Hrow:
            (nth_valid (get_heap mem1 IndCpadGame.table_addr) iR
              i_in_range)=> [[m0 m1] c].
        have Hrow_prop :
            nth_valid (get_heap mem1 IndCpadGame.table_addr) iR
              i_in_range = (m0, m1, c).
          exact: Hrow.
        have Hprefix_supp :
            ((m0, m1, c), mem1) \in dinsupp
              (Pr_code (ind_cpad_decrypt_prefix_code max_queries iR) memR).
          rewrite /ind_cpad_decrypt_prefix_code.
          rewrite Pr_code_get /assertD Hcount /= Pr_code_put Pr_code_get.
          apply: (dinsupp_assertD_intro _ _ _ _ i_in_range).
          rewrite Pr_code_ret.
          apply/dinsuppP.
          rewrite dunit1E.
          apply/eqP.
          by rewrite Hrow_prop eqxx oner_neq0.
        have Hready :=
          Hprefix_vector iR memR Hinv ((m0, m1, c), mem1) Hprefix_supp.
        have [_ Hcont] :=
          ind_cpad_decrypt_cont_pyth1_from_metric_encoding_ready_vector_bound
            (m0, m1, c) Henc.
        have Hpre_cont :
            (let '((_, memL0), (_, memR0)) :=
                ((tt, mem1), (tt, mem1)) in
              (eq_op memL0 memR0) &&
              challenge_decrypt_prefix_row_ready_vector_bound
                (m0, m1, c) memL0).
          by rewrite eqxx Hready.
        have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
          Hcont mem1 mem1 tt tt Hpre_cont.
        exists P, Q.
        split; first exact: Hdist.
        split.
        * move=> out.
          rewrite (HmarginL out).
          symmetry.
          apply: complete_output_heap_ext=> out'.
          have Hrange_eq :
              (iR < length (get_heap mem1 IndCpadGame.table_addr))%N = true.
            exact: i_in_range.
          rewrite (Pr_code_assertD_true_ext _ _ Hrange_eq mem1 out').
          rewrite /ind_cpad_real_decrypt_cont.
          rewrite (nth_valid_irrel
            (get_heap mem1 IndCpadGame.table_addr) iR
            Hrange_eq i_in_range).
          by rewrite Hrow.
        split.
        * move=> out.
          rewrite (HmarginR out).
          symmetry.
          apply: complete_output_heap_ext=> out'.
          have Hrange_eq :
              (iR < length (get_heap mem1 IndCpadGame.table_addr))%N = true.
            exact: i_in_range.
          rewrite (Pr_code_assertD_true_ext _ _ Hrange_eq mem1 out').
          rewrite /ind_cpad_sim_decrypt_cont.
          rewrite (nth_valid_irrel
            (get_heap mem1 IndCpadGame.table_addr) iR
            Hrange_eq i_in_range).
          by rewrite Hrow.
        by split.
      + apply: pyth1_current_refl_witness.
        * exact: noise_flooding_per_query_epsilon_nonnegative.
        * move=> out.
          have Hrange_false :
              (iR < length (get_heap mem1 IndCpadGame.table_addr))%N = false.
            case Hrange:
                (iR < length (get_heap mem1 IndCpadGame.table_addr))%N.
            - by move: i_not_in_range; rewrite Hrange.
            - by [].
          rewrite (Pr_code_assertD_false_ext _ _ mem1 Hrange_false out).
          by rewrite (Pr_code_assertD_false_ext _ _ mem1 Hrange_false out).
        * by move=> y Hy.
        * by move=> y Hy.
    - apply: pyth1_current_refl_witness.
      + exact: noise_flooding_per_query_epsilon_nonnegative.
      + move=> out.
        by rewrite /assertD /= !Pr_code_fail.
      + by move=> y Hy.
      + by move=> y Hy.
  Qed.

  Lemma ind_cpad_decrypt_code_pyth1 max_queries :
    finite_message_encoding_cert ->
    ⊨Pyth1 ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (ind_cpad_real_decrypt_code max_queries)
      ≈( noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier )
      (ind_cpad_sim_decrypt_code max_queries)
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    move=> Henc.
    exact: (ind_cpad_decrypt_code_pyth1_from_metric_encoding_ready_vector_bound
      max_queries Henc
      (ind_cpad_decrypt_prefix_code_readies_row_vector_bound
        max_queries)).
  Qed.

  Lemma ind_cpad_decrypt_code_pyth1_from_metric_encoding
      max_queries :
    finite_message_encoding_cert ->
    ⊨Pyth1 ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (ind_cpad_real_decrypt_code max_queries)
      ≈( noise_flooding_per_query_epsilon
        dim gaussian_width_multiplier )
      (ind_cpad_sim_decrypt_code max_queries)
    ⦃ fun _ : chOption message * heap => true ⦄.
  Proof.
    exact: ind_cpad_decrypt_code_pyth1.
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
    finite_message_encoding_cert ->
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
    move=> Henc.
    have Hcode :=
      ind_cpad_decrypt_code_pyth_short_from_metric_encoding
        max_queries Henc.
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

  Lemma ind_cpad_decrypt_resolve_pyth_from_metric_encoding_ready_vector_bound
      max_queries :
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    ⊨Pyth ⦃ same_input_invariant_pre challenge_heap_valid ⦄
      (fun x : nat =>
        resolve (IndCpadGame.IndCpadOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
      ≈( cat_tuple [tuple 0]
        (cat_tuple
          [tuple noise_flooding_per_query_epsilon
            dim gaussian_width_multiplier] [tuple 0]) )
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
          [tuple noise_flooding_per_query_epsilon
            dim gaussian_width_multiplier] [tuple 0]) )
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

  Lemma ind_cpad_decrypt_resolve_pyth1_from_metric_encoding_ready_vector_bound
      max_queries :
    finite_message_encoding_cert ->
    decrypt_prefix_ready_vector_bound_cert max_queries ->
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
      let '(_, mem) := out in challenge_heap_valid mem ⦄.
  Proof.
    move=> Henc Hprefix_vector.
    have Hcode :=
      ind_cpad_decrypt_code_pyth1_from_metric_encoding_ready_vector_bound
        max_queries Henc Hprefix_vector.
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

  Lemma ind_cpad_decrypt_resolve_pyth1 max_queries :
    finite_message_encoding_cert ->
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
      let '(_, mem) := out in challenge_heap_valid mem ⦄.
  Proof.
    move=> Henc.
    exact: (ind_cpad_decrypt_resolve_pyth1_from_metric_encoding_ready_vector_bound
      max_queries Henc
      (ind_cpad_decrypt_prefix_code_readies_row_vector_bound
        max_queries)).
  Qed.

  Lemma ind_cpad_decrypt_resolve_pyth1_from_metric_encoding
      max_queries :
    finite_message_encoding_cert ->
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
      let '(_, mem) := out in challenge_heap_valid mem ⦄.
  Proof.
    exact: ind_cpad_decrypt_resolve_pyth1.
  Qed.

  Lemma pythagorean_tv_bound_cat0_singleton (eps : R) :
    pythagorean_tv_bound (cat_tuple [tuple 0] [tuple eps]) =
    Num.sqrt (eps / 2).
  Proof.
    rewrite /pythagorean_tv_bound /tuple_sum /=.
    rewrite !big_ord_recl big_ord0 /=.
    by rewrite !(tnth_nth 0) /= add0r addr0.
  Qed.

  Lemma tuple_sum_noise_flooding_vector_call_error :
    tuple_sum
      (cat_tuple [tuple 0]
        (cat_tuple
          [tuple noise_flooding_per_query_epsilon
            dim gaussian_width_multiplier] [tuple 0])) =
    noise_flooding_per_query_epsilon dim gaussian_width_multiplier.
  Proof.
    by rewrite !tuple_sum_cat !tuple_sum_singleton add0r addr0.
  Qed.

  Lemma ind_cpad_decrypt_resolve_additive_error_short max_queries :
    finite_message_encoding_cert ->
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
    move=> Henc.
    rewrite -pythagorean_tv_bound_cat0_singleton.
    exact: (MicciancioWalterRule _ _ _ _ _
      (ind_cpad_decrypt_resolve_pyth_short max_queries Henc)).
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

  Lemma resolve_alpha (P P' : nom_package) (o : opsig) (x : src o) :
    P ≡ P' ->
    resolve P o x ≡ resolve P' o x.
  Proof.
    move=> [π Hπ].
    exists π.
    rewrite rename_resolve.
    change (resolve (val (π ∙ P)) o x = resolve (val P') o x).
    by rewrite Hπ.
  Qed.

  Definition sim_decrypt_reduction_adversary_heap_eq
      (A : nom_package) (memL memR : heap) : Prop :=
    heap_eq_on_renamed
      (sim_decrypt_reduction_moved_adversary_perm A)
      (loc (ind_cpad_moved_adversary A)) memL memR.

  Lemma sim_decrypt_reduction_adversary_heap_eq_refl
      (A : nom_package) mem :
    sim_decrypt_reduction_adversary_heap_eq A mem
      (sim_decrypt_reduction_moved_adversary_perm A ∙ mem).
  Proof.
    exact: heap_eq_on_renamed_refl.
  Qed.

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

  Lemma sim_decrypt_reduction_adv_heap_rel_project A memL memR :
    sim_decrypt_reduction_adv_heap_rel A memL memR ->
    sim_decrypt_reduction_heap_rel memL memR.
  Proof. by case. Qed.

  Lemma same_input_sim_decrypt_reduction_adv_pre_project
      A {T : choice_type} (inps : (T * heap) * (T * heap)) :
    same_input_sim_decrypt_reduction_adv_pre A inps ->
    same_input_sim_decrypt_reduction_pre inps.
  Proof.
    case: inps=> [[xL memL] [xR memR]] /=.
    move=> [-> [Hrel _]].
    by rewrite /same_input_sim_decrypt_reduction_pre /= eqxx Hrel.
  Qed.

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

  Lemma supports_same_result_sim_decrypt_reduction_adv_opt_pr_ge1
      A {out_t : choice_type}
      (d : {distr
        (option (out_t * heap) * option (out_t * heap)) / R})
      (outL outR : {distr (out_t * heap) / R}) :
    clean_coupling d (complete outL) (complete outR) ->
    supports_same_result_sim_decrypt_reduction_adv_opt A d ->
    \P_[d] same_result_opt >= 1.
  Proof.
    move=> [HdL _] Hsupport.
    have Hdweight : dweight d = 1.
      rewrite -(dmargin_dweight fst d).
      transitivity (dweight (complete outL)).
      - apply: eq_psum=> z.
        by rewrite !mul1r HdL.
      - exact: complete_dweight.
    rewrite (pr_eq1_of_support d same_result_opt Hdweight).
    - exact: lexx.
    - move=> outs Houts.
      exact: (same_result_sim_decrypt_reduction_adv_result_opt A outs
        (Hsupport outs Houts)).
  Qed.

  Lemma supports_same_result_sim_decrypt_reduction_adv_opt_rel_pr_ge1
      A {out_t : choice_type}
      (d : {distr
        (option (out_t * heap) * option (out_t * heap)) / R})
      (outL outR : {distr (out_t * heap) / R}) :
    clean_coupling d (complete outL) (complete outR) ->
    supports_same_result_sim_decrypt_reduction_adv_opt A d ->
    \P_[d] same_result_sim_decrypt_reduction_opt >= 1.
  Proof.
    move=> [HdL _] Hsupport.
    have Hdweight : dweight d = 1.
      rewrite -(dmargin_dweight fst d).
      transitivity (dweight (complete outL)).
      - apply: eq_psum=> z.
        by rewrite !mul1r HdL.
      - exact: complete_dweight.
    rewrite (pr_eq1_of_support d
      same_result_sim_decrypt_reduction_opt Hdweight).
    - exact: lexx.
    - move=> outs Houts.
      exact: (same_result_sim_decrypt_reduction_adv_opt_project A outs
        (Hsupport outs Houts)).
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

  Definition ind_cpa_reduction_sim_top_init_code
      (input : (bool * (pk_t * evk_t))%type) :
      raw_code (bool * (pk_t * evk_t))%type :=
    let '(b, (pk, evk)) := input in
    ready ← get IndCpaDSim.ready_addr ;;
    #assert (~~ ready) ;;
    #put IndCpaDSim.ready_addr := true ;;
    #put IndCpaDSim.pk_addr := Some pk ;;
    #put IndCpaDSim.evk_addr := Some evk ;;
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

  Lemma ind_cpa_reduction_sim_top_init_outer_initialized_heapE b pk evk :
    Pr_code (ind_cpa_reduction_sim_top_init_code (b, (pk, evk)))
      (reduction_outer_initialized_heap b pk evk) =1
    dunit ((b, (pk, evk)), reduction_initialized_heap b pk evk).
  Proof.
    move=> out.
    rewrite /ind_cpa_reduction_sim_top_init_code.
    rewrite Pr_code_get reduction_outer_initialized_heap_ready /assertD /=.
    rewrite !Pr_code_put Pr_code_ret.
    by rewrite /reduction_outer_initialized_heap /reduction_initialized_heap.
  Qed.

  Lemma ind_cpa_reduction_outer_sim_top_init_code_emptyE :
    Pr_code
      (init ← ind_cpa_reduction_outer_challenge_init_code tt ;;
       ind_cpa_reduction_sim_top_init_code init) empty_heap =1
    Pr_code (ind_cpa_reduction_challenge_init_code tt) empty_heap.
  Proof.
    move=> out.
    transitivity
      ((\dlet_(b <- dflip (1 / 2))
        \dlet_(keys <- keygen)
          let '(pk, evk, _) := keys in
          dunit ((b, (pk, evk)), reduction_initialized_heap b pk evk))
        out).
    - rewrite Pr_code_bind.
      rewrite /ind_cpa_reduction_outer_challenge_init_code.
      rewrite Pr_code_sample __deprecated__dlet_dlet.
      apply: eq_in_dlet=> // b _ out_b.
      rewrite Pr_code_sample __deprecated__dlet_dlet.
      apply: eq_in_dlet=> // keys _ out_keys.
      case: keys=> [[pk evk] sk].
      rewrite !Pr_code_put Pr_code_ret dlet_unit.
      exact: (ind_cpa_reduction_sim_top_init_outer_initialized_heapE
        b pk evk out_keys).
    - symmetry.
      rewrite /ind_cpa_reduction_challenge_init_code.
      rewrite Pr_code_sample.
      apply: eq_in_dlet=> // b _ out_b.
      rewrite Pr_code_sample.
      apply: eq_in_dlet=> // keys _ out_keys.
      case: keys=> [[pk evk] sk].
      by rewrite !Pr_code_put Pr_code_ret /reduction_initialized_heap.
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

  Lemma ind_cpa_reduction_challenge_init_code_empty_shape out :
    out \in
      dinsupp
        (Pr_code (ind_cpa_reduction_challenge_init_code tt) empty_heap) ->
    exists b pk evk sk,
      keygen (pk, evk, sk) != 0 /\
      out = ((b, (pk, evk)), reduction_initialized_heap b pk evk).
  Proof.
    rewrite /ind_cpa_reduction_challenge_init_code.
    rewrite Pr_code_sample.
    move=> Hout.
    have [b Hb Hout_b] := @dinsupp_dlet R _ _ _ _ _ Hout.
    rewrite Pr_code_sample in Hout_b.
    have [keys Hkeys Hout_keys] := @dinsupp_dlet R _ _ _ _ _ Hout_b.
    case: keys Hkeys Hout_keys=> [[pk evk] sk] Hkeys.
    rewrite !Pr_code_put Pr_code_ret.
    move=> Hout_ret.
    exists b, pk, evk, sk.
    split; first exact: Hkeys.
    exact: in_dunit Hout_ret.
  Qed.

  Lemma ind_cpad_reduction_challenge_init_heaps_rel b pk evk sk :
    (pk, evk, sk) \in dinsupp keygen ->
    sim_decrypt_reduction_heap_rel
      (challenge_initialized_heap b pk evk sk)
      (reduction_initialized_heap b pk evk).
  Proof.
    move=> Hkeys.
    apply: sim_decrypt_reduction_heap_rel_initialized.
    exact: (keygen_support_good (pk, evk, sk) Hkeys).
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

  Lemma ind_cpad_moved_adversary_separateC (A : nom_package) :
    fseparate (loc (ind_cpad_moved_adversary A))
      IndCpadGame.oracle_mem_spec.
  Proof.
    rewrite fseparate_disj /ind_cpad_moved_adversary.
    change (disj (move (IndCpadGame.IndCpadChallenger : nom_package) A)
      (IndCpadGame.IndCpadChallenger : nom_package)).
    by rewrite disjC; exact: move_disj.
  Qed.

  Lemma ind_cpa_reduction_moved_adversary_sim_separate
      (A : nom_package) :
    fseparate IndCpaDSim.oracle_mem_spec
      (loc (ind_cpa_reduction_moved_adversary A)).
  Proof.
    rewrite fseparate_disj /ind_cpa_reduction_moved_adversary.
    change (disj (IndCpaDSim.IndCpaSimTop : nom_package)
      (move (IndCpaDSim.IndCpaSimTop : nom_package) A)).
    exact: move_disj.
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

  Lemma ind_cpa_reduction_outer_disj
      (A : nom_package) max_queries :
    disj (IndCpaSecurity.IndCpaGame.IndCpaChallenger : nom_package)
      (IndCpaDSim.IndCpaReduction A max_queries).
  Proof.
    rewrite /disj /=.
    change (disj IndCpaSecurity.IndCpaGame.IndCpa_locs
      (loc (IndCpaDSim.IndCpaReduction A max_queries))).
    rewrite disjC -fseparate_disj.
    exact: ind_cpa_reduction_outer_separate.
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

  Lemma ind_cpad_reduction_challenge_init_adv_support
      (A : nom_package) :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    supports_same_result_sim_decrypt_reduction_adv_opt A
      (shared_complete_sample_coupling
        ind_cpad_reduction_challenge_init_sample
        ind_cpad_reduction_challenge_init_outL
        ind_cpad_reduction_challenge_init_outR).
  Proof.
    move=> Houter outs Houts.
    rewrite /shared_complete_sample_coupling in Houts.
    have [os Hos Hinner] := @dinsupp_dlet R _ _ _ _ _ Houts.
    case: os Hos Hinner=> [sample|] Hos Hinner.
    - have Houts_eq : outs =
          (Some (ind_cpad_reduction_challenge_init_outL sample),
           Some (ind_cpad_reduction_challenge_init_outR sample)).
        exact: in_dunit Hinner.
      rewrite Houts_eq.
      clear Hinner Houts_eq.
      case: sample Hos=> [b [[pk evk] sk]] Hsample.
      exact: (same_result_sim_decrypt_reduction_adv_opt_initialized
        A b pk evk sk Houter
        (ind_cpad_reduction_challenge_init_sample_keygen
          b pk evk sk Hsample)).
    - have -> : outs = (None, None).
        exact: in_dunit Hinner.
      by [].
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

  Lemma ind_cpad_reduction_challenge_init_adv_support_named
      (A : nom_package) :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    supports_same_result_sim_decrypt_reduction_adv_opt A
      ind_cpad_reduction_challenge_init_coupling.
  Proof.
    exact: ind_cpad_reduction_challenge_init_adv_support.
  Qed.

  Lemma ind_cpad_reduction_challenge_init_coupling_margins :
    clean_coupling ind_cpad_reduction_challenge_init_coupling
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
    split.
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

  Lemma ind_cpad_reduction_challenge_init_adv_coupling
      (A : nom_package) :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    clean_coupling ind_cpad_reduction_challenge_init_coupling
      (complete (Pr_code (ind_cpad_challenge_init_code tt) empty_heap))
      (complete
        (Pr_code (ind_cpa_reduction_challenge_init_code tt) empty_heap)) /\
    supports_same_result_sim_decrypt_reduction_adv_opt A
      ind_cpad_reduction_challenge_init_coupling.
  Proof.
    move=> Houter.
    split.
    - exact: ind_cpad_reduction_challenge_init_coupling_margins.
    - exact: ind_cpad_reduction_challenge_init_adv_support_named.
  Qed.

  Definition sim_decrypt_reduction_adv_continuation_witness
      (A : nom_package) {in_t out_t : choice_type}
      (contL contR : in_t -> raw_code out_t) : Prop :=
    forall memL memR xL xR,
      exists d,
        clean_coupling d
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
    clean_coupling
      (sim_decrypt_reduction_adv_continuation_kernel
        A contL contR Hcont xy)
      (complete_bind_kernel KL xy.1)
      (complete_bind_kernel KR xy.2).
  Proof.
    case: xy=> [[ymemL|] [ymemR|]] /=.
    - case: ymemL=> yL memL; case: ymemR=> yR memR /=.
      rewrite /sim_decrypt_reduction_adv_continuation_kernel /=.
      case: (boolp.constructive_indefinite_description
        (Hcont memL memR yL yR))=> d [[HdL HdR] Hsupport] /=.
      split; [exact: HdL | exact: HdR].
    - case: ymemL=> yL memL.
      rewrite /sim_decrypt_reduction_adv_continuation_kernel /=.
      have [HdL HdR] :=
        complete_bind_fallback_coupling_margins
          (fun ymem : mid_t * heap => Pr_code (contL ymem.1) ymem.2)
          (fun ymem : mid_t * heap => Pr_code (contR ymem.1) ymem.2)
          (Some (yL, memL), None).
      split.
      + exact: HdL.
      + exact: HdR.
    - case: ymemR=> yR memR.
      rewrite /sim_decrypt_reduction_adv_continuation_kernel /=.
      have [HdL HdR] :=
        complete_bind_fallback_coupling_margins
          (fun ymem : mid_t * heap => Pr_code (contL ymem.1) ymem.2)
          (fun ymem : mid_t * heap => Pr_code (contR ymem.1) ymem.2)
          (None, Some (yR, memR)).
      split.
      + exact: HdL.
      + exact: HdR.
    - rewrite /sim_decrypt_reduction_adv_continuation_kernel /=.
      have [HdL HdR] :=
        complete_bind_fallback_coupling_margins
          (fun ymem : mid_t * heap => Pr_code (contL ymem.1) ymem.2)
          (fun ymem : mid_t * heap => Pr_code (contR ymem.1) ymem.2)
          (None, None).
      split.
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
    - split.
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

  Lemma sim_decrypt_reduction_adv_continuation_witness_bind
      (A : nom_package) {in_t mid_t out_t : choice_type}
      (progL progR : in_t -> raw_code mid_t)
      (contL contR : mid_t -> raw_code out_t) :
    sim_decrypt_reduction_adv_continuation_witness A progL progR ->
    sim_decrypt_reduction_adv_continuation_witness A contL contR ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun x => y ← progL x ;; contL y)
      (fun x => y ← progR x ;; contR y).
  Proof.
    move=> Hprog Hcont memL memR xL xR.
    have [d0 [Hd0 Hprog_support_if]] := Hprog memL memR xL xR.
    pose KL (ymem : mid_t * heap) := Pr_code (contL ymem.1) ymem.2.
    pose KR (ymem : mid_t * heap) := Pr_code (contR ymem.1) ymem.2.
    pose K :=
      sim_decrypt_reduction_adv_continuation_kernel A contL contR Hcont.
    exists (\dlet_(xy <- d0) K xy).
    split.
    - have Hbind := coupling_bind_kernel d0
        (complete (Pr_code (progL xL) memL))
        (complete (Pr_code (progR xR) memR))
        K (complete_bind_kernel KL) (complete_bind_kernel KR)
        Hd0
        (sim_decrypt_reduction_adv_continuation_kernel_margins
          A contL contR Hcont).
      move: Hbind=> [HL HR].
      split.
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
        have Hcont_pre :
            same_input_sim_decrypt_reduction_adv_pre A
              ((yL, memL'), (yR, memR')).
          exact: (same_result_sim_decrypt_reduction_adv_opt_some_pre
            A yL yR memL' memR' Hmid).
        have Hsupport :
            supports_same_result_sim_decrypt_reduction_adv_opt A
              (K (Some (yL, memL'), Some (yR, memR'))).
          rewrite /K.
          exact: (sim_decrypt_reduction_adv_continuation_kernel_support
            A contL contR Hcont yL yR memL' memR' Hcont_pre).
        exact: (Hsupport outs Hinner).
      + case: ymemL=> yL memL' Hmid.
        by [].
      + case: ymemR=> yR memR' Hmid.
        by [].
      + move=> _ Hinner.
        have -> : outs = (None, None).
          rewrite /K /sim_decrypt_reduction_adv_continuation_kernel
            /complete_bind_fallback_coupling /complete_bind_kernel
            /product_coupling in Hinner.
          rewrite !dlet_unit in Hinner.
        exact: in_dunit Hinner.
        by [].
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
        clean_coupling (K xy)
          (complete_bind_kernel KL xy.1)
          (complete_bind_kernel KR xy.2).
      case: xy=> [[ymemL|] [ymemR|]] /=.
      - case: ymemL=> yL memL'; case: ymemR=> yR memR'.
        rewrite /K /=.
        case Heq: (eq_op yL yR).
        + move/eqP: Heq=> Heq.
          subst yR.
          case: (boolp.constructive_indefinite_description
            (Hcont yL memL' memR' xL xR))=> d [[HdL HdR] Hsupport] /=.
          split; [exact: HdL | exact: HdR].
        + have [HdL HdR] :=
            completed_fallback_coupling_margins
              (Pr_code (contL yL xL) memL')
              (Pr_code (contR yR xR) memR').
          split.
          * exact: HdL.
          * exact: HdR.
      - case: ymemL=> yL memL'.
        have [HdL HdR] :=
          complete_bind_fallback_coupling_margins KL KR
            (Some (yL, memL'), None).
        split.
        + exact: HdL.
        + exact: HdR.
      - case: ymemR=> yR memR'.
        have [HdL HdR] :=
          complete_bind_fallback_coupling_margins KL KR
            (None, Some (yR, memR')).
        split.
        + exact: HdL.
        + exact: HdR.
      - have [HdL HdR] :=
          complete_bind_fallback_coupling_margins KL KR (None, None).
        split.
        + exact: HdL.
        + exact: HdR.
    exists (\dlet_(xy <- d0) K xy).
    split.
    - have Hbind := coupling_bind_kernel d0
        (complete (Pr_code (progL xL) memL))
        (complete (Pr_code (progR xR) memR))
        K (complete_bind_kernel KL) (complete_bind_kernel KR)
        Hd0 HK.
      move: Hbind=> [HL HR].
      split.
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
        split.
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
      - move: Hd=> [HL HR].
        split.
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
      + move: Hd=> [HL HR].
        split.
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
        split.
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
    have Hd0 : clean_coupling d0
        (complete (dmargin outL D))
        (complete (dmargin outR D)).
      have [HmarginL HmarginR] :=
        shared_complete_sample_coupling_margins D outL outR.
      split.
      + exact: HmarginL.
      + exact: HmarginR.
    have HK xy :
        clean_coupling (K xy)
          (complete_bind_kernel KL xy.1)
          (complete_bind_kernel KR xy.2).
      case: xy=> [[ymemL|] [ymemR|]] /=.
      - case: ymemL=> aL memL'; case: ymemR=> aR memR'.
        rewrite /K /=.
        destruct (@idP (eq_op aL aR)) as [Heq|Hneq].
        + move/eqP: Heq=> Heq.
          subst aR.
          case: (boolp.constructive_indefinite_description
            (Hcont aL memL' memR' xL xR))=> d [[HdL HdR] Hsupport] /=.
          split; [exact: HdL | exact: HdR].
        + have [HdL HdR] :=
            completed_fallback_coupling_margins
              (Pr_code (contL aL xL) memL')
              (Pr_code (contR aR xR) memR').
          split.
          * exact: HdL.
          * exact: HdR.
      - case: ymemL=> aL memL'.
        have [HdL HdR] :=
          complete_bind_fallback_coupling_margins KL KR
            (Some (aL, memL'), None).
        split.
        + exact: HdL.
        + exact: HdR.
      - case: ymemR=> aR memR'.
        have [HdL HdR] :=
          complete_bind_fallback_coupling_margins KL KR
            (None, Some (aR, memR')).
        split.
        + exact: HdL.
        + exact: HdR.
      - have [HdL HdR] :=
          complete_bind_fallback_coupling_margins KL KR (None, None).
        split.
        + exact: HdL.
        + exact: HdR.
    exists (\dlet_(xy <- d0) K xy).
    split.
    - have Hbind := coupling_bind_kernel d0
        (complete (dmargin outL D)) (complete (dmargin outR D))
        K (complete_bind_kernel KL) (complete_bind_kernel KR) Hd0 HK.
      move: Hbind=> [HL HR].
      split.
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
    clean_coupling d
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
    move=> Ho Houter [Hheap Hadv] [HdL HdR] Hprob outs Houts.
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
    ⊨AE_opt ⦃ same_input_sim_decrypt_reduction_pre ⦄
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
        split.
        * exact: HdL.
        * exact: HdR.
      + move=> Hpre.
        case: Hpre=> _ [Hrel _].
        move: Hrel_bool.
        by rewrite Hrel.
  Qed.

  Lemma sim_decrypt_reduction_adv_continuation_witness_encrypt_prefix
      (A : nom_package) max_queries {in_t : choice_type}
      (x : message * message) :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun _ : in_t =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_encrypt
            (chProd message message) ciphertext) x)
      (fun _ : in_t =>
        code_link
          (resolve (IndCpaDSim.IndCpadOracle max_queries)
            (mkopsig IndCpadGame.oracle_encrypt
              (chProd message message) ciphertext) x)
          IndCpaSecurity.IndCpaGame.IndCpaOracle).
  Proof.
    move=> Houter.
    exact: (sim_decrypt_reduction_adv_continuation_witness_oracle_prefix
      A max_queries (in_t := in_t)
      (mkopsig IndCpadGame.oracle_encrypt
        (chProd message message) ciphertext) x
      ind_cpad_encrypt_in_adv_import Houter
      (ind_cpad_sim_decrypt_reduction_encrypt_resolve_outer_link_rel_ae
        max_queries)).
  Qed.

  Lemma sim_decrypt_reduction_adv_continuation_witness_eval1_prefix
      (A : nom_package) max_queries {in_t : choice_type}
      (x : unary_gate * nat) :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun _ : in_t =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_eval1
            (chProd unary_gate nat) ciphertext) x)
      (fun _ : in_t =>
        code_link
          (resolve (IndCpaDSim.IndCpadOracle max_queries)
            (mkopsig IndCpadGame.oracle_eval1
              (chProd unary_gate nat) ciphertext) x)
          IndCpaSecurity.IndCpaGame.IndCpaOracle).
  Proof.
    move=> Houter.
    exact: (sim_decrypt_reduction_adv_continuation_witness_oracle_prefix
      A max_queries (in_t := in_t)
      (mkopsig IndCpadGame.oracle_eval1
        (chProd unary_gate nat) ciphertext) x
      ind_cpad_eval1_in_adv_import Houter
      (ind_cpad_sim_decrypt_reduction_eval1_resolve_outer_link_rel_ae
        max_queries)).
  Qed.

  Lemma sim_decrypt_reduction_adv_continuation_witness_eval2_prefix
      (A : nom_package) max_queries {in_t : choice_type}
      (x : (binary_gate * nat) * nat) :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun _ : in_t =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_eval2
            (chProd (chProd binary_gate nat) nat) ciphertext) x)
      (fun _ : in_t =>
        code_link
          (resolve (IndCpaDSim.IndCpadOracle max_queries)
            (mkopsig IndCpadGame.oracle_eval2
              (chProd (chProd binary_gate nat) nat) ciphertext) x)
          IndCpaSecurity.IndCpaGame.IndCpaOracle).
  Proof.
    move=> Houter.
    exact: (sim_decrypt_reduction_adv_continuation_witness_oracle_prefix
      A max_queries (in_t := in_t)
      (mkopsig IndCpadGame.oracle_eval2
        (chProd (chProd binary_gate nat) nat) ciphertext) x
      ind_cpad_eval2_in_adv_import Houter
      (ind_cpad_sim_decrypt_reduction_eval2_resolve_outer_link_rel_ae
        max_queries)).
  Qed.

  Lemma sim_decrypt_reduction_adv_continuation_witness_decrypt_prefix
      (A : nom_package) max_queries {in_t : choice_type}
      (x : nat) :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun _ : in_t =>
        resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
      (fun _ : in_t =>
        code_link
          (resolve (IndCpaDSim.IndCpadOracle max_queries)
            (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
          IndCpaSecurity.IndCpaGame.IndCpaOracle).
  Proof.
    move=> Houter.
    exact: (sim_decrypt_reduction_adv_continuation_witness_oracle_prefix
      A max_queries (in_t := in_t)
      (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x
      ind_cpad_decrypt_in_adv_import Houter
      (ind_cpad_sim_decrypt_reduction_decrypt_resolve_outer_link_rel_ae
        max_queries)).
  Qed.

  Lemma sim_decrypt_reduction_adv_continuation_witness_encrypt_call
      (A : nom_package) max_queries {in_t out_t : choice_type}
      (x : message * message)
      (contL contR : ciphertext -> in_t -> raw_code out_t) :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    (forall c,
      sim_decrypt_reduction_adv_continuation_witness A
        (contL c) (contR c)) ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun inp =>
        c ← resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_encrypt
            (chProd message message) ciphertext) x ;;
        contL c inp)
      (fun inp =>
        c ← code_link
          (resolve (IndCpaDSim.IndCpadOracle max_queries)
            (mkopsig IndCpadGame.oracle_encrypt
              (chProd message message) ciphertext) x)
          IndCpaSecurity.IndCpaGame.IndCpaOracle ;;
        contR c inp).
  Proof.
    move=> Houter Hcont.
    apply: sim_decrypt_reduction_adv_continuation_witness_bind_input.
    - exact: (sim_decrypt_reduction_adv_continuation_witness_encrypt_prefix
        A max_queries (in_t := in_t) x Houter).
    - exact: Hcont.
  Qed.

  Lemma sim_decrypt_reduction_adv_continuation_witness_eval1_call
      (A : nom_package) max_queries {in_t out_t : choice_type}
      (x : unary_gate * nat)
      (contL contR : ciphertext -> in_t -> raw_code out_t) :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    (forall c,
      sim_decrypt_reduction_adv_continuation_witness A
        (contL c) (contR c)) ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun inp =>
        c ← resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_eval1
            (chProd unary_gate nat) ciphertext) x ;;
        contL c inp)
      (fun inp =>
        c ← code_link
          (resolve (IndCpaDSim.IndCpadOracle max_queries)
            (mkopsig IndCpadGame.oracle_eval1
              (chProd unary_gate nat) ciphertext) x)
          IndCpaSecurity.IndCpaGame.IndCpaOracle ;;
        contR c inp).
  Proof.
    move=> Houter Hcont.
    apply: sim_decrypt_reduction_adv_continuation_witness_bind_input.
    - exact: (sim_decrypt_reduction_adv_continuation_witness_eval1_prefix
        A max_queries (in_t := in_t) x Houter).
    - exact: Hcont.
  Qed.

  Lemma sim_decrypt_reduction_adv_continuation_witness_eval2_call
      (A : nom_package) max_queries {in_t out_t : choice_type}
      (x : (binary_gate * nat) * nat)
      (contL contR : ciphertext -> in_t -> raw_code out_t) :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    (forall c,
      sim_decrypt_reduction_adv_continuation_witness A
        (contL c) (contR c)) ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun inp =>
        c ← resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_eval2
            (chProd (chProd binary_gate nat) nat) ciphertext) x ;;
        contL c inp)
      (fun inp =>
        c ← code_link
          (resolve (IndCpaDSim.IndCpadOracle max_queries)
            (mkopsig IndCpadGame.oracle_eval2
              (chProd (chProd binary_gate nat) nat) ciphertext) x)
          IndCpaSecurity.IndCpaGame.IndCpaOracle ;;
        contR c inp).
  Proof.
    move=> Houter Hcont.
    apply: sim_decrypt_reduction_adv_continuation_witness_bind_input.
    - exact: (sim_decrypt_reduction_adv_continuation_witness_eval2_prefix
        A max_queries (in_t := in_t) x Houter).
    - exact: Hcont.
  Qed.

  Lemma sim_decrypt_reduction_adv_continuation_witness_decrypt_call
      (A : nom_package) max_queries {in_t out_t : choice_type}
      (x : nat)
      (contL contR : chOption message -> in_t -> raw_code out_t) :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    (forall m,
      sim_decrypt_reduction_adv_continuation_witness A
        (contL m) (contR m)) ->
    sim_decrypt_reduction_adv_continuation_witness A
      (fun inp =>
        m ← resolve (IndCpadSimDecryptOracle max_queries)
          (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x ;;
        contL m inp)
      (fun inp =>
        m ← code_link
          (resolve (IndCpaDSim.IndCpadOracle max_queries)
            (mkopsig IndCpadGame.oracle_decrypt nat (chOption message)) x)
          IndCpaSecurity.IndCpaGame.IndCpaOracle ;;
        contR m inp).
  Proof.
    move=> Houter Hcont.
    apply: sim_decrypt_reduction_adv_continuation_witness_bind_input.
    - exact: (sim_decrypt_reduction_adv_continuation_witness_decrypt_prefix
        A max_queries (in_t := in_t) x Houter).
    - exact: Hcont.
  Qed.

  Lemma ind_cpad_sim_decrypt_reduction_resolve_outer_link_rel_ae
      max_queries (o : opsig) :
    fhas IndCpadGame.IndCpadAdv_import o ->
    ⊨AE_opt ⦃ same_input_sim_decrypt_reduction_pre ⦄
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
    ⊨AE_opt ⦃ game_initial_pre ⦄
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
    have Hfinal_coupling : clean_coupling finalD (complete leftD)
        (complete rightD).
      have Hbind := coupling_bind_kernel d0
        (complete (Pr_code (ind_cpad_challenge_init_code tt) empty_heap))
        (complete
          (Pr_code (ind_cpa_reduction_challenge_init_code tt) empty_heap))
        K (complete_bind_kernel KL) (complete_bind_kernel KR)
        ind_cpad_reduction_challenge_init_coupling_margins
        (sim_decrypt_reduction_adv_continuation_kernel_margins
          A guessL guessR Hcont).
      move: Hbind=> [HL HR].
      split.
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
      move: Hfinal_coupling=> [HfinalL _].
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

  Lemma ind_cpad_compiled_guess_decrypt_replacement_from_compile_ready_vector_bound
      (A : nom_package) max_queries :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    ⊨AE_opt ⦃ same_input_invariant_pre challenge_heap_valid ⦄
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
    exact: (compileTupleRule max_queries nat (chOption message)
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
          [tuple noise_flooding_per_query_epsilon
            dim gaussian_width_multiplier] [tuple 0]))
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
    exact: (ind_cpad_compiled_guess_decrypt_replacement_from_compile_ready_vector_bound
      A max_queries A_valid
      (ind_cpad_decrypt_prefix_code_readies_row_vector_bound
        max_queries)).
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

  Definition ind_cpa_reduction_unfresh_open_game_code
    (A : nom_package) (max_queries : nat) (_ : chUnit) :
    raw_code bool :=
    resolve
      ((IndCpaSecurity.IndCpaGame.IndCpaChallenger ∘
        ind_cpa_reduction A max_queries)%share)
      (IndCpaSecurity.IndCpaGame.main, ('unit, 'bool)) tt.

  Definition ind_cpa_reduction_open_guess_code
      (A : nom_package) (max_queries : nat)
      (input : (bool * (pk_t * evk_t))%type) : raw_code bool :=
    let '(b, (pk, evk)) := input in
    b' ← resolve
      (move (IndCpaSecurity.IndCpaGame.IndCpaChallenger : nom_package)
        (ind_cpa_reduction A max_queries))
        (mkopsig IndCpaSecurity.IndCpaGame.adv_guess
          (chProd pk_t evk_t) chBool) (pk, evk) ;;
    ret (eq_op b' b).

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

  Definition ind_cpa_reduction_factored_outer_open_game_code
      (A : nom_package) (max_queries : nat) (_ : chUnit) :
      raw_code bool :=
    init ← ind_cpa_reduction_outer_challenge_init_code tt ;;
    ind_cpa_reduction_open_guess_code A max_queries init.

  Definition ind_cpa_reduction_unfresh_factored_outer_open_game_code
      (A : nom_package) (max_queries : nat) (_ : chUnit) :
      raw_code bool :=
    init ← ind_cpa_reduction_outer_challenge_init_code tt ;;
    ind_cpa_reduction_unfresh_open_guess_code A max_queries init.

  Lemma ind_cpa_reduction_open_game_code_factored_outer
      (A : nom_package) max_queries x :
    ind_cpa_reduction_open_game_code A max_queries x =
    ind_cpa_reduction_factored_outer_open_game_code A max_queries x.
  Proof.
    case: x=> [].
    rewrite /ind_cpa_reduction_open_game_code
      /ind_cpa_reduction_factored_outer_open_game_code
      /ind_cpa_reduction_outer_challenge_init_code
      /ind_cpa_reduction_open_guess_code
      /IndCpaSecurity.IndCpaGame.IndCpaChallenger.
    rewrite sep_linkE.
    rewrite resolve_link.
    rewrite resolve_set /= coerce_kleisliE.
    ssprove_match_commut_gen.
    case: a0=> [[pk evk] sk] /=.
    ssprove_match_commut_gen.
  Qed.

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

  Lemma ind_cpa_reduction_unfresh_open_game_code_alpha
      (A : nom_package) max_queries x :
    ind_cpa_reduction_unfresh_open_game_code A max_queries x ≡
    ind_cpa_reduction_open_game_code A max_queries x.
  Proof.
    rewrite /ind_cpa_reduction_unfresh_open_game_code
      /ind_cpa_reduction_open_game_code /ind_cpa_reduction.
    exact: (resolve_alpha
      ((IndCpaSecurity.IndCpaGame.IndCpaChallenger ∘
        IndCpaDSim.IndCpaReduction A max_queries)%share)
      ((IndCpaSecurity.IndCpaGame.IndCpaChallenger ∘
        IndCpaDSim.IndCpaReduction A max_queries)%sep)
      (IndCpaSecurity.IndCpaGame.main, ('unit, 'bool)) tt
      (share_link_sep_link (ind_cpa_reduction_outer_disj A max_queries))).
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

  Definition ind_cpa_reduction_factored_outer_linked_game_code
      (A : nom_package) (max_queries : nat) (_ : chUnit) :
      raw_code bool :=
    init ← ind_cpa_reduction_outer_challenge_init_code tt ;;
    code_link
      (ind_cpa_reduction_open_guess_code A max_queries init)
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

  Lemma ind_cpa_reduction_linked_game_code_factored_outer
      (A : nom_package) max_queries x :
    ind_cpa_reduction_linked_game_code A max_queries x =
    ind_cpa_reduction_factored_outer_linked_game_code A max_queries x.
  Proof.
    case: x=> [].
    rewrite /ind_cpa_reduction_linked_game_code
      /ind_cpa_reduction_factored_outer_linked_game_code.
    rewrite ind_cpa_reduction_open_game_code_factored_outer.
    rewrite /ind_cpa_reduction_factored_outer_open_game_code.
    rewrite code_link_bind.
    rewrite ind_cpa_reduction_outer_challenge_init_code_link_closed.
    by [].
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

  Lemma ind_cpad_reduction_challenge_init_adv_rel_ae
      (A : nom_package) :
    fseparate (loc (ind_cpa_reduction_moved_adversary A))
      IndCpaSecurity.IndCpaGame.IndCpa_locs ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      ind_cpad_challenge_init_code
      ≈( 0 )
      ind_cpa_reduction_challenge_init_code
    ⦃ same_result_sim_decrypt_reduction_opt ⦄.
  Proof.
    move=> Houter.
    split; first exact: lexx.
    move=> memL memR xL xR Hpre.
    rewrite /game_initial_pre in Hpre.
    move/eqP: Hpre=> Hpre.
    inversion Hpre; subst.
    exists ind_cpad_reduction_challenge_init_coupling.
    split.
    - exact: ind_cpad_reduction_challenge_init_coupling_margins.
    - rewrite subr0.
      exact: (supports_same_result_sim_decrypt_reduction_adv_opt_rel_pr_ge1
        A ind_cpad_reduction_challenge_init_coupling
        (Pr_code (ind_cpad_challenge_init_code tt) empty_heap)
        (Pr_code (ind_cpa_reduction_challenge_init_code tt) empty_heap)
        ind_cpad_reduction_challenge_init_coupling_margins
        (ind_cpad_reduction_challenge_init_adv_support_named A Houter)).
  Qed.

  Lemma ind_cpa_reduction_linked_to_factored_outer_ae
      (A : nom_package) max_queries :
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpa_reduction_linked_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_factored_outer_linked_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    apply: (additiveErrorOptConseqRule
      (ind_cpa_reduction_linked_game_code A max_queries)
      (ind_cpa_reduction_factored_outer_linked_game_code A max_queries)
      game_initial_pre game_initial_pre
      same_output_heap_opt same_game_output_opt
      0 0).
    - by [].
    - move=> outs.
      exact: same_output_heap_game_output_opt.
    - exact: lexx.
    apply: additiveErrorOptSameOutputTvdEqRule.
    - exact: lexx.
    - move=> memL memR xL xR Hpre.
      rewrite /game_initial_pre in Hpre.
      move/eqP: Hpre=> Hpre.
      inversion Hpre; subst.
      rewrite ind_cpa_reduction_linked_game_code_factored_outer.
      exact: total_variation_refl_le0.
  Qed.

  Lemma ind_cpa_reduction_factored_outer_to_linked_ae
      (A : nom_package) max_queries :
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpa_reduction_factored_outer_linked_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_linked_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    apply: (additiveErrorOptConseqRule
      (ind_cpa_reduction_factored_outer_linked_game_code A max_queries)
      (ind_cpa_reduction_linked_game_code A max_queries)
      game_initial_pre game_initial_pre
      same_output_heap_opt same_game_output_opt
      0 0).
    - by [].
    - move=> outs.
      exact: same_output_heap_game_output_opt.
    - exact: lexx.
    apply: additiveErrorOptSameOutputTvdEqRule.
    - exact: lexx.
    - move=> memL memR xL xR Hpre.
      rewrite /game_initial_pre in Hpre.
      move/eqP: Hpre=> Hpre.
      inversion Hpre; subst.
      rewrite -ind_cpa_reduction_linked_game_code_factored_outer.
      exact: total_variation_refl_le0.
  Qed.

  Lemma ind_cpa_reduction_unfresh_linked_to_factored_outer_ae
      (A : nom_package) max_queries :
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpa_reduction_unfresh_linked_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_unfresh_factored_outer_linked_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    apply: (additiveErrorOptConseqRule
      (ind_cpa_reduction_unfresh_linked_game_code A max_queries)
      (ind_cpa_reduction_unfresh_factored_outer_linked_game_code A max_queries)
      game_initial_pre game_initial_pre
      same_output_heap_opt same_game_output_opt
      0 0).
    - by [].
    - move=> outs.
      exact: same_output_heap_game_output_opt.
    - exact: lexx.
    apply: additiveErrorOptSameOutputTvdEqRule.
    - exact: lexx.
    - move=> memL memR xL xR Hpre.
      rewrite /game_initial_pre in Hpre.
      move/eqP: Hpre=> Hpre.
      inversion Hpre; subst.
      rewrite ind_cpa_reduction_unfresh_linked_game_code_factored_outer.
      exact: total_variation_refl_le0.
  Qed.

  Lemma ind_cpa_reduction_unfresh_factored_outer_to_linked_ae
      (A : nom_package) max_queries :
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpa_reduction_unfresh_factored_outer_linked_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_unfresh_linked_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    apply: (additiveErrorOptConseqRule
      (ind_cpa_reduction_unfresh_factored_outer_linked_game_code A max_queries)
      (ind_cpa_reduction_unfresh_linked_game_code A max_queries)
      game_initial_pre game_initial_pre
      same_output_heap_opt same_game_output_opt
      0 0).
    - by [].
    - move=> outs.
      exact: same_output_heap_game_output_opt.
    - exact: lexx.
    apply: additiveErrorOptSameOutputTvdEqRule.
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
      exact: same_output_heap_game_output_opt.
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
      exact: same_output_heap_game_output_opt.
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

  Lemma ind_cpad_reduction_challenge_init_rel_total_ae :
    ⊨AE ⦃ game_initial_pre ⦄
      ind_cpad_challenge_init_code
      ≈( 0 )
      ind_cpa_reduction_challenge_init_code
    ⦃ same_input_sim_decrypt_reduction_pre ⦄.
  Proof.
    split; first exact: lexx.
    move=> memL memR xL xR Hpre.
    rewrite /game_initial_pre in Hpre.
    move/eqP: Hpre=> Hpre.
    inversion Hpre; subst.
    pose initD : {distr (bool * (pk_t * evk_t * sk_t)) / R} :=
      \dlet_(b <- dflip (1 / 2))
        \dlet_(keys <- keygen) dunit (b, keys).
    pose outL (sample : bool * (pk_t * evk_t * sk_t)) :=
      let '(b, ((pk, evk), sk)) := sample in
      ((b, (pk, evk)), challenge_initialized_heap b pk evk sk).
    pose outR (sample : bool * (pk_t * evk_t * sk_t)) :=
      let '(b, ((pk, evk), _)) := sample in
      ((b, (pk, evk)), reduction_initialized_heap b pk evk).
    have HinitD_weight : dweight initD = 1.
      rewrite /initD dweight_dlet.
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
    exists (shared_complete_sample_coupling initD outL outR).
    split.
    - have [HmarginL HmarginR] :=
        shared_complete_sample_coupling_margins initD outL outR.
      split.
      + move=> z.
        rewrite HmarginL.
        apply: complete_distr_ext=> y.
        rewrite /initD /outL /ind_cpad_challenge_init_code.
        rewrite dmarginE Pr_code_sample.
        rewrite __deprecated__dlet_dlet.
        apply: eq_in_dlet=> // b _ y'.
        rewrite Pr_code_sample.
        rewrite __deprecated__dlet_dlet.
        apply: eq_in_dlet=> // keys _ y''.
        case: keys=> [[pk evk] sk].
        by rewrite dlet_unit /challenge_initialized_heap !Pr_code_put Pr_code_ret.
      + move=> z.
        rewrite HmarginR.
        apply: complete_distr_ext=> y.
        rewrite /initD /outR /ind_cpa_reduction_challenge_init_code.
        rewrite dmarginE Pr_code_sample.
        rewrite __deprecated__dlet_dlet.
        apply: eq_in_dlet=> // b _ y'.
        rewrite Pr_code_sample.
        rewrite __deprecated__dlet_dlet.
        apply: eq_in_dlet=> // keys _ y''.
        case: keys=> [[pk evk] sk].
        by rewrite dlet_unit /reduction_initialized_heap !Pr_code_put Pr_code_ret.
    - rewrite subr0.
      apply: shared_complete_sample_coupling_pr_ge1_total.
      + exact: HinitD_weight.
      + move=> sample Hsample.
        case: sample Hsample=> [b [[pk evk] sk]] Hsample /=.
        have Hkeys : (pk, evk, sk) \in dinsupp keygen.
          move: Hsample.
          rewrite /initD.
          move=> Hsample.
          have [b' Hb' Hafter_b] := @dinsupp_dlet R _ _ _ _ _ Hsample.
          have [keys' Hkeys' Hafter_keys] :=
            @dinsupp_dlet R _ _ _ _ _ Hafter_b.
          have Heq :
              (b, (pk, evk, sk)) = (b', keys').
            exact: in_dunit Hafter_keys.
          inversion Heq; subst keys'.
          exact: Hkeys'.
        have Hrel :=
          ind_cpad_reduction_challenge_init_heaps_rel b pk evk sk Hkeys.
        rewrite /lift_loss_post /same_input_sim_decrypt_reduction_pre
          /outL /outR /= eqxx.
        exact: Hrel.
  Qed.

  Lemma ind_cpad_reduction_challenge_init_rel_ae :
    ⊨AE_opt ⦃ game_initial_pre ⦄
      ind_cpad_challenge_init_code
      ≈( 0 )
      ind_cpa_reduction_challenge_init_code
    ⦃ same_result_sim_decrypt_reduction_opt ⦄.
  Proof.
    apply: (additiveErrorOptConseqRule
      ind_cpad_challenge_init_code
      ind_cpa_reduction_challenge_init_code
      game_initial_pre game_initial_pre
      (lift_loss_post same_input_sim_decrypt_reduction_pre)
      same_result_sim_decrypt_reduction_opt 0 0).
    - by [].
    - move=> [outL outR] Hpost.
      case: outL Hpost=> [[initL memL]|] Hpost.
      + case: outR Hpost=> [[initR memR]|] Hpost; last by [].
        rewrite /lift_loss_post /same_input_sim_decrypt_reduction_pre
          /same_result_sim_decrypt_reduction_opt /= in Hpost *.
        move/andP: Hpost=> [/eqP -> Hrel].
        by rewrite eqxx Hrel.
      + by case: outR Hpost=> [[initR memR]|] Hpost.
    - exact: lexx.
    - exact: ind_cpad_reduction_challenge_init_rel_total_ae.
  Qed.

  Lemma ind_cpad_reduction_factored_result_bridge_from_guess
      (guessL guessR :
        (bool * (pk_t * evk_t))%type -> raw_code bool) :
    ⊨AE_opt ⦃ same_input_sim_decrypt_reduction_pre ⦄
      guessL
      ≈( 0 )
      guessR
    ⦃ same_result_opt ⦄ ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (fun _ : chUnit =>
        init ← ind_cpad_challenge_init_code tt ;;
        guessL init)
      ≈( 0 )
      (fun _ : chUnit =>
        init ← ind_cpa_reduction_challenge_init_code tt ;;
        guessR init)
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> Hguess.
    have Hguess_game :
        ⊨AE_opt ⦃ same_input_sim_decrypt_reduction_pre ⦄
          guessL
          ≈( 0 )
          guessR
        ⦃ same_game_result_opt ⦄.
      apply: (additiveErrorOptConseqRule
        guessL guessR
        same_input_sim_decrypt_reduction_pre
        same_input_sim_decrypt_reduction_pre
        same_result_opt same_game_result_opt 0 0).
      - by [].
      - move=> outs.
        by rewrite /same_result_opt /same_game_result_opt.
      - exact: lexx.
      - exact: Hguess.
    have -> : (0 : R) = 0 + 0 by rewrite addr0.
    exact: (additiveErrorOptSeqRule
      ind_cpad_challenge_init_code
      ind_cpa_reduction_challenge_init_code
      guessL guessR
      game_initial_pre
      same_input_sim_decrypt_reduction_pre
      same_game_result_opt
      0 0
      ind_cpad_reduction_challenge_init_rel_total_ae
      Hguess_game).
  Qed.

  Definition ind_cpa_reduction_factored_game_code_from_guess
      (guessR : (bool * (pk_t * evk_t))%type -> raw_code bool)
      (_ : chUnit) : raw_code bool :=
    init ← ind_cpa_reduction_challenge_init_code tt ;;
    guessR init.

  Lemma ind_cpa_reduction_direct_factored_game_code_from_guess
      (A : nom_package) max_queries x :
    ind_cpa_reduction_direct_factored_game_code A max_queries x =
    ind_cpa_reduction_factored_game_code_from_guess
      (ind_cpa_reduction_direct_guess_code A max_queries) x.
  Proof. by []. Qed.

  Lemma ind_cpad_sim_decrypt_to_factored_reduction_from_guess_ae
      (A : nom_package) max_queries
      (guessR : (bool * (pk_t * evk_t))%type -> raw_code bool) :
    ⊨AE_opt ⦃ same_input_sim_decrypt_reduction_pre ⦄
      (fun init =>
        code_link
          (ind_cpad_open_guess_code A init)
          (IndCpadSimDecryptOracle max_queries))
      ≈( 0 )
      guessR
    ⦃ same_result_opt ⦄ ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpad_sim_decrypt_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_factored_game_code_from_guess guessR)
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> Hguess.
    have Hfactored :=
      ind_cpad_reduction_factored_result_bridge_from_guess
        (fun init =>
          code_link
            (ind_cpad_open_guess_code A init)
            (IndCpadSimDecryptOracle max_queries))
        guessR Hguess.
    split; first exact: Hfactored.1.
    move=> memL memR xL xR Hpre.
    have [d [Hd Hpost]] := Hfactored.2 memL memR xL xR Hpre.
    exists d.
    split; last exact: Hpost.
    move: Hd.
    rewrite (ind_cpad_sim_decrypt_game_code_factored A max_queries xL).
    rewrite /ind_cpad_factored_sim_decrypt_game_code.
    rewrite /ind_cpa_reduction_factored_game_code_from_guess.
    by [].
  Qed.

  Lemma ind_cpad_sim_decrypt_to_direct_reduction_from_guess_ae
      (A : nom_package) max_queries :
    ⊨AE_opt ⦃ same_input_sim_decrypt_reduction_pre ⦄
      (fun init =>
        code_link
          (ind_cpad_open_guess_code A init)
          (IndCpadSimDecryptOracle max_queries))
      ≈( 0 )
      (ind_cpa_reduction_direct_guess_code A max_queries)
    ⦃ same_result_opt ⦄ ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpad_sim_decrypt_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_direct_factored_game_code A max_queries)
    ⦃ same_game_result_opt ⦄.
  Proof.
    exact: ind_cpad_sim_decrypt_to_factored_reduction_from_guess_ae.
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
    ⊨AE_opt ⦃ game_initial_pre ⦄
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
    ⊨AE_opt ⦃ game_initial_pre ⦄
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
    ⊨AE_opt ⦃ game_initial_pre ⦄
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
      move/andP=> [/andP [Hinv /eqP Hinit] /eqP Hmem].
      subst initR; subst memR.
      by rewrite /same_input_invariant_pre Hinv !eqxx.
    - by [].
    apply: (additiveErrorTvdEqPostTotalRule
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
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpad_factored_compiled_real_guess_game_code A max_queries)
      ≈( compile_security_error max_queries )
      (ind_cpad_factored_compiled_sim_decrypt_guess_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> A_valid Hprefix_vector.
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
      (ind_cpad_compiled_guess_decrypt_replacement_from_compile_ready_vector_bound
        A max_queries A_valid Hprefix_vector)).
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
    exact: (ind_cpad_factored_compiled_guess_decrypt_replacement_ready_vector_bound
      A max_queries A_valid
      (ind_cpad_decrypt_prefix_code_readies_row_vector_bound
        max_queries)).
  Qed.

  Lemma ind_cpad_compiled_open_decrypt_replacement_from_guess_factoring_ready_vector_bound
      (A : nom_package) max_queries :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
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
    exact: (ind_cpad_compiled_open_decrypt_replacement_from_guess_factoring_ready_vector_bound
      A max_queries A_valid
      (ind_cpad_decrypt_prefix_code_readies_row_vector_bound
        max_queries)).
  Qed.

  Lemma ind_cpad_game_to_compiled_sim_decrypt_additive_error_ready_vector_bound
      (A : nom_package) max_queries :
    Package IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
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
    exact: (ind_cpad_game_to_compiled_sim_decrypt_additive_error_ready_vector_bound
      A max_queries A_valid
      (ind_cpad_decrypt_prefix_code_readies_row_vector_bound
        max_queries)).
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
      (ind_cpad_compiled_sim_decrypt_self_link_game_code A max_queries)
      (ind_cpad_sim_decrypt_game_code A max_queries)
      game_initial_pre game_initial_pre
      same_output_heap_opt same_game_output_opt
      0 0).
    - by [].
    - move=> outs.
      exact: same_output_heap_game_output_opt.
    - by [].
    apply: additiveErrorOptSameOutputTvdEqRule.
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
      exact: same_output_heap_game_output_opt.
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
        exact: same_game_output_same_output_heap_opt.
      + exact: lexx.
      + exact: HLM.
    - apply: (additiveErrorOptConseqRule
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
    - split.
      + exact: HdL.
      + exact: HdR.
    - apply: (le_trans Hprob).
      apply: subset_pr=> xy Hxy.
      case: xy Hxy=> outL' outR'.
      by rewrite /same_game_result_opt /strip.
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

  Lemma additiveErrorOptSameGameResultRenameRule
      (prog : chUnit -> raw_code bool) {π} :
    ⊨AE_opt ⦃ game_initial_pre ⦄
      prog
      ≈( 0 )
      (fun x => π ∙ prog x)
    ⦃ same_game_result_opt ⦄.
  Proof.
    apply: additiveErrorOptSameGameResultTvdEqRule.
    - exact: lexx.
    - move=> memL memR xL xR Hpre.
      rewrite /game_initial_pre in Hpre.
      move/eqP: Hpre=> Hpre.
      inversion Hpre; subst.
      apply: total_variation_eq_le0.
      apply: complete_ext=> out.
      symmetry.
      exact: (dmargin_fst_Pr_code_rename_empty (prog tt) out).
  Qed.

  Lemma additiveErrorOptSameGameResultAlphaRule
      (progL progR : chUnit -> raw_code bool) :
    (forall x, progL x ≡ progR x) ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      progL
      ≈( 0 )
      progR
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> Halpha.
    apply: additiveErrorOptSameGameResultTvdEqRule.
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

  Lemma ind_cpa_reduction_unfresh_open_to_open_ae
      (A : nom_package) max_queries :
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpa_reduction_unfresh_open_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_open_game_code A max_queries)
    ⦃ same_game_result_opt ⦄.
  Proof.
    apply: additiveErrorOptSameGameResultAlphaRule.
    exact: ind_cpa_reduction_unfresh_open_game_code_alpha.
  Qed.

  Lemma ind_cpa_reduction_unfresh_linked_to_linked_ae
      (A : nom_package) max_queries :
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpa_reduction_unfresh_linked_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_linked_game_code A max_queries)
    ⦃ same_game_result_opt ⦄.
  Proof.
    apply: additiveErrorOptSameGameResultAlphaRule.
    exact: ind_cpa_reduction_unfresh_linked_game_code_alpha.
  Qed.

  Lemma additiveErrorOptSameGameResultTvBound
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
        additiveErrorOptSameGameResultTvBound
          progL progM game_initial_pre ε memL memL xL xL HLM Hpre.
      have HtvMR :=
        additiveErrorOptSameGameResultTvBound
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
    apply: (additiveErrorOptConseqRule
      progL progR game_initial_pre game_initial_pre
      same_game_output_opt same_game_result_opt ε ε).
    - by [].
    - exact: same_game_output_result_opt.
    - exact: lexx.
    - exact: Hae.
  Qed.

  Lemma ind_cpa_reduction_direct_factored_to_unfresh_factored_outer_linked_ae
      (A : nom_package) max_queries :
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpa_reduction_direct_factored_game_code A max_queries)
      ≈( 0 )
      (ind_cpa_reduction_unfresh_factored_outer_linked_game_code A max_queries)
    ⦃ same_game_result_opt ⦄.
  Proof.
    apply: additiveErrorOptSameGameResultTvdEqRule.
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
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpad_compiled_sim_decrypt_game_code A max_queries)
      ≈( 0 )
      (ind_cpad_compiled_sim_decrypt_self_link_game_code A max_queries)
    ⦃ same_game_output_opt ⦄.
  Proof.
    move=> A_valid.
    apply: (additiveErrorOptConseqRule
      (ind_cpad_compiled_sim_decrypt_game_code A max_queries)
      (ind_cpad_compiled_sim_decrypt_self_link_game_code A max_queries)
      game_initial_pre game_initial_pre
      same_output_heap_opt same_game_output_opt
      0 0).
    - by [].
    - move=> outs.
      exact: same_output_heap_game_output_opt.
    - exact: lexx.
    apply: additiveErrorOptSameOutputTvdEqRule.
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
    ⊨AE_opt ⦃ game_initial_pre ⦄
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
      additiveErrorOptSameGameOutputToResult
        (ind_cpa_reduction_unfresh_factored_outer_linked_game_code
          A max_queries)
        (ind_cpa_reduction_unfresh_linked_game_code A max_queries)
        0
        (ind_cpa_reduction_unfresh_factored_outer_to_linked_ae
          A max_queries).
    have Hunfresh_linked :=
      ind_cpa_reduction_unfresh_linked_to_linked_ae A max_queries.
    have H1 :=
      additiveErrorOptSameGameResultTriangleRule
        (ind_cpad_sim_decrypt_game_code A max_queries)
        (ind_cpa_reduction_direct_factored_game_code A max_queries)
        (ind_cpa_reduction_unfresh_factored_outer_linked_game_code
          A max_queries)
        0 0 Hdirect Hdirect_unfresh_factored.
    have H2 :=
      additiveErrorOptSameGameResultTriangleRule
        (ind_cpad_sim_decrypt_game_code A max_queries)
        (ind_cpa_reduction_unfresh_factored_outer_linked_game_code
          A max_queries)
        (ind_cpa_reduction_unfresh_linked_game_code A max_queries)
        (0 + 0) 0 H1 Hunfresh_factored.
    have H3 :=
      additiveErrorOptSameGameResultTriangleRule
        (ind_cpad_sim_decrypt_game_code A max_queries)
        (ind_cpa_reduction_unfresh_linked_game_code A max_queries)
        (ind_cpa_reduction_linked_game_code A max_queries)
        ((0 + 0) + 0) 0 H2 Hunfresh_linked.
    apply: (additiveErrorOptConseqRule
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
    apply: (additiveErrorOptSameGameResultTvBound
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
      additiveErrorOptSameGameResultTvBound
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
  Lemma ind_cpa_reduction_additive_error_from_compile_ready_vector_bound
    (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
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
    exact: (ind_cpa_reduction_additive_error_from_compile_ready_vector_bound
      A max_queries A_valid
      (ind_cpad_decrypt_prefix_code_readies_row_vector_bound
        max_queries)).
  Qed.

  Lemma ind_cpa_reduction_additive_error_ready_vector_bound
      (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    ⊨AE_opt ⦃ game_initial_pre ⦄
      (ind_cpad_game_code A max_queries)
      ≈( security_loss max_queries / 2 )
      (ind_cpa_reduction_game_code A max_queries)
    ⦃ same_game_result_opt ⦄.
  Proof.
    move=> A_valid Hprefix_vector.
    rewrite security_loss_halfE.
    exact: (ind_cpa_reduction_additive_error_from_compile_ready_vector_bound
      A max_queries A_valid Hprefix_vector).
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
    exact: (ind_cpa_reduction_additive_error_ready_vector_bound
      A max_queries A_valid
      (ind_cpad_decrypt_prefix_code_readies_row_vector_bound
        max_queries)).
  Qed.

  Theorem ind_cpa_reduction_bound_ready_vector_bound
      (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    IndCpadGame.winning_probability max_queries A <=
    IndCpaSecurity.IndCpaGame.winning_probability
      (ind_cpa_reduction A max_queries) +
    security_loss max_queries.
  Proof.
    move=> A_valid Hprefix_vector.
    have Hae := ind_cpa_reduction_additive_error_ready_vector_bound
      A max_queries A_valid Hprefix_vector.
    apply: (ind_cpa_reduction_bound_from_additive_error
      A max_queries _ Hae).
    lra.
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
    exact: (ind_cpa_reduction_bound_ready_vector_bound
      A max_queries A_valid
      (ind_cpad_decrypt_prefix_code_readies_row_vector_bound
        max_queries)).
  Qed.

  Theorem is_secure_ready_vector_bound (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    decrypt_prefix_ready_vector_bound_cert max_queries ->
    IndCpadGame.winning_probability max_queries A <= security_bound max_queries.
  Proof.
    move=> A_valid Hprefix_vector.
    rewrite /security_bound /security_loss.
    apply: (le_trans
      (ind_cpa_reduction_bound_ready_vector_bound
        A max_queries A_valid Hprefix_vector)).
    rewrite lerD2r.
    exact: (IndCpaSecurity.is_secure
      (ind_cpa_reduction A max_queries)
      (ind_cpa_reduction_valid A max_queries A_valid)).
  Qed.

  (* IND-CPAD security follows by applying IND-CPA security to the reduction. *)
  Theorem is_secure (A : nom_package) max_queries :
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    IndCpadGame.winning_probability max_queries A <= security_bound max_queries.
  Proof.
    move=> A_valid.
    exact: (is_secure_ready_vector_bound
      A max_queries A_valid
      (ind_cpad_decrypt_prefix_code_readies_row_vector_bound
        max_queries)).
  Qed.
End NoiseFloodingSecure.
