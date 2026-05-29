From Stdlib Require Import Utf8 BinInt.
From extructures Require Import ord fset fmap.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot all_order all_algebra reals distr.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
From SSProve Require Import NominalPrelude.
From Mending.Schemes Require Import ApproxFHE Indcpa Indcpad.
From Mending.Constructions Require Import NoiseFlooding.
From Mending.Security Require Import IndcpadSimulator.
From Mending.Schemes.Utils Require Import IntVec.

Import PackageNotation.
Import GRing.Theory Num.Theory Order.Theory Order.POrderTheory.

Local Open Scope package_scope.
Local Open Scope ring_scope.

(* TODO fill with actual value *)
Definition global_epsilon (max_queries : nat) (gaussian_width_multiplier : R) : R :=
  1 / 1000%R.

(* Glue code *)
Module Type NoiseFloodingIsIndCpad
  (Scheme : ApproxFheScheme)
  (Metric : ApproxFheMetric(Scheme))
  (Params : NoiseFloodingParams).
  Module NF := NoiseFlooding(Scheme)(Metric)(Params).
  Module IndCpadGame := IndCpad NF.
  Module IndCpaDSim := IndCpadSimulator(Scheme)(Metric)(Params).

  Parameter security_bound : nat -> R.
  Axiom is_secure : forall (A : nom_package) max_queries,
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    IndCpadGame.winning_probability A <= security_bound max_queries.
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

  Lemma ind_cpa_reduction_valid :
    forall (A : nom_package) max_queries,
      Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
      Package IndCpaSecurity.IndCpaGame.IndCpaAdv_import
        IndCpaSecurity.IndCpaGame.IndCpaAdv_export
        (ind_cpa_reduction A max_queries).
  Proof.
    move=> A max_queries A_valid.
    rewrite /reduction_locs /ind_cpa_reduction.
    exact: (IndCpaDSim.IndCpaReduction_valid A max_queries A_valid).
  Qed.

  Axiom ind_cpa_reduction_bound :
    forall (A : nom_package) max_queries,
      IndCpadGame.winning_probability A <=
      IndCpaSecurity.IndCpaGame.winning_probability
        (ind_cpa_reduction A max_queries) +
      security_loss max_queries.

  Theorem is_secure : forall (A : nom_package) max_queries,
    Package IndCpaDSim.IndCpadAdv_import IndCpaDSim.IndCpadAdv_export A ->
    IndCpadGame.winning_probability A <= security_bound max_queries.
  Proof.
    move=> A max_queries A_valid.
    rewrite /security_bound /security_loss.
    apply: (le_trans (ind_cpa_reduction_bound A max_queries)).
    rewrite lerD2r.
    exact: (IndCpaSecurity.is_secure
      (ind_cpa_reduction A max_queries)
      (ind_cpa_reduction_valid A max_queries A_valid)).
  Qed.
End NoiseFloodingSecure.
