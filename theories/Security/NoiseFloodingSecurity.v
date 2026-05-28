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
  Include IsIndCpad(NF).
End NoiseFloodingIsIndCpad.

(* Main theorem *)
Module NoiseFloodingSecure
  (Import Scheme : ApproxFheScheme)
  (Import Metric : ApproxFheMetric(Scheme))
  (Import Correctness : ApproxCorrectness(Scheme)(Metric))
  (Import IndCpa : IsIndCpa(Scheme))
  (Import Params : NoiseFloodingParams)
  : NoiseFloodingIsIndCpad(Scheme)(Metric)(Params).
  Module NF := NoiseFlooding(Scheme)(Metric)(Params).
  Definition security_loss (max_queries : nat) :=
    IndCpa.security_loss + global_epsilon max_queries gaussian_width_multiplier.
  Module IndCpadGame := IndCpad NF.
  Module IndCpaDSim := IndCpadSimulator(Scheme)(Metric)(Params).

  Notation " 'adv_keys " := (pk_t × evk_t) (in custom pack_type at level 2).
  Notation " 'message_pair " := (message × message) (in custom pack_type at level 2).
  Notation " 'ciphertext " := ciphertext (in custom pack_type at level 2).

  Definition ind_cpa_reduction (A : raw_package) (max_queries : nat) : raw_package :=
    IndCpaDSim.IndCpaReduction A max_queries.

  Parameter reduction_locs : Locations -> Locations.

  Axiom ind_cpa_reduction_valid :
    forall LA A max_queries,
      ValidPackage LA
        IndCpadGame.IndCpadAdv_import
        IndCpadGame.IndCpadAdv_export A ->
      fseparate LA IndCpadGame.oracle_mem_spec ->
      ValidPackage (reduction_locs LA)
        IndCpa.IndCpaGame.IndCpaAdv_import
        IndCpa.IndCpaGame.IndCpaAdv_export
        (ind_cpa_reduction A max_queries).

  Axiom ind_cpa_reduction_fseparate :
    forall LA,
      fseparate LA IndCpadGame.oracle_mem_spec ->
      fseparate (reduction_locs LA) IndCpa.IndCpaGame.IndCpa_locs.

  Axiom ind_cpa_reduction_bound :
    forall LA A max_queries,
      ValidPackage LA
        IndCpadGame.IndCpadAdv_import
        IndCpadGame.IndCpadAdv_export A ->
      fseparate LA IndCpadGame.oracle_mem_spec ->
      IndCpadGame.winning_probability A <=
      IndCpa.IndCpaGame.winning_probability
        (ind_cpa_reduction A max_queries) +
      global_epsilon max_queries gaussian_width_multiplier.

  Theorem is_secure : forall LA A max_queries,
    ValidPackage LA
      IndCpadGame.IndCpadAdv_import
      IndCpadGame.IndCpadAdv_export A ->
    fseparate LA IndCpadGame.oracle_mem_spec ->
    IndCpadGame.winning_probability A <= security_loss max_queries.
  Proof.
    move=> LA A max_queries hA hsep.
    rewrite /security_loss.
    apply: (le_trans (ind_cpa_reduction_bound LA A max_queries hA hsep)).
    rewrite lerD2r.
    exact: (IndCpa.is_secure
      (reduction_locs LA)
      (ind_cpa_reduction A max_queries)
      (ind_cpa_reduction_valid LA A max_queries hA hsep)
      (ind_cpa_reduction_fseparate LA hsep)).
  Qed.
End NoiseFloodingSecure.
