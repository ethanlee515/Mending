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
  (* TODO Restore at some point after nominal upgrade
  Include IsIndCpad(NF).
  *)
  Module IndCpadGame := IndCpad NF.
  Module IndCpaDSim := IndCpadSimulator(Scheme)(Metric)(Params).

  Parameter security_loss : nat -> R.
  Axiom is_secure_package : forall (A : IndCpaDSim.IndCpadAdv_t) max_queries,
    IndCpadGame.winning_probability A <= security_loss max_queries.
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

  Definition ind_cpa_reduction (A : IndCpaDSim.IndCpadAdv_t)
    (max_queries : nat) :=
    IndCpaDSim.IndCpaReduction_package A max_queries.

  Definition reduction_locs (A : IndCpaDSim.IndCpadAdv_t)
    (max_queries : nat) : Locations :=
    IndCpaDSim.IndCpaReduction_locs A max_queries.

  Lemma ind_cpa_reduction_valid :
    forall (A : IndCpaDSim.IndCpadAdv_t) max_queries,
      ValidPackage (reduction_locs A max_queries)
        IndCpa.IndCpaGame.IndCpaAdv_import
        IndCpa.IndCpaGame.IndCpaAdv_export
        (ind_cpa_reduction A max_queries).
  Proof.
    move=> A max_queries.
    exact: IndCpaDSim.IndCpaReduction_valid.
  Qed.

  Axiom ind_cpa_reduction_fseparate :
    forall (A : IndCpaDSim.IndCpadAdv_t) max_queries,
      fseparate (reduction_locs A max_queries) IndCpa.IndCpaGame.IndCpa_locs.

  Axiom ind_cpa_reduction_bound :
    forall (A : IndCpaDSim.IndCpadAdv_t) max_queries,
      IndCpadGame.winning_probability A <=
      IndCpa.IndCpaGame.winning_probability
        (ind_cpa_reduction A max_queries) +
      global_epsilon max_queries gaussian_width_multiplier.

  Theorem is_secure_package : forall (A : IndCpaDSim.IndCpadAdv_t) max_queries,
    IndCpadGame.winning_probability A <= security_loss max_queries.
  Proof.
    move=> A max_queries.
    rewrite /security_loss.
    apply: (le_trans (ind_cpa_reduction_bound A max_queries)).
    rewrite lerD2r.
    exact: (IndCpa.is_secure
      (reduction_locs A max_queries)
      (ind_cpa_reduction A max_queries)
      (ind_cpa_reduction_valid A max_queries)
      (ind_cpa_reduction_fseparate A max_queries)).
  Qed.
End NoiseFloodingSecure.
