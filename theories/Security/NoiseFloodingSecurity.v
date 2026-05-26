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

  Definition reduction_guess := IndCpadGame.guess.
  Definition reduction_adv_guess := IndCpa.IndCpaGame.adv_guess.
  Definition reduction_cpa_encrypt := IndCpa.IndCpaGame.oracle_encrypt.
  Definition reduction_sim_encrypt := IndCpaDSim.oracle_encrypt.

  Definition ReductionTop_t := package
    [interface
      #val #[reduction_guess] : 'unit → 'bool
    ]
    [interface
      #val #[reduction_adv_guess] : 'unit → 'bool
    ].

  Definition ReductionTop : ReductionTop_t :=
    [package emptym ;
      #def #[reduction_adv_guess] (_ : 'unit) : 'bool
      {
        b ← call [ reduction_guess ] : { 'unit ~> 'bool } tt ;;
        ret b
      }
    ].

  Definition ReductionBase_t := package
    [interface
      #val #[reduction_cpa_encrypt] : 'message_pair → 'ciphertext
    ]
    [interface
      #val #[reduction_sim_encrypt] : 'message_pair → 'ciphertext
    ].

  Definition ReductionBase : ReductionBase_t :=
    [package emptym ;
      #def #[reduction_sim_encrypt] (messages : 'message_pair) : 'ciphertext
      {
        c ← call [ reduction_cpa_encrypt ] :
          { message × message ~> ciphertext } messages ;;
        ret c
      }
    ].

  Definition ind_cpa_reduction
    (A : IndCpadGame.IndCpadAdv_t) (max_queries : nat) : raw_package :=
    ReductionTop ∘ A ∘ IndCpaDSim.IndCpadOracle max_queries ∘ ReductionBase.

  Axiom ind_cpa_reduction_bound :
    forall (A : IndCpadGame.IndCpadAdv_t) (max_queries : nat),
      IndCpadGame.winning_probability A <=
      IndCpa.IndCpaGame.winning_probability
        (ind_cpa_reduction A max_queries) +
      global_epsilon max_queries gaussian_width_multiplier.

  Theorem is_secure : forall (A : IndCpadGame.IndCpadAdv_t) (max_queries : nat),
    IndCpadGame.winning_probability A <= security_loss max_queries.
  Proof.
    move=> A max_queries.
    rewrite /security_loss.
    apply: (le_trans (ind_cpa_reduction_bound A max_queries)).
    rewrite lerD2r.
    exact: IndCpa.is_secure.
  Qed.
End NoiseFloodingSecure.
