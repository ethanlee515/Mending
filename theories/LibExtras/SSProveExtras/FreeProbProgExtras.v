From Stdlib Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Crypt Require Import ChoiceAsOrd choice_type FreeProbProg.
From Mending.LibExtras.SSProveExtras Require Import SubDistrExtras.

Definition P_OP_clean : Type :=
  { X : choice_type & ord_relmonObj SDistr_clean X }.

Definition P_AR_clean : P_OP_clean -> choiceType :=
  fun op => projT1 op.

Definition rFreePr_clean :=
  rFree P_OP_clean P_AR_clean.

Definition rFreeProb_squ_clean :=
  product_rmon rFreePr_clean rFreePr_clean.

Lemma P_OP_cleanE : P_OP = P_OP_clean.
Proof. reflexivity. Qed.

Lemma rFreePr_cleanE : rFreePr = rFreePr_clean.
Proof. reflexivity. Qed.

Lemma rFreeProb_squ_cleanE : rFreeProb_squ = rFreeProb_squ_clean.
Proof. reflexivity. Qed.
