From Stdlib Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect tuple.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
Import PackageNotation.
Local Open Scope form_scope.
Local Open Scope package_scope.
Local Open Scope seq_scope.

Fixpoint chVec (t: choice_type) (n: nat) :=
  match n with
  | 0 => chUnit
  | S i => chProd t (chVec t i)
  end.

Fixpoint toVec {t : choice_type} {n : nat} (vs : n.-tuple t) : chVec t n :=
  match n return n.-tuple t -> chVec t n with
  | 0 => fun _ => tt
  | S i => fun w => (thead w, toVec (behead_tuple w))
  end vs.

Fixpoint fromVec {t : choice_type} {n: nat} (v : chVec t n) : n.-tuple t :=
  match n return chVec t n -> n.-tuple t with
  | 0 => fun _ => [tuple]
  | S i => fun w => let '(h, t) := w in cons_tuple h (fromVec t)
  end v.
