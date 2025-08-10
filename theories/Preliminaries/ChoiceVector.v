From Stdlib Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect tuple.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
Import PackageNotation.
Local Open Scope form_scope.
Local Open Scope package_scope.
Local Open Scope seq_scope.

Set Bullet Behavior "Strict Subproofs".

Fixpoint chVec (t: choice_type) (n: nat) :=
  match n with
  | 0 => chUnit
  | S i => chProd t (chVec t i)
  end.

Fixpoint toVec {t : choice_type} {n : nat}
    : n.-tuple t -> chVec t n :=
  match n with
  | 0 => fun _ => tt
  | S i => fun w => (thead w, toVec (behead_tuple w))
  end.

Fixpoint fromVec {t : choice_type} {n: nat}
    : chVec t n -> n.-tuple t :=
  match n with
  | 0 => fun _ => [tuple]
  | S i => fun w => let '(h, t) := w in cons_tuple h (fromVec t)
  end.

Lemma toVecK {t : choice_type} {n : nat} (v : chVec t n) :
  toVec (fromVec v) = v.
Proof.
elim: n v.
- move => v.
  by case: v.
- move => n IH v /=.
  admit.
Admitted.

Lemma fromVecK {t : choice_type} {n : nat} (v : n.-tuple t) :
  fromVec (toVec v) = v.
Proof.
elim: n v.
- rewrite /fromVec /toVec /=.
  move => v.
  symmetry.
  exact: tuple0.
- admit.
Admitted.