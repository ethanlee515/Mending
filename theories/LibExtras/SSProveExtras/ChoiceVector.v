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

(* SSProve compatible vectors *)

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

(* Non-uniform tuples *)
(*
Fixpoint nonuniform_vec {n : nat}
  : n.-tuple choice_type -> choice_type :=
match n with
| 0 => fun _ => chUnit
| S m => fun types => chProd (thead types) (nonuniform_vec (behead types))
end.

Program Definition nth_nonuniform_vec {dim : nat} {types : dim.-tuple choice_type}
  (vec : nonuniform_vec types) (n : 'I_dim) (gt0_n : dim > 0) : (tnth types n).
Admitted.
*)

