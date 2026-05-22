From Stdlib Require Import Utf8 List Lia.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".

Local Obligation Tactic := simpl.

Program Definition nth_valid {A} (lst : list A) (n : nat)
    (index_valid : n < length lst) : A :=
  match nth_error lst n with
  | Some a => a
  | None => _
  end.
Next Obligation.
move => A lst n index_valid H.
symmetry in H.
apply nth_error_None in H.
move/ltP in index_valid.
lia.
Defined.
