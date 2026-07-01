From Stdlib Require Import Utf8 List Lia.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot all_order all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".

Fixpoint nth_valid {A} (lst : list A) (n : nat)
    {struct lst} : n < length lst -> A :=
  match lst as lst', n as n' return n' < length lst' -> A with
  | [::], _ => fun H => False_rect _ (notF H)
  | x :: _, 0 => fun _ => x
  | _ :: xs, n'.+1 => fun H => nth_valid xs n' H
  end.

Lemma List_In_mem {A : eqType} (x : A) (s : list A) :
  In x s -> x \in s.
Proof.
elim: s=> [|y ys IH] //=.
case=> [->|Hin].
  by rewrite inE eqxx.
by rewrite inE IH ?orbT.
Qed.

Lemma nth_valid_nth_error {A} (lst : list A) n
    (index_valid : n < length lst) :
  nth_error lst n = Some (nth_valid lst n index_valid).
Proof.
by elim: lst n index_valid=> [|x xs IH] [|n] H //=.
Qed.

Lemma nth_valid_in {A : eqType} (lst : list A) n
    (index_valid : n < length lst) :
  nth_valid lst n index_valid \in lst.
Proof.
apply: List_In_mem.
exact: (nth_error_In _ _ (nth_valid_nth_error lst n index_valid)).
Qed.
