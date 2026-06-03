Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Section RealTupleExtras.

Context {R : realType}.

Fixpoint sum_squares (lst : list R) : R :=
  match lst with
  | [::] => 0
  | head :: tail => head * head + sum_squares tail
  end.

Definition l2_norm (eps_lst : list R) := Num.sqrt (sum_squares eps_lst).

Definition tuple_sum {n : nat} (s : n.-tuple R) : R :=
  \sum_(i < n) tnth s i.

Definition tuple_sum_squares {n : nat} (s : n.-tuple R) : R :=
  \sum_(i < n) (tnth s i) ^+ 2.

Definition two_norm {n : nat} (s : n.-tuple R) : R :=
  Num.sqrt (tuple_sum_squares s).

Definition pythagorean_tv_bound {n : nat} (s : n.-tuple R) : R :=
  Num.sqrt (tuple_sum s / 2).

End RealTupleExtras.
