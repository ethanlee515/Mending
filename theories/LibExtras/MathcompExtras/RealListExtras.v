Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Section RealListExtras.

Context {R : realType}.

Fixpoint sum_squares (lst : list R) : R :=
  match lst with
  | [::] => 0
  | head :: tail => head * head + sum_squares tail
  end.

Definition l2_norm (eps_lst : list R) := Num.sqrt (sum_squares eps_lst).

Fixpoint list_sum (s : list R) : R :=
  match s with
  | [::] => 0
  | head :: tail => head + list_sum tail
  end.

Definition pythagorean_tv_bound (s : list R) : R :=
  Num.sqrt (list_sum s / 2).

End RealListExtras.
