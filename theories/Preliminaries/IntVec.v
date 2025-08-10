Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp Require Import reals realsum exp sequences realseq distr.

Local Open Scope ring_scope.

Definition max_norm {n} (v : n.-tuple int) : nat :=
  \big[Order.max/0]_(i < n) absz (tnth v i).

Definition ivec_sub {n} (v w : n.-tuple int) : n.-tuple int :=
  [tuple (tnth v i - tnth w i) | i < n].

Definition ivec_dist {n} (v w : n.-tuple int) : nat :=
  max_norm (ivec_sub v w).