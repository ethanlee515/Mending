From Stdlib Require Import Unicode.Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import reals distr.
From mathcomp Require Import realseq realsum exp.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

Open Scope ring_scope.

Section DistrExtras.

Context {R : realType}.

Definition statistical_distance {T : choiceType} (P Q : {distr T / R}) : R :=
  sum (fun x => `| P x - Q x |).

(* -- Conditional distributions -- *)
(* Will adapt from EasyCrypt *)

Definition dcond {T : choiceType} (P : {distr T / R}) (p : pred T)
  : {distr T / R}.
Admitted.

End DistrExtras.

