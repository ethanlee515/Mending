Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra all_reals distr.
From mathcomp Require Import realseq realsum exp.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

Local Open Scope ring_scope.

Section KL_Divergence.

Context {R: realType} {T:choiceType}.

Definition δ_KL (P Q : {distr T / R}) : R :=
  sum (fun x => P x * ln (P x / Q x)).

End KL_Divergence.