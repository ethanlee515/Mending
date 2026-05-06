Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra all_reals distr.
From mathcomp Require Import realseq realsum exp.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

Local Open Scope ring_scope.

Section KL_Divergence.

Context {R: realType}.

Definition kl_divergence {T : choiceType} (P Q : {distr T / R}) : R :=
  \E_[P] (fun x => ln (P x / Q x)).

Lemma mass1_kl_left {T : choiceType} (P Q : {distr T / R}) :
  dweight P = 1 ->
  kl_divergence P Q =
    \E_[P] (fun x => ln (P x / Q x)).
Proof. by []. Qed.

Definition δ_KL {T : choiceType} (P Q : {distr T / R}) : R :=
  sum (fun x => P x * ln (P x / Q x)).

End KL_Divergence.
