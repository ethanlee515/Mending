Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra all_reals distr.
From mathcomp Require Import realseq realsum exp.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From Mending.LibExtras.MathcompExtras Require Import DistrExtras.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

Section KL_Core.

Context {R: realType}.

Definition δ_KL {T : choiceType} (P Q : {distr T / R}) : R :=
  \E_[P] (fun x => ln (P x / Q x)).

Definition absolute_continuous {T : choiceType} (P Q : {distr T / R}) : Prop :=
  forall x, Q x = 0 -> P x = 0.

Lemma mass1_kl_left {T : choiceType} (P Q : {distr T / R}) :
  dweight P = 1 ->
  δ_KL P Q =
    \E_[P] (fun x => ln (P x / Q x)).
Proof. by []. Qed.

Lemma kl_ext {T : choiceType} (P P' Q Q' : {distr T / R}) :
  P =1 P' ->
  Q =1 Q' ->
  δ_KL P Q = δ_KL P' Q'.
Proof.
move=> HP HQ.
rewrite /δ_KL.
rewrite (expectation_distr_ext P P' _ HP).
apply: expectation_ext=> x.
by rewrite -HP -HQ.
Qed.

Lemma kl_left_dnull {T : choiceType} (P Q : {distr T / R}) :
  P =1 dnull ->
  δ_KL P Q = 0.
Proof.
move=> HP.
rewrite /δ_KL.
rewrite (expectation_distr_ext P dnull _ HP).
exact: expectation_dnull.
Qed.

Lemma kl_self {T : choiceType} (P : {distr T / R}) :
  δ_KL P P = 0.
Proof.
rewrite /δ_KL /esp.
rewrite (eq_sum (F2 := fun _ : T => 0)).
  exact: sum0.
move=> x.
case Px0: (P x == 0).
  by rewrite (eqP Px0) mulr0.
have HPx : P x != 0 by rewrite Px0.
have -> : P x / P x = 1 by rewrite divff ?unitfE ?HPx.
by rewrite ln1 mul0r.
Qed.

Lemma absolute_continuous_positive {T : choiceType}
    (P Q : {distr T / R}) (x : T) :
  absolute_continuous P Q ->
  0 < P x -> 0 < Q x.
Proof.
move=> Hac HPx.
rewrite lt_def ge0_mu andbT.
apply/negP=> /eqP HQx0.
have HPx0 := Hac x HQx0.
by rewrite HPx0 ltxx in HPx.
Qed.

Lemma kl_dmargin_injective {T U : choiceType}
    (f : T -> U) (P Q : {distr T / R}) :
  injective f ->
  δ_KL (dmargin f P) (dmargin f Q) = δ_KL P Q.
Admitted.

Lemma kl_dlet_data_processing {T U : choiceType}
    (P Q : {distr T / R}) (K : T -> {distr U / R}) :
  (forall x, dweight (K x) = 1) ->
  δ_KL (\dlet_(x <- P) K x) (\dlet_(x <- Q) K x) <= δ_KL P Q.
Admitted.

Lemma expectation_le_const_on_support {T : choiceType}
    (P : {distr T / R}) (f : T -> R) (c : R) :
  dweight P = 1 ->
  0 <= c ->
  (forall x, 0 <= f x) ->
  (forall x, 0 < P x -> f x <= c) ->
  \E_[P] f <= c.
Proof.
move=> HP Hc Hf Hbound.
rewrite /esp.
have Hpoint x : 0 <= f x * P x <= c * P x.
  apply/andP; split.
  - by rewrite mulr_ge0 ?Hf ?ge0_mu.
  - case Px0: (P x == 0).
    + by rewrite (eqP Px0) !mulr0.
    + apply: ler_wpM2r; first exact: ge0_mu.
      apply: Hbound.
      by rewrite lt_def Px0 ge0_mu.
have smG : summable (fun x : T => c * P x).
  change (summable (c \*o P)).
  exact: summableZ.
have smF : summable (fun x : T => f x * P x).
  apply: (le_summable (F2 := fun x : T => c * P x)); first exact: Hpoint.
  exact: smG.
apply: (le_trans (le_sum smF smG _)).
  by move=> x; have /andP[_ hx] := Hpoint x.
change (\E_[P] (fun=> c) <= c).
by rewrite exp_cst HP mul1r.
Qed.

Lemma kl_nonnegative {T : choiceType} (P Q : {distr T / R}) :
  absolute_continuous P Q ->
  dweight P = 1 ->
  0 <= δ_KL P Q.
Admitted.

End KL_Core.
