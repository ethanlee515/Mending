Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra all_reals distr.
From mathcomp Require Import realseq realsum exp.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From Mending.LibExtras.MathcompExtras Require Import DistrExtras.
From Mending.Probability.KL Require Import Core ChainPointwise.
From Mending.Probability Require Import ConditionalCoordinate.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

Section KL_Conditional.

Context {R: realType}.

Lemma conditional_second_absolute_continuous {T U : choiceType}
    (P Q : {distr (T * U) / R}) (x : T) :
  absolute_continuous P Q ->
  absolute_continuous (conditional_second P x) (conditional_second Q x).
Admitted.

Lemma conditional_second_kl_nonnegative {T U : choiceType}
    (P Q : {distr (T * U) / R}) (x : T) :
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  0 <= δ_KL (conditional_second P x) (conditional_second Q x).
Admitted.

(* Explicit marginal expectation rule for the KL integrand. *)
Lemma expectation_dmargin_kl {T U : choiceType}
    (P Q : {distr (T * U) / R}) :
  \E_[P]
    (fun xy : T * U =>
      ln (dmargin (fun xy : T * U => xy.1) P xy.1 /
          dmargin (fun xy : T * U => xy.1) Q xy.1)) =
  \E_[dmargin (fun xy : T * U => xy.1) P]
    (fun x : T =>
      ln (dmargin (fun xy : T * U => xy.1) P x /
          dmargin (fun xy : T * U => xy.1) Q x)).
Admitted.

(* Explicit conditional expectation rule for the KL integrand. *)
Lemma expectation_conditional_kl {T U : choiceType}
    (P Q : {distr (T * U) / R}) :
  \E_[P]
    (fun xy : T * U =>
      ln (conditional_second P xy.1 xy.2 /
          conditional_second Q xy.1 xy.2)) =
  \E_[dmargin (fun xy : T * U => xy.1) P]
    (fun x : T =>
      δ_KL (conditional_second P x) (conditional_second Q x)).
Admitted.

Lemma kl_chain_rule_decomp {T U : choiceType}
    (P Q : {distr (T * U) / R}) :
  (fun xy : T * U => ln (P xy / Q xy)) =1
    (fun xy : T * U =>
      ln (dmargin (fun xy : T * U => xy.1) P xy.1 /
          dmargin (fun xy : T * U => xy.1) Q xy.1) +
      ln (conditional_second P xy.1 xy.2 /
          conditional_second Q xy.1 xy.2)).
Admitted.

Lemma kl_chain_rule_split {T U : choiceType}
    (P Q : {distr (T * U) / R}) :
  \E_[P]
    (fun xy : T * U =>
      ln (dmargin (fun xy : T * U => xy.1) P xy.1 /
          dmargin (fun xy : T * U => xy.1) Q xy.1) +
      ln (conditional_second P xy.1 xy.2 /
          conditional_second Q xy.1 xy.2)) =
  \E_[P] (fun xy : T * U =>
      ln (dmargin (fun xy : T * U => xy.1) P xy.1 /
          dmargin (fun xy : T * U => xy.1) Q xy.1)) +
  \E_[P] (fun xy : T * U =>
      ln (conditional_second P xy.1 xy.2 /
          conditional_second Q xy.1 xy.2)).
Admitted.

Lemma kl_chain_rule {T U : choiceType}
    (P Q : {distr (T * U) / R}) :
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  δ_KL P Q =
    δ_KL (dmargin (fun xy : T * U => xy.1) P)
         (dmargin (fun xy : T * U => xy.1) Q) +
    \E_[dmargin (fun xy : T * U => xy.1) P]
      (fun x => δ_KL (conditional_second P x) (conditional_second Q x)).
Proof.
move=> Hac HP HQ.
pose Pm := dmargin (fun xy : T * U => xy.1) P.
pose Qm := dmargin (fun xy : T * U => xy.1) Q.
have Hmarg :
    \E_[P] (fun xy : T * U => ln (Pm xy.1 / Qm xy.1)) =
    δ_KL Pm Qm.
  rewrite /δ_KL /esp /Pm /Qm.
  exact: (expectation_dmargin_kl P Q).
have Hcond :
    \E_[P]
      (fun xy : T * U =>
        ln (conditional_second P xy.1 xy.2 /
            conditional_second Q xy.1 xy.2)) =
    \E_[Pm] (fun x => δ_KL (conditional_second P x)
                                 (conditional_second Q x)).
  exact: (expectation_conditional_kl P Q).
have Hdecomp := kl_chain_rule_decomp P Q.
have Hsplit := kl_chain_rule_split P Q.
rewrite /δ_KL.
have Hlhs :
    \E_[P] (fun xy : T * U => ln (P xy / Q xy)) =
    \E_[P]
      (fun xy : T * U =>
        ln (Pm xy.1 / Qm xy.1) +
        ln (conditional_second P xy.1 xy.2 /
            conditional_second Q xy.1 xy.2)).
  exact: (expectation_ext P _ _ Hdecomp).
rewrite Hlhs.
rewrite Hsplit.
rewrite Hmarg Hcond.
by [].
Qed.

Corollary kl_conditional_sup_bound {T U : choiceType}
    (P Q : {distr (T * U) / R}) (eps0 eps1 : R) :
  0 <= eps1 ->
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  δ_KL (dmargin (fun xy : T * U => xy.1) P)
       (dmargin (fun xy : T * U => xy.1) Q) <= eps0 ->
  (forall x,
    0 < dmargin (fun xy : T * U => xy.1) P x ->
    δ_KL (conditional_second P x) (conditional_second Q x) <= eps1) ->
  δ_KL P Q <= eps0 + eps1.
Proof.
move=> Heps1 Hac HP HQ Hmarg Hcond.
rewrite (kl_chain_rule P Q Hac HP HQ).
apply: lerD.
- exact: Hmarg.
- apply: expectation_le_const_on_support.
  + by rewrite dmargin_dweight.
  + exact: Heps1.
  + move=> x.
    exact: (conditional_second_kl_nonnegative P Q x Hac HP HQ).
  + exact: Hcond.
Qed.

Lemma iterated_kl_chain_bound
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R) :
  (forall i : 'I_n, 0 <= tnth eps i) ->
  finite_kl P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  (forall (i : 'I_n) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a)) ->
  (forall (i : 'I_n) (a : i.-tuple A),
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <= tnth eps i) ->
  δ_KL P Q <= \sum_(i < n) tnth eps i.
Proof.
move=> Heps Hfin HP HQ Hfincond Hcond.
exact: (iterated_kl_chain_bound_via_pointwise
  P Q eps Heps HP HQ Hfin Hfincond Hcond).
Qed.

End KL_Conditional.
