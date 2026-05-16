Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra all_reals distr.
From mathcomp Require Import realseq realsum exp.
From mathcomp Require Import lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From Mending Require Import DistrExtras.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

Section KL_Divergence.

Context {R: realType}.

Definition δ_KL {T : choiceType} (P Q : {distr T / R}) : R :=
  \E_[P] (fun x => ln (P x / Q x)).

Definition absolute_continuous {T : choiceType} (P Q : {distr T / R}) : Prop :=
  forall x, Q x = 0 -> P x = 0.

Definition total_variation {T : choiceType} (P Q : {distr T / R}) : R :=
  (1 / 2) * statistical_distance P Q.

Definition conditional_second {T U : choiceType}
    (P : {distr (T * U) / R}) (x : T) : {distr U / R} :=
  dmargin (fun xy : T * U => xy.2)
    (dcond P (fun xy : T * U => xy.1 == x)).

Definition tuple_prefix_eq {n : nat} {Ω : choiceType}
    {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i)
    (i : 'I_n) (a : forall j : 'I_n, X j) (omega : Ω) : bool :=
  [forall j : 'I_n, (j < i)%N ==> (coord j omega == a j)].

Definition conditional_coordinate {n : nat} {Ω : choiceType}
    {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i)
    (P : {distr Ω / R}) (i : 'I_n) (a : forall j : 'I_n, X j)
    : {distr (X i) / R} :=
  dmargin (coord i)
    (dcond P (fun omega : Ω => tuple_prefix_eq coord i a omega)).

Definition coordinates_separate {n : nat} {Ω : choiceType}
    {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i) : Prop :=
  forall omega1 omega2 : Ω,
    (forall i : 'I_n, coord i omega1 = coord i omega2) ->
    omega1 = omega2.

Lemma mass1_kl_left {T : choiceType} (P Q : {distr T / R}) :
  dweight P = 1 ->
  δ_KL P Q =
    \E_[P] (fun x => ln (P x / Q x)).
Proof. by []. Qed.

Lemma expectation_le_const_on_support {T : choiceType}
    (P : {distr T / R}) (f : T -> R) (c : R) :
  dweight P = 1 ->
  (forall x, 0 < P x -> f x <= c) ->
  \E_[P] f <= c.
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
Admitted.

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
move=> _ Hac HP HQ Hmarg Hcond.
rewrite (kl_chain_rule P Q Hac HP HQ).
apply: lerD.
- exact: Hmarg.
- apply: expectation_le_const_on_support.
  + by rewrite dmargin_dweight.
  + exact: Hcond.
Qed.

Lemma iterated_kl_chain_bound
    {n : nat} {Ω : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i)
    (P Q : {distr Ω / R}) (eps : n.-tuple R) :
  coordinates_separate coord ->
  (forall i : 'I_n, 0 <= tnth eps i) ->
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  (forall (i : 'I_n) (a : forall j : 'I_n, X j),
    δ_KL (conditional_coordinate coord P i a)
         (conditional_coordinate coord Q i a) <= tnth eps i) ->
  δ_KL P Q <= \sum_(i < n) tnth eps i.
Admitted.

Lemma pinsker {T : choiceType} (P Q : {distr T / R}) :
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  total_variation P Q <= Num.sqrt (δ_KL P Q / 2).
Admitted.

Theorem pythagorean_probability_preservation
    {n : nat} {Ω : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i)
    (P Q : {distr Ω / R}) (eps : n.-tuple R) :
  coordinates_separate coord ->
  (forall i : 'I_n, 0 <= tnth eps i) ->
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  (forall (i : 'I_n) (a : forall j : 'I_n, X j),
    δ_KL (conditional_coordinate coord P i a)
         (conditional_coordinate coord Q i a) <= tnth eps i) ->
  total_variation P Q <= Num.sqrt ((\sum_(i < n) tnth eps i) / 2).
Proof.
move=> Hsep Heps Hac HP HQ Hcond.
have Hpin := pinsker P Q Hac HP HQ.
apply: (le_trans Hpin).
apply: ler_wsqrtr.
have Hkl :
    δ_KL P Q <= \sum_(i < n) tnth eps i :=
  iterated_kl_chain_bound coord P Q eps Hsep Heps Hac HP HQ Hcond.
lra.
Qed.

Corollary pythagorean_probability_preservation_sup_pinsker
    {n : nat} {Ω : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i)
    (P Q : {distr Ω / R}) (eps : R) :
  coordinates_separate coord ->
  0 <= eps ->
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  (forall (i : 'I_n) (a : forall j : 'I_n, X j),
    δ_KL (conditional_coordinate coord P i a)
         (conditional_coordinate coord Q i a) <= eps) ->
  total_variation P Q <= Num.sqrt ((n%:R * eps) / 2).
Proof.
move=> Hsep Heps Hac HP HQ Hcond.
pose eps_tuple : n.-tuple R := [tuple eps | i < n].
have Heps_tuple : forall i : 'I_n, 0 <= tnth eps_tuple i.
  by move=> i; rewrite /eps_tuple tnth_mktuple.
have Hcond_tuple : forall (i : 'I_n) (a : forall j : 'I_n, X j),
    δ_KL (conditional_coordinate coord P i a)
         (conditional_coordinate coord Q i a) <= tnth eps_tuple i.
  by move=> i a; rewrite /eps_tuple tnth_mktuple; apply: Hcond.
have Htv :=
  pythagorean_probability_preservation coord P Q eps_tuple
    Hsep Heps_tuple Hac HP HQ Hcond_tuple.
apply: (le_trans Htv).
apply: ler_wsqrtr.
rewrite (eq_bigr (fun _ : 'I_n => eps)); last first.
  by move=> i _; rewrite /eps_tuple tnth_mktuple.
by rewrite big_const_ord iter_addr_0 mulr_natl.
Qed.

End KL_Divergence.
