Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra all_reals distr.
From mathcomp Require Import realseq realsum exp.
From mathcomp Require Import lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From Mending.LibExtras.MathcompExtras Require Import DistrExtras RealListExtras.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

Section KL_Divergence.

Context {R: realType}.

Definition δ_KL {T : choiceType} (P Q : {distr T / R}) : R :=
  \E_[P] (fun x => ln (P x / Q x)).

Definition absolute_continuous {T : choiceType} (P Q : {distr T / R}) : Prop :=
  forall x, Q x = 0 -> P x = 0.

Definition conditional_second {T U : choiceType}
    (P : {distr (T * U) / R}) (x : T) : {distr U / R} :=
  dmargin (fun xy : T * U => xy.2)
    (dcond P (fun xy : T * U => xy.1 == x)).

Definition coordinate_prefix_eq {n : nat} {Ω : choiceType}
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
    (dcond P (fun omega : Ω => coordinate_prefix_eq coord i a omega)).

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

Lemma kl_dmargin_injective {T U : choiceType}
    (f : T -> U) (P Q : {distr T / R}) :
  injective f ->
  δ_KL (dmargin f P) (dmargin f Q) = δ_KL P Q.
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
  0 <= δ_KL P Q.
Admitted.

(* Conditioning lemma: probabilities under dcond are honest conditional probabilities. *)
Lemma pr_dcond {T : choiceType} (mu : {distr T / R})
    (p : pred T) (A : pred T) :
  \P_[dcond mu p] A = \P_[mu, p] A.
Admitted.

(* A pointwise formula for the conditional second-coordinate distribution. *)
Lemma conditional_secondE {T U : choiceType}
    (P : {distr (T * U) / R}) (x : T) (y : U) :
  conditional_second P x y =
    if dmargin (fun xy : T * U => xy.1) P x == 0 then 0
    else P (x, y) / dmargin (fun xy : T * U => xy.1) P x.
Admitted.

(* Joint factorization: P(x,y) = P_X(x) * P_{Y|X=x}(y). *)
Lemma conditional_second_factorization {T U : choiceType}
    (P : {distr (T * U) / R}) (x : T) (y : U) :
  P (x, y) =
    dmargin (fun xy : T * U => xy.1) P x *
    conditional_second P x y.
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
  + move=> x; exact: kl_nonnegative.
  + exact: Hcond.
Qed.

Lemma iterated_kl_chain_bound
    {n : nat} {Ω : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i)
    (P Q : {distr Ω / R}) (eps : list R) :
  size eps = n ->
  coordinates_separate coord ->
  (forall i : 'I_n, 0 <= nth 0 eps i) ->
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  (forall (i : 'I_n) (a : forall j : 'I_n, X j),
    δ_KL (conditional_coordinate coord P i a)
         (conditional_coordinate coord Q i a) <= nth 0 eps i) ->
  δ_KL P Q <= list_sum eps.
Admitted.

Lemma ln_r_ineq (r : R) :
  0 < r ->
  r * ln r - r + 1 >= (r - 1)^2 / (r + 1).
Admitted.

Lemma kl_lower_bound_chi2 {T : choiceType} (P Q : {distr T / R}) :
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  δ_KL P Q >=
    sum (fun x : T =>
      Q x * ((P x / Q x - 1)^2 / (P x / Q x + 1))).
Admitted.

Lemma chi2_sum_nonneg {T : choiceType} (P Q : {distr T / R}) :
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  0 <=
    sum (fun x : T =>
      Q x * ((P x / Q x - 1)^2 / (P x / Q x + 1))).
Admitted.

Lemma divide_by_two_le (a b : R) :
  a <= b ->
  a / 2 <= b / 2.
Admitted.

Lemma divide_by_two_nonneg (a : R) :
  0 <= a ->
  0 <= a / 2.
Admitted.

Lemma sqrt_monotone_nonneg (a b : R) :
  0 <= a ->
  0 <= b ->
  a <= b ->
  Num.sqrt a <= Num.sqrt b.
Admitted.

Lemma total_variation_chi2_bound {T : choiceType} (P Q : {distr T / R}) :
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  total_variation P Q <=
    Num.sqrt (
      sum (fun x : T =>
        Q x * ((P x / Q x - 1)^2 / (P x / Q x + 1))) / 2).
Admitted.

Lemma pinsker {T : choiceType} (P Q : {distr T / R}) :
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  total_variation P Q <= Num.sqrt (δ_KL P Q / 2).
Proof.
move=> Hac HP HQ.
have Hchi :
    sum (fun x : T =>
      Q x * ((P x / Q x - 1)^2 / (P x / Q x + 1))) <=
    δ_KL P Q :=
  kl_lower_bound_chi2 P Q Hac HP HQ.
have Htv :
    total_variation P Q <=
      Num.sqrt (
        sum (fun x : T =>
          Q x * ((P x / Q x - 1)^2 / (P x / Q x + 1))) / 2) :=
  total_variation_chi2_bound P Q Hac HP HQ.
have Hchi2 :
    sum (fun x : T =>
      Q x * ((P x / Q x - 1)^2 / (P x / Q x + 1))) / 2 <=
    δ_KL P Q / 2 :=
  divide_by_two_le _ _ Hchi.
have Hsum_nonneg :
    0 <=
      sum (fun x : T =>
        Q x * ((P x / Q x - 1)^2 / (P x / Q x + 1))) / 2 :=
  divide_by_two_nonneg _ (chi2_sum_nonneg P Q Hac HP HQ).
have Hkl_nonneg : 0 <= δ_KL P Q / 2 :=
  divide_by_two_nonneg _ (kl_nonnegative P Q).
apply: (le_trans Htv).
apply: sqrt_monotone_nonneg.
- exact: Hsum_nonneg.
- exact: Hkl_nonneg.
- exact: Hchi2.
Qed.

Theorem pythagorean_probability_preservation
    {n : nat} {Ω : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i)
    (P Q : {distr Ω / R}) (eps : list R) :
  size eps = n ->
  coordinates_separate coord ->
  (forall i : 'I_n, 0 <= nth 0 eps i) ->
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  (forall (i : 'I_n) (a : forall j : 'I_n, X j),
    δ_KL (conditional_coordinate coord P i a)
         (conditional_coordinate coord Q i a) <= nth 0 eps i) ->
  total_variation P Q <= Num.sqrt (list_sum eps / 2).
Proof.
move=> Hsize Hsep Heps Hac HP HQ Hcond.
have Hpin := pinsker P Q Hac HP HQ.
apply: (le_trans Hpin).
apply: ler_wsqrtr.
have Hkl : δ_KL P Q <= list_sum eps :=
  iterated_kl_chain_bound coord P Q eps Hsize Hsep Heps Hac HP HQ Hcond.
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
Admitted.

End KL_Divergence.
