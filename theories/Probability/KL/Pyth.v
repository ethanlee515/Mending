(* Distribution facts for Pythagorean errors. *)

Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals realsum exp distr.
From mathcomp Require Import lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From Mending.Probability Require Import Ae.
From Mending.Probability.KL Require Import Core Conditional Pinsker.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras RealTupleExtras.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

Section PythagoreanDistributionJudgments.

Context {R : realType}.

Theorem pythagorean_probability_preservation
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R) :
  (forall i : 'I_n, 0 <= tnth eps i) ->
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  (forall (i : 'I_n) (a : forall j : 'I_n, A),
    δ_KL (conditional_coordinate P i a)
         (conditional_coordinate Q i a) <=
      tnth eps i) ->
  total_variation P Q <= Num.sqrt ((\sum_(i < n) tnth eps i) / 2).
Proof.
move=> Heps Hac HP HQ Hcond.
have Hpin := pinsker P Q Hac HP HQ.
apply: (le_trans Hpin).
apply: ler_wsqrtr.
have Hkl :
    δ_KL P Q <= \sum_(i < n) tnth eps i :=
  iterated_kl_chain_bound P Q eps Heps Hac HP HQ Hcond.
lra.
Qed.

Corollary pythagorean_probability_preservation_sup_pinsker
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : R) :
  0 <= eps ->
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  (forall (i : 'I_n) (a : forall j : 'I_n, A),
    δ_KL (conditional_coordinate P i a)
         (conditional_coordinate Q i a) <= eps) ->
  total_variation P Q <= Num.sqrt ((n%:R * eps) / 2).
Proof.
move=> Heps Hac HP HQ Hcond.
pose eps_tuple : n.-tuple R := [tuple eps | i < n].
have Heps_tuple : forall i : 'I_n, 0 <= tnth eps_tuple i.
  by move=> i; rewrite /eps_tuple tnth_mktuple.
have Hcond_tuple : forall (i : 'I_n) (a : forall j : 'I_n, A),
    δ_KL (conditional_coordinate P i a)
         (conditional_coordinate Q i a) <=
      tnth eps_tuple i.
  by move=> i a; rewrite /eps_tuple tnth_mktuple; apply: Hcond.
have Htv :=
  pythagorean_probability_preservation P Q eps_tuple
    Heps_tuple Hac HP HQ Hcond_tuple.
apply: (le_trans Htv).
apply: ler_wsqrtr.
rewrite (eq_bigr (fun _ : 'I_n => eps)); last first.
  by move=> i _; rewrite /eps_tuple tnth_mktuple.
by rewrite big_const_ord iter_addr_0 mulr_natl.
Qed.

Definition pythDist
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R) : Prop :=
  (forall i : 'I_n, 0 <= tnth eps i) /\
  absolute_continuous P Q /\
  dweight P = 1 /\
  dweight Q = 1 /\
  forall (i : 'I_n) (a : forall j : 'I_n, A),
    δ_KL (conditional_coordinate P i a)
         (conditional_coordinate Q i a) <=
      tnth eps i.

Lemma pythDist_total_variation
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R) :
  pythDist P Q eps ->
  total_variation P Q <= Num.sqrt ((\sum_(i < n) tnth eps i) / 2).
Proof.
move=> [Heps [Hac [HP [HQ Hcond]]]].
exact: (pythagorean_probability_preservation P Q eps
          Heps Hac HP HQ Hcond).
Qed.

Lemma pythDist_final_total_variation
    {n : nat} {A : choiceType}
    (P Q : {distr (n.+1.-tuple A) / R}) (eps : n.+1.-tuple R) :
  pythDist P Q eps ->
  total_variation (dmargin (fun omega => tnth omega ord_max) P)
    (dmargin (fun omega => tnth omega ord_max) Q) <=
    pythagorean_tv_bound eps.
Admitted.

Lemma pythDist_bind_same_kernel
  {n : nat}
  {A mid_t out_t : choiceType}
  (h_mid : mid_t -> A)
  (h_out : out_t -> A)
  (ML MR : {distr mid_t / R})
  (K : mid_t -> {distr out_t / R})
  (mid : pred mid_t)
  (post : pred out_t)
  (eps : n.+1.-tuple R)
  (P0 Q0 : {distr (n.+1.-tuple A) / R}) :
  pythDist P0 Q0 eps ->
  dmargin (fun omega => tnth omega ord_max) P0
    =1 dmargin h_mid ML ->
  dmargin (fun omega => tnth omega ord_max) Q0
    =1 dmargin h_mid MR ->
  (forall y, y \in dinsupp ML -> mid y) ->
  (forall y, y \in dinsupp MR -> mid y) ->
  (forall y, mid y -> forall x, x \in dinsupp (K y) -> post x) ->
  exists (P Q : {distr (n.+1.-tuple A) / R}),
    pythDist P Q eps /\
    dmargin (fun omega => tnth omega ord_max) P
      =1 dmargin h_out (\dlet_(y <- ML) K y) /\
    dmargin (fun omega => tnth omega ord_max) Q
      =1 dmargin h_out (\dlet_(y <- MR) K y) /\
    (forall x, x \in dinsupp (\dlet_(y <- ML) K y) -> post x) /\
    (forall x, x \in dinsupp (\dlet_(y <- MR) K y) -> post x).
Admitted.

End PythagoreanDistributionJudgments.
