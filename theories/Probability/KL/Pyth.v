(* Distribution facts for Pythagorean errors. *)

Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals realsum exp distr.
From mathcomp Require Import lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From Mending.Probability Require Import Ae.
From Mending.Probability.KL Require Import Core Conditional Pinsker.
From Mending.Probability Require Import ConditionalCoordinate.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras TupleExtras.

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

Lemma pythDist_refl
  {n : nat} {A : choiceType}
  (P : {distr (n.-tuple A) / R}) (eps : n.-tuple R) :
  (forall i : 'I_n, 0 <= tnth eps i) ->
  dweight P = 1 ->
  pythDist P P eps.
Proof.
move=> Heps HP.
split; first exact: Heps.
split.
  by move=> x ->.
split; first exact: HP.
split; first exact: HP.
move=> i a.
rewrite kl_self.
exact: Heps i.
Qed.

Fixpoint pythCallErrors (q : nat) (eps : R) : (q.*2).+3.-tuple R :=
  if q is q'.+1 then
    cat_tuple [tuple 0; eps] (pythCallErrors q' eps)
  else
    [tuple 0; eps; 0].

Lemma pythCallErrors_nonneg (q : nat) (eps : R) :
  0 <= eps ->
  forall i : 'I_(q.*2).+3, 0 <= tnth (pythCallErrors q eps) i.
Proof.
move=> Heps.
elim: q=> [|q IH] i.
- rewrite /=.
  by case: i=> [[|[|[|n]]]].
- rewrite /=.
  apply: (cat_tuple_nonneg [tuple 0; eps] (pythCallErrors q eps) i).
  + by case=> [[|[|n]]].
  exact: IH.
Qed.

Lemma pythCallErrors0 (eps : R) :
  pythCallErrors 0 eps = [tuple 0; eps; 0].
Proof.
by [].
Qed.

Lemma pythCallErrorsS (q : nat) (eps : R) :
  pythCallErrors q.+1 eps =
  cat_tuple [tuple 0; eps] (pythCallErrors q eps).
Proof.
by [].
Qed.

Lemma tuple_sum_pythCallErrors (q : nat) (eps : R) :
  tuple_sum (pythCallErrors q eps) = q.+1%:R * eps.
Proof.
elim: q=> [|q IH].
- rewrite /tuple_sum /= !big_ord_recl big_ord0 /=.
  by rewrite !(tnth_nth 0) /= !addr0 !add0r mul1r.
- rewrite /tuple_sum /= big_ord_recl /= big_ord_recl /=.
  rewrite !(tnth_nth 0) /=.
  have Htail :
      \sum_(i < q.+1.*2.+1)
        tnth (cat_tuple [tuple 0; eps] (pythCallErrors q eps))
          (lift ord0 (lift ord0 i)) =
      tuple_sum (pythCallErrors q eps).
    rewrite /tuple_sum.
    apply: eq_bigr=> i _.
    have Hi : (1.+1 <= lift ord0 (lift ord0 i))%N by [].
    rewrite (cat_tuple_tnth_suffix [tuple 0; eps] (pythCallErrors q eps)
      (lift ord0 (lift ord0 i)) Hi).
    have -> :
        @Ordinal (q.*2.+3) (lift ord0 (lift ord0 i) - 2)
          (@cat_tuple_suffix_bound 1 (q.*2.+2)
            (lift ord0 (lift ord0 i)) Hi) = i.
      apply: val_inj.
      by rewrite /= /bump !leq0n !add1n !subSS subn0.
    by [].
  rewrite Htail IH add0r.
  by rewrite -[q.+2%:R]natr1 mulrDl mul1r addrC.
Qed.

Lemma pythagorean_tv_bound_pythCallErrors (q : nat) (eps : R) :
  pythagorean_tv_bound (pythCallErrors q eps) =
  Num.sqrt ((q.+1%:R * eps) / 2).
Proof.
by rewrite /pythagorean_tv_bound tuple_sum_pythCallErrors.
Qed.

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
Proof.
move=> [Heps [Hac [HP [HQ Hcond]]]].
pose final := fun omega : n.+1.-tuple A => tnth omega ord_max.
have HPfinal : dweight (dmargin final P) = 1 by rewrite dmargin_dweight.
have HQfinal : dweight (dmargin final Q) = 1 by rewrite dmargin_dweight.
have Hpin := pinsker (dmargin final P) (dmargin final Q)
  (dmargin_absolute_continuous final P Q Hac)
  HPfinal HQfinal.
apply: (le_trans Hpin).
rewrite /pythagorean_tv_bound /tuple_sum.
apply: ler_wsqrtr.
have Hdata := kl_dmargin_data_processing final P Q Hac.
have Hchain := iterated_kl_chain_bound P Q eps Heps Hac HP HQ Hcond.
have Hkl := le_trans Hdata Hchain.
lra.
Qed.

End PythagoreanDistributionJudgments.
