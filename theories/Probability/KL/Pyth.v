(* Distribution facts for Pythagorean errors. *)

Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals realsum exp distr.
From mathcomp Require Import lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From Mending.Probability.KL Require Import Core Pinsker ChainPointwise.
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
  dweight P = 1 ->
  dweight Q = 1 ->
  (forall (i : 'I_n) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a)) ->
  (forall (i : 'I_n) (a : i.-tuple A),
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <=
      tnth eps i) ->
  total_variation P Q <= Num.sqrt ((\sum_(i < n) tnth eps i) / 2).
Proof.
move=> Heps HP HQ Hfin Hcond.
have Hcond_all : forall (i : 'I_n) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a) /\
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <=
      tnth eps i.
  by move=> i a; split; [exact: Hfin | exact: Hcond].
have Hac : absolute_continuous P Q.
  exact: (coordinate_finite_kl_absolute_continuous P Q HP HQ Hfin).
have HfinPQ : finite_kl P Q.
  exact: (coordinate_bounded_kl_finite_kl P Q eps
    Heps HP HQ Hcond_all).
have Hpin := pinsker P Q HfinPQ HP HQ.
apply: (le_trans Hpin).
apply: ler_wsqrtr.
have Hkl :
    δ_KL P Q <= \sum_(i < n) tnth eps i :=
  iterated_kl_chain_bound_via_pointwise
    P Q eps Heps HP HQ HfinPQ Hfin Hcond.
lra.
Qed.

Corollary pythagorean_probability_preservation_sup_pinsker
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : R) :
  0 <= eps ->
  dweight P = 1 ->
  dweight Q = 1 ->
  (forall (i : 'I_n) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a)) ->
  (forall (i : 'I_n) (a : i.-tuple A),
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <= eps) ->
  total_variation P Q <= Num.sqrt ((n%:R * eps) / 2).
Proof.
move=> Heps HP HQ Hfin Hcond.
pose eps_tuple : n.-tuple R := [tuple eps | i < n].
have Heps_tuple : forall i : 'I_n, 0 <= tnth eps_tuple i.
  by move=> i; rewrite /eps_tuple tnth_mktuple.
have Hcond_tuple : forall (i : 'I_n) (a : i.-tuple A),
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <=
      tnth eps_tuple i.
  by move=> i a; rewrite /eps_tuple tnth_mktuple; apply: Hcond.
have Htv :=
  pythagorean_probability_preservation P Q eps_tuple
    Heps_tuple HP HQ Hfin Hcond_tuple.
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
  dweight P = 1 /\
  dweight Q = 1 /\
  (forall (i : 'I_n) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a) /\
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <=
      tnth eps i).

Lemma pythDist_absolute_continuous
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R) :
  pythDist P Q eps -> absolute_continuous P Q.
Proof.
move=> [Heps [HP [HQ Hcond]]].
exact: (finite_kl_absolute_continuous P Q
  (coordinate_bounded_kl_finite_kl P Q eps Heps HP HQ Hcond)).
Qed.

Lemma pythDist_cond_finite_kl
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R) :
  pythDist P Q eps ->
  forall (i : 'I_n) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a).
Proof.
move=> [_ [_ [_ Hcond]]] i a.
by have [Hfin _] := Hcond i a.
Qed.

Lemma pythDist_cond_bound
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R) :
  pythDist P Q eps ->
  forall (i : 'I_n) (a : i.-tuple A),
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <=
      tnth eps i.
Proof.
move=> [_ [_ [_ Hcond]]] i a.
by have [_ Hle] := Hcond i a.
Qed.

Lemma pythDist_finite_kl
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R) :
  pythDist P Q eps -> finite_kl P Q.
Proof.
move=> [Heps [HP [HQ Hcond]]].
exact: (coordinate_bounded_kl_finite_kl P Q eps Heps HP HQ Hcond).
Qed.

Lemma pythDist_refl
  {n : nat} {A : choiceType}
  (P : {distr (n.-tuple A) / R}) (eps : n.-tuple R) :
  (forall i : 'I_n, 0 <= tnth eps i) ->
  dweight P = 1 ->
  pythDist P P eps.
Proof.
move=> Heps HP.
split; first exact: Heps.
split; first exact: HP.
split; first exact: HP.
move=> i a.
split.
  exact: finite_kl_refl.
rewrite kl_self.
exact: Heps i.
Qed.

Definition singleton_pyth_trace {A : choiceType} (x : A) : 1.-tuple A :=
  [tuple x].

Lemma dmargin_singleton_pyth_trace
    {A : choiceType} (D : {distr A / R}) (x : A) :
  dmargin (@singleton_pyth_trace A) D (singleton_pyth_trace x) = D x.
Proof.
rewrite dmargin_psumE.
rewrite (realsum.psum_finseq (r := [:: x])).
- by rewrite big_seq1 eqxx mul1r ger0_norm ?ge0_mu.
- by [].
move=> y.
rewrite !inE.
case Hyx: (y == x); first by rewrite (eqP Hyx).
case Hsing : (singleton_pyth_trace y == singleton_pyth_trace x).
- move/eqP: Hsing=> Hsing.
  have Hy_eq : y = x.
    move: (congr1 (fun t => tnth t ord0) Hsing).
    by rewrite /singleton_pyth_trace !tnth0.
  by rewrite Hy_eq eqxx in Hyx.
by rewrite /= mul0r eqxx.
Qed.

Lemma dmargin_singleton_pyth_trace_final
    {A : choiceType} (D : {distr A / R}) :
  dmargin (fun omega : 1.-tuple A => tnth omega ord0)
    (dmargin (@singleton_pyth_trace A) D) =1 D.
Proof.
move=> x.
rewrite dmargin_psumE.
rewrite (realsum.psum_finseq (r := [:: singleton_pyth_trace x])).
- rewrite big_seq1 /singleton_pyth_trace tnth0 eqxx mul1r.
  by rewrite dmargin_singleton_pyth_trace ger0_norm ?ge0_mu.
- by [].
move=> omega.
rewrite !inE.
case Homega : (omega == singleton_pyth_trace x); first by rewrite (eqP Homega).
have Htnth : tnth omega ord0 != x.
  apply/negP=> /eqP Hx.
  have Homega_eq : omega = singleton_pyth_trace x.
    apply: eq_from_tnth=> j.
    by rewrite [j]ord1 /singleton_pyth_trace tnth0 Hx.
  by rewrite Homega_eq eqxx in Homega.
move/negbTE: Htnth=> Htnth0.
by rewrite Htnth0 mul0r eqxx.
Qed.

Lemma pythDist_kl_singleton
    {A : choiceType} (P Q : {distr A / R}) (eps : R) :
  0 <= eps ->
  finite_kl P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  δ_KL P Q <= eps ->
  pythDist
    (dmargin (@singleton_pyth_trace A) P)
    (dmargin (@singleton_pyth_trace A) Q)
    [tuple eps].
Proof.
move=> Heps Hfin HP HQ Hkl.
pose lift := @singleton_pyth_trace A.
have Hcond (D : {distr A / R}) (HD : dweight D = 1) x :
    forall a : 0.-tuple A,
    @conditional_coordinate R 1 A (dmargin lift D) ord0 a x = D x.
  move=> a.
  rewrite /conditional_coordinate dmargin_psumE.
  rewrite (realsum.psum_finseq (r := [:: lift x])).
  - rewrite big_seq1.
    have Htrue (omega : 1.-tuple A) :
        @tuple_prefix_eq 1 A ord0 a omega.
      by rewrite /tuple_prefix_eq; apply/forallP=> j; case: j.
    have Hdcond :
        dcond (dmargin lift D)
          (fun omega => @tuple_prefix_eq 1 A ord0 a omega)
          (lift x) = dmargin lift D (lift x).
      rewrite dcondE /prc.
      have -> : \P_[dmargin lift D]
          (fun omega => (omega == lift x) &&
            (@tuple_prefix_eq 1 A ord0 a omega)) =
        \P_[dmargin lift D] (pred1 (lift x)).
        apply: eq_pr=> omega.
        rewrite /tuple_prefix_eq.
        change (((omega == lift x) &&
          [forall j : 'I_0,
            tnth omega (widen_ord (ltnW (ltn_ord ord0)) j) ==
              tnth a j]) = (omega == lift x)).
        have -> : [forall j : 'I_0,
            tnth omega (widen_ord (ltnW (ltn_ord ord0)) j) ==
              tnth a j] = true.
          by apply/forallP=> j; case: j.
        by rewrite andbT.
      have -> : \P_[dmargin lift D]
          (fun omega => @tuple_prefix_eq 1 A ord0 a omega) =
        \P_[dmargin lift D] predT.
        apply: eq_pr=> omega.
        by rewrite /tuple_prefix_eq; apply/forallP=> j; case: j.
      by rewrite -pr_pred1 dmargin_dweight HD divr1.
    rewrite Hdcond /lift /singleton_pyth_trace tnth0 eqxx mul1r.
    by rewrite dmargin_singleton_pyth_trace ger0_norm ?ge0_mu.
  - by [].
  move=> omega.
  rewrite !inE.
  case Homega : (omega == lift x); first by rewrite (eqP Homega).
  have Htnth : tnth omega ord0 != x.
    apply/negP=> /eqP Hx.
    have Homega_eq : omega = lift x.
      apply: eq_from_tnth=> j.
      by rewrite [j]ord1 /lift /singleton_pyth_trace tnth0 Hx.
    by rewrite Homega_eq eqxx in Homega.
  move/negbTE: Htnth=> Htnth0.
  by rewrite Htnth0 mul0r eqxx.
split.
- by move=> i; rewrite [i]ord1.
split.
  by rewrite dmargin_dweight.
split.
  by rewrite dmargin_dweight.
move=> i.
rewrite [i]ord1.
move=> a.
split.
- apply: (finite_kl_ext P
    (conditional_coordinate (dmargin lift P) a) Q
    (conditional_coordinate (dmargin lift Q) a)).
  + move=> z; symmetry; exact: (Hcond P HP z a).
  + move=> z; symmetry; exact: (Hcond Q HQ z a).
  + exact: Hfin.
- rewrite tnth0.
  rewrite (kl_ext (conditional_coordinate (dmargin lift P) a) P
    (conditional_coordinate (dmargin lift Q) a) Q).
  + exact: Hkl.
  + move=> z; exact: (Hcond P HP z a).
  + move=> z; exact: (Hcond Q HQ z a).
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
move=> Hdist.
case: Hdist=> Heps [HP [HQ Hcond_all]].
have Hfin : forall (i : 'I_n) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a).
  by move=> i a; have [Hfin _] := Hcond_all i a.
have Hcond : forall (i : 'I_n) (a : i.-tuple A),
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <=
      tnth eps i.
  by move=> i a; have [_ Hle] := Hcond_all i a.
exact: (pythagorean_probability_preservation P Q eps
          Heps HP HQ Hfin Hcond).
Qed.

Lemma pythDist_final_total_variation
    {n : nat} {A : choiceType}
    (P Q : {distr (n.+1.-tuple A) / R}) (eps : n.+1.-tuple R) :
  pythDist P Q eps ->
  total_variation (dmargin (fun omega => tnth omega ord_max) P)
    (dmargin (fun omega => tnth omega ord_max) Q) <=
    pythagorean_tv_bound eps.
Proof.
move=> Hdist.
case: Hdist=> Heps [HP [HQ Hcond_all]].
have Hfin : forall (i : 'I_n.+1) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a).
  by move=> i a; have [Hfin _] := Hcond_all i a.
have Hcond : forall (i : 'I_n.+1) (a : i.-tuple A),
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <=
      tnth eps i.
  by move=> i a; have [_ Hle] := Hcond_all i a.
pose final := fun omega : n.+1.-tuple A => tnth omega ord_max.
have HfinPQ : finite_kl P Q.
  exact: (coordinate_bounded_kl_finite_kl P Q eps Heps HP HQ Hcond_all).
have Hpin := pinsker P Q HfinPQ HP HQ.
apply: (le_trans (total_variation_dmargin_le final P Q)).
apply: (le_trans Hpin).
rewrite /pythagorean_tv_bound /tuple_sum.
apply: ler_wsqrtr.
have Hchain := iterated_kl_chain_bound_via_pointwise
  P Q eps Heps HP HQ HfinPQ Hfin Hcond.
lra.
Qed.

End PythagoreanDistributionJudgments.
