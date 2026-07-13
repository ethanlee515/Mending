(* Distribution facts for Pythagorean errors. *)

Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals realsum exp distr.
From mathcomp Require Import lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From Mending.Probability.KL Require Import Core Pinsker ChainPointwise.
From Mending.Probability Require Import ConditionalCoordinate DletTuple.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras TupleExtras.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

Section PythagoreanDistributionJudgments.

Context {R : realType}.

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

Lemma pythDist_kl_bound
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R) :
  pythDist P Q eps ->
  δ_KL P Q <= \sum_(i < n) tnth eps i.
Proof.
move=> [Heps [HP [HQ Hcond_all]]].
have HfinPQ : finite_kl P Q.
  exact: (coordinate_bounded_kl_finite_kl P Q eps Heps HP HQ Hcond_all).
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
exact: (iterated_kl_chain_bound_via_pointwise
  P Q eps Heps HP HQ HfinPQ Hfin Hcond).
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

Lemma pythDist_ext
  {n : nat} {A : choiceType}
  (P P' Q Q' : {distr (n.-tuple A) / R}) (eps : n.-tuple R) :
  P =1 P' ->
  Q =1 Q' ->
  pythDist P Q eps ->
  pythDist P' Q' eps.
Proof.
move=> HP HQ [Heps [HPmass [HQmass Hcond]]].
split; first exact: Heps.
split.
- rewrite (pr_ext P' P predT); first exact: HPmass.
  by move=> x; symmetry; exact: HP.
split.
- rewrite (pr_ext Q' Q predT); first exact: HQmass.
  by move=> x; symmetry; exact: HQ.
move=> i a.
have HcondP :=
  conditional_coordinate_dist_ext P P' i a HP.
have HcondQ :=
  conditional_coordinate_dist_ext Q Q' i a HQ.
have [Hfin Hkl] := Hcond i a.
split.
- exact: (finite_kl_ext _ _ _ _ HcondP HcondQ Hfin).
rewrite -(kl_ext
  (conditional_coordinate P a)
  (conditional_coordinate P' a)
  (conditional_coordinate Q a)
  (conditional_coordinate Q' a) HcondP HcondQ).
exact: Hkl.
Qed.

Lemma pythDist_dlet_cat_const
  {ℓ1 ℓ2 : nat}
  {A : choiceType}
  (P0 Q0 : {distr ((ℓ1.+1).-tuple A) / R})
  (P1 Q1 : {distr ((ℓ2.+1).-tuple A) / R})
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R) :
  pythDist P0 Q0 s1 ->
  pythDist P1 Q1 s2 ->
  pythDist
    (\dlet_(omega0 <- P0)
     \dlet_(omega1 <- P1)
       dunit (cat_tuple omega0 omega1))
    (\dlet_(omega0 <- Q0)
     \dlet_(omega1 <- Q1)
       dunit (cat_tuple omega0 omega1))
    (cat_tuple s1 s2).
Proof.
move=> Hdist0 Hdist1.
move: Hdist0=> [Hs1 [HP0 [HQ0 Hcond0]]].
move: Hdist1=> [Hs2 [HP1 [HQ1 Hcond1]]].
have Hdist0 : pythDist P0 Q0 s1.
  by split; first exact: Hs1; split; first exact: HP0;
     split; first exact: HQ0.
have Hdist1 : pythDist P1 Q1 s2.
  by split; first exact: Hs2; split; first exact: HP1;
     split; first exact: HQ1.
pose P :=
  \dlet_(omega0 <- P0)
  \dlet_(omega1 <- P1)
    dunit (cat_tuple omega0 omega1).
pose Q :=
  \dlet_(omega0 <- Q0)
  \dlet_(omega1 <- Q1)
    dunit (cat_tuple omega0 omega1).
change (pythDist P Q (cat_tuple s1 s2)).
split.
- move=> i.
  apply: (cat_tuple_nonneg s1 s2 i).
  + exact: Hs1.
  + exact: Hs2.
split.
- rewrite /P.
  rewrite (pr_dlet_cat_prefix_lift_eq P0 (fun _ => P1)
    predT predT (fun _ => HP1)); last by move=> omega0 omega1.
  exact: HP0.
split.
- rewrite /Q.
  rewrite (pr_dlet_cat_prefix_lift_eq Q0 (fun _ => Q1)
    predT predT (fun _ => HQ1)); last by move=> omega0 omega1.
  exact: HQ0.
move=> i a.
split.
- case: (ltnP i ℓ1.+1)=> Hi.
  + pose i0 : 'I_(ℓ1.+1) := Ordinal Hi.
    have Hfin0 := pythDist_cond_finite_kl P0 Q0 s1 Hdist0 i0 a.
    apply: (finite_kl_ext _ _ _ _ _ _ Hfin0).
    * move=> x; symmetry.
      exact: (conditional_coordinate_dlet_cat_prefix_eq
        P0 (fun _ => P1) i a Hi (fun _ => HP1) x).
    * move=> x; symmetry.
      exact: (conditional_coordinate_dlet_cat_prefix_eq
        Q0 (fun _ => Q1) i a Hi (fun _ => HQ1) x).
  have Hzero_fin :
      P0 (catTuplePrefix i Hi a) = 0 ->
      finite_kl (conditional_coordinate P a)
        (conditional_coordinate Q a).
    move=> HP0z.
    apply: finite_kl_left_dnull.
    exact: (conditional_coordinate_dlet_cat_suffix_zero_prefix
      P0 (fun _ => P1) i a Hi HP0z).
  have Hac0 := pythDist_absolute_continuous P0 Q0 s1 Hdist0.
  case HP0z: (P0 (catTuplePrefix i Hi a) == 0).
    exact: Hzero_fin (eqP HP0z).
  have HP0pos : 0 < P0 (catTuplePrefix i Hi a).
    by rewrite lt_def ge0_mu HP0z.
  have HQ0pos : 0 < Q0 (catTuplePrefix i Hi a).
    exact: (absolute_continuous_positive P0 Q0 _ Hac0 HP0pos).
  have Hfin1 := pythDist_cond_finite_kl P1 Q1 s2 Hdist1
    (catTupleSuffixIndex i Hi) (catTupleSuffixAssignment i Hi a).
  apply: (finite_kl_ext _ _ _ _ _ _ Hfin1).
  + move=> x; symmetry.
    exact: (conditional_coordinate_dlet_cat_suffix_eq
      P0 (fun _ => P1) i a Hi
      (catTuplePrefix i Hi a) erefl HP0pos x).
  + move=> x; symmetry.
    exact: (conditional_coordinate_dlet_cat_suffix_eq
      Q0 (fun _ => Q1) i a Hi
      (catTuplePrefix i Hi a) erefl HQ0pos x).
case: (ltnP i ℓ1.+1)=> Hi.
  pose i0 : 'I_(ℓ1.+1) := Ordinal Hi.
  rewrite (kl_ext
    (conditional_coordinate P a)
    (@conditional_coordinate _ _ _ P0 i0 a)
    (conditional_coordinate Q a)
    (@conditional_coordinate _ _ _ Q0 i0 a)).
  - rewrite (cat_tuple_tnth_prefix s1 s2 i Hi).
    exact: (pythDist_cond_bound P0 Q0 s1 Hdist0 i0 a).
  - exact: (conditional_coordinate_dlet_cat_prefix_eq
      P0 (fun _ => P1) i a Hi (fun _ => HP1)).
  - exact: (conditional_coordinate_dlet_cat_prefix_eq
      Q0 (fun _ => Q1) i a Hi (fun _ => HQ1)).
have Hac0 := pythDist_absolute_continuous P0 Q0 s1 Hdist0.
case HP0z: (P0 (catTuplePrefix i Hi a) == 0).
  rewrite (kl_left_dnull (conditional_coordinate P a)
    (conditional_coordinate Q a)).
  - rewrite (cat_tuple_tnth_suffix s1 s2 i Hi).
    exact: Hs2.
  exact: (conditional_coordinate_dlet_cat_suffix_zero_prefix
    P0 (fun _ => P1) i a Hi (eqP HP0z)).
have HP0pos : 0 < P0 (catTuplePrefix i Hi a).
  by rewrite lt_def ge0_mu HP0z.
have HQ0pos : 0 < Q0 (catTuplePrefix i Hi a).
  exact: (absolute_continuous_positive P0 Q0 _ Hac0 HP0pos).
rewrite (kl_ext
  (conditional_coordinate P a)
  (conditional_coordinate P1 (catTupleSuffixAssignment i Hi a))
  (conditional_coordinate Q a)
  (conditional_coordinate Q1 (catTupleSuffixAssignment i Hi a))).
- rewrite (cat_tuple_tnth_suffix s1 s2 i Hi).
  exact: (pythDist_cond_bound P1 Q1 s2 Hdist1
    (catTupleSuffixIndex i Hi) (catTupleSuffixAssignment i Hi a)).
- exact: (conditional_coordinate_dlet_cat_suffix_eq
    P0 (fun _ => P1) i a Hi
    (catTuplePrefix i Hi a) erefl HP0pos).
- exact: (conditional_coordinate_dlet_cat_suffix_eq
    Q0 (fun _ => Q1) i a Hi
    (catTuplePrefix i Hi a) erefl HQ0pos).
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

Definition pythCallErrorBlock {ℓ : nat} (s : (ℓ.+1).-tuple R) :=
  cat_tuple [tuple 0] s.

Definition pythCallErrorBase {ℓ : nat} (s : (ℓ.+1).-tuple R) :=
  cat_tuple (pythCallErrorBlock s) [tuple 0].

Definition pythCallErrorStep {ℓ1 ℓ2 : nat}
    (s : (ℓ1.+1).-tuple R) (tail : (ℓ2.+1).-tuple R) :=
  cat_tuple (pythCallErrorBlock s) tail.

Definition pythCallContErrorBase {ℓ : nat} (s : (ℓ.+1).-tuple R) :=
  cat_tuple s [tuple 0].

Definition pythCallContErrorStep {ℓ1 ℓ2 : nat}
    (s : (ℓ1.+1).-tuple R) (tail : (ℓ2.+1).-tuple R) :=
  cat_tuple s tail.

Definition pythErrorTuple := {ℓ : nat & (ℓ.+1).-tuple R}.

Definition packPythErrorTuple {ℓ : nat}
    (s : (ℓ.+1).-tuple R) : pythErrorTuple :=
  existT _ ℓ s.

Definition pythErrorTupleIndex (e : pythErrorTuple) : nat :=
  projT1 e.

Definition pythErrorTupleTuple (e : pythErrorTuple) :
    (pythErrorTupleIndex e).+1.-tuple R :=
  projT2 e.

Definition pythErrorTupleSum (e : pythErrorTuple) : R :=
  tuple_sum (pythErrorTupleTuple e).

Definition pythErrorTupleNonneg (e : pythErrorTuple) : Prop :=
  forall i, 0 <= tnth (pythErrorTupleTuple e) i.

Definition pythErrorTupleTvBound (e : pythErrorTuple) : R :=
  pythagorean_tv_bound (pythErrorTupleTuple e).

Fixpoint pythCallErrorsTuple {ℓ : nat}
    (q : nat) (s : (ℓ.+1).-tuple R) : pythErrorTuple :=
  match q with
  | 0 => packPythErrorTuple (pythCallErrorBase s)
  | q'.+1 =>
      packPythErrorTuple
        (pythCallErrorStep s
          (pythErrorTupleTuple (pythCallErrorsTuple q' s)))
  end.

Lemma pythCallErrorBlock_nonneg {ℓ : nat}
    (s : (ℓ.+1).-tuple R) :
  (forall i : 'I_(ℓ.+1), 0 <= tnth s i) ->
  forall i, 0 <= tnth (pythCallErrorBlock s) i.
Proof.
move=> Hs i.
apply: (cat_tuple_nonneg [tuple 0] s i).
- by move=> j; rewrite [j]ord1.
- exact: Hs.
Qed.

Lemma pythCallErrorBase_nonneg {ℓ : nat}
    (s : (ℓ.+1).-tuple R) :
  (forall i : 'I_(ℓ.+1), 0 <= tnth s i) ->
  forall i, 0 <= tnth (pythCallErrorBase s) i.
Proof.
move=> Hs i.
apply: (cat_tuple_nonneg (pythCallErrorBlock s) [tuple 0] i).
- exact: pythCallErrorBlock_nonneg.
- by move=> j; rewrite [j]ord1.
Qed.

Lemma pythCallErrorStep_nonneg {ℓ1 ℓ2 : nat}
    (s : (ℓ1.+1).-tuple R) (tail : (ℓ2.+1).-tuple R) :
  (forall i : 'I_(ℓ1.+1), 0 <= tnth s i) ->
  (forall i : 'I_(ℓ2.+1), 0 <= tnth tail i) ->
  forall i, 0 <= tnth (pythCallErrorStep s tail) i.
Proof.
move=> Hs Htail i.
apply: (cat_tuple_nonneg (pythCallErrorBlock s) tail i).
- exact: pythCallErrorBlock_nonneg.
- exact: Htail.
Qed.

Lemma pythCallContErrorBase_nonneg {ℓ : nat}
    (s : (ℓ.+1).-tuple R) :
  (forall i : 'I_(ℓ.+1), 0 <= tnth s i) ->
  forall i, 0 <= tnth (pythCallContErrorBase s) i.
Proof.
move=> Hs i.
apply: (cat_tuple_nonneg s [tuple 0] i).
- exact: Hs.
- by move=> j; rewrite [j]ord1.
Qed.

Lemma pythCallContErrorStep_nonneg {ℓ1 ℓ2 : nat}
    (s : (ℓ1.+1).-tuple R) (tail : (ℓ2.+1).-tuple R) :
  (forall i : 'I_(ℓ1.+1), 0 <= tnth s i) ->
  (forall i : 'I_(ℓ2.+1), 0 <= tnth tail i) ->
  forall i, 0 <= tnth (pythCallContErrorStep s tail) i.
Proof.
move=> Hs Htail i.
apply: (cat_tuple_nonneg s tail i).
- exact: Hs.
- exact: Htail.
Qed.

Lemma tuple_sum_pythCallErrorBlock {ℓ : nat}
    (s : (ℓ.+1).-tuple R) :
  tuple_sum (pythCallErrorBlock s) = tuple_sum s.
Proof.
by rewrite /pythCallErrorBlock tuple_sum_cat tuple_sum_singleton add0r.
Qed.

Lemma tuple_sum_pythCallErrorBase {ℓ : nat}
    (s : (ℓ.+1).-tuple R) :
  tuple_sum (pythCallErrorBase s) = tuple_sum s.
Proof.
rewrite /pythCallErrorBase tuple_sum_cat tuple_sum_pythCallErrorBlock.
by rewrite tuple_sum_singleton addr0.
Qed.

Lemma tuple_sum_pythCallErrorStep {ℓ1 ℓ2 : nat}
    (s : (ℓ1.+1).-tuple R) (tail : (ℓ2.+1).-tuple R) :
  tuple_sum (pythCallErrorStep s tail) =
  tuple_sum s + tuple_sum tail.
Proof.
by rewrite /pythCallErrorStep tuple_sum_cat tuple_sum_pythCallErrorBlock.
Qed.

Lemma pythCallErrorBaseE {ℓ : nat}
    (s : (ℓ.+1).-tuple R) :
  pythCallErrorBase s = cat_tuple [tuple 0] (pythCallContErrorBase s).
Proof.
by apply: val_inj.
Qed.

Lemma pythCallErrorStepE {ℓ1 ℓ2 : nat}
    (s : (ℓ1.+1).-tuple R) (tail : (ℓ2.+1).-tuple R) :
  pythCallErrorStep s tail =
  cat_tuple [tuple 0] (pythCallContErrorStep s tail).
Proof.
by apply: val_inj.
Qed.

Lemma pythCallErrorsTuple_nonneg {ℓ : nat}
    (q : nat) (s : (ℓ.+1).-tuple R) :
  (forall i : 'I_(ℓ.+1), 0 <= tnth s i) ->
  pythErrorTupleNonneg (pythCallErrorsTuple q s).
Proof.
move=> Hs.
elim: q=> [|q IH] /=.
- exact: pythCallErrorBase_nonneg.
- exact: (pythCallErrorStep_nonneg s
    (pythErrorTupleTuple (pythCallErrorsTuple q s)) Hs IH).
Qed.

Lemma tuple_sum_pythCallErrorsTuple {ℓ : nat}
    (q : nat) (s : (ℓ.+1).-tuple R) :
  pythErrorTupleSum (pythCallErrorsTuple q s) = q.+1%:R * tuple_sum s.
Proof.
elim: q=> [|q IH] /=.
- by rewrite /pythErrorTupleSum /= tuple_sum_pythCallErrorBase mul1r.
- rewrite /pythErrorTupleSum /= tuple_sum_pythCallErrorStep.
  change
    (tuple_sum s + pythErrorTupleSum (pythCallErrorsTuple q s) =
      q.+2%:R * tuple_sum s).
  by rewrite IH -[q.+2%:R]natr1 mulrDl mul1r addrC.
Qed.

Lemma pythagorean_tv_bound_pythCallErrorsTuple {ℓ : nat}
    (q : nat) (s : (ℓ.+1).-tuple R) :
  pythErrorTupleTvBound (pythCallErrorsTuple q s) =
  Num.sqrt ((q.+1%:R * tuple_sum s) / 2).
Proof.
rewrite /pythErrorTupleTvBound /pythagorean_tv_bound.
change
  (Num.sqrt (pythErrorTupleSum (pythCallErrorsTuple q s) / 2) =
   Num.sqrt ((q.+1%:R * tuple_sum s) / 2)).
by rewrite tuple_sum_pythCallErrorsTuple.
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
