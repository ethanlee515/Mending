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

Lemma coordinate_finite_kl_absolute_continuous
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) :
  dweight P = 1 ->
  dweight Q = 1 ->
  (forall (i : 'I_n) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a)) ->
  absolute_continuous P Q.
Admitted.

Lemma norm_le_of_ge0_le (x y : R) :
  0 <= x -> x <= y -> `|x| <= y.
Proof.
move=> Hx Hxy.
have -> : `|x| = x by rewrite ger0_norm.
exact: Hxy.
Qed.

Lemma fposD_le (x y : R) :
  fpos (fun _ : unit => x + y) tt <=
  fpos (fun _ : unit => x) tt + fpos (fun _ : unit => y) tt.
Proof.
rewrite /fpos /= !ger0_norm ?le_max ?lexx //.
rewrite ge_max.
apply/andP; split; first by rewrite addr_ge0 ?le_max ?lexx.
have Hx : x <= Num.max 0 x by rewrite le_max lexx orbT.
have Hy : y <= Num.max 0 y by rewrite le_max lexx orbT.
exact: (le_trans (lerD Hx Hy) (lexx _)).
Qed.

Lemma fpos_sum_le {I : finType} (F : I -> R) :
  fpos (fun _ : unit => \sum_i F i) tt <=
  \sum_i fpos (fun _ : unit => F i) tt.
Proof.
elim: (index_enum I)=> [|i s IH].
  by rewrite !big_nil /fpos /= max_l ?normr0.
rewrite !big_cons.
apply: (le_trans (fposD_le (F i) (\sum_(j <- s) F j))).
exact: lerD.
Qed.

Lemma psum_fpos_le_fpos_sum_plus_fneg {T : choiceType} (F : T -> R) :
  summable F ->
  psum (fpos F) <=
  `|fpos (fun _ : unit => sum F) tt| + psum (fneg F).
Proof.
move=> Hsumm.
rewrite /sum.
set p := psum (fpos F).
set q := psum (fneg F).
have Hp : 0 <= p by exact: ge0_psum.
have Hq : 0 <= q by exact: ge0_psum.
rewrite /fpos /=.
case Hle : (p - q <= 0).
  rewrite max_l // !normr0 add0r.
  have Hle' : p - q <= 0 by rewrite Hle.
  have -> : p = p - q + q by rewrite subrK.
  rewrite -[leRHS]add0r.
  apply: lerD; first exact: Hle'.
  exact: lexx.
have Hgt : 0 < p - q by rewrite ltNge Hle.
rewrite max_r; last exact: ltW Hgt.
have Hnorm : `|p - q| = p - q by rewrite ger0_norm ?ltW.
rewrite Hnorm Hnorm.
by rewrite subrK.
Qed.

Lemma scaled_kl_integrand_fneg_psum_le
    {T : choiceType} (P Q : {distr T / R}) (c : R) :
  0 <= c ->
  absolute_continuous P Q ->
  psum (fneg (fun x => c * (P x * ln (P x / Q x)))) <= c.
Proof.
move=> Hc Hac.
rewrite (eq_psum (F2 := fun x => c * fneg
  (fun x => P x * ln (P x / Q x)) x)); last first.
  move=> x.
  have := fnegZ (fun x => P x * ln (P x / Q x)) Hc x.
  by rewrite /=.
rewrite psumZ //.
rewrite -[leRHS]mulr1.
apply: ler_wpM2l; first exact: Hc.
apply: (le_trans _ (le1_mu Q)).
apply: le_psum; last exact: summable_mu.
move=> x; apply/andP; split; first exact: ge0_fneg.
rewrite /fneg.
exact: (kl_integrand_fneg_le_q (P x) (Q x)
  (ge0_mu P x) (ge0_mu Q x) (Hac x)).
Qed.

Lemma scaled_kl_integrand_fpos_psum_le
    {T : choiceType} (P Q : {distr T / R}) (c : R) :
  0 <= c ->
  finite_kl P Q ->
  psum (fpos (fun x => c * (P x * ln (P x / Q x)))) <=
  `|fpos (fun _ : unit => c * δ_KL P Q) tt| + c.
Proof.
move=> Hc [Hac Hsumm].
pose S := fun x => P x * ln (P x / Q x).
have Hsumm_c : summable (fun x => c * S x).
  apply: (eq_summable (S1 := c \*o S)).
    by move=> x.
  exact: summableZ.
apply: (le_trans (psum_fpos_le_fpos_sum_plus_fneg
  (fun x => c * S x) Hsumm_c)).
apply: lerD.
- have Hsum_scaled :
    sum (fun x => c * S x) = c * δ_KL P Q.
  rewrite (eq_sum (F2 := c \*o S)); last by move=> x.
  rewrite sumZ /S /δ_KL /esp.
  congr (c * _).
  apply/eq_sum=> x.
  by rewrite mulrC.
  by rewrite Hsum_scaled.
- exact: (scaled_kl_integrand_fneg_psum_le P Q c Hc Hac).
Qed.

Lemma fpos_mul_le_of_le (p r l : R) :
  0 <= p -> p <= r ->
  fpos (fun _ : unit => p * l) tt <=
  fpos (fun _ : unit => r * l) tt.
Proof.
move=> Hp Hpr.
have Hr : 0 <= r := le_trans Hp Hpr.
rewrite /fpos /=.
case Hl : (l <= 0).
  have Hle0 : l <= 0 by rewrite Hl.
  have Hple0 : p * l <= 0 := mulr_ge0_le0 Hp Hle0.
  have Hrle0 : r * l <= 0 := mulr_ge0_le0 Hr Hle0.
  by rewrite (max_l Hple0) (max_l Hrle0) !normr0.
have Hlt : 0 < l by rewrite ltNge Hl.
have Hl_ge0 : 0 <= l := ltW Hlt.
have Hpge0 : 0 <= p * l by rewrite mulr_ge0.
have Hrge0 : 0 <= r * l by rewrite mulr_ge0.
rewrite (max_r Hpge0) (max_r Hrge0) !ger0_norm //.
apply: ler_wpM2r; first exact: ltW Hlt.
exact: Hpr.
Qed.

Lemma finite_sum_fpos_scaled_le {T : choiceType}
    (J : seq T) (p : pred T) (F : T -> R) (r l : R) :
  (forall x, 0 <= F x) ->
  \sum_(x <- J | p x) F x <= r ->
  \sum_(x <- J | p x) `|fpos (fun _ : unit => F x * l) tt| <=
  `|fpos (fun _ : unit => r * l) tt|.
Proof.
move=> HF Hsum.
have Hsum_ge0 : 0 <= \sum_(x <- J | p x) F x.
  by apply: sumr_ge0=> x _; exact: HF.
have Hr : 0 <= r := le_trans Hsum_ge0 Hsum.
rewrite /fpos /=.
case Hl : (l <= 0).
  have Hle0 : l <= 0 by rewrite Hl.
  have Hrle0 : r * l <= 0 := mulr_ge0_le0 Hr Hle0.
  rewrite (max_l Hrle0) normr0.
  rewrite big1 // => x _.
  have Hxle0 : F x * l <= 0 := mulr_ge0_le0 (HF x) Hle0.
  by rewrite (max_l Hxle0) !normr0.
have Hlt : 0 < l by rewrite ltNge Hl.
have Hlge0 : 0 <= l := ltW Hlt.
have Hrge0 : 0 <= r * l := mulr_ge0 Hr Hlge0.
rewrite (max_r Hrge0) !ger0_norm ?mulr_ge0 //.
rewrite (eq_bigr (fun x => F x * l)); last first.
  move=> x _.
  have Hxge0 : 0 <= F x * l := mulr_ge0 (HF x) Hlge0.
  by rewrite (max_r Hxge0) !ger0_norm.
rewrite -big_distrl.
exact: ler_wpM2r.
Qed.

Lemma finite_sum_partition_by_image {T U : choiceType}
    (J : seq T) (f : T -> U) (p : pred T) (G : T -> R) :
  (forall x, 0 <= G x) ->
  \sum_(x <- J | p x) G x <=
  \sum_(y <- undup [seq f x | x <- J])
    \sum_(x <- J | p x && (f x == y)) G x.
Proof.
move=> HG.
rewrite [leLHS]big_mkcond.
rewrite [leLHS]big_seq_cond.
rewrite [leRHS](eq_bigr (fun y =>
  \sum_(x <- J) (if p x && (f x == y) then G x else 0))); last first.
  by move=> y _; rewrite big_mkcond.
rewrite [leRHS]exchange_big.
rewrite [leRHS]big_seq_cond.
apply: ler_sum=> x /andP[HxJ _].
case Hpx : (p x); last first.
  apply: sumr_ge0=> y _.
  exact: lexx.
pose y0 := f x.
have Hy0 : y0 \in undup [seq f x0 | x0 <- J].
  rewrite mem_undup.
  apply/mapP; exists x=> //.
have Hu : uniq (undup [seq f x0 | x0 <- J]) by rewrite undup_uniq.
rewrite (bigD1_seq y0 Hy0 Hu) /= /y0 eqxx.
rewrite lerDl.
apply: sumr_ge0=> y _.
case: (f x == y); first exact: (HG x).
exact: lexx.
Qed.

Definition coordinate_log_contribution
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R})
    (x : n.-tuple A) (i : 'I_n) : R :=
  ln (conditional_coordinate P (tuple_prefix i (tnth x)) (tnth x i) /
      conditional_coordinate Q (tuple_prefix i (tnth x)) (tnth x i)).

Lemma kl_integrand_chain_decomp_pointwise
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) :
  absolute_continuous P Q ->
  forall x : n.-tuple A,
    P x * ln (P x / Q x) =
    \sum_(i < n) P x * coordinate_log_contribution P Q x i.
Admitted.

Lemma finite_sum_coordinate_log_contribution_partition_prefix
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R})
    (i : 'I_n) (J : seq (n.-tuple A)) :
  uniq J ->
  \sum_(x <- J)
    `|fpos
      (fun x => P x * coordinate_log_contribution P Q x i) x| <=
  \sum_(a <- undup [seq tuple_prefix i (tnth x) | x <- J])
    \sum_(x <- J | tuple_prefix_eq a x)
      `|fpos
        (fun x => P x * coordinate_log_contribution P Q x i) x|.
Proof.
move=> Huniq.
rewrite [leLHS]big_mkcond.
rewrite [leLHS]big_seq_cond.
rewrite [leRHS](eq_bigr (fun a =>
    \sum_(x <- J)
      (if tuple_prefix_eq a x then
        `|fpos
          (fun x => P x * coordinate_log_contribution P Q x i) x|
       else 0))); last first.
  by move=> a _; rewrite big_mkcond.
rewrite [leRHS]exchange_big.
rewrite [leRHS]big_seq_cond.
apply: ler_sum=> x /andP[HxJ _].
set t := `|fpos _ _|.
pose a0 := tuple_prefix i (tnth x).
have Ha0 : a0 \in undup [seq tuple_prefix i (tnth x) | x <- J].
  rewrite mem_undup.
  apply/mapP; exists x=> //.
have Hu : uniq (undup [seq tuple_prefix i (tnth x) | x <- J]) by rewrite undup_uniq.
have Hprefix : tuple_prefix_eq a0 x.
  apply/forallP=> j.
  rewrite /a0 /tuple_prefix_eq /tuple_prefix tnth_mktuple.
  by rewrite eqxx.
rewrite (bigD1_seq a0 Ha0 Hu) /= Hprefix.
rewrite -/t.
rewrite lerDl.
apply: sumr_ge0=> a _.
case: (tuple_prefix_eq a x); first exact: normr_ge0.
exact: lexx.
Qed.

Lemma coordinate_log_contribution_prefix
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R})
    (i : 'I_n) (a : i.-tuple A) (x : n.-tuple A) :
  tuple_prefix_eq a x ->
  coordinate_log_contribution P Q x i =
  ln (conditional_coordinate P a (tnth x i) /
      conditional_coordinate Q a (tnth x i)).
Proof.
move=> Hprefix.
have Ha : tuple_prefix i (tnth x) = a.
  apply: eq_from_tnth=> j.
  rewrite /tuple_prefix tnth_mktuple.
  by move/forallP: Hprefix=> /(_ j) /eqP.
by rewrite /coordinate_log_contribution Ha.
Qed.

Lemma point_mass_le_prefix_coordinate_mass
    {n : nat} {A : choiceType}
    (P : {distr (n.-tuple A) / R})
    (i : 'I_n) (a : i.-tuple A) (x : n.-tuple A) :
  tuple_prefix_eq a x ->
  P x <=
  \P_[P] (fun y => tuple_prefix_eq a y) *
  conditional_coordinate P a (tnth x i).
Admitted.

Lemma finite_sum_coordinate_log_contribution_partition_coordinate
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R})
    (i : 'I_n) (J : seq (n.-tuple A)) (a : i.-tuple A) :
  uniq J ->
  \sum_(x <- J | tuple_prefix_eq a x)
    `|fpos
      (fun x => P x * coordinate_log_contribution P Q x i) x| <=
  \sum_(b <- undup [seq tnth x i | x <- J])
    \sum_(x <- J | tuple_prefix_eq a x && (tnth x i == b))
      `|fpos
        (fun x => P x * coordinate_log_contribution P Q x i) x|.
Proof.
move=> _.
exact: (finite_sum_partition_by_image
  J (fun x => tnth x i) (fun x => tuple_prefix_eq a x)
  (fun x => `|fpos
    (fun x => P x * coordinate_log_contribution P Q x i) x|)
  (fun x => normr_ge0 _)).
Qed.

Lemma finite_sum_selected_prefix_coordinate_mass_le
    {n : nat} {A : choiceType}
    (P : {distr (n.-tuple A) / R})
    (i : 'I_n) (J : seq (n.-tuple A)) (a : i.-tuple A) (b : A) :
  \sum_(x <- J | tuple_prefix_eq a x && (tnth x i == b)) P x <=
  \P_[P] (fun x => tuple_prefix_eq a x) *
  conditional_coordinate P a b.
Admitted.

Lemma finite_sum_prefix_coordinate_fiber_log_bound
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R})
    (i : 'I_n) (J : seq (n.-tuple A)) (a : i.-tuple A) (b : A) :
  \sum_(x <- J | tuple_prefix_eq a x && (tnth x i == b))
    `|fpos
      (fun x => P x * coordinate_log_contribution P Q x i) x| <=
  `|fpos
    (fun b : A =>
      \P_[P] (fun x => tuple_prefix_eq a x) *
      (conditional_coordinate P a b *
       ln (conditional_coordinate P a b /
           conditional_coordinate Q a b))) b|.
Admitted.

Lemma finite_sum_coordinate_log_contribution_prefix_coordinate_group_bound
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R})
    (i : 'I_n) (J : seq (n.-tuple A)) (a : i.-tuple A) :
  uniq J ->
  \sum_(x <- J | tuple_prefix_eq a x)
    `|fpos
      (fun x => P x * coordinate_log_contribution P Q x i) x| <=
  \sum_(b <- undup [seq tnth x i | x <- J])
    `|fpos
      (fun b : A =>
        \P_[P] (fun x => tuple_prefix_eq a x) *
        (conditional_coordinate P a b *
         ln (conditional_coordinate P a b /
             conditional_coordinate Q a b))) b|.
Proof.
move=> Huniq.
apply: (le_trans
  (finite_sum_coordinate_log_contribution_partition_coordinate P Q i J a Huniq)).
apply: ler_sum=> b _.
exact: finite_sum_prefix_coordinate_fiber_log_bound.
Qed.

Lemma finite_sum_coordinate_log_contribution_prefix_bound
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R})
    (i : 'I_n) (J : seq (n.-tuple A)) (a : i.-tuple A) :
  uniq J ->
  finite_kl (conditional_coordinate P a) (conditional_coordinate Q a) ->
  \sum_(x <- J | tuple_prefix_eq a x)
    `|fpos
      (fun x => P x * coordinate_log_contribution P Q x i) x| <=
  psum (fpos
    (fun b : A =>
      \P_[P] (fun x => tuple_prefix_eq a x) *
      (conditional_coordinate P a b *
       ln (conditional_coordinate P a b /
           conditional_coordinate Q a b)))).
Proof.
move=> Huniq Hfin.
apply: (le_trans
  (finite_sum_coordinate_log_contribution_prefix_coordinate_group_bound
    P Q i J a Huniq)).
apply: gerfinseq_psum; first exact: undup_uniq.
apply: summable_fpos.
pose S := fun b : A =>
  conditional_coordinate P a b *
  ln (conditional_coordinate P a b / conditional_coordinate Q a b).
apply: (eq_summable (S1 :=
  \P_[P] (fun x => tuple_prefix_eq a x) \*o S)).
  by move=> b.
exact: (@summableZ R A S
  (\P_[P] (fun x => tuple_prefix_eq a x))
  (finite_kl_summable _ _ Hfin)).
Qed.

Lemma finite_sum_coordinate_log_contribution_group_bound
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R})
    (i : 'I_n) (J : seq (n.-tuple A)) :
  (forall a : i.-tuple A,
    finite_kl (conditional_coordinate P a) (conditional_coordinate Q a)) ->
  uniq J ->
  \sum_(x <- J)
    `|fpos
      (fun x => P x * coordinate_log_contribution P Q x i) x| <=
  \sum_(a <- undup [seq tuple_prefix i (tnth x) | x <- J])
    psum (fpos
      (fun b : A =>
        \P_[P] (fun x => tuple_prefix_eq a x) *
        (conditional_coordinate P a b *
         ln (conditional_coordinate P a b /
             conditional_coordinate Q a b)))).
Proof.
move=> Hfin Huniq.
apply: (le_trans
  (finite_sum_coordinate_log_contribution_partition_prefix P Q i J Huniq)).
apply: ler_sum=> a _.
exact: (finite_sum_coordinate_log_contribution_prefix_bound P Q i J a Huniq (Hfin a)).
Qed.

Lemma prefix_coordinate_scaled_fpos_psum_bound
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R})
    (i : 'I_n) (a : i.-tuple A) :
  finite_kl
    (conditional_coordinate P a)
    (conditional_coordinate Q a) ->
  psum (fpos
    (fun b : A =>
      \P_[P] (fun x => tuple_prefix_eq a x) *
      (conditional_coordinate P a b *
       ln (conditional_coordinate P a b /
           conditional_coordinate Q a b)))) <=
  `|fpos
    (fun a =>
      \P_[P] (fun x => tuple_prefix_eq a x) *
      δ_KL (conditional_coordinate P a)
           (conditional_coordinate Q a)) a| +
  \P_[P] (fun x => tuple_prefix_eq a x).
Proof.
move=> Hfin.
exact: (scaled_kl_integrand_fpos_psum_le
  (conditional_coordinate P a)
  (conditional_coordinate Q a)
  (\P_[P] (fun x => tuple_prefix_eq a x))
  (ge0_pr _ _) Hfin).
Qed.

Lemma finite_sum_selected_prefix_mass_le1
    {n : nat} {A : choiceType}
    (P : {distr (n.-tuple A) / R})
    (i : 'I_n) (J : seq (n.-tuple A)) :
  \sum_(a <- undup [seq tuple_prefix i (tnth x) | x <- J])
    \P_[P] (fun x => tuple_prefix_eq a x) <= 1.
Proof.
have Hprefix (a : i.-tuple A) (x : n.-tuple A) :
    (tuple_prefix i (tnth x) == a) = tuple_prefix_eq a x.
  apply/eqP/forallP=> [H j|H].
    rewrite -H /tuple_prefix tnth_mktuple.
    by [].
  apply: eq_from_tnth=> j.
  rewrite /tuple_prefix tnth_mktuple.
  by move: (H j)=> /eqP.
have Hdmargin (a : i.-tuple A) :
    dmargin (fun x : n.-tuple A => tuple_prefix i (tnth x)) P a =
    \P_[P] (fun x => tuple_prefix_eq a x).
  rewrite dmargin_psumE /pr.
  apply: eq_psum=> x.
  by rewrite Hprefix.
rewrite (eq_bigr (fun a =>
  dmargin (fun x : n.-tuple A => tuple_prefix i (tnth x)) P a)); last first.
  by move=> a _; rewrite Hdmargin.
rewrite (eq_bigr (fun a =>
  `|dmargin (fun x : n.-tuple A => tuple_prefix i (tnth x)) P a|));
  last by move=> a _; rewrite ger0_norm ?ge0_mu.
have Hpsum :
    \sum_(a <- undup [seq tuple_prefix i (tnth x) | x <- J])
      `|dmargin (fun x : n.-tuple A => tuple_prefix i (tnth x)) P a| <=
    psum (fun a : i.-tuple A =>
      dmargin (fun x : n.-tuple A => tuple_prefix i (tnth x)) P a).
  apply: gerfinseq_psum.
  - exact: undup_uniq.
  - exact: summable_mu.
exact: (le_trans Hpsum (le1_mu _)).
Qed.

(* Single-coordinate finite-positive bound.

   This is the remaining fiber argument: group the finite set first by prefix
   [a] and current coordinate [b], compare its mass to
   [Pr_P(prefix=a) * conditional_coordinate P a b], then use the negative-part
   KL bound to pay at most one unit of prefix mass across the selected prefixes.
 *)
Lemma finite_sum_fpos_coordinate_log_contribution_bound
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R})
    (i : 'I_n) (J : seq (n.-tuple A)) :
  dweight P = 1 ->
  dweight Q = 1 ->
  absolute_continuous P Q ->
  (forall a : i.-tuple A,
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a)) ->
  uniq J ->
  \sum_(x <- J)
    `|fpos
      (fun x => P x * coordinate_log_contribution P Q x i) x| <=
  (\sum_(a <- undup [seq tuple_prefix i (tnth x) | x <- J])
      `|fpos
        (fun a =>
          \P_[P] (fun x => tuple_prefix_eq a x) *
          δ_KL (conditional_coordinate P a)
               (conditional_coordinate Q a)) a|) +
  1.
Proof.
move=> HP HQ Hac Hfin Huniq.
apply: (le_trans
  (finite_sum_coordinate_log_contribution_group_bound P Q i J Hfin Huniq)).
apply: (le_trans _ _).
  apply: ler_sum=> a _.
  exact: (prefix_coordinate_scaled_fpos_psum_bound P Q i a (Hfin a)).
rewrite big_split /=.
apply: lerD; first exact: lexx.
exact: finite_sum_selected_prefix_mass_le1.
Qed.

Lemma finite_sum_fpos_kl_chain_terms_from_pointwise
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) :
  (forall x : n.-tuple A,
    P x * ln (P x / Q x) =
    \sum_(i < n) P x * coordinate_log_contribution P Q x i) ->
  forall J : seq (n.-tuple A),
    \sum_(x <- J)
      `|fpos (fun x => P x * ln (P x / Q x)) x| <=
    \sum_(i < n)
      \sum_(x <- J)
        `|fpos
          (fun x => P x * coordinate_log_contribution P Q x i) x|.
Proof.
move=> Hpoint J.
rewrite exchange_big.
apply: ler_sum=> x _.
rewrite ger0_norm ?ge0_fpos.
rewrite (eq_bigr (fun i =>
  fpos (fun x => P x * coordinate_log_contribution P Q x i) x));
  last by move=> i _; rewrite ger0_norm ?ge0_fpos.
rewrite /fpos Hpoint /=.
change (fpos (fun _ : unit =>
          \sum_(i < n) P x * coordinate_log_contribution P Q x i) tt <=
        \sum_(i < n)
          fpos
            (fun _ : unit =>
              P x * coordinate_log_contribution P Q x i) tt).
exact: fpos_sum_le.
by [].
Qed.

Lemma finite_sum_fpos_kl_chain_decomp_from_pointwise
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) :
  dweight P = 1 ->
  dweight Q = 1 ->
  absolute_continuous P Q ->
  (forall (i : 'I_n) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a)) ->
  (forall x : n.-tuple A,
    P x * ln (P x / Q x) =
    \sum_(i < n) P x * coordinate_log_contribution P Q x i) ->
  forall J : seq (n.-tuple A),
    uniq J ->
    \sum_(x <- J)
      `|fpos (fun x => P x * ln (P x / Q x)) x| <=
    \sum_(i < n)
      ((\sum_(a <- undup [seq tuple_prefix i (tnth x) | x <- J])
          `|fpos
            (fun a =>
              \P_[P] (fun x => tuple_prefix_eq a x) *
              δ_KL (conditional_coordinate P a)
                   (conditional_coordinate Q a)) a|) +
       1).
Proof.
move=> HP HQ Hac Hfin Hpoint J Huniq.
apply: (le_trans (finite_sum_fpos_kl_chain_terms_from_pointwise P Q Hpoint J)).
apply: ler_sum=> i _.
exact: (finite_sum_fpos_coordinate_log_contribution_bound
  P Q i J HP HQ Hac (fun a => Hfin i a) Huniq).
Qed.

Lemma iterated_kl_chain_bound_from_pointwise
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R) :
  (forall i : 'I_n, 0 <= tnth eps i) ->
  dweight P = 1 ->
  dweight Q = 1 ->
  absolute_continuous P Q ->
  (forall x : n.-tuple A,
    P x * ln (P x / Q x) =
    \sum_(i < n) P x * coordinate_log_contribution P Q x i) ->
  (forall (i : 'I_n) (a : i.-tuple A),
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <= tnth eps i) ->
  δ_KL P Q <= \sum_(i < n) tnth eps i.
Admitted.

Lemma iterated_kl_chain_bound_via_pointwise
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R) :
  (forall i : 'I_n, 0 <= tnth eps i) ->
  dweight P = 1 ->
  dweight Q = 1 ->
  absolute_continuous P Q ->
  (forall (i : 'I_n) (a : i.-tuple A),
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <= tnth eps i) ->
  δ_KL P Q <= \sum_(i < n) tnth eps i.
Proof.
move=> Heps HP HQ Hac Hcond.
apply: (iterated_kl_chain_bound_from_pointwise P Q eps
  Heps HP HQ Hac _ Hcond).
exact: (kl_integrand_chain_decomp_pointwise P Q Hac).
Qed.

Lemma finite_sum_fpos_kl_chain_decomp
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) :
  dweight P = 1 ->
  dweight Q = 1 ->
  absolute_continuous P Q ->
  (forall (i : 'I_n) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a)) ->
  forall J : seq (n.-tuple A),
    uniq J ->
    \sum_(x <- J)
      `|fpos (fun x => P x * ln (P x / Q x)) x| <=
    \sum_(i < n)
      ((\sum_(a <- undup [seq tuple_prefix i (tnth x) | x <- J])
          `|fpos
            (fun a =>
              \P_[P] (fun x => tuple_prefix_eq a x) *
              δ_KL (conditional_coordinate P a)
                   (conditional_coordinate Q a)) a|) +
       1).
Proof.
move=> HP HQ Hac Hfin J Huniq.
apply: (finite_sum_fpos_kl_chain_decomp_from_pointwise P Q HP HQ Hac Hfin).
  exact: (kl_integrand_chain_decomp_pointwise P Q Hac).
exact: Huniq.
Qed.

Lemma tuple_prefix_eq_prefix
    {n : nat} {A : choiceType}
    (i : 'I_n) (a : i.-tuple A) (x : n.-tuple A) :
  (tuple_prefix i (tnth x) == a) = tuple_prefix_eq a x.
Proof.
apply/eqP/forallP=> [H j|H].
  rewrite -H /tuple_prefix tnth_mktuple.
  by [].
apply: eq_from_tnth=> j.
rewrite /tuple_prefix tnth_mktuple.
by move: (H j)=> /eqP.
Qed.

Lemma dmargin_tuple_prefixE
    {n : nat} {A : choiceType}
    (P : {distr (n.-tuple A) / R})
    (i : 'I_n) (a : i.-tuple A) :
  dmargin (fun x : n.-tuple A => tuple_prefix i (tnth x)) P a =
  \P_[P] (fun x => tuple_prefix_eq a x).
Proof.
rewrite dmargin_psumE /pr.
apply: eq_psum=> x.
by rewrite tuple_prefix_eq_prefix.
Qed.

Lemma finite_sum_prefix_event_mass_le1
    {n : nat} {A : choiceType}
    (P : {distr (n.-tuple A) / R})
    (i : 'I_n) (J : seq (i.-tuple A)) :
  uniq J ->
  \sum_(a <- J) \P_[P] (fun x => tuple_prefix_eq a x) <= 1.
Proof.
move=> Huniq.
rewrite (eq_bigr (fun a =>
  dmargin (fun x : n.-tuple A => tuple_prefix i (tnth x)) P a)); last first.
  by move=> a _; rewrite dmargin_tuple_prefixE.
rewrite (eq_bigr (fun a =>
  `|dmargin (fun x : n.-tuple A => tuple_prefix i (tnth x)) P a|));
  last by move=> a _; rewrite ger0_norm ?ge0_mu.
have Hpsum :
    \sum_(a <- J)
      `|dmargin (fun x : n.-tuple A => tuple_prefix i (tnth x)) P a| <=
    psum (fun a : i.-tuple A =>
      dmargin (fun x : n.-tuple A => tuple_prefix i (tnth x)) P a).
  apply: gerfinseq_psum.
  - exact: Huniq.
  - exact: summable_mu.
exact: (le_trans Hpsum (le1_mu _)).
Qed.

Lemma prefix_coordinate_kl_contribution_bound
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R)
    (i : 'I_n) (J : seq (n.-tuple A)) :
  0 <= tnth eps i ->
  (forall a : i.-tuple A,
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a) /\
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <=
      tnth eps i) ->
  \sum_(a <- undup [seq tuple_prefix i (tnth x) | x <- J])
    `|fpos
      (fun a =>
        \P_[P] (fun x => tuple_prefix_eq a x) *
        δ_KL (conditional_coordinate P a)
             (conditional_coordinate Q a)) a| <=
  tnth eps i.
Proof.
move=> Heps_i Hcond.
pose pref_mass (a : i.-tuple A) :=
  \P_[P] (fun x => tuple_prefix_eq a x).
pose klc (a : i.-tuple A) :=
  δ_KL (conditional_coordinate P a) (conditional_coordinate Q a).
have Hpoint a :
    `|fpos (fun a => pref_mass a * klc a) a| <=
    tnth eps i * pref_mass a.
  rewrite /fpos.
  case Hle0: (pref_mass a * klc a <= 0).
    rewrite max_l // normr0.
    have Hprod : 0 <= tnth eps i * pref_mass a.
      apply: mulr_ge0; first exact: Heps_i.
      exact: ge0_pr.
    by rewrite normr0.
  have Hgt0 : 0 < pref_mass a * klc a.
    by rewrite ltNge Hle0.
  have Hge0 : 0 <= pref_mass a * klc a := ltW Hgt0.
  rewrite max_r; last by [].
  set e :=
    \P_[P] (fun x => tuple_prefix_eq a x) *
    δ_KL (conditional_coordinate P a) (conditional_coordinate Q a).
  have Hge0e : 0 <= e.
    rewrite /e.
    exact: Hge0.
  rewrite normr_id.
  apply: (norm_le_of_ge0_le e (tnth eps i * pref_mass a));
    first exact: Hge0e.
  rewrite /e [tnth eps i * _]mulrC.
  apply: ler_wpM2l; first exact: ge0_pr.
  by have [_ Hle] := Hcond a.
have Hsumpoint :
    \sum_(a <- undup [seq tuple_prefix i (tnth x) | x <- J])
      `|fpos
        (fun a =>
          \P_[P] (fun x => tuple_prefix_eq a x) *
          δ_KL (conditional_coordinate P a)
               (conditional_coordinate Q a)) a| <=
    \sum_(a <- undup [seq tuple_prefix i (tnth x) | x <- J])
      tnth eps i * pref_mass a.
  apply: ler_sum=> a _.
  exact: Hpoint.
apply: (le_trans Hsumpoint).
rewrite -mulr_sumr.
apply: (le_trans (ler_wpM2l Heps_i
  (finite_sum_prefix_event_mass_le1 P i
    (undup [seq tuple_prefix i (tnth x) | x <- J]) (undup_uniq _)))).
by rewrite mulr1.
Qed.

Lemma finite_sum_fpos_kl_from_coordinate_bounded_kl
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R) :
  (forall i : 'I_n, 0 <= tnth eps i) ->
  dweight P = 1 ->
  dweight Q = 1 ->
  (forall (i : 'I_n) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a) /\
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <=
      tnth eps i) ->
  forall J : seq (n.-tuple A),
    uniq J ->
    \sum_(x <- J)
      `|fpos (fun x => P x * ln (P x / Q x)) x| <=
    (\sum_(i < n) tnth eps i) + n%:R.
Proof.
move=> Heps HP HQ Hcond J Huniq.
have Hfin : forall (i : 'I_n) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a).
  by move=> i a; have [Hfin _] := Hcond i a.
have Hac : absolute_continuous P Q.
  exact: (coordinate_finite_kl_absolute_continuous P Q HP HQ Hfin).
apply: (le_trans (finite_sum_fpos_kl_chain_decomp
  P Q HP HQ Hac Hfin J Huniq)).
rewrite big_split /=.
apply: lerD.
- apply: ler_sum=> i _.
  exact: (prefix_coordinate_kl_contribution_bound
    P Q eps i J (Heps i) (fun a => Hcond i a)).
- by rewrite big_const_ord iter_addr_0.
Qed.

Lemma summable_fpos_kl_from_coordinate_bounded_kl
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R) :
  (forall i : 'I_n, 0 <= tnth eps i) ->
  dweight P = 1 ->
  dweight Q = 1 ->
  (forall (i : 'I_n) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a) /\
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <=
      tnth eps i) ->
  summable (fpos (fun x => P x * ln (P x / Q x))).
Proof.
move=> Heps HP HQ Hcond.
apply/summable_seqP.
exists ((\sum_(i < n) tnth eps i) + n%:R).
  have Hsum_nonneg : 0 <= \sum_(i < n) tnth eps i.
    by apply: sumr_ge0=> i _; exact: Heps.
  have Hn_nonneg : 0 <= n%:R :> R by exact: ler0n.
  lra.
move=> J Huniq.
exact: (finite_sum_fpos_kl_from_coordinate_bounded_kl
  P Q eps Heps HP HQ Hcond J Huniq).
Qed.

Lemma summable_kl_from_coordinate_bounded_kl
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R) :
  (forall i : 'I_n, 0 <= tnth eps i) ->
  dweight P = 1 ->
  dweight Q = 1 ->
  (forall (i : 'I_n) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a) /\
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <=
      tnth eps i) ->
  summable (fun x => P x * ln (P x / Q x)).
Proof.
move=> Heps HP HQ Hcond.
have Hfin : forall (i : 'I_n) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a).
  by move=> i a; have [Hfin _] := Hcond i a.
have Hac : absolute_continuous P Q.
  exact: (coordinate_finite_kl_absolute_continuous P Q HP HQ Hfin).
apply: summable_from_fpos_fneg.
- exact: (summable_fpos_kl_from_coordinate_bounded_kl
    P Q eps Heps HP HQ Hcond).
- exact: (summable_fneg_kl_integrand P Q Hac).
Qed.

Lemma coordinate_bounded_kl_finite_kl
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R) :
  (forall i : 'I_n, 0 <= tnth eps i) ->
  dweight P = 1 ->
  dweight Q = 1 ->
  (forall (i : 'I_n) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a) /\
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <=
      tnth eps i) ->
  finite_kl P Q.
Proof.
move=> Heps HP HQ Hcond.
have Hfin : forall (i : 'I_n) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a).
  by move=> i a; have [Hfin _] := Hcond i a.
split.
- exact: (coordinate_finite_kl_absolute_continuous P Q HP HQ Hfin).
- exact: (summable_kl_from_coordinate_bounded_kl
    P Q eps Heps HP HQ Hcond).
Qed.

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
  iterated_kl_chain_bound P Q eps Heps Hac HP HQ Hcond.
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
move=> [_ [HP [HQ Hcond]]].
have Hfin : forall (i : 'I_n) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a).
  by move=> i a; have [Hfin _] := Hcond i a.
exact: (coordinate_finite_kl_absolute_continuous P Q HP HQ Hfin).
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
have Hac := pythDist_absolute_continuous P Q eps Hdist.
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
have HPfinal : dweight (dmargin final P) = 1 by rewrite dmargin_dweight.
have HQfinal : dweight (dmargin final Q) = 1 by rewrite dmargin_dweight.
have HfinPQ : finite_kl P Q.
  exact: (coordinate_bounded_kl_finite_kl P Q eps Heps HP HQ Hcond_all).
have Hfinfinal : finite_kl (dmargin final P) (dmargin final Q).
  exact: (finite_kl_dmargin final P Q HfinPQ).
have Hpin := pinsker (dmargin final P) (dmargin final Q)
  Hfinfinal HPfinal HQfinal.
apply: (le_trans Hpin).
rewrite /pythagorean_tv_bound /tuple_sum.
apply: ler_wsqrtr.
have Hdata := kl_dmargin_data_processing final P Q Hac.
have Hchain := iterated_kl_chain_bound P Q eps Heps Hac HP HQ Hcond.
have Hkl := le_trans Hdata Hchain.
lra.
Qed.

End PythagoreanDistributionJudgments.
