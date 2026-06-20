(* Pointwise coordinate-chain facts for KL over tuples. *)

Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals realsum exp distr.
From mathcomp Require Import lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From mathcomp.algebra_tactics Require Import ring.

From Mending.Probability.KL Require Import Core.
From Mending.Probability Require Import ConditionalCoordinate.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras TupleExtras.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

Section KL_ChainPointwise.

Context {R : realType}.

Lemma tuple_prefix_ord_max_last_eq
    {n : nat} {A : choiceType} (x y : n.+1.-tuple A) :
  tuple_prefix_eq (tuple_prefix ord_max (tnth x)) y &&
    (tnth y ord_max == tnth x ord_max) =
  (y == x).
Proof.
apply/idP/eqP=> [/andP[Hprefix Hlast]|->].
- apply: eq_from_tnth=> j.
  case Hj : (j < n)%N.
    have Hpref := forallP Hprefix (Ordinal Hj).
    rewrite /tuple_prefix tnth_mktuple in Hpref.
    have Hw :
        widen_ord (ltnW (ltn_ord ord_max)) (Ordinal Hj) = j
      by apply: val_inj.
    by move: Hpref; rewrite Hw=> /eqP.
  have Hjlast : j = ord_max.
    apply: val_inj.
    have Hjle : (j <= n)%N by rewrite -ltnS.
    by move: Hjle; rewrite leq_eqVlt Hj orbF=> /eqP.
  by rewrite Hjlast; exact/eqP.
- rewrite eqxx andbT.
  apply/forallP=> j.
  by rewrite /tuple_prefix tnth_mktuple.
Qed.

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

Lemma sum_le_of_psum_fpos_le_add_fneg {T : choiceType}
    (F : T -> R) (c : R) :
  psum (fpos F) <= c + psum (fneg F) ->
  sum F <= c.
Proof.
move=> Hle.
rewrite /sum.
lra.
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

Lemma sum_scaled_kl_integrand
    {T : choiceType} (P Q : {distr T / R}) (c : R) :
  finite_kl P Q ->
  sum (fun x => c * (P x * ln (P x / Q x))) =
  c * δ_KL P Q.
Proof.
move=> Hfin.
pose S := fun x : T => P x * ln (P x / Q x).
rewrite (eq_sum (F2 := c \*o S)); last by move=> x.
rewrite sumZ /S /δ_KL /esp.
congr (c * _).
apply/eq_sum=> x.
by rewrite mulrC.
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

Lemma finite_sum_fneg_scaled_le {T : choiceType}
    (J : seq T) (p : pred T) (F : T -> R) (r l : R) :
  (forall x, 0 <= F x) ->
  \sum_(x <- J | p x) F x <= r ->
  \sum_(x <- J | p x) `|fneg (fun _ : unit => F x * l) tt| <=
  `|fneg (fun _ : unit => r * l) tt|.
Proof.
move=> HF Hsum.
have Hsum_ge0 : 0 <= \sum_(x <- J | p x) F x.
  by apply: sumr_ge0=> x _; exact: HF.
have Hr : 0 <= r := le_trans Hsum_ge0 Hsum.
rewrite /fneg /=.
case Hl : (0 <= l).
  have Hlge0 : 0 <= l by rewrite Hl.
  have Hrge0 : 0 <= r * l := mulr_ge0 Hr Hlge0.
  rewrite (min_l Hrge0) normr0.
  rewrite big1 // => x _.
  have Hxge0 : 0 <= F x * l := mulr_ge0 (HF x) Hlge0.
  by rewrite (min_l Hxge0) !normr0.
have Hlt : l < 0 by rewrite ltNge Hl.
have Hle0 : l <= 0 := ltW Hlt.
have Hrle0 : r * l <= 0 := mulr_ge0_le0 Hr Hle0.
rewrite (min_r Hrle0).
rewrite ger0_norm ?normr_ge0.
rewrite ler0_norm //.
rewrite (eq_bigr (fun x => `|F x * l|)); last first.
  move=> x _.
  have Hxle0 : F x * l <= 0 := mulr_ge0_le0 (HF x) Hle0.
  by rewrite (min_r Hxle0) ger0_norm ?normr_ge0.
rewrite (eq_bigr (fun x => F x * (- l))); last first.
  move=> x _.
  have Hxle0 : F x * l <= 0 := mulr_ge0_le0 (HF x) Hle0.
  by rewrite ler0_norm // -mulrN.
rewrite -big_distrl.
have Hnl : 0 <= - l by lra.
apply: (le_trans (ler_wpM2r Hnl Hsum)).
by rewrite mulrN.
by [].
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
  dweight P = 1 ->
  dweight Q = 1 ->
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

Lemma prefix_coordinate_pr_factor
    {n : nat} {A : choiceType}
    (P : {distr (n.-tuple A) / R})
    (i : 'I_n) (a : i.-tuple A) (b : A) :
  \P_[P] (fun x => tuple_prefix_eq a x && (tnth x i == b)) =
  \P_[P] (fun x => tuple_prefix_eq a x) *
  conditional_coordinate P a b.
Proof.
case Hpref0 : (\P_[P] (fun x => tuple_prefix_eq a x) == 0).
  move/eqP: Hpref0=> Hpref0.
  rewrite Hpref0 mul0r.
  rewrite /pr.
  apply/psum_eq0=> x.
  case Hev : (tuple_prefix_eq a x && (tnth x i == b)).
    have Hprefix : x \in [eta tuple_prefix_eq a].
      by move/andP: Hev=> [].
    have Hpx0 : P x = 0 := pr_eq0 Hpref0 Hprefix.
    by rewrite mul1r Hpx0.
  by rewrite mul0r.
rewrite /conditional_coordinate.
rewrite (pr_pred1
  (dmargin (fun omega : n.-tuple A => tnth omega i)
    (dcond P (fun omega : n.-tuple A => tuple_prefix_eq a omega))) b).
rewrite pr_dmargin pr_dcond /prc.
set p0 := \P_[P] [eta tuple_prefix_eq a].
set q0 := \P_[P]
  [predI [pred x0 | tnth x0 i \in pred1 b] & [eta tuple_prefix_eq a]].
have Hp0nz : p0 != 0 by rewrite /p0 Hpref0.
rewrite mulrC -mulrA mulVr ?mulr1 ?unitfE //.
rewrite /pr.
apply/eq_psum=> x.
rewrite !inE -!topredE /=.
case: (tuple_prefix_eq a x); case: (tnth x i == b);
  rewrite ?mul0r ?mul1r //.
Qed.

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
Proof.
case: n P Q=> [|n] P Q HP HQ Hfin x HQx0.
- have Hpred1 : pred1 x =1 predT.
    move=> y.
    by rewrite /pred1 (tuple0 y) (tuple0 x).
  have HQx1 : Q x = 1.
    rewrite pr_pred1 /pr.
    rewrite (eq_psum (F2 := Q)); last by move=> y; rewrite Hpred1 mul1r.
    by rewrite -pr_predT HQ.
  exfalso.
  move: (@oner_eq0 R).
  by rewrite -HQx1 HQx0 eqxx.
- pose i : 'I_n.+1 := ord_max.
  pose a : i.-tuple A := tuple_prefix i (tnth x).
  pose b : A := tnth x i.
  have Hevent (mu : {distr (n.+1.-tuple A) / R}) :
      \P_[mu] (fun y => tuple_prefix_eq a y && (tnth y i == b)) = mu x.
    rewrite pr_pred1 /pr /a /b /i.
    apply: eq_psum=> y.
    by rewrite tuple_prefix_ord_max_last_eq.
  have HcondQ0 : conditional_coordinate Q a b = 0.
    case Hpref0 : (\P_[Q] (fun y => tuple_prefix_eq a y) == 0).
      by rewrite (conditional_coordinate_zero_prefix Q i a (eqP Hpref0)) dnullE.
    have Hprod0 :
        \P_[Q] (fun y => tuple_prefix_eq a y) *
          conditional_coordinate Q a b = 0.
      rewrite -prefix_coordinate_pr_factor Hevent HQx0.
      by [].
    apply/eqP.
    move/eqP: Hprod0.
    rewrite mulf_eq0.
    have -> : \P_[Q] (fun y => tuple_prefix_eq a y) == 0 = false
      by [].
    by rewrite orFb.
  have HcondP0 : conditional_coordinate P a b = 0.
    have [Hac _] := Hfin i a.
    exact: Hac b HcondQ0.
  have HprodP0 :
      \P_[P] (fun y => tuple_prefix_eq a y) *
        conditional_coordinate P a b = 0
    by rewrite HcondP0 mulr0.
  move: HprodP0.
  rewrite -prefix_coordinate_pr_factor Hevent.
  by [].
Qed.

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
  uniq J ->
  \sum_(x <- J | tuple_prefix_eq a x && (tnth x i == b)) P x <=
  \P_[P] (fun x => tuple_prefix_eq a x) *
  conditional_coordinate P a b.
Proof.
move=> Huniq.
set E := fun x : n.-tuple A => tuple_prefix_eq a x && (tnth x i == b).
rewrite -prefix_coordinate_pr_factor /pr -/E.
suff Hpoint :
    \sum_(x <- J | E x) P x <=
    \sum_(x <- J | E x) `| (E x)%:R * P x | by
  apply: (le_trans Hpoint _); rewrite -big_filter;
  exact: (gerfinseq_psum
    (S := fun x => (E x)%:R * P x)
    (r := filter E J) (filter_uniq _ Huniq) (summable_pr E P)).
apply: ler_sum=> x Hx.
move: Hx.
rewrite /E.
case: (tuple_prefix_eq a x && (tnth x i == b))=> //= Hx.
  by rewrite mul1r ger0_norm ?ge0_mu.
Qed.

Lemma finite_sum_prefix_coordinate_fiber_log_bound
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R})
    (i : 'I_n) (J : seq (n.-tuple A)) (a : i.-tuple A) (b : A) :
  uniq J ->
  \sum_(x <- J | tuple_prefix_eq a x && (tnth x i == b))
    `|fpos
      (fun x => P x * coordinate_log_contribution P Q x i) x| <=
  `|fpos
    (fun b : A =>
      \P_[P] (fun x => tuple_prefix_eq a x) *
      (conditional_coordinate P a b *
       ln (conditional_coordinate P a b /
           conditional_coordinate Q a b))) b|.
Proof.
move=> Huniq.
set l := ln (conditional_coordinate P a b / conditional_coordinate Q a b).
set r := \P_[P] (fun x => tuple_prefix_eq a x) *
  conditional_coordinate P a b.
rewrite (eq_bigr (fun x => `|fpos (fun _ : unit => P x * l) tt|));
  last first.
  move=> x /andP[Hprefix /eqP Hb].
  rewrite /fpos /= /l.
  rewrite (coordinate_log_contribution_prefix P Q i a x Hprefix).
  by rewrite Hb.
apply: (le_trans
  (finite_sum_fpos_scaled_le
    J (fun x => tuple_prefix_eq a x && (tnth x i == b))
    (fun x => P x) r l (fun x => ge0_mu P x)
    (finite_sum_selected_prefix_coordinate_mass_le P i J a b Huniq))).
rewrite /r /l.
by rewrite -mulrA.
Qed.

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
exact: (finite_sum_prefix_coordinate_fiber_log_bound P Q i J a b Huniq).
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

Lemma prefix_coordinate_weighted_kl_sum
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R})
    (i : 'I_n) (a : i.-tuple A) :
  finite_kl
    (conditional_coordinate P a)
    (conditional_coordinate Q a) ->
  sum
    (fun b : A =>
      \P_[P] (fun x => tuple_prefix_eq a x) *
      (conditional_coordinate P a b *
       ln (conditional_coordinate P a b /
           conditional_coordinate Q a b))) =
  \P_[P] (fun x => tuple_prefix_eq a x) *
  δ_KL (conditional_coordinate P a)
       (conditional_coordinate Q a).
Proof.
move=> Hfin.
exact: (sum_scaled_kl_integrand
  (conditional_coordinate P a)
  (conditional_coordinate Q a)
  (\P_[P] (fun x => tuple_prefix_eq a x)) Hfin).
Qed.

Lemma conditional_coordinate_kl_nonnegative
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R})
    (i : 'I_n) (a : i.-tuple A) :
  absolute_continuous P Q ->
  0 <= δ_KL (conditional_coordinate P a)
             (conditional_coordinate Q a).
Proof.
move=> Hac.
case Hpref0 : (\P_[P] (fun x => tuple_prefix_eq a x) == 0).
  rewrite (kl_left_dnull (conditional_coordinate P a)
    (conditional_coordinate Q a)).
    exact: lexx.
  exact: (conditional_coordinate_zero_prefix P i a (eqP Hpref0)).
have Hpref_pos : 0 < \P_[P] (fun x => tuple_prefix_eq a x).
  by rewrite lt_def ge0_pr Hpref0.
apply: kl_nonnegative.
  exact: conditional_coordinate_absolute_continuous.
rewrite /conditional_coordinate dmargin_dweight.
exact: dcond_mass1.
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

Lemma summable_finite_ord_sum
    {T : choiceType} {m : nat} (F : 'I_m -> T -> R) :
  (forall i : 'I_m, summable (F i)) ->
  summable (fun x => \sum_(i < m) F i x).
Proof.
move=> Hsumm.
elim: m F Hsumm=> [|m IH] F Hsumm.
  apply: (eq_summable (S1 := fun _ : T => 0)); last exact: summable0.
  by move=> x; rewrite big_ord0.
apply: (eq_summable
  (S1 := fun x : T =>
    F ord0 x + \sum_(i < m) F (lift ord0 i) x)).
  by move=> x; rewrite big_ord_recl.
apply: summableD.
  exact: Hsumm.
apply: IH=> i.
exact: Hsumm.
Qed.

Lemma sum_finite_ord_sum
    {T : choiceType} {m : nat} (F : 'I_m -> T -> R) :
  (forall i : 'I_m, summable (F i)) ->
  sum (fun x => \sum_(i < m) F i x) =
  \sum_(i < m) sum (F i).
Proof.
move=> Hsumm.
elim: m F Hsumm=> [|m IH] F Hsumm.
  rewrite big_ord0.
  rewrite (eq_sum (F2 := fun _ : T => 0)); first exact: sum0.
  by move=> x; rewrite big_ord0.
rewrite big_ord_recl.
rewrite (eq_sum (F2 := fun x : T =>
  F ord0 x + \sum_(i < m) F (lift ord0 i) x)); last first.
  by move=> x; rewrite big_ord_recl.
rewrite sumD.
  congr (_ + _).
  apply: IH=> i.
  exact: Hsumm.
  exact: Hsumm.
apply: summable_finite_ord_sum=> i.
exact: Hsumm.
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
  exact: (kl_integrand_chain_decomp_pointwise P Q HP HQ Hac).
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

Lemma summable_dmargin_comp
    {T U : choiceType} (P : {distr T / R}) (f : T -> U) (h : U -> R) :
  summable (fun x => P x * h (f x)) ->
  summable (fun y => dmargin f P y * h y).
Proof.
move=> Hsumm.
pose F := fun x : T => P x * h (f x).
pose G := fun y : U => dmargin f P y * h y.
have HposF x : fpos F x = P x * fpos h (f x).
  rewrite /F.
  have := fposZ h (ge0_mu P x) (f x).
  by [].
have HnegF x : fneg F x = P x * fneg h (f x).
  rewrite /F.
  have := fnegZ h (ge0_mu P x) (f x).
  by [].
have HposG y : fpos G y = dmargin f P y * fpos h y.
  rewrite /G.
  have := fposZ h (ge0_mu (dmargin f P) y) y.
  by [].
have HnegG y : fneg G y = dmargin f P y * fneg h y.
  rewrite /G.
  have := fnegZ h (ge0_mu (dmargin f P) y) y.
  by [].
have Hpos_summable : summable (fun x : T => P x * fpos h (f x)).
  apply: (eq_summable (S1 := fpos F)); first by move=> x; rewrite HposF.
  exact: summable_fpos.
have Hneg_summable : summable (fun x : T => P x * fneg h (f x)).
  apply: (eq_summable (S1 := fneg F)); first by move=> x; rewrite HnegF.
  exact: summable_fneg.
apply: summable_from_fpos_fneg.
- apply: (eq_summable (S1 := fun y : U =>
    psum (fun x : T => (f x == y)%:R * (P x * fpos h (f x))))).
    move=> y.
    rewrite HposG dmargin_psumE.
    rewrite [psum _ * fpos h y]mulrC -psumZ; last exact: ge0_fpos.
    apply: eq_psum=> x.
    case Hfy : (f x == y).
      have Hfy_bool := Hfy.
      move/eqP: Hfy=> Hfy_eq.
      rewrite /= Hfy_bool Hfy_eq.
      have -> : true%:R = (1 : R) by [].
      ring.
    rewrite /= Hfy.
    have -> : false%:R = (0 : R) by [].
    by rewrite !mul0r !mulr0.
  apply: (summable_fiber_psum f (fun x : T => P x * fpos h (f x))).
  + by move=> x; rewrite mulr_ge0 ?ge0_mu ?ge0_fpos.
  + exact: Hpos_summable.
- apply: (eq_summable (S1 := fun y : U =>
    psum (fun x : T => (f x == y)%:R * (P x * fneg h (f x))))).
    move=> y.
    rewrite HnegG dmargin_psumE.
    rewrite [psum _ * fneg h y]mulrC -psumZ; last exact: ge0_fneg.
    apply: eq_psum=> x.
    case Hfy : (f x == y).
      have Hfy_bool := Hfy.
      move/eqP: Hfy=> Hfy_eq.
      rewrite /= Hfy_bool Hfy_eq.
      have -> : true%:R = (1 : R) by [].
      ring.
    rewrite /= Hfy.
    have -> : false%:R = (0 : R) by [].
    by rewrite !mul0r !mulr0.
  apply: (summable_fiber_psum f (fun x : T => P x * fneg h (f x))).
  + by move=> x; rewrite mulr_ge0 ?ge0_mu ?ge0_fneg.
  + exact: Hneg_summable.
Qed.

Lemma sum_dmargin_comp
    {T U : choiceType} (P : {distr T / R}) (f : T -> U) (h : U -> R) :
  summable (fun x => P x * h (f x)) ->
  sum (fun x => P x * h (f x)) =
  sum (fun y => dmargin f P y * h y).
Proof.
move=> Hsumm.
pose F := fun x : T => P x * h (f x).
pose G := fun y : U => dmargin f P y * h y.
have HposF x : fpos F x = P x * fpos h (f x).
  rewrite /F.
  have := fposZ h (ge0_mu P x) (f x).
  by [].
have HnegF x : fneg F x = P x * fneg h (f x).
  rewrite /F.
  have := fnegZ h (ge0_mu P x) (f x).
  by [].
have HposG y : fpos G y = dmargin f P y * fpos h y.
  rewrite /G.
  have := fposZ h (ge0_mu (dmargin f P) y) y.
  by [].
have HnegG y : fneg G y = dmargin f P y * fneg h y.
  rewrite /G.
  have := fnegZ h (ge0_mu (dmargin f P) y) y.
  by [].
have Hpos_summable : summable (fun x : T => P x * fpos h (f x)).
  apply: (eq_summable (S1 := fpos F)); first by move=> x; rewrite HposF.
  exact: summable_fpos.
have Hneg_summable : summable (fun x : T => P x * fneg h (f x)).
  apply: (eq_summable (S1 := fneg F)); first by move=> x; rewrite HnegF.
  exact: summable_fneg.
rewrite /sum.
rewrite (eq_psum HposF) (eq_psum HnegF).
rewrite (eq_psum HposG) (eq_psum HnegG).
rewrite (partition_psum f Hpos_summable).
rewrite (partition_psum f Hneg_summable).
congr (_ - _).
- apply: eq_psum=> y.
  rewrite dmargin_psumE.
  rewrite [psum _ * fpos h y]mulrC -psumZ; last exact: ge0_fpos.
  apply: eq_psum=> x.
  case Hfy : (f x == y).
    move/eqP: Hfy=> Hfy.
    rewrite Hfy /= !mulr1.
    by rewrite Hfy eqxx mul1r mulrC.
  by rewrite /= Hfy mulr0 mul0r mulr0.
- apply: eq_psum=> y.
  rewrite dmargin_psumE.
  rewrite [psum _ * fneg h y]mulrC -psumZ; last exact: ge0_fneg.
  apply: eq_psum=> x.
  case Hfy : (f x == y).
    move/eqP: Hfy=> Hfy.
    rewrite Hfy /= !mulr1.
    by rewrite Hfy eqxx mul1r mulrC.
	  by rewrite /= Hfy mulr0 mul0r mulr0.
Qed.

Lemma psum_pair_fst_fiber
    {T U : choiceType} (S : T * U -> R) (x : T) :
  (forall xy, 0 <= S xy) ->
  psum (fun xy : T * U => (xy.1 == x)%:R * S xy) =
  psum (fun y : U => S (x, y)).
Proof.
move=> HS.
rewrite (@reindex_psum_onto R (T * U)%type U
  (fun xy : T * U => (xy.1 == x)%:R * S xy)
  [pred xy : T * U | xy.1 == x]
  (fun y : U => (x, y))
  (fun xy : T * U => if xy.1 == x then Some xy.2 else None)).
- apply/eq_psum=> y.
  by rewrite eqxx mul1r.
- move=> xy Hxy.
  case Hxyx : (xy.1 == x); first by [].
  by move: Hxy; rewrite Hxyx mul0r eqxx.
- case=> x' y /= Hx'.
  move: Hx'; rewrite /= => /eqP Hx'.
  change (x' = x) in Hx'.
  by rewrite Hx' eqxx.
- by move=> y _; rewrite eqxx.
Qed.

Lemma summable_pair_fst_rows_nonneg
    {T U : choiceType} (S : T * U -> R) :
  (forall xy, 0 <= S xy) ->
  summable S ->
  summable (fun x : T => psum (fun y : U => S (x, y))).
Proof.
move=> HS Hsumm.
apply: (eq_summable
  (S1 := fun x : T =>
    psum (fun xy : T * U => (xy.1 == x)%:R * S xy))).
  move=> x.
  by rewrite psum_pair_fst_fiber.
exact: (summable_fiber_psum (fun xy : T * U => xy.1) S HS Hsumm).
Qed.

Lemma sum_pair_fst_rows
    {T U : choiceType} (F : T * U -> R) :
  summable F ->
  (forall x : T, summable (fun y : U => F (x, y))) ->
  sum F = sum (fun x : T => sum (fun y : U => F (x, y))).
Proof.
move=> Hsumm Hrow.
pose A := fun x : T => psum (fun y : U => fpos F (x, y)).
pose B := fun x : T => psum (fun y : U => fneg F (x, y)).
have HA : summable A.
  apply: summable_pair_fst_rows_nonneg.
  - move=> xy; exact: ge0_fpos.
  - exact: summable_fpos.
have HB : summable B.
  apply: summable_pair_fst_rows_nonneg.
  - move=> xy; exact: ge0_fneg.
  - exact: summable_fneg.
rewrite (eq_sum (F2 := A \+ (fun x : T => - B x))); last first.
  move=> x.
  by rewrite /A /B /sum.
rewrite (@sumD R T A (fun x : T => - B x) HA (summableN HB)).
rewrite sumN.
have HsumA : sum A = psum A by rewrite -psum_sum // => x; exact: ge0_psum.
have HsumB : sum B = psum B by rewrite -psum_sum // => x; exact: ge0_psum.
rewrite HsumA HsumB.
rewrite -(psum_pair (S := fpos F) (summable_fpos Hsumm)).
rewrite -(psum_pair (S := fneg F) (summable_fneg Hsumm)).
by rewrite /sum.
Qed.

Lemma dmargin_prefix_coordinateE
    {n : nat} {A : choiceType}
    (P : {distr (n.-tuple A) / R})
    (i : 'I_n) (a : i.-tuple A) (b : A) :
  dmargin (fun x : n.-tuple A => (tuple_prefix i (tnth x), tnth x i)) P
    (a, b) =
  \P_[P] (fun x => tuple_prefix_eq a x) *
  conditional_coordinate P a b.
Proof.
rewrite dmargin_psumE -prefix_coordinate_pr_factor /pr.
apply: eq_psum=> x.
case Hprefix : (tuple_prefix_eq a x);
  case Hb : (tnth x i == b).
- have Hpair : (tuple_prefix i (tnth x), tnth x i) == (a, b).
    rewrite xpair_eqE Hb andbT.
    by rewrite tuple_prefix_eq_prefix.
  by rewrite Hpair /= !mul1r.
- have Hpair : ((tuple_prefix i (tnth x), tnth x i) == (a, b)) = false.
    rewrite xpair_eqE Hb andbF.
    by [].
  by rewrite Hpair /= !mul0r.
- have Hpair : ((tuple_prefix i (tnth x), tnth x i) == (a, b)) = false.
    have Hpa : (tuple_prefix i (tnth x) == a) = false.
      by rewrite tuple_prefix_eq_prefix.
    by rewrite xpair_eqE Hpa.
  by rewrite Hpair /= !mul0r.
- have Hpair : ((tuple_prefix i (tnth x), tnth x i) == (a, b)) = false.
    rewrite xpair_eqE Hb andbF.
    by [].
  by rewrite Hpair /= !mul0r.
Qed.

Lemma summable_prefix_coordinate_weighted_kl
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R)
    (i : 'I_n) :
  0 <= tnth eps i ->
  absolute_continuous P Q ->
  (forall a : i.-tuple A,
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <=
      tnth eps i) ->
  summable
    (fun a : i.-tuple A =>
      \P_[P] (fun x => tuple_prefix_eq a x) *
      δ_KL (conditional_coordinate P a)
           (conditional_coordinate Q a)).
Proof.
move=> Heps_i Hac Hcond.
pose pref_mass (a : i.-tuple A) :=
  \P_[P] (fun x => tuple_prefix_eq a x).
pose pref_dmargin :=
  dmargin (fun x : n.-tuple A => tuple_prefix i (tnth x)) P.
have Hpref_summable : summable pref_mass.
  apply: (eq_summable (S1 := pref_dmargin)).
    by move=> a; rewrite /pref_dmargin dmargin_tuple_prefixE.
  exact: summable_mu.
have Hbound a :
    0 <= pref_mass a *
      δ_KL (conditional_coordinate P a)
           (conditional_coordinate Q a) <=
    tnth eps i * pref_mass a.
  apply/andP; split.
    apply: mulr_ge0; first exact: ge0_pr.
    exact: conditional_coordinate_kl_nonnegative.
  rewrite [tnth eps i * _]mulrC.
  apply: ler_wpM2l; first exact: ge0_pr.
  exact: Hcond.
apply: (le_summable (F2 := fun a => tnth eps i * pref_mass a)).
  exact: Hbound.
apply: summableZ.
exact: Hpref_summable.
Qed.

Lemma sum_prefix_coordinate_weighted_kl_bound
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R)
    (i : 'I_n) :
  0 <= tnth eps i ->
  absolute_continuous P Q ->
  (forall a : i.-tuple A,
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <=
      tnth eps i) ->
  sum
    (fun a : i.-tuple A =>
      \P_[P] (fun x => tuple_prefix_eq a x) *
      δ_KL (conditional_coordinate P a)
           (conditional_coordinate Q a)) <=
  tnth eps i.
Proof.
move=> Heps_i Hac Hcond.
pose pref_mass (a : i.-tuple A) :=
  \P_[P] (fun x => tuple_prefix_eq a x).
pose H := fun a : i.-tuple A =>
  pref_mass a *
  δ_KL (conditional_coordinate P a)
       (conditional_coordinate Q a).
have Hnonneg a : 0 <= H a.
  rewrite /H.
  apply: mulr_ge0; first exact: ge0_pr.
  exact: conditional_coordinate_kl_nonnegative.
have Hpref_summable : summable pref_mass.
  apply: (eq_summable
    (S1 := dmargin (fun x : n.-tuple A => tuple_prefix i (tnth x)) P)).
    by move=> a; rewrite dmargin_tuple_prefixE.
  exact: summable_mu.
have Hpref_psum : psum pref_mass <= 1.
  rewrite (eq_psum
    (F2 := dmargin (fun x : n.-tuple A => tuple_prefix i (tnth x)) P));
    last by move=> a; rewrite dmargin_tuple_prefixE.
  exact: le1_mu.
rewrite -psum_sum; last exact: Hnonneg.
apply: (le_trans _ _).
  apply: (le_psum (F2 := tnth eps i \*o pref_mass)).
    move=> a.
    apply/andP; split; first exact: Hnonneg.
    rewrite /H /pref_mass /=.
    rewrite [X in _ <= X]mulrC.
    apply: ler_wpM2l; first exact: ge0_pr.
    exact: Hcond.
  change (summable (tnth eps i \*o pref_mass)).
  exact: summableZ.
rewrite psumZ //.
apply: (le_trans (ler_wpM2l Heps_i Hpref_psum)).
by rewrite mulr1.
Qed.

Lemma finite_sum_fneg_coordinate_log_contribution_partition_prefix
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R})
    (i : 'I_n) (J : seq (n.-tuple A)) :
  uniq J ->
  \sum_(x <- J)
    `|fneg
      (fun x => P x * coordinate_log_contribution P Q x i) x| <=
  \sum_(a <- undup [seq tuple_prefix i (tnth x) | x <- J])
    \sum_(x <- J | tuple_prefix_eq a x)
      `|fneg
        (fun x => P x * coordinate_log_contribution P Q x i) x|.
Proof.
move=> Huniq.
rewrite [leLHS]big_mkcond.
rewrite [leLHS]big_seq_cond.
rewrite [leRHS](eq_bigr (fun a =>
    \sum_(x <- J)
      (if tuple_prefix_eq a x then
        `|fneg
          (fun x => P x * coordinate_log_contribution P Q x i) x|
       else 0))); last first.
  by move=> a _; rewrite big_mkcond.
rewrite [leRHS]exchange_big.
rewrite [leRHS]big_seq_cond.
apply: ler_sum=> x /andP[HxJ _].
set t := `|fneg _ _|.
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

Lemma finite_sum_fneg_coordinate_log_contribution_partition_coordinate
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R})
    (i : 'I_n) (J : seq (n.-tuple A)) (a : i.-tuple A) :
  uniq J ->
  \sum_(x <- J | tuple_prefix_eq a x)
    `|fneg
      (fun x => P x * coordinate_log_contribution P Q x i) x| <=
  \sum_(b <- undup [seq tnth x i | x <- J])
    \sum_(x <- J | tuple_prefix_eq a x && (tnth x i == b))
      `|fneg
        (fun x => P x * coordinate_log_contribution P Q x i) x|.
Proof.
move=> _.
exact: (finite_sum_partition_by_image
  J (fun x => tnth x i) (fun x => tuple_prefix_eq a x)
  (fun x => `|fneg
    (fun x => P x * coordinate_log_contribution P Q x i) x|)
  (fun x => normr_ge0 _)).
Qed.

Lemma finite_sum_prefix_coordinate_fiber_log_fneg_bound
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R})
    (i : 'I_n) (J : seq (n.-tuple A)) (a : i.-tuple A) (b : A) :
  uniq J ->
  \sum_(x <- J | tuple_prefix_eq a x && (tnth x i == b))
    `|fneg
      (fun x => P x * coordinate_log_contribution P Q x i) x| <=
  `|fneg
    (fun b : A =>
      \P_[P] (fun x => tuple_prefix_eq a x) *
      (conditional_coordinate P a b *
       ln (conditional_coordinate P a b /
           conditional_coordinate Q a b))) b|.
Proof.
move=> Huniq.
set l := ln (conditional_coordinate P a b / conditional_coordinate Q a b).
set r := \P_[P] (fun x => tuple_prefix_eq a x) *
  conditional_coordinate P a b.
rewrite (eq_bigr (fun x => `|fneg (fun _ : unit => P x * l) tt|));
  last first.
  move=> x /andP[Hprefix /eqP Hb].
  rewrite /fneg /= /l.
  rewrite (coordinate_log_contribution_prefix P Q i a x Hprefix).
  by rewrite Hb.
apply: (le_trans
  (finite_sum_fneg_scaled_le
    J (fun x => tuple_prefix_eq a x && (tnth x i == b))
    (fun x => P x) r l (fun x => ge0_mu P x)
    (finite_sum_selected_prefix_coordinate_mass_le P i J a b Huniq))).
rewrite /r /l.
by rewrite -mulrA.
Qed.

Lemma finite_sum_fneg_coordinate_log_contribution_prefix_coordinate_group_bound
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R})
    (i : 'I_n) (J : seq (n.-tuple A)) (a : i.-tuple A) :
  uniq J ->
  \sum_(x <- J | tuple_prefix_eq a x)
    `|fneg
      (fun x => P x * coordinate_log_contribution P Q x i) x| <=
  \sum_(b <- undup [seq tnth x i | x <- J])
    `|fneg
      (fun b : A =>
        \P_[P] (fun x => tuple_prefix_eq a x) *
        (conditional_coordinate P a b *
         ln (conditional_coordinate P a b /
             conditional_coordinate Q a b))) b|.
Proof.
move=> Huniq.
apply: (le_trans
  (finite_sum_fneg_coordinate_log_contribution_partition_coordinate P Q i J a Huniq)).
apply: ler_sum=> b _.
exact: (finite_sum_prefix_coordinate_fiber_log_fneg_bound P Q i J a b Huniq).
Qed.

Lemma finite_sum_fneg_coordinate_log_contribution_prefix_bound
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R})
    (i : 'I_n) (J : seq (n.-tuple A)) (a : i.-tuple A) :
  uniq J ->
  absolute_continuous
    (conditional_coordinate P a) (conditional_coordinate Q a) ->
  \sum_(x <- J | tuple_prefix_eq a x)
    `|fneg
      (fun x => P x * coordinate_log_contribution P Q x i) x| <=
  psum (fneg
    (fun b : A =>
      \P_[P] (fun x => tuple_prefix_eq a x) *
      (conditional_coordinate P a b *
       ln (conditional_coordinate P a b /
           conditional_coordinate Q a b)))).
Proof.
move=> Huniq Hac.
apply: (le_trans
  (finite_sum_fneg_coordinate_log_contribution_prefix_coordinate_group_bound
    P Q i J a Huniq)).
apply: gerfinseq_psum; first exact: undup_uniq.
apply: (eq_summable (S1 :=
  \P_[P] (fun x => tuple_prefix_eq a x) \*o
  fneg (fun b : A =>
    conditional_coordinate P a b *
    ln (conditional_coordinate P a b /
        conditional_coordinate Q a b)))).
  move=> b.
  have := fnegZ
    (fun b : A =>
      conditional_coordinate P a b *
      ln (conditional_coordinate P a b /
          conditional_coordinate Q a b))
    (ge0_pr (fun x => tuple_prefix_eq a x) P) b.
  by [].
apply: summableZ.
exact: (summable_fneg_kl_integrand
  (conditional_coordinate P a) (conditional_coordinate Q a) Hac).
Qed.

Lemma finite_sum_fneg_coordinate_log_contribution_group_bound
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R})
    (i : 'I_n) (J : seq (n.-tuple A)) :
  (forall a : i.-tuple A,
    absolute_continuous
      (conditional_coordinate P a) (conditional_coordinate Q a)) ->
  uniq J ->
  \sum_(x <- J)
    `|fneg
      (fun x => P x * coordinate_log_contribution P Q x i) x| <=
  \sum_(a <- undup [seq tuple_prefix i (tnth x) | x <- J])
    psum (fneg
      (fun b : A =>
        \P_[P] (fun x => tuple_prefix_eq a x) *
        (conditional_coordinate P a b *
         ln (conditional_coordinate P a b /
             conditional_coordinate Q a b)))).
Proof.
move=> Hac Huniq.
apply: (le_trans
  (finite_sum_fneg_coordinate_log_contribution_partition_prefix P Q i J Huniq)).
apply: ler_sum=> a _.
exact: (finite_sum_fneg_coordinate_log_contribution_prefix_bound
  P Q i J a Huniq (Hac a)).
Qed.

Lemma finite_sum_fneg_coordinate_log_contribution_bound
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R})
    (i : 'I_n) (J : seq (n.-tuple A)) :
  (forall a : i.-tuple A,
    finite_kl (conditional_coordinate P a)
              (conditional_coordinate Q a)) ->
  uniq J ->
  \sum_(x <- J)
    `|fneg
      (fun x => P x * coordinate_log_contribution P Q x i) x| <=
  1.
Proof.
move=> Hfin Huniq.
have Hac (a : i.-tuple A) : absolute_continuous
    (conditional_coordinate P a) (conditional_coordinate Q a).
  by have [Hac _] := Hfin a.
apply: (le_trans
  (finite_sum_fneg_coordinate_log_contribution_group_bound P Q i J Hac Huniq)).
apply: (le_trans _ (finite_sum_selected_prefix_mass_le1 P i J)).
apply: ler_sum=> a _.
exact: (scaled_kl_integrand_fneg_psum_le
  (conditional_coordinate P a) (conditional_coordinate Q a)
  (\P_[P] (fun x => tuple_prefix_eq a x))
  (ge0_pr (fun x => tuple_prefix_eq a x) P) (Hac a)).
Qed.


Lemma sum_coordinate_log_contribution_prefix_weighted
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (i : 'I_n) :
  summable (fun x => P x * coordinate_log_contribution P Q x i) ->
  summable (fun a : i.-tuple A =>
    \P_[P] (fun x => tuple_prefix_eq a x) *
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a)) ->
  (forall a : i.-tuple A,
    finite_kl (conditional_coordinate P a)
              (conditional_coordinate Q a)) ->
  sum (fun x => P x * coordinate_log_contribution P Q x i) =
  sum (fun a : i.-tuple A =>
    \P_[P] (fun x => tuple_prefix_eq a x) *
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a)).
Proof.
move=> Hsumm _ Hfin.
pose fpair (x : n.-tuple A) := (tuple_prefix i (tnth x), tnth x i).
pose hpair (ab : i.-tuple A * A) :=
  ln (conditional_coordinate P ab.1 ab.2 /
      conditional_coordinate Q ab.1 ab.2).
have Hsumm_fpair :
    summable (fun x : n.-tuple A => P x * hpair (fpair x)).
  apply: (eq_summable
    (S1 := fun x : n.-tuple A => P x * coordinate_log_contribution P Q x i)).
    by move=> x; rewrite /fpair /hpair /coordinate_log_contribution.
  exact: Hsumm.
rewrite (eq_sum
  (F2 := fun x : n.-tuple A => P x * hpair (fpair x))); last first.
  by move=> x; rewrite /fpair /hpair /coordinate_log_contribution.
rewrite (sum_dmargin_comp P fpair hpair Hsumm_fpair).
pose F := fun ab : i.-tuple A * A =>
  \P_[P] (fun x => tuple_prefix_eq ab.1 x) *
  (conditional_coordinate P ab.1 ab.2 *
   ln (conditional_coordinate P ab.1 ab.2 /
       conditional_coordinate Q ab.1 ab.2)).
have Hsumm_pair : summable F.
  apply: (eq_summable
    (S1 := fun ab : i.-tuple A * A => dmargin fpair P ab * hpair ab)).
    case=> a b.
    by rewrite /F /hpair /fpair dmargin_prefix_coordinateE mulrA.
  exact: (summable_dmargin_comp P fpair hpair Hsumm_fpair).
rewrite (eq_sum (F2 := F)); last first.
  case=> a b.
  by rewrite /F /hpair /fpair dmargin_prefix_coordinateE mulrA.
rewrite (sum_pair_fst_rows F Hsumm_pair); last first.
  move=> a.
  apply: (eq_summable
    (S1 := \P_[P] (fun x => tuple_prefix_eq a x) \*o
      (fun b : A =>
        conditional_coordinate P a b *
        ln (conditional_coordinate P a b /
            conditional_coordinate Q a b)))).
    move=> b.
    by rewrite /F.
  apply: summableZ.
  exact: (finite_kl_summable
    (conditional_coordinate P a) (conditional_coordinate Q a) (Hfin a)).
apply/eq_sum=> a.
rewrite (eq_sum
  (F2 := fun b : A =>
    \P_[P] (fun x => tuple_prefix_eq a x) *
    (conditional_coordinate P a b *
     ln (conditional_coordinate P a b /
         conditional_coordinate Q a b)))); last first.
  by move=> b; rewrite /F.
exact: (sum_scaled_kl_integrand
  (conditional_coordinate P a) (conditional_coordinate Q a)
  (\P_[P] (fun x => tuple_prefix_eq a x)) (Hfin a)).
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

Lemma finite_sum_fpos_coordinate_log_contribution_bound_eps
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R)
    (i : 'I_n) (J : seq (n.-tuple A)) :
  0 <= tnth eps i ->
  dweight P = 1 ->
  dweight Q = 1 ->
  absolute_continuous P Q ->
  (forall a : i.-tuple A,
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a) /\
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <=
      tnth eps i) ->
  uniq J ->
  \sum_(x <- J)
    `|fpos
      (fun x => P x * coordinate_log_contribution P Q x i) x| <=
  tnth eps i + 1.
Proof.
move=> Heps_i HP HQ Hac Hcond Huniq.
have Hfin (a : i.-tuple A) : finite_kl
    (conditional_coordinate P a) (conditional_coordinate Q a).
  by have [Hfin _] := Hcond a.
apply: (le_trans
  (finite_sum_fpos_coordinate_log_contribution_bound
    P Q i J HP HQ Hac Hfin Huniq)).
apply: lerD; last exact: lexx.
exact: (prefix_coordinate_kl_contribution_bound
  P Q eps i J Heps_i Hcond).
Qed.

Lemma summable_coordinate_log_contribution
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R)
    (i : 'I_n) :
  0 <= tnth eps i ->
  dweight P = 1 ->
  dweight Q = 1 ->
  absolute_continuous P Q ->
  (forall a : i.-tuple A,
    finite_kl (conditional_coordinate P a)
              (conditional_coordinate Q a)) ->
  (forall a : i.-tuple A,
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <=
      tnth eps i) ->
  summable (fun x => P x * coordinate_log_contribution P Q x i).
Proof.
move=> Heps_i HP HQ Hac Hfin Hcond.
apply: summable_from_fpos_fneg.
- apply/summable_seqP.
  exists (tnth eps i + 1); first by lra.
  move=> J Huniq.
  exact: (finite_sum_fpos_coordinate_log_contribution_bound_eps
    P Q eps i J Heps_i HP HQ Hac
    (fun a => conj (Hfin a) (Hcond a)) Huniq).
- apply/summable_seqP.
  exists 1; first by lra.
  move=> J Huniq.
  exact: (finite_sum_fneg_coordinate_log_contribution_bound
    P Q i J Hfin Huniq).
Qed.

Lemma sum_coordinate_log_contribution_bound
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R)
    (i : 'I_n) :
  0 <= tnth eps i ->
  dweight P = 1 ->
  dweight Q = 1 ->
  absolute_continuous P Q ->
  (forall a : i.-tuple A,
    finite_kl (conditional_coordinate P a)
              (conditional_coordinate Q a)) ->
  (forall a : i.-tuple A,
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <=
      tnth eps i) ->
  sum (fun x => P x * coordinate_log_contribution P Q x i) <=
  tnth eps i.
Proof.
move=> Heps_i HP HQ Hac Hfin Hcond.
have Hsumm_coord : summable
    (fun x => P x * coordinate_log_contribution P Q x i).
  exact: (summable_coordinate_log_contribution
    P Q eps i Heps_i HP HQ Hac Hfin Hcond).
have Hsumm_pref : summable
    (fun a : i.-tuple A =>
      \P_[P] (fun x => tuple_prefix_eq a x) *
      δ_KL (conditional_coordinate P a)
           (conditional_coordinate Q a)).
  exact: (summable_prefix_coordinate_weighted_kl P Q eps i Heps_i Hac Hcond).
rewrite (sum_coordinate_log_contribution_prefix_weighted
  P Q i Hsumm_coord Hsumm_pref Hfin).
exact: (sum_prefix_coordinate_weighted_kl_bound P Q eps i Heps_i Hac Hcond).
Qed.


Lemma iterated_kl_chain_bound_from_pointwise
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R) :
  (forall i : 'I_n, 0 <= tnth eps i) ->
  dweight P = 1 ->
  dweight Q = 1 ->
  finite_kl P Q ->
  (forall (i : 'I_n) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a)) ->
  (forall x : n.-tuple A,
    P x * ln (P x / Q x) =
    \sum_(i < n) P x * coordinate_log_contribution P Q x i) ->
  (forall (i : 'I_n) (a : i.-tuple A),
  δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <= tnth eps i) ->
  δ_KL P Q <= \sum_(i < n) tnth eps i.
Proof.
move=> Heps HP HQ Hfin Hfincond Hpoint Hcond.
have Hac : absolute_continuous P Q :=
  finite_kl_absolute_continuous P Q Hfin.
pose F (i : 'I_n) (x : n.-tuple A) :=
  P x * coordinate_log_contribution P Q x i.
have HsummF : forall i : 'I_n, summable (F i).
  move=> i.
  exact: (summable_coordinate_log_contribution P Q eps i
    (Heps i) HP HQ Hac (fun a => Hfincond i a) (fun a => Hcond i a)).
rewrite /δ_KL /esp.
rewrite (eq_sum (F2 := fun x => P x * ln (P x / Q x))); last first.
  by move=> x; rewrite mulrC.
have Hsum_eq :
    sum (fun x => P x * ln (P x / Q x)) =
    sum (fun x => \sum_(i < n) F i x).
  apply/eq_sum=> x.
  by rewrite /F Hpoint.
rewrite Hsum_eq.
rewrite (sum_finite_ord_sum F HsummF).
apply: ler_sum=> i _.
exact: (sum_coordinate_log_contribution_bound P Q eps i
  (Heps i) HP HQ Hac (fun a => Hfincond i a) (fun a => Hcond i a)).
Qed.

Lemma iterated_kl_chain_bound_via_pointwise
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R) :
  (forall i : 'I_n, 0 <= tnth eps i) ->
  dweight P = 1 ->
  dweight Q = 1 ->
  finite_kl P Q ->
  (forall (i : 'I_n) (a : i.-tuple A),
    finite_kl
      (conditional_coordinate P a)
      (conditional_coordinate Q a)) ->
  (forall (i : 'I_n) (a : i.-tuple A),
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <= tnth eps i) ->
  δ_KL P Q <= \sum_(i < n) tnth eps i.
Proof.
move=> Heps HP HQ Hfin Hfincond Hcond.
have Hac : absolute_continuous P Q := finite_kl_absolute_continuous P Q Hfin.
apply: (iterated_kl_chain_bound_from_pointwise P Q eps
  Heps HP HQ Hfin Hfincond _ Hcond).
exact: (kl_integrand_chain_decomp_pointwise P Q HP HQ Hac).
Qed.


Lemma prefix_coordinate_weighted_kl_bound
    {n : nat} {A : choiceType}
    (P Q : {distr (n.-tuple A) / R}) (eps : n.-tuple R)
    (i : 'I_n) (J : seq (n.-tuple A)) :
  0 <= tnth eps i ->
  (forall a : i.-tuple A,
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <=
      tnth eps i) ->
  \sum_(a <- undup [seq tuple_prefix i (tnth x) | x <- J])
    \P_[P] (fun x => tuple_prefix_eq a x) *
    δ_KL (conditional_coordinate P a)
         (conditional_coordinate Q a) <=
  tnth eps i.
Proof.
move=> Heps_i Hcond.
pose pref_mass (a : i.-tuple A) :=
  \P_[P] (fun x => tuple_prefix_eq a x).
have Hsumpoint :
    \sum_(a <- undup [seq tuple_prefix i (tnth x) | x <- J])
      pref_mass a *
      δ_KL (conditional_coordinate P a)
           (conditional_coordinate Q a) <=
    \sum_(a <- undup [seq tuple_prefix i (tnth x) | x <- J])
      tnth eps i * pref_mass a.
  apply: ler_sum=> a _.
  rewrite [tnth eps i * _]mulrC.
  apply: ler_wpM2l; first exact: ge0_pr.
  exact: Hcond.
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

End KL_ChainPointwise.
