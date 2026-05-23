From Stdlib Require Import Utf8 Lia.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq choice bigop order all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp Require Import reals realsum exp sequences realseq distr.
Set Warnings "-notation-incompatible-prefix".
From mathcomp Require Import xfinmap.
Set Warnings "notation-incompatible-prefix".
From mathcomp Require Import lra.
Import GRing.Theory Num.Theory Order.Theory.

From Mending.Probability Require Import DiscreteGaussian DiscreteGaussianKL.
From Mending.LibExtras.MathcompExtras Require Import RealSumExtras DistrExtras.

Local Open Scope ring_scope.

Section DiscreteGaussianTail.

Context {R : realType}.

Definition discrete_gaussian_tail_event (center : int) (k : nat) : pred int :=
  [pred x | (k <= absz (x - center))%N].

Definition mirrored_geometric_tail (s : R) (k : nat) : R :=
  psum (fun x : int => ((k <= absz x)%N)%:R * geom_above s (absz x)).

Definition geometric_tail_bound (s : R) (k : nat) : R :=
  2 * (max_step_ratio s ^+ k / (1 - max_step_ratio s)).

Lemma gaussian_weight_ge1 (s : R) :
  s > 0 -> 1 <= sum (gaussian s).
Proof.
move=> gt0_s.
rewrite -psum_sum; last exact: ge0_gaussian.
have H := ger1_psum (S := gaussian s) 0 (summable_gaussian s gt0_s).
rewrite /gaussian /= in H.
have g0 : (0%:~R / s) ^ 2 = 0 :> R by lra.
rewrite g0 oppr0 mul0r expR0 normr1 in H.
exact: H.
Qed.

Lemma centered_discrete_gaussian_le_geom (s : R) (x : int) :
  s > 0 ->
  centered_discrete_gaussian s x <= geom_above s (absz x).
Proof.
move=> gt0_s.
rewrite centered_discrete_gaussianE // gaussian_pdfE //.
have ge1_sum : 1 <= sum (gaussian s) by exact: gaussian_weight_ge1.
have gt0_sum : 0 < sum (gaussian s) by exact: gt0_weight_gaussian.
apply: le_trans (le_gauss_geo s x gt0_s).
rewrite ler_pdivrMr //.
rewrite -[leLHS]mulr1.
apply: ler_wpM2l; first exact: ge0_gaussian.
exact: ge1_sum.
Qed.

Lemma summable_mirrored_geometric_tail (s : R) (k : nat) :
  s > 0 ->
  summable (fun x : int => ((k <= absz x)%N)%:R * geom_above s (absz x)).
Proof.
move=> gt0_s.
apply: (mirror_summable (fun n : nat => ((k <= n)%N)%:R * geom_above s n)).
apply: (le_summable (F2 := geom_above s)).
- move=> n; apply/andP; split.
  + rewrite mulr_ge0 ?ler0n //.
    rewrite /geom_above.
    apply: ge0_geo.
    rewrite /max_step_ratio; exact: expR_ge0.
  case: (k <= n)%N; first by rewrite mul1r.
  rewrite mul0r.
  rewrite /geom_above.
  apply: ge0_geo.
  rewrite /max_step_ratio; exact: expR_ge0.
rewrite /geom_above.
apply: summable_geo.
rewrite /max_step_ratio /=.
apply/andP; split; first exact: expR_ge0.
rewrite expR_lt1.
suff: (1 / s) ^ 2 > 0 by lra.
rewrite /exprz /= expr2.
have H : 1 / s > 0 by exact: divr_gt0.
exact: mulr_gt0.
Qed.

Lemma centered_discrete_gaussian_tail_bound (s : R) (k : nat) :
  s > 0 ->
  \P_[centered_discrete_gaussian s] [pred x | (k <= absz x)%N] <=
    mirrored_geometric_tail s k.
Proof.
move=> gt0_s.
rewrite /mirrored_geometric_tail /pr.
apply: le_psum; last exact: summable_mirrored_geometric_tail.
move=> x; apply/andP; split.
- by rewrite mulr_ge0 ?ler0n ?ge0_mu.
- case Htail: (k <= absz x)%N.
  + rewrite /= Htail !mul1r.
    exact: (centered_discrete_gaussian_le_geom s x gt0_s).
  by rewrite /= Htail !mul0r.
Qed.

Lemma discrete_gaussian_tail_geometric_bound (center : int) (s : R) (k : nat) :
  s > 0 ->
  \P_[discrete_gaussian center s] (discrete_gaussian_tail_event center k) <=
    mirrored_geometric_tail s k.
Proof.
move=> gt0_s.
rewrite /discrete_gaussian_tail_event.
rewrite -(pr_dmargin [pred x | (k <= absz x)%N]
  (fun x : int => x - center) (discrete_gaussian center s)).
rewrite /mirrored_geometric_tail /pr.
apply: le_psum; last exact: summable_mirrored_geometric_tail.
move=> x; apply/andP; split.
- by rewrite mulr_ge0 ?ler0n ?ge0_mu.
- rewrite (discrete_gaussian_translate center s gt0_s x).
  case Htail: (k <= absz x)%N.
  + rewrite /= Htail !mul1r.
    exact: (centered_discrete_gaussian_le_geom s x gt0_s).
  by rewrite /= Htail !mul0r.
Qed.

Lemma psum_geometric_le (r : R) :
  0 <= r < 1 ->
  psum (geometric 1 r) <= 1 / (1 - r).
Proof.
move=> r01.
have ge0_r : 0 <= r by case/andP: r01.
have lt1_r : r < 1 by case/andP: r01.
apply: psum_le => J uniq_J.
rewrite (eq_bigr (fun n => geometric 1 r n)); last first.
  move=> n _.
  rewrite ger0_norm //.
  exact: ge0_geo.
apply: (le_trans
  (y := \sum_(0 <= i < S (max_nat_lst J)) geometric 1 r i)).
  rewrite (split_sum J) //.
  suff: 0 <= \sum_(n <- compl J (S (max_nat_lst J))) geometric 1 r n by lra.
  apply: ge0_bigsum => n.
  exact: ge0_geo.
rewrite big_mkord.
rewrite finite_sum_geoE; last lra.
suff: 0 <= r ^ S (max_nat_lst J) / (1 - r) by lra.
apply: divr_ge0.
- exact: exprn_ge0.
by lra.
Qed.

Lemma summable_geometric_tail (r : R) (k : nat) :
  0 <= r < 1 ->
  summable (fun n : nat => ((k <= n)%N)%:R * geometric 1 r n).
Proof.
move=> r01.
apply: (le_summable (F2 := geometric 1 r)).
- move=> n; apply/andP; split.
  + rewrite mulr_ge0 ?ler0n //.
    apply: ge0_geo.
    by case/andP: r01.
  case: (k <= n)%N; first by rewrite mul1r.
  rewrite mul0r.
  apply: ge0_geo.
  by case/andP: r01.
apply: summable_geo.
exact: r01.
Qed.

Lemma psum_geometric_tail_le (r : R) (k : nat) :
  0 < r < 1 ->
  psum (fun n : nat => ((k <= n)%N)%:R * geometric 1 r n) <=
    r ^+ k / (1 - r).
Proof.
move=> r01.
have gt0_r : 0 < r by case/andP: r01.
have ge0_r : 0 <= r by exact: ltW.
have lt1_r : r < 1 by case/andP: r01.
rewrite (reindex_psum
  (S := fun n : nat => ((k <= n)%N)%:R * geometric 1 r n)
  (P := [pred n | (k <= n)%N])
  (h := fun m : nat => (m + k)%N)).
- rewrite (eq_psum (F2 := (r ^+ k) \*o geometric 1 r)); last first.
    move=> m /=.
    rewrite addnC leq_addr mul1r /geometric /= !mul1r.
    by rewrite exprD.
  rewrite psumZ ?exprn_ge0 //.
  apply: ler_wpM2l; first exact: exprn_ge0.
  rewrite -[leRHS]mul1r.
  apply: psum_geometric_le.
  by apply/andP; split.
- move=> n.
  rewrite inE.
  case Hkn: (k <= n)%N => //=.
  by rewrite mul0r eqxx.
exists (fun n : nat => (n - k)%N) => [m Hmk | n Hn].
- move: Hmk; rewrite inE => Hmk.
  by rewrite addnK.
move: Hn; rewrite inE => Hn.
by rewrite subnK.
Qed.

Lemma nonnegative_absz_inj (x y : int) :
  0 <= x -> 0 <= y -> absz x = absz y -> x = y.
Proof. lia. Qed.

Lemma negative_absz_inj (x y : int) :
  x < 0 -> y < 0 -> absz x = absz y -> x = y.
Proof. lia. Qed.

Lemma positive_side_le_geometric_tail (r : R) (k : nat) (J : seq int) :
  0 <= r < 1 ->
  uniq J ->
  (forall x, x \in J -> 0 <= x) ->
  \sum_(x <- J) `| ((k <= absz x)%N)%:R * geometric 1 r (absz x) | <=
    psum (fun n : nat => ((k <= n)%N)%:R * geometric 1 r n).
Proof.
move=> r01 uniq_J nonneg_J.
have uniq_abs : uniq [seq absz x | x <- J].
  rewrite map_inj_in_uniq //.
  move=> x y xJ yJ eq_abs.
  apply: nonnegative_absz_inj eq_abs; exact: nonneg_J.
rewrite -(big_map absz predT
  (fun n => `| ((k <= n)%N)%:R * geometric 1 r n |)).
apply: ger_big_psum.
- exact: uniq_abs.
exact: summable_geometric_tail.
Qed.

Lemma negative_side_le_geometric_tail (r : R) (k : nat) (J : seq int) :
  0 <= r < 1 ->
  uniq J ->
  (forall x, x \in J -> x < 0) ->
  \sum_(x <- J) `| ((k <= absz x)%N)%:R * geometric 1 r (absz x) | <=
    psum (fun n : nat => ((k <= n)%N)%:R * geometric 1 r n).
Proof.
move=> r01 uniq_J neg_J.
have uniq_abs : uniq [seq absz x | x <- J].
  rewrite map_inj_in_uniq //.
  move=> x y xJ yJ eq_abs.
  apply: negative_absz_inj eq_abs; exact: neg_J.
rewrite -(big_map absz predT
  (fun n => `| ((k <= n)%N)%:R * geometric 1 r n |)).
apply: ger_big_psum.
- exact: uniq_abs.
exact: summable_geometric_tail.
Qed.

Lemma psum_mirrored_geometric_tail_le (r : R) (k : nat) :
  0 < r < 1 ->
  psum (fun x : int => ((k <= absz x)%N)%:R * geometric 1 r (absz x)) <=
    2 * (r ^+ k / (1 - r)).
Proof.
move=> r01.
have ge0_r : 0 <= r by case/andP: r01 => /ltW.
have lt1_r : r < 1 by case/andP: r01.
have r01w : 0 <= r < 1 by apply/andP; split.
apply: psum_le => J uniq_J.
pose posJ := [seq x <- J | 0 <= x].
pose negJ := filter (predC (Order.le 0)) J.
rewrite (perm_big (posJ ++ negJ)) /=; last first.
  rewrite perm_sym.
  apply permEl.
  exact: perm_filterC.
rewrite big_cat.
have le_pos :
    \sum_(x <- posJ) `| ((k <= absz x)%N)%:R * geometric 1 r (absz x) | <=
    psum (fun n : nat => ((k <= n)%N)%:R * geometric 1 r n).
  apply: positive_side_le_geometric_tail => //.
  - exact: filter_uniq.
  move=> x.
  by rewrite mem_filter => /andP[].
have le_neg :
    \sum_(x <- negJ) `| ((k <= absz x)%N)%:R * geometric 1 r (absz x) | <=
    psum (fun n : nat => ((k <= n)%N)%:R * geometric 1 r n).
  apply: negative_side_le_geometric_tail => //.
  - exact: filter_uniq.
  move=> x.
  rewrite mem_filter /predC /= => /andP[/negP nx _].
  lia.
have le_tail := psum_geometric_tail_le r k r01.
apply: le_trans (_ :
  psum (fun n : nat => ((k <= n)%N)%:R * geometric 1 r n) +
  psum (fun n : nat => ((k <= n)%N)%:R * geometric 1 r n) <= _).
- exact: lerD.
set G := psum _.
have -> : G + G = 2 * G by lra.
apply: ler_wpM2l; first by rewrite ler0n.
exact: le_tail.
Qed.

Lemma mirrored_geometric_tail_le_closed (s : R) (k : nat) :
  s > 0 ->
  mirrored_geometric_tail s k <= geometric_tail_bound s k.
Proof.
move=> gt0_s.
rewrite /mirrored_geometric_tail /geometric_tail_bound /geom_above.
apply: psum_mirrored_geometric_tail_le.
rewrite /max_step_ratio.
apply/andP; split; first exact: expR_gt0.
rewrite expR_lt1.
suff: (1 / s) ^ 2 > 0 by lra.
rewrite /exprz /= expr2.
have H : 1 / s > 0 by exact: divr_gt0.
exact: mulr_gt0.
Qed.

Lemma discrete_gaussian_tail_bound (center : int) (s : R) (k : nat) :
  s > 0 ->
  \P_[discrete_gaussian center s] (discrete_gaussian_tail_event center k) <=
    geometric_tail_bound s k.
Proof.
move=> gt0_s.
apply: (le_trans (discrete_gaussian_tail_geometric_bound center s k gt0_s)).
exact: mirrored_geometric_tail_le_closed.
Qed.

End DiscreteGaussianTail.
