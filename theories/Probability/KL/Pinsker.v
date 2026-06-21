Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra all_reals distr.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import realseq realsum exp lra topology normedtype derive realfun.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From mathcomp.algebra_tactics Require Import ring.

From Mending.LibExtras.MathcompExtras Require Import DistrExtras.
From Mending.Probability.KL Require Import Core.

Import GRing.Theory Num.Theory Order.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section KL_Pinsker.

Context {R: realType}.

Lemma deriv_div_const (q x : R) :
  (fun z : R => z / q)^`()%classic x = q^-1.
Proof.
rewrite derive1Mr; last exact: derivable_id.
by rewrite derive1_id mul1r.
Qed.

Lemma derivable_div_const (q x : R) :
  derivable (fun z : R => z / q) x 1.
Proof.
apply: derivableM; first exact: derivable_id.
exact: derivable_cst.
Qed.

Lemma is_derive_div_const (q x : R) :
  is_derive x 1 (fun z : R => z / q) q^-1.
Proof.
apply: DeriveDef; first exact: derivable_div_const.
by rewrite -derive1E deriv_div_const.
Qed.

Lemma derivable_ln_div_const (q x : R) :
  0 < q -> 0 < x -> derivable (fun z : R => ln (z / q)) x 1.
Proof.
move=> Hq Hx.
rewrite (_ : (fun z : R => ln (z / q)) =
  (ln (R:=R)) \o (fun z : R => z / q)); last by [].
apply: ex_derive.
apply: is_derive1_comp.
have Hxq : 0 < x / q by rewrite divr_gt0.
exact: is_derive1_ln.
Qed.

Lemma deriv_ln_div_const (q x : R) :
  0 < q -> 0 < x ->
  (fun z : R => ln (z / q))^`()%classic x = x^-1.
Proof.
move=> Hq Hx.
rewrite (_ : (fun z : R => ln (z / q)) =
  (ln (R:=R)) \o (fun z : R => z / q)); last by [].
rewrite derive1_comp; last 2 first.
- exact: derivable_div_const.
- have Hxq : 0 < x / q by rewrite divr_gt0.
  by apply: ex_derive; exact: is_derive1_ln.
rewrite deriv_div_const.
have Hxq : 0 < x / q by rewrite divr_gt0.
rewrite derive1E.
have [_ ->] := is_derive1_ln Hxq.
field.
by rewrite !lt0r_neq0.
Qed.

Lemma derivable_onem (x : R) :
  derivable (fun z : R => 1 - z) x 1.
Proof.
apply: derivableB; first exact: derivable_cst.
exact: derivable_id.
Qed.

Lemma deriv_onem (x : R) :
  (fun z : R => 1 - z)^`()%classic x = -1.
Proof.
rewrite derive1E deriveB; last 2 first.
- exact: derivable_cst.
- exact: derivable_id.
by rewrite derive_cst derive_id sub0r.
Qed.

Lemma derivable_sub_const (q x : R) :
  derivable (fun z : R => z - q) x 1.
Proof.
apply: derivableB; first exact: derivable_id.
exact: derivable_cst.
Qed.

Lemma deriv_sub_const (q x : R) :
  (fun z : R => z - q)^`()%classic x = 1.
Proof.
rewrite derive1E deriveB; last 2 first.
- exact: derivable_id.
- exact: derivable_cst.
by rewrite derive_id derive_cst subr0.
Qed.

Lemma derivable_sq_shift (q x : R) :
  derivable (fun z : R => (z - q)^+2) x 1.
Proof.
rewrite (_ : (fun z : R => (z - q)^+2) =
  (fun z : R => (z - q) * (z - q))); last first.
  by apply/funext=> z; rewrite expr2.
apply: derivableM; exact: derivable_sub_const.
Qed.

Lemma deriv_sq_shift (q x : R) :
  (fun z : R => (z - q)^+2)^`()%classic x = 2 * (x - q).
Proof.
rewrite (_ : (fun z : R => (z - q)^+2) =
  (fun u : R => u^+2) \o (fun z : R => z - q)); last by [].
rewrite derive1_comp; last 2 first.
- exact: derivable_sub_const.
- exact: exprn_derivable.
by rewrite exp_derive1 deriv_sub_const /= expr1 mulr1 scaler_nat mulr_natl.
Qed.

Lemma derivable_onem_div_const (q x : R) :
  derivable (fun z : R => (1 - z) / (1 - q)) x 1.
Proof.
apply: derivableM; first exact: derivable_onem.
exact: derivable_cst.
Qed.

Lemma deriv_onem_div_const (q x : R) :
  (fun z : R => (1 - z) / (1 - q))^`()%classic x =
  - (1 - q)^-1.
Proof.
rewrite derive1Mr; last exact: derivable_onem.
by rewrite deriv_onem mulN1r.
Qed.

Lemma derivable_ln_onem_div_const (q x : R) :
  q < 1 -> x < 1 ->
  derivable (fun z : R => ln ((1 - z) / (1 - q))) x 1.
Proof.
move=> Hq Hx.
rewrite (_ : (fun z : R => ln ((1 - z) / (1 - q))) =
  (ln (R:=R)) \o (fun z : R => (1 - z) / (1 - q))); last by [].
apply: ex_derive.
apply: is_derive1_comp.
have Hpos : 0 < (1 - x) / (1 - q) by rewrite divr_gt0; lra.
exact: is_derive1_ln.
Qed.

Lemma deriv_ln_onem_div_const (q x : R) :
  q < 1 -> x < 1 ->
  (fun z : R => ln ((1 - z) / (1 - q)))^`()%classic x =
  - (1 - x)^-1.
Proof.
move=> Hq Hx.
rewrite (_ : (fun z : R => ln ((1 - z) / (1 - q))) =
  (ln (R:=R)) \o (fun z : R => (1 - z) / (1 - q))); last by [].
rewrite derive1_comp; last 2 first.
- exact: derivable_onem_div_const.
- have Hpos : 0 < (1 - x) / (1 - q) by rewrite divr_gt0; lra.
  by apply: ex_derive; exact: is_derive1_ln.
rewrite deriv_onem_div_const.
have Hpos : 0 < (1 - x) / (1 - q) by rewrite divr_gt0; lra.
rewrite derive1E.
have [_ ->] := is_derive1_ln Hpos.
field.
by rewrite !subr_eq0; lra.
Qed.

Definition binary_kl (p q : R) :=
  p * ln (p / q) + (1 - p) * ln ((1 - p) / (1 - q)).

Definition bern_gap (p q : R) :=
  binary_kl p q - 2 * (p - q)^+2.

Definition bern_gap_deriv_expr (q x : R) :=
  ln (x / q) - ln ((1 - x) / (1 - q)) - 4 * (x - q).

Lemma deriv_xln_div_const (q x : R) :
  0 < q -> 0 < x ->
  (fun z : R => z * ln (z / q))^`()%classic x =
    ln (x / q) + 1.
Proof.
move=> Hq Hx.
rewrite derive1E deriveM; last 2 first.
- exact: derivable_id.
- exact: derivable_ln_div_const.
rewrite derive_id -derive1E deriv_ln_div_const //.
rewrite /GRing.scale /= mulfV ?lt0r_neq0 //.
ring.
Qed.

Lemma deriv_onem_xln_onem_div_const (q x : R) :
  q < 1 -> x < 1 ->
  (fun z : R => (1 - z) * ln ((1 - z) / (1 - q)))^`()%classic x =
    - ln ((1 - x) / (1 - q)) - 1.
Proof.
move=> Hq Hx.
rewrite derive1E deriveM; last 2 first.
- exact: derivable_onem.
- exact: derivable_ln_onem_div_const.
rewrite deriveB ?derive_cst ?derive_id //.
rewrite -derive1E deriv_ln_onem_div_const //.
rewrite /GRing.scale /=.
field.
by rewrite !subr_eq0; lra.
Qed.

Lemma derivable_binary_kl (q x : R) :
  0 < q -> q < 1 -> 0 < x -> x < 1 ->
  derivable (fun z : R => binary_kl z q) x 1.
Proof.
move=> Hq0 Hq1 Hx0 Hx1.
rewrite /binary_kl.
apply: derivableD.
- apply: derivableM; first exact: derivable_id.
  exact: derivable_ln_div_const.
- apply: derivableM; first exact: derivable_onem.
  exact: derivable_ln_onem_div_const.
Qed.

Lemma deriv_binary_kl (q x : R) :
  0 < q -> q < 1 -> 0 < x -> x < 1 ->
  (fun z : R => binary_kl z q)^`()%classic x =
    ln (x / q) - ln ((1 - x) / (1 - q)).
Proof.
move=> Hq0 Hq1 Hx0 Hx1.
rewrite /binary_kl.
rewrite derive1E deriveD; last 2 first.
- apply: derivableM; first exact: derivable_id.
  exact: derivable_ln_div_const.
- apply: derivableM; first exact: derivable_onem.
  exact: derivable_ln_onem_div_const.
rewrite -!derive1E.
rewrite deriv_xln_div_const // deriv_onem_xln_onem_div_const //.
ring.
Qed.

Lemma deriv_bern_gap (q x : R) :
  0 < q -> q < 1 -> 0 < x -> x < 1 ->
  (fun z : R => bern_gap z q)^`()%classic x =
    bern_gap_deriv_expr q x.
Proof.
move=> Hq0 Hq1 Hx0 Hx1.
rewrite /bern_gap.
rewrite derive1E deriveB; last 2 first.
- exact: derivable_binary_kl.
- apply: derivableM; first exact: derivable_cst.
  exact: derivable_sq_shift.
rewrite -!derive1E.
rewrite deriv_binary_kl //.
rewrite derive1Ml; last exact: derivable_sq_shift.
rewrite deriv_sq_shift.
rewrite /bern_gap_deriv_expr.
ring.
Qed.

Lemma derivable_bern_gap (q x : R) :
  0 < q -> q < 1 -> 0 < x -> x < 1 ->
  derivable (fun z : R => bern_gap z q) x 1.
Proof.
move=> Hq0 Hq1 Hx0 Hx1.
rewrite /bern_gap.
apply: derivableB.
- exact: derivable_binary_kl.
- apply: derivableM; first exact: derivable_cst.
  exact: derivable_sq_shift.
Qed.

Lemma is_derive_bern_gap (q x : R) :
  0 < q -> q < 1 -> 0 < x -> x < 1 ->
  is_derive x 1 (fun z : R => bern_gap z q) (bern_gap_deriv_expr q x).
Proof.
move=> Hq0 Hq1 Hx0 Hx1.
apply: DeriveDef; first exact: derivable_bern_gap.
by rewrite -derive1E deriv_bern_gap.
Qed.

Lemma derivable_bern_gap_deriv_expr (q x : R) :
  0 < q -> q < 1 -> 0 < x -> x < 1 ->
  derivable (fun z : R => bern_gap_deriv_expr q z) x 1.
Proof.
move=> Hq0 Hq1 Hx0 Hx1.
rewrite /bern_gap_deriv_expr.
apply: derivableB.
- apply: derivableB.
  + exact: derivable_ln_div_const.
  + exact: derivable_ln_onem_div_const.
- apply: derivableM; first exact: derivable_cst.
  exact: derivable_sub_const.
Qed.

Lemma deriv_bern_gap_prime_expr (q x : R) :
  0 < q -> q < 1 -> 0 < x -> x < 1 ->
  (fun z : R => bern_gap_deriv_expr q z)^`()%classic x =
    x^-1 + (1 - x)^-1 - 4.
Proof.
move=> Hq0 Hq1 Hx0 Hx1.
rewrite /bern_gap_deriv_expr.
rewrite derive1E deriveB; last 2 first.
- apply: derivableB.
  + exact: derivable_ln_div_const.
  + exact: derivable_ln_onem_div_const.
- apply: derivableM; first exact: derivable_cst.
  exact: derivable_sub_const.
rewrite deriveB; last 2 first.
- exact: derivable_ln_div_const.
- exact: derivable_ln_onem_div_const.
rewrite -!derive1E.
rewrite deriv_ln_div_const // deriv_ln_onem_div_const //.
rewrite derive1Ml; last exact: derivable_sub_const.
rewrite deriv_sub_const.
ring.
Qed.

Lemma bern_gap_second_derivative_expr_nonneg (x : R) :
  0 < x -> x < 1 ->
  0 <= x^-1 + (1 - x)^-1 - 4.
Proof.
move=> Hx0 Hx1.
have H1x : 0 < 1 - x by lra.
have Hden : 0 < x * (1 - x) by rewrite mulr_gt0.
rewrite (_ : x^-1 + (1 - x)^-1 - 4 =
  ((2 * x - 1)^+2) / (x * (1 - x))).
  by rewrite divr_ge0 ?sqr_ge0 ?ltW.
field.
by rewrite !gt_eqF.
Qed.

Lemma bern_gap_deriv_expr_nondecreasing (q : R) :
  0 < q -> q < 1 ->
  {in `]0, 1[%R &, {homo bern_gap_deriv_expr q : x y / x <= y}}.
Proof.
move=> Hq0 Hq1.
apply: ger0_derive1_le_oo.
- move=> x Hx.
  move: Hx; rewrite in_itv /= => /andP[Hx0 Hx1].
  exact: (derivable_bern_gap_deriv_expr q x Hq0 Hq1 Hx0 Hx1).
- move=> x Hx.
  move: Hx; rewrite in_itv /= => /andP[Hx0 Hx1].
  rewrite deriv_bern_gap_prime_expr //.
  exact: bern_gap_second_derivative_expr_nonneg.
- rewrite -continuous_open_subspace //.
  apply: derivable_within_continuous=> x Hx.
  move: Hx; rewrite in_itv /= => /andP[Hx0 Hx1].
  exact: (derivable_bern_gap_deriv_expr q x Hq0 Hq1 Hx0 Hx1).
Qed.

Lemma bern_gap_diag (q : R) :
  0 < q -> q < 1 ->
  bern_gap q q = 0.
Proof.
move=> Hq0 Hq1.
rewrite /bern_gap /binary_kl subrr expr0n mulr0 subr0.
have Hqq : q / q = 1 by rewrite divff ?lt0r_neq0.
have H1qq : (1 - q) / (1 - q) = 1.
  by rewrite divff ?subr_eq0; lra.
by rewrite Hqq H1qq !ln1 !mulr0 addr0.
Qed.

Lemma deriv_bern_gap_diag (q : R) :
  0 < q -> q < 1 ->
  (fun z : R => bern_gap z q)^`()%classic q = 0.
Proof.
move=> Hq0 Hq1.
rewrite deriv_bern_gap // /bern_gap_deriv_expr.
have Hqq : q / q = 1 by rewrite divff ?lt0r_neq0.
have H1qq : (1 - q) / (1 - q) = 1.
  by rewrite divff ?subr_eq0; lra.
rewrite Hqq H1qq !ln1.
ring.
Qed.

Lemma bern_gap_deriv_expr_diag (q : R) :
  0 < q -> q < 1 ->
  bern_gap_deriv_expr q q = 0.
Proof.
move=> Hq0 Hq1.
rewrite /bern_gap_deriv_expr.
have Hqq : q / q = 1 by rewrite divff ?lt0r_neq0.
have H1qq : (1 - q) / (1 - q) = 1.
  by rewrite divff ?subr_eq0; lra.
rewrite Hqq H1qq !ln1.
ring.
Qed.

Lemma ln_lower_exp_ratio (r h : R) :
  0 < r ->
  r * h - sequences.expR h + 1 <= r * ln r - r + 1.
Proof.
move=> Hr.
have Hpos : 0 < sequences.expR h / r by rewrite divr_gt0 ?expR_gt0.
have Harg_gt : -1 < sequences.expR h / r - 1 by lra.
have Hln := le_ln1Dx Harg_gt.
have Harg : 1 + (sequences.expR h / r - 1) = sequences.expR h / r by ring.
rewrite Harg in Hln.
rewrite ln_div in Hln.
- rewrite (@expRK R h) in Hln.
  have Hscaled := ler_wpM2l (ltW Hr) Hln.
  have Hcancel : r * (sequences.expR h / r) = sequences.expR h.
    by rewrite mulrC divfK ?lt0r_neq0.
  have Hrhs : r * (sequences.expR h / r - 1) = sequences.expR h - r.
    by rewrite mulrBr Hcancel; ring.
  rewrite Hrhs in Hscaled.
  lra.
- by rewrite qualifE /= expR_gt0.
- by rewrite qualifE.
Qed.

Lemma kl_integrand_variational_pointwise (p q h : R) :
  0 <= p ->
  0 <= q ->
  (q = 0 -> p = 0) ->
  p * h - q * (sequences.expR h - 1) <=
    p * ln (p / q) - p + q.
Proof.
move=> Hp Hq Hac.
case Hq0: (q == 0).
  have Hp0 : p = 0 by exact: Hac (eqP Hq0).
  rewrite (eqP Hq0) Hp0 !mul0r sub0r addr0.
  have Hexp_nonneg : 0 <= sequences.expR h by exact: expR_ge0.
  lra.
case Hp0: (p == 0).
  rewrite (eqP Hp0) mul0r.
  have Hqpos : 0 < q by rewrite lt_def Hq Hq0.
  have Hexp_nonneg : 0 <= sequences.expR h by exact: expR_ge0.
  have Hprod : 0 <= q * sequences.expR h.
    exact: mulr_ge0 Hq Hexp_nonneg.
  lra.
have Hqpos : 0 < q by rewrite lt_def Hq Hq0.
have Hppos : 0 < p by rewrite lt_def Hp Hp0.
pose r := p / q.
have Hrpos : 0 < r by rewrite /r divr_gt0.
have Hineq := ln_lower_exp_ratio r h Hrpos.
have Hscaled := ler_wpM2l (ltW Hqpos) Hineq.
have HpE : p = q * r by rewrite /r mulrC divfK ?lt0r_neq0.
rewrite HpE.
have Hscaled_lhs :
    q * (r * h - sequences.expR h + 1) =
    q * r * h - q * (sequences.expR h - 1) by ring.
have Hscaled_rhs :
    q * (r * ln r - r + 1) =
    q * r * ln r - q * r + q by ring.
rewrite Hscaled_lhs Hscaled_rhs in Hscaled.
have Hratio : q * r / q = r.
  by rewrite [q * r]mulrC divfK ?lt0r_neq0.
rewrite Hratio.
exact: Hscaled.
Qed.

Lemma kl_variational_bound {T : choiceType} (P Q : {distr T / R})
    (h : T -> R) :
  finite_kl P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  summable (fun x => P x * h x) ->
  summable (fun x => Q x * (sequences.expR (h x) - 1)) ->
  sum (fun x => P x * h x) -
    sum (fun x => Q x * (sequences.expR (h x) - 1)) <= δ_KL P Q.
Proof.
move=> Hfin HP HQ HsummPh HsummQe.
have Hac := finite_kl_absolute_continuous P Q Hfin.
pose F := fun x : T =>
  P x * h x - Q x * (sequences.expR (h x) - 1).
pose G := fun x : T =>
  P x * ln (P x / Q x) - P x + Q x.
have HsummF : summable F.
  apply: (eq_summable
    (S1 := (fun x => P x * h x) \+
      (fun x => - (Q x * (sequences.expR (h x) - 1))))).
    by move=> x; rewrite /F /=; ring.
  apply: summableD; first exact: HsummPh.
  exact: summableN.
have HsummG : summable G.
  apply: (eq_summable
    (S1 := (fun x => P x * ln (P x / Q x)) \+
      ((fun x => - P x) \+ Q))).
    by move=> x; rewrite /G /=; ring.
  apply: summableD; first exact: finite_kl_summable.
  apply: summableD; first exact: summableN.
  exact: summable_mu.
have Hpoint x : F x <= G x.
  rewrite /F /G.
  exact: (kl_integrand_variational_pointwise
    (P x) (Q x) (h x) (ge0_mu P x) (ge0_mu Q x) (Hac x)).
have Hle := le_sum HsummF HsummG Hpoint.
rewrite /F in Hle.
rewrite (@sumD R T (fun x => P x * h x)
  (fun x => - (Q x * (sequences.expR (h x) - 1)))
  HsummPh (summableN HsummQe)) in Hle.
have HGsum :
    sum G =
    sum ((fun x => P x * ln (P x / Q x)) \+
      ((fun x : T => - P x) \+ Q)).
  apply/eq_sum=> x.
  by rewrite /G /=; ring.
rewrite HGsum in Hle.
have HsummNPQ : summable ((fun x : T => - P x) \+ Q).
  apply: summableD; first exact: summableN.
  exact: summable_mu.
rewrite (@sumD R T (fun x => P x * ln (P x / Q x))
  ((fun x : T => - P x) \+ Q)
  (finite_kl_summable P Q Hfin) HsummNPQ) in Hle.
rewrite (@sumD R T (fun x : T => - P x) Q
  (summableN (summable_mu P)) (summable_mu Q)) in Hle.
have HsumP : sum P = 1.
  by rewrite -(@psum_sum R T P) ?ge0_mu // -pr_predT HP.
have HsumQ : sum Q = 1.
  by rewrite -(@psum_sum R T Q) ?ge0_mu // -pr_predT HQ.
have HsumNegQe :
    sum (fun x : T => - (Q x * (sequences.expR (h x) - 1))) =
    - sum (fun x : T => Q x * (sequences.expR (h x) - 1)).
  exact: sumN.
rewrite HsumNegQe sumN HsumP HsumQ in Hle.
have Hdelta :
    δ_KL P Q = sum (fun x : T => P x * ln (P x / Q x)).
  rewrite /δ_KL /esp.
  apply/eq_sum=> x.
  by rewrite mulrC.
have Hcancel_mass :
    sum (fun x : T => P x * ln (P x / Q x)) + (-1 + 1) =
    sum (fun x : T => P x * ln (P x / Q x)) by ring.
rewrite Hcancel_mass in Hle.
rewrite Hdelta.
exact: Hle.
Qed.

Lemma summable_abs_diff {T : choiceType}
    (P Q : {distr T / R}) :
  summable (fun x => `|P x - Q x|).
Proof.
apply: le_summable.
- move=> x.
  apply/andP; split; first exact: normr_ge0.
  have Hnorm := ler_normB (P x) (Q x).
  have HPge : 0 <= P x := ge0_mu P x.
  have HQge : 0 <= Q x := ge0_mu Q x.
  rewrite (ger0_norm HPge) (ger0_norm HQge) in Hnorm.
  exact: Hnorm.
- apply: summableD; exact: summable_mu.
Qed.

Definition tv_sign {T : choiceType}
    (P Q : {distr T / R}) (x : T) : R :=
  if Q x <= P x then 1 else -1.

Lemma tv_sign_norm {T : choiceType}
    (P Q : {distr T / R}) x :
  `|tv_sign P Q x| = 1.
Proof.
rewrite /tv_sign; case: ifP=> _; first exact: normr1.
by rewrite normrN normr1.
Qed.

Lemma diff_mul_tv_sign_norm {T : choiceType}
    (P Q : {distr T / R}) x :
  (P x - Q x) * tv_sign P Q x = `|P x - Q x|.
Proof.
rewrite /tv_sign; case: ifP=> Hle.
- rewrite mulr1 ger0_norm //.
  lra.
- rewrite mulrN mulr1 ltr0_norm; first by ring.
  lra.
Qed.

Lemma summable_mu_tv_sign {T : choiceType}
    (P Q M : {distr T / R}) :
  summable (fun x => M x * tv_sign P Q x).
Proof.
apply/summable_abs.
apply: (eq_summable (S1 := M)); last exact: summable_mu.
move=> x /=.
rewrite normrM tv_sign_norm (ger0_norm (ge0_mu M x)).
by rewrite mulr1.
Qed.

Lemma tv_sign_expectation_gap {T : choiceType}
    (P Q : {distr T / R}) :
  sum (fun x => P x * tv_sign P Q x) -
    sum (fun x => Q x * tv_sign P Q x) =
  2 * total_variation P Q.
Proof.
pose s := tv_sign P Q.
have HsP : summable (fun x => P x * s x).
  exact: summable_mu_tv_sign.
have HsQ : summable (fun x => Q x * s x).
  exact: summable_mu_tv_sign.
have Hdiff :
    sum (fun x => P x * s x) - sum (fun x => Q x * s x) =
    sum (fun x => (P x - Q x) * s x).
  rewrite -sumN -(@sumD R T (fun x => P x * s x)
    (fun x => - (Q x * s x)) HsP (summableN HsQ)).
  apply/eq_sum=> x; rewrite /s /=; ring.
rewrite Hdiff.
have Hnorm :
    sum (fun x => (P x - Q x) * s x) =
    sum (fun x => `|P x - Q x|).
  apply/eq_sum=> x; exact: diff_mul_tv_sign_norm.
rewrite Hnorm /total_variation.
lra.
Qed.

Definition tv_event {T : choiceType}
    (P Q : {distr T / R}) : pred T :=
  [pred x | Q x <= P x].

Lemma tv_signE {T : choiceType}
    (P Q : {distr T / R}) x :
  tv_sign P Q x = 2 * (tv_event P Q x)%:R - 1.
Proof.
rewrite /tv_sign /tv_event /=.
case H: (Q x <= P x); rewrite ?mulr1 ?mulr0; ring.
Qed.

Lemma sum_pr_indicator {T : choiceType}
    (M : {distr T / R}) (A : pred T) :
  sum (fun x => (A x)%:R * M x) = \P_[M] A.
Proof.
by rewrite /pr -psum_sum // => x; rewrite mulr_ge0 ?ler0n ?ge0_mu.
Qed.

Lemma summable_pr_scaled {T : choiceType}
    (M : {distr T / R}) (A : pred T) (c : R) :
  summable (c \*o (fun x => (A x)%:R * M x)).
Proof.
apply: summableZ.
exact: summable_pr.
Qed.

Lemma tv_sign_expectation_pr {T : choiceType}
    (P Q M : {distr T / R}) :
  sum (fun x => M x * tv_sign P Q x) =
  2 * \P_[M] (tv_event P Q) - dweight M.
Proof.
pose A := tv_event P Q.
rewrite (eq_sum (F2 := fun x => 2 * ((A x)%:R * M x) - M x)); last first.
  move=> x.
  rewrite tv_signE /A mulrBr mulr1.
  ring.
rewrite (@sumD R T (fun x => 2 * ((A x)%:R * M x)) (fun x => - M x)).
- rewrite sumN.
  rewrite (@sumZ R T (fun x => (A x)%:R * M x) 2) sum_pr_indicator.
  have HsumM : sum M = dweight M.
    by rewrite -psum_sum ?ge0_mu // -pr_predT.
  rewrite HsumM.
  ring.
- change (summable (2 \*o (fun x => (A x)%:R * M x))).
  apply: summableZ.
  exact: summable_pr.
- exact: summableN; exact: summable_mu.
Qed.

Lemma tv_event_pr_gap {T : choiceType}
    (P Q : {distr T / R}) :
  dweight P = 1 ->
  dweight Q = 1 ->
  \P_[P] (tv_event P Q) - \P_[Q] (tv_event P Q) =
  total_variation P Q.
Proof.
move=> HP HQ.
have Hgap := tv_sign_expectation_gap P Q.
rewrite !tv_sign_expectation_pr HP HQ in Hgap.
lra.
Qed.

Lemma pr_bound {T : choiceType} (M : {distr T / R}) (A : pred T) :
  dweight M = 1 ->
  0 <= \P_[M] A /\ \P_[M] A <= 1.
Proof.
move=> HM.
split; first exact: ge0_pr.
exact: le1_pr.
Qed.

Lemma event_binary_absolute_continuous {T : choiceType}
    (P Q : {distr T / R}) (A : pred T) :
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  (\P_[Q] A = 0 -> \P_[P] A = 0) /\
  (1 - \P_[Q] A = 0 -> 1 - \P_[P] A = 0).
Proof.
move=> Hac HP HQ.
have Hzero B : \P_[Q] B = 0 -> \P_[P] B = 0.
  move=> HQB0.
  rewrite /pr.
  apply: psum_eq0 => x.
  case Hx: (B x); last by rewrite mul0r.
  rewrite mul1r.
  exact: Hac (pr_eq0 HQB0 Hx).
split; first exact: Hzero.
move=> HQAc0.
have HQc0 : \P_[Q] (predC A) = 0.
  rewrite pr_predC HQ.
  lra.
have HPc0 := Hzero (predC A) HQc0.
move: HPc0.
rewrite pr_predC HP.
lra.
Qed.

Lemma dmargin_event_true {T : choiceType}
    (P : {distr T / R}) (A : pred T) :
  dmargin A P true = \P_[P] A.
Proof.
rewrite pr_pred1 pr_dmargin.
apply/eq_pr=> x.
by rewrite /in_mem /=; case: (A x).
Qed.

Lemma dmargin_event_false {T : choiceType}
    (P : {distr T / R}) (A : pred T) :
  dweight P = 1 ->
  dmargin A P false = 1 - \P_[P] A.
Proof.
move=> HP.
rewrite pr_pred1 pr_dmargin.
transitivity (\P_[P] (predC A)).
  apply/eq_pr=> x.
  by rewrite /in_mem /=; case: (A x).
by rewrite pr_predC HP.
Qed.

Lemma binary_kl_dmargin_event {T : choiceType}
    (P Q : {distr T / R}) (A : pred T) :
  dweight P = 1 ->
  dweight Q = 1 ->
  δ_KL (dmargin A P) (dmargin A Q) =
  binary_kl (\P_[P] A) (\P_[Q] A).
Proof.
move=> HP HQ.
rewrite /δ_KL /esp.
rewrite (sum_finseq (r := [:: true; false])); last 2 first.
- by [].
- by move=> b _; case: b.
rewrite big_cons big_cons big_nil addr0.
rewrite !dmargin_event_true !dmargin_event_false //.
rewrite /binary_kl.
ring.
Qed.

Lemma binary_event_data_processing {T : choiceType}
    (P Q : {distr T / R}) (A : pred T) :
  finite_kl P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  binary_kl (\P_[P] A) (\P_[Q] A) <= δ_KL P Q.
Proof.
move=> Hfin HP HQ.
have Hac := finite_kl_absolute_continuous P Q Hfin.
have Hkl := finite_kl_summable P Q Hfin.
pose pA := fun x : T => (A x)%:R * P x.
pose qA := fun x : T => (A x)%:R * Q x.
pose pC := fun x : T => (predC A x)%:R * P x.
pose qC := fun x : T => (predC A x)%:R * Q x.
pose i := fun x : T => P x * ln (P x / Q x).
pose iA := fun x : T => pA x * ln (pA x / qA x).
pose iC := fun x : T => pC x * ln (pC x / qC x).
have HpA x : 0 <= pA x by rewrite /pA mulr_ge0 ?ler0n ?ge0_mu.
have HqA x : 0 <= qA x by rewrite /qA mulr_ge0 ?ler0n ?ge0_mu.
have HpC x : 0 <= pC x by rewrite /pC mulr_ge0 ?ler0n ?ge0_mu.
have HqC x : 0 <= qC x by rewrite /qC mulr_ge0 ?ler0n ?ge0_mu.
have Hsm_pA : summable pA by rewrite /pA; exact: summable_pr.
have Hsm_qA : summable qA by rewrite /qA; exact: summable_pr.
have Hsm_pC : summable pC by rewrite /pC; exact: summable_pr.
have Hsm_qC : summable qC by rewrite /qC; exact: summable_pr.
have Hsm_iA : summable iA.
  apply: (eq_summable
    (S1 := fun x : T => (A x)%:R * i x)).
    move=> x.
    rewrite /iA /i /pA /qA.
    by case: (A x); rewrite ?mul1r ?mul0r.
  exact: summable_condl.
have Hsm_iC : summable iC.
  apply: (eq_summable
    (S1 := fun x : T => (predC A x)%:R * i x)).
    move=> x.
    rewrite /iC /i /pC /qC.
    by case: (predC A x); rewrite ?mul1r ?mul0r.
  exact: summable_condl.
have HacA x : qA x = 0 -> pA x = 0.
  rewrite /pA /qA.
  case: (A x); last by rewrite !mul0r.
  by rewrite !mul1r; exact: Hac x.
have HacC x : qC x = 0 -> pC x = 0.
  rewrite /pC /qC.
  case: (predC A x); last by rewrite !mul0r.
  by rewrite !mul1r; exact: Hac x.
have HlogA :=
  log_sum_inequality_finite pA qA HpA HqA
    Hsm_pA Hsm_qA Hsm_iA HacA.
have HlogC :=
  log_sum_inequality_finite pC qC HpC HqC
    Hsm_pC Hsm_qC Hsm_iC HacC.
have HpAE : psum pA = \P_[P] A by rewrite /pA /pr.
have HqAE : psum qA = \P_[Q] A by rewrite /qA /pr.
have HpCE : psum pC = 1 - \P_[P] A.
  change (\P_[P] (predC A) = 1 - \P_[P] A).
  by rewrite pr_predC HP.
have HqCE : psum qC = 1 - \P_[Q] A.
  change (\P_[Q] (predC A) = 1 - \P_[Q] A).
  by rewrite pr_predC HQ.
have Hbinary :
    binary_kl (\P_[P] A) (\P_[Q] A) <= sum iA + sum iC.
  apply: (le_trans _ (lerD HlogA HlogC)).
  rewrite /binary_kl HpAE HqAE HpCE HqCE.
  exact: lexx.
rewrite /δ_KL /esp.
rewrite (eq_sum (F2 := i)); last by move=> x; rewrite /i mulrC.
have Hrhs : sum i = sum iA + sum iC.
  rewrite (sumID A Hkl).
  congr (_ + _).
  - apply/eq_sum=> x.
    rewrite /iA /i /pA /qA.
    by case: (A x); rewrite ?mul1r ?mul0r.
  - apply/eq_sum=> x.
    rewrite /iC /i /pC /qC.
    by rewrite /predC /=; case: (A x); rewrite ?mul1r ?mul0r.
by rewrite Hrhs.
Qed.

Lemma bern_gap_nonneg_right_of_diag (p q : R) :
  0 < q -> q < 1 ->
  q <= p -> p < 1 ->
  0 <= bern_gap p q.
Proof.
move=> Hq0 Hq1 Hqp Hp1.
case Hpq_eq: (p == q).
  have -> : p = q by move/eqP: Hpq_eq.
  have Hdiag : bern_gap q q = 0 by exact: bern_gap_diag.
  rewrite Hdiag.
  exact: (lexx (0 : R)).
have Hqp_lt : q < p.
  rewrite lt_def Hqp /=.
  by rewrite Hpq_eq.
have Hp0 : 0 < p by lra.
have Hcont :
    continuous (from_subspace
      [set` `[q, p]%R] (fun z : R => bern_gap z q)).
  apply: derivable_within_continuous=> x Hx.
  move: Hx; rewrite in_itv /= => /andP[Hqx Hxp].
  have Hx0 : 0 < x by lra.
  have Hx1 : x < 1 by lra.
  exact: (derivable_bern_gap q x Hq0 Hq1 Hx0 Hx1).
have Hisder :
    forall x : R, x \in `]q, p[%R ->
    is_derive x 1 (fun z : R => bern_gap z q) (bern_gap_deriv_expr q x).
  move=> x Hx.
  move: Hx; rewrite in_itv /= => /andP[Hqx Hxp].
  have Hx0 : 0 < x by lra.
  have Hx1 : x < 1 by lra.
  exact: (is_derive_bern_gap q x Hq0 Hq1 Hx0 Hx1).
have [c Hc Hmvt] :=
  @MVT_segment R (fun z : R => bern_gap z q)
    (bern_gap_deriv_expr q) q p Hqp Hisder Hcont.
move: Hc; rewrite in_itv /= => /andP[Hqc Hcp].
have Hc0 : 0 < c by lra.
have Hc1 : c < 1 by lra.
have HqInt : q \in `]0, 1[%R.
  by rewrite in_itv /=; apply/andP; split.
have HcInt : c \in `]0, 1[%R.
  by rewrite in_itv /=; apply/andP; split.
have Hmono := bern_gap_deriv_expr_nondecreasing q Hq0 Hq1.
have Hder_ge :
    0 <= bern_gap_deriv_expr q c.
  rewrite -(bern_gap_deriv_expr_diag q Hq0 Hq1).
  exact: Hmono.
have Hprod : 0 <= bern_gap_deriv_expr q c * (p - q).
  by rewrite mulr_ge0 // subr_ge0.
have Hdiag := bern_gap_diag q Hq0 Hq1.
rewrite Hdiag in Hmvt.
lra.
Qed.

Lemma bern_gap_nonneg_left_of_diag (p q : R) :
  0 < p ->
  p <= q -> q < 1 ->
  0 <= bern_gap p q.
Proof.
move=> Hp0 Hpq Hq1.
case Hpq_eq: (p == q).
  have Hp_eq_q : p = q by move/eqP: Hpq_eq.
  have Hq0diag : 0 < q by lra.
  rewrite Hp_eq_q.
  have Hdiag : bern_gap q q = 0 by exact: bern_gap_diag.
  rewrite Hdiag.
    exact: (lexx (0 : R)).
have Hpq_lt : p < q.
  rewrite lt_def Hpq /=.
  by rewrite eq_sym Hpq_eq.
have Hq0 : 0 < q by lra.
have Hp1 : p < 1 by lra.
have Hcont :
    continuous (from_subspace
      [set` `[p, q]%R] (fun z : R => bern_gap z q)).
  apply: derivable_within_continuous=> x Hx.
  move: Hx; rewrite in_itv /= => /andP[Hpx Hxq].
  have Hx0 : 0 < x by lra.
  have Hx1 : x < 1 by lra.
  exact: (derivable_bern_gap q x Hq0 Hq1 Hx0 Hx1).
have Hisder :
    forall x : R, x \in `]p, q[%R ->
    is_derive x 1 (fun z : R => bern_gap z q) (bern_gap_deriv_expr q x).
  move=> x Hx.
  move: Hx; rewrite in_itv /= => /andP[Hpx Hxq].
  have Hx0 : 0 < x by lra.
  have Hx1 : x < 1 by lra.
  exact: (is_derive_bern_gap q x Hq0 Hq1 Hx0 Hx1).
have [c Hc Hmvt] :=
  @MVT_segment R (fun z : R => bern_gap z q)
    (bern_gap_deriv_expr q) p q Hpq Hisder Hcont.
move: Hc; rewrite in_itv /= => /andP[Hpc Hcq].
have Hc0 : 0 < c by lra.
have Hc1 : c < 1 by lra.
have HqInt : q \in `]0, 1[%R.
  by rewrite in_itv /=; apply/andP; split.
have HcInt : c \in `]0, 1[%R.
  by rewrite in_itv /=; apply/andP; split.
have Hmono := bern_gap_deriv_expr_nondecreasing q Hq0 Hq1.
have Hder_le :
    bern_gap_deriv_expr q c <= 0.
  rewrite -(bern_gap_deriv_expr_diag q Hq0 Hq1).
  exact: Hmono.
have Hprod : bern_gap_deriv_expr q c * (q - p) <= 0.
  rewrite mulr_le0_ge0 //.
  by rewrite subr_ge0.
have Hdiag := bern_gap_diag q Hq0 Hq1.
rewrite Hdiag in Hmvt.
lra.
Qed.

Lemma binary_pinsker_quadratic_interior (p q : R) :
  0 < p -> p < 1 ->
  0 < q -> q < 1 ->
  0 <= bern_gap p q.
Proof.
move=> Hp0 Hp1 Hq0 Hq1.
case: (lerP p q)=> Hpq.
- exact: (bern_gap_nonneg_left_of_diag p q Hp0 Hpq Hq1).
- exact: (bern_gap_nonneg_right_of_diag p q Hq0 Hq1 (ltW Hpq) Hp1).
Qed.

Definition ln_onem_quad_gap (x : R) :=
  - ln ((1 - x) / (1 - 0)) - 2 * (x - 0)^+2.

Lemma derivable_ln_onem_quad_gap (x : R) :
  x < 1 ->
  derivable ln_onem_quad_gap x 1.
Proof.
move=> Hx1.
rewrite /ln_onem_quad_gap.
apply: derivableB.
- apply: derivableN.
  exact: (derivable_ln_onem_div_const 0 x _ Hx1).
- apply: derivableM; first exact: derivable_cst.
  exact: derivable_sq_shift.
Qed.

Lemma deriv_ln_onem_quad_gap (x : R) :
  x < 1 ->
  (ln_onem_quad_gap)^`()%classic x = (1 - x)^-1 - 4 * x.
Proof.
move=> Hx1.
rewrite /ln_onem_quad_gap.
rewrite derive1E deriveB; last 2 first.
- apply: derivableN.
  exact: (derivable_ln_onem_div_const 0 x _ Hx1).
- apply: derivableM; first exact: derivable_cst.
  exact: derivable_sq_shift.
rewrite deriveN; last exact: (derivable_ln_onem_div_const 0 x _ Hx1).
rewrite -derive1E deriv_ln_onem_div_const //.
rewrite deriveM; last 2 first.
- exact: derivable_cst.
- exact: derivable_sq_shift.
rewrite derive_cst.
rewrite -derive1E.
rewrite deriv_sq_shift.
rewrite scaler0 scaler_nat mulr_natl subr0.
ring.
Qed.

Lemma deriv_ln_onem_quad_gap_nonneg (x : R) :
  x < 1 ->
  0 <= (1 - x)^-1 - 4 * x.
Proof.
move=> Hx1.
have Hden : 0 < 1 - x by lra.
rewrite (_ : (1 - x)^-1 - 4 * x =
  ((2 * x - 1)^+2) / (1 - x)).
  by rewrite divr_ge0 ?sqr_ge0 ?ltW.
field.
by rewrite subr_eq0; lra.
Qed.

Lemma ln_onem_quad_gap_nondecreasing :
  {in `]-1, 1[%R &, {homo ln_onem_quad_gap : x y / x <= y}}.
Proof.
apply: ger0_derive1_le_oo.
- move=> x Hx.
  move: Hx; rewrite in_itv /= => /andP[_ Hx1].
  exact: derivable_ln_onem_quad_gap.
- move=> x Hx.
  move: Hx; rewrite in_itv /= => /andP[_ Hx1].
  rewrite deriv_ln_onem_quad_gap //.
  exact: deriv_ln_onem_quad_gap_nonneg.
- rewrite -continuous_open_subspace //.
  apply: derivable_within_continuous=> x Hx.
  move: Hx; rewrite in_itv /= => /andP[_ Hx1].
  exact: derivable_ln_onem_quad_gap.
Qed.

Lemma ln_inv_onem_quadratic (q : R) :
  0 < q -> q < 1 ->
  2 * q^+2 <= ln (1 / (1 - q)).
Proof.
move=> Hq0 Hq1.
have H0 : ((0 : R) \in `]-1, 1[%R)%bool.
  by rewrite in_itv /=; apply/andP; split; lra.
have Hq : (q \in `]-1, 1[%R)%bool.
  by rewrite in_itv /=; apply/andP; split; lra.
have Hmono := ln_onem_quad_gap_nondecreasing 0 q H0 Hq (ltW Hq0).
have Hgap0 : ln_onem_quad_gap 0 = 0.
  rewrite /ln_onem_quad_gap !subr0 expr0n mulr0 subr0.
  by rewrite divff ?oner_eq0 // ln1 oppr0.
have Hgapq :
    ln_onem_quad_gap q =
    ln (1 / (1 - q)) - 2 * q^+2.
  rewrite /ln_onem_quad_gap subr0.
  have Hln : ln (1 / (1 - q)) = - ln ((1 - q) / (1 - 0)).
    rewrite ln_div ?qualifE /=; last first.
    - by rewrite subr_gt0.
    - by rewrite ltr01.
    rewrite ln1.
    have -> : (1 - q) / (1 - 0) = 1 - q by rewrite subr0 divr1.
    ring.
  rewrite Hln.
  rewrite !subr0 !divr1.
  lra.
rewrite Hgap0 Hgapq in Hmono.
lra.
Qed.

Lemma ln_inv_quadratic (q : R) :
  0 < q -> q < 1 ->
  2 * (1 - q)^+2 <= ln (1 / q).
Proof.
move=> Hq0 Hq1.
have H1q0 : 0 < 1 - q by lra.
have H1q1 : 1 - q < 1 by lra.
have H := ln_inv_onem_quadratic (1 - q) H1q0 H1q1.
have Hden : 1 - (1 - q) = q by ring.
  rewrite Hden in H.
exact: H.
Qed.

Lemma binary_pinsker_quadratic_left_boundary (q : R) :
  0 < q -> q < 1 ->
  0 <= bern_gap 0 q.
Proof.
move=> Hq0 Hq1.
have Hln := ln_inv_onem_quadratic q Hq0 Hq1.
rewrite /bern_gap /binary_kl.
rewrite !subr0 mul0r add0r mul1r.
have Hsq : (0 - q)^+2 = q^+2 by ring.
rewrite Hsq.
lra.
Qed.

Lemma binary_pinsker_quadratic_right_boundary (q : R) :
  0 < q -> q < 1 ->
  0 <= bern_gap 1 q.
Proof.
move=> Hq0 Hq1.
have Hln := ln_inv_quadratic q Hq0 Hq1.
rewrite /bern_gap /binary_kl.
rewrite subrr mul0r addr0 mul1r.
lra.
Qed.

Lemma binary_pinsker_quadratic (p q : R) :
  0 <= p -> p <= 1 ->
  0 <= q -> q <= 1 ->
  (q = 0 -> p = 0) ->
  (1 - q = 0 -> 1 - p = 0) ->
  2 * (p - q)^+2 <= binary_kl p q.
Proof.
move=> Hp0 Hp1 Hq0 Hq1 Hac0 Hac1.
have Hgap : 0 <= bern_gap p q.
  case Hq0b: (q == 0).
    have Hq0eq : q = 0 by exact/eqP.
    have Hp0eq : p = 0 by exact: Hac0 Hq0eq.
    rewrite Hq0eq Hp0eq.
    rewrite /bern_gap /binary_kl !subr0 !mul0r.
    rewrite divff ?oner_eq0 // ln1 mul1r addr0 expr0n mulr0 subr0.
    exact: lexx.
  case Hq1b: (1 - q == 0).
    have Hq1eq : 1 - q = 0 by exact/eqP.
    have Hp1eq : 1 - p = 0 by exact: Hac1 Hq1eq.
    have -> : q = 1 by lra.
    have -> : p = 1 by lra.
    rewrite /bern_gap /binary_kl !subrr !mul0r addr0.
    rewrite divff ?oner_eq0 // ln1 mul1r expr0n mulr0 subr0.
    exact: lexx.
  have Hq0lt : 0 < q by rewrite lt_def Hq0 Hq0b.
  have Hq1lt : q < 1.
    have H1q : 0 < 1 - q by rewrite lt_def ?Hq1b //; lra.
    lra.
  case Hp0b: (p == 0).
    have -> : p = 0 by exact/eqP.
    exact: binary_pinsker_quadratic_left_boundary.
  case Hp1b: (1 - p == 0).
    have Hp1eq : 1 - p = 0 by exact/eqP.
    have -> : p = 1 by lra.
    exact: binary_pinsker_quadratic_right_boundary.
  have Hp0lt : 0 < p by rewrite lt_def Hp0 Hp0b.
  have Hp1lt : p < 1.
    have H1p : 0 < 1 - p by rewrite lt_def ?Hp1b //; lra.
    lra.
  exact: binary_pinsker_quadratic_interior.
move: Hgap.
rewrite /bern_gap.
lra.
Qed.

Lemma total_variation_nonneg {T : choiceType}
    (P Q : {distr T / R}) :
  0 <= total_variation P Q.
Proof.
rewrite /total_variation.
apply: mulr_ge0; first by lra.
rewrite -psum_sum; first exact: ge0_psum.
move=> x; exact: normr_ge0.
Qed.

Lemma pinsker_from_quadratic (tv kl : R) :
  0 <= tv ->
  2 * tv ^+ 2 <= kl ->
  tv <= Num.sqrt (kl / 2).
Proof.
move=> Htv Hquad.
have Htv_sqrt : tv = Num.sqrt (tv ^+ 2).
  by rewrite sqrtr_sqr ger0_norm.
rewrite Htv_sqrt.
apply: ler_wsqrtr.
lra.
Qed.

Lemma pinsker_quadratic_bound {T : choiceType} (P Q : {distr T / R}) :
  finite_kl P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  2 * total_variation P Q ^+ 2 <= δ_KL P Q.
Proof.
move=> Hfin HP HQ.
pose A := tv_event P Q.
pose p := \P_[P] A.
pose q := \P_[Q] A.
have [Hp0 Hp1] := pr_bound P A HP.
have [Hq0 Hq1] := pr_bound Q A HQ.
have Hac := finite_kl_absolute_continuous P Q Hfin.
have [Hac0 Hac1] := event_binary_absolute_continuous P Q A Hac HP HQ.
have Hbinary :
    2 * (p - q)^+2 <= binary_kl p q.
  exact: binary_pinsker_quadratic.
have Hdp :
    binary_kl p q <= δ_KL P Q.
  exact: binary_event_data_processing.
have Hgap : p - q = total_variation P Q.
  by rewrite /p /q /A tv_event_pr_gap.
rewrite -Hgap.
exact: le_trans Hbinary Hdp.
Qed.

Lemma pinsker {T : choiceType} (P Q : {distr T / R}) :
  finite_kl P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  total_variation P Q <= Num.sqrt (δ_KL P Q / 2).
Proof.
move=> Hfin HP HQ.
exact: pinsker_from_quadratic (total_variation P Q) (δ_KL P Q)
  (total_variation_nonneg P Q)
  (pinsker_quadratic_bound P Q Hfin HP HQ).
Qed.

End KL_Pinsker.
