Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format,-notation-incompatible-prefix".
From mathcomp Require Import all_boot all_order all_algebra all_reals distr boolp.
From mathcomp Require Import realseq realsum exp interval_inference convex xfinmap.
From mathcomp Require Import lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format,notation-incompatible-prefix".
From mathcomp.algebra_tactics Require Import ring.

From Mending.LibExtras.MathcompExtras Require Import DistrExtras RealSumExtras.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.
Local Open Scope convex_scope.

Section KL_Core.

Context {R: realType}.

Definition δ_KL {T : choiceType} (P Q : {distr T / R}) : R :=
  \E_[P] (fun x => ln (P x / Q x)).

Definition absolute_continuous {T : choiceType} (P Q : {distr T / R}) : Prop :=
  forall x, Q x = 0 -> P x = 0.

(* Division and [ln] are totalized, so summability alone would not rule out
   support-mismatch cases where [Q x = 0] and [P x > 0]. *)
Definition finite_kl {T : choiceType} (P Q : {distr T / R}) : Prop :=
  absolute_continuous P Q /\
  summable (fun x => P x * ln (P x / Q x)).

Lemma finite_kl_absolute_continuous {T : choiceType}
    (P Q : {distr T / R}) :
  finite_kl P Q -> absolute_continuous P Q.
Proof. by case. Qed.

Lemma finite_kl_summable {T : choiceType}
    (P Q : {distr T / R}) :
  finite_kl P Q -> summable (fun x => P x * ln (P x / Q x)).
Proof. by case. Qed.

Lemma finite_kl_refl {T : choiceType} (P : {distr T / R}) :
  finite_kl P P.
Proof.
split; first by move=> x ->.
apply: (eq_summable (S1 := fun _ : T => 0)); last exact: summable0.
move=> x.
case Px0: (P x == 0).
  by rewrite (eqP Px0) mul0r.
have HPx : P x != 0 by rewrite Px0.
have -> : P x / P x = 1 by rewrite divff ?unitfE ?HPx.
by rewrite ln1 mulr0.
Qed.

Lemma finite_kl_ext {T : choiceType}
    (P P' Q Q' : {distr T / R}) :
  P =1 P' ->
  Q =1 Q' ->
  finite_kl P Q ->
  finite_kl P' Q'.
Proof.
move=> HP HQ [Hac Hsumm].
split.
- move=> x HQx0.
  rewrite -HP.
  apply: Hac.
  by rewrite HQ.
- apply: (eq_summable (S1 := fun x => P x * ln (P x / Q x))).
    by move=> x; rewrite -HP -HQ.
  exact: Hsumm.
Qed.

Lemma finite_kl_left_dnull {T : choiceType} (P Q : {distr T / R}) :
  P =1 dnull ->
  finite_kl P Q.
Proof.
move=> HP.
split.
- by move=> x _; rewrite HP dnullE.
- apply: (eq_summable (S1 := fun _ : T => 0)); last exact: summable0.
  by move=> x; rewrite HP dnullE mul0r.
Qed.

Lemma kl_ext {T : choiceType} (P P' Q Q' : {distr T / R}) :
  P =1 P' ->
  Q =1 Q' ->
  δ_KL P Q = δ_KL P' Q'.
Proof.
move=> HP HQ.
rewrite /δ_KL.
rewrite (expectation_distr_ext P P' _ HP).
apply: expectation_ext=> x.
by rewrite -HP -HQ.
Qed.

Lemma kl_left_dnull {T : choiceType} (P Q : {distr T / R}) :
  P =1 dnull ->
  δ_KL P Q = 0.
Proof.
move=> HP.
rewrite /δ_KL.
rewrite (expectation_distr_ext P dnull _ HP).
exact: expectation_dnull.
Qed.

Lemma kl_self {T : choiceType} (P : {distr T / R}) :
  δ_KL P P = 0.
Proof.
rewrite /δ_KL /esp.
rewrite (eq_sum (F2 := fun _ : T => 0)).
  exact: sum0.
move=> x.
case Px0: (P x == 0).
  by rewrite (eqP Px0) mulr0.
have HPx : P x != 0 by rewrite Px0.
have -> : P x / P x = 1 by rewrite divff ?unitfE ?HPx.
by rewrite ln1 mul0r.
Qed.

Lemma absolute_continuous_positive {T : choiceType}
    (P Q : {distr T / R}) (x : T) :
  absolute_continuous P Q ->
  0 < P x -> 0 < Q x.
Proof.
move=> Hac HPx.
rewrite lt_def ge0_mu andbT.
apply/negP=> /eqP HQx0.
have HPx0 := Hac x HQx0.
by rewrite HPx0 ltxx in HPx.
Qed.

Lemma kl_integrand_geNq (p q : R) :
  0 <= p ->
  0 <= q ->
  (q = 0 -> p = 0) ->
  - q <= p * ln (p / q).
Proof.
move=> Hp Hq Hac.
case q0: (q == 0).
  move/eqP: q0=> qE.
  have pE := Hac qE.
  by rewrite qE pE mul0r oppr0.
case p0: (p == 0).
  rewrite (eqP p0) mul0r.
  by rewrite oppr_le0.
have Hqpos : 0 < q by rewrite lt_def Hq q0.
have Hppos : 0 < p by rewrite lt_def Hp p0.
pose r := p / q.
have Hrpos : 0 < r by rewrite /r divr_gt0.
have Hinvpos : 0 < r^-1 by rewrite invr_gt0.
have Harg : -1 < r^-1 - 1 by lra.
have Hln := le_ln1Dx Harg.
have Hsum : 1 + (r^-1 - 1) = r^-1 by ring.
rewrite Hsum in Hln.
rewrite lnV in Hln; last by rewrite qualifE.
have Hmul := ler_wpM2l (ltW Hrpos) Hln.
rewrite mulrN mulrBr mulrV ?unitfE ?lt0r_neq0 // mulr1 in Hmul.
have Hrminus : r - 1 <= r * ln r by lra.
have Hbasic : -1 <= r * ln r by lra.
have HpE : p = q * r by rewrite /r mulrC divfK ?lt0r_neq0.
change (- q <= p * ln r).
rewrite HpE -mulrA -mulrN1.
by apply: ler_wpM2l; [exact: ltW Hqpos | exact: Hbasic].
Qed.

Lemma kl_integrand_fneg_le_q (p q : R) :
  0 <= p ->
  0 <= q ->
  (q = 0 -> p = 0) ->
  `|Num.min 0 (p * ln (p / q))| <= q.
Proof.
move=> Hp Hq Hac.
have Hlower := kl_integrand_geNq p q Hp Hq Hac.
case: (leP 0 (p * ln (p / q)))=> Hkl.
  by rewrite normr0.
rewrite ltr0_norm //.
by rewrite -lerN2 opprK.
Qed.

Lemma summable_fneg_kl_integrand {T : choiceType}
    (P Q : {distr T / R}) :
  absolute_continuous P Q ->
  summable (fneg (fun x => P x * ln (P x / Q x))).
Proof.
move=> Hac.
apply: (le_summable (F2 := Q)); last exact: summable_mu.
move=> x; apply/andP; split; first exact: ge0_fneg.
rewrite /fneg.
exact: (kl_integrand_fneg_le_q (P x) (Q x)
  (ge0_mu P x) (ge0_mu Q x) (Hac x)).
Qed.

Lemma summable_fiber_psum {T U : choiceType}
    (f : T -> U) (S : T -> R) :
  (forall x, 0 <= S x) ->
  summable S ->
  summable (fun y => psum (fun x => (f x == y)%:R * S x)).
Proof.
move=> HS smS.
apply/summable_seqP; exists (psum S); first exact: ge0_psum.
move=> J uqJ.
rewrite (eq_bigr (fun y => psum (fun x => (f x == y)%:R * S x)));
  last by move=> y _; rewrite ger0_norm ?ge0_psum.
rewrite (@psum_bigop R T U (fun y x => (f x == y)%:R * S x) predT J).
- apply: le_psum; last exact: smS.
  move=> x; apply/andP; split.
  + apply: sumr_ge0=> y _.
    by rewrite mulr_ge0 ?HS ?ler0n.
  + case HfxJ : (f x \in J).
    * rewrite (bigD1_seq (f x) HfxJ uqJ) /= eqxx mul1r.
      rewrite big1 ?addr0 // => y.
      by rewrite eq_sym=> /negbTE ->; rewrite mul0r.
    * rewrite big_seq_cond big1 ?mul0r // => y /andP[Hy _].
      case Hfy : (f x == y); last by rewrite mul0r.
      by move: HfxJ; rewrite (eqP Hfy) Hy.
- by move=> y x; rewrite mulr_ge0 ?HS ?ler0n.
- by move=> y; exact: (@summable_condl R T S (fun x => f x == y) smS).
Qed.

Lemma summable_from_fpos_fneg {T : choiceType} (F : T -> R) :
  summable (fpos F) ->
  summable (fneg F) ->
  summable F.
Proof.
move=> Hpos Hneg.
apply: (eq_summable (S1 := fun x => fpos F x - fneg F x)).
  by move=> x; rewrite fposBfneg.
apply: summableD; first exact: Hpos.
exact: summableN.
Qed.

Lemma summable_kernel_weighted_pair_nonneg {T U : choiceType}
    (S : T -> R) (K : T -> {distr U / R}) :
  (forall x, 0 <= S x) ->
  summable S ->
  summable (fun xy : T * U => K xy.1 xy.2 * S xy.1).
Proof.
move=> HS smS.
exists (psum S)=> J.
rewrite (@big_fset_seq R 0 +%R (T * U)%type J
  (fun xy : T * U => `|K xy.1 xy.2 * S xy.1|)).
rewrite (@partition_big_imfset R 0 +%R _ _ fst J
  (fun xy : T * U => `|K xy.1 xy.2 * S xy.1|)).
pose X := [fset xy.1 | xy in J]%fset.
have HX := gerfin_psum X smS.
rewrite (@big_fset_seq R 0 +%R T X (fun x => `|S x|)) in HX.
apply: (le_trans _ HX).
apply: ler_sum=> x _.
rewrite ger0_norm ?HS //.
set F := [fset xy in J | xy.1 == x]%fset.
have Hfiber :
    \sum_(xy <- J | xy.1 == x) `|K xy.1 xy.2 * S xy.1| =
    \sum_(xy <- F) K x xy.2 * S x.
  rewrite /F big_fset /=.
  apply: eq_bigr=> xy /eqP Hx.
  by rewrite Hx ger0_norm ?mulr_ge0 ?ge0_mu ?HS.
have Hmass : \sum_(xy <- F) K x xy.2 <= 1.
  have Huniq : uniq [seq xy.2 | xy <- enum_fset F].
    rewrite map_inj_in_uniq ?uniq_fset_keys //.
    move=> [x1 y1] [x2 y2].
    rewrite /F !in_fset /=.
    move=> /andP[_ /eqP Hx1] /andP[_ /eqP Hx2] Hy.
    congr (_, _).
      move: Hx1 Hx2=> /= Hx1 Hx2.
      by rewrite Hx1 Hx2.
    exact: Hy.
  rewrite -(big_map snd predT (fun y => K x y)).
  apply: (le_trans _ (le1_mu (K x))).
  apply: (le_trans _ (gerfinseq_psum Huniq (summable_mu (K x)))).
  apply/ler_sum=> y _.
  by rewrite ger0_norm ?ge0_mu.
rewrite Hfiber.
rewrite -(@big_fset_seq R 0 +%R (T * U)%type F
  (fun xy => K x xy.2 * S x)).
rewrite -mulr_suml.
rewrite -(@big_fset_seq R 0 +%R (T * U)%type F
  (fun xy => K x xy.2)) in Hmass.
apply: (le_trans (ler_wpM2r (HS x) Hmass)).
by rewrite mul1r.
Qed.

Lemma dmargin_injectiveE {T U : choiceType}
    (f : T -> U) (P : {distr T / R}) :
  injective f ->
  forall x, dmargin f P (f x) = P x.
Proof.
move=> Hf x.
rewrite dmargin_psumE.
rewrite (psum_finseq (r := [:: x])).
- by rewrite big_seq1 eqxx mul1r ger0_norm ?ge0_mu.
- by [].
move=> z.
rewrite inE.
case Hfz : (f z == f x); last by rewrite mul0r eqxx.
rewrite mul1r=> _.
have Hzx : z = x := Hf _ _ (eqP Hfz).
by move: Hzx=> ->; rewrite inE.
Qed.

Lemma dmargin_comp {T U V : choiceType}
    (f : U -> V) (g : T -> U) (P : {distr T / R}) :
  dmargin f (dmargin g P) =1 dmargin (fun x => f (g x)) P.
Proof.
move=> z.
by rewrite !pr_pred1 !pr_dmargin.
Qed.

Lemma finite_kl_dmargin_injective {T U : choiceType}
    (f : T -> U) (P Q : {distr T / R}) :
  injective f ->
  finite_kl P Q ->
  finite_kl (dmargin f P) (dmargin f Q).
Proof.
move=> Hf Hfin.
split.
- move=> y.
  rewrite !dmargin_psumE=> HQy0.
  apply: psum_eq0=> x.
  case Hfx : (f x == y); last by rewrite mul0r.
  rewrite mul1r.
  have Hfiber_summable : summable (fun x => (f x == y)%:R * Q x).
    exact: summable_condl.
  have HQx0 : Q x = 0.
    have := eq0_psum Hfiber_summable HQy0 x.
    by rewrite Hfx mul1r.
  by rewrite (finite_kl_absolute_continuous P Q Hfin x HQx0).
- pose F := fun x : T => P x * ln (P x / Q x).
  pose G := fun y : U =>
    dmargin f P y * ln (dmargin f P y / dmargin f Q y).
  have HFsm : summable F := finite_kl_summable P Q Hfin.
  have HFabssm : summable (fun x => `|F x|).
    exact: (proj2 (summable_abs F) HFsm).
  have Hfiber_sm y :
      summable (fun x : T => (f x == y)%:R * `|F x|).
    exact: summable_condl.
  have G_notin_image y :
      ~~ `[< exists x : T, f x == y >] -> G y = 0.
    move=> Hy.
    have Hd : dmargin f P y = 0.
      rewrite dmargin_psumE.
      apply: psum_eq0=> x.
      case Hfx : (f x == y); last by rewrite mul0r.
      move: Hy=> /negP Hy.
      case: Hy; apply/asboolP.
      by exists x.
    by rewrite /G Hd mul0r.
  have Hbound y :
      `|G y| <=
      psum (fun x : T => (f x == y)%:R * `|F x|).
    case Hy : `[< exists x : T, f x == y >].
    - move/asboolP: Hy=> [x Hfx].
      have HGy : G y = F x.
        by rewrite /G /F -(eqP Hfx) !dmargin_injectiveE.
      rewrite HGy.
      have Hle := @gerfinseq_psum R T
        (fun x0 : T => (f x0 == y)%:R * `|F x0|) [:: x]
        (isT : uniq [:: x]) (Hfiber_sm y).
      apply: (le_trans _ Hle).
      rewrite big_seq1 Hfx mul1r.
      by rewrite normr_id ?normr_ge0.
    - have Hnot : ~~ `[< exists x : T, f x == y >] by rewrite Hy.
      rewrite (G_notin_image y Hnot) normr0.
      exact: ge0_psum.
  apply/summable_abs.
  apply: (le_summable
    (F2 := fun y => psum (fun x : T => (f x == y)%:R * `|F x|))).
  - move=> y; apply/andP; split; first exact: normr_ge0.
    exact: Hbound.
  apply: summable_fiber_psum.
  - move=> x; exact: normr_ge0.
  exact: HFabssm.
Qed.

Lemma kl_dmargin_injective {T U : choiceType}
    (f : T -> U) (P Q : {distr T / R}) :
  injective f ->
  finite_kl P Q ->
  δ_KL (dmargin f P) (dmargin f Q) = δ_KL P Q.
Proof.
move=> Hf _.
pose G := fun y : U =>
  dmargin f P y * ln (dmargin f P y / dmargin f Q y).
pose F := fun x : T => P x * ln (P x / Q x).
pose Img : pred U := fun y => `[< exists x : T, f x == y >].
pose inv y : option T :=
  if pselect (exists x : T, f x == y) is left Hy
  then Some (xchoose Hy) else None.
have invK y : y \in Img -> omap f (inv y) = Some y.
  rewrite /Img /inv => /asboolP Hy.
  case: pselect=> [Hy'|nHy] /=.
    by rewrite (eqP (xchooseP Hy')).
  by case: nHy.
have inv_fK x : inv (f x) = Some x.
  rewrite /inv.
  case: pselect=> [Hy|nHy] /=.
    congr Some.
    apply: Hf.
    by apply/eqP; exact: (xchooseP Hy).
  by case: nHy; exists x.
have G_notin_image y : ~~ (y \in Img) -> G y = 0.
  move=> Hy.
  have Hd : dmargin f P y = 0.
    rewrite dmargin_psumE.
    apply: psum_eq0=> x.
    case Hfx : (f x == y); last by rewrite mul0r.
    move: Hy; rewrite /Img=> /negP Hy.
    case: Hy; apply/asboolP.
    by exists x.
  by rewrite /G Hd mul0r.
have fposG_support y : fpos G y != 0 -> y \in Img.
  apply: contraR=> Hy.
  have -> : fpos G y = 0.
    by rewrite /fpos (G_notin_image y Hy) maxxx normr0.
  by rewrite eqxx.
have fnegG_support y : fneg G y != 0 -> y \in Img.
  apply: contraR=> Hy.
  have -> : fneg G y = 0.
    by rewrite /fneg (G_notin_image y Hy) minxx normr0.
  by rewrite eqxx.
have reindex_fpos :
    psum (fpos G) = psum (fun x : T => fpos G (f x)).
  apply: (@reindex_psum_onto R U T (fpos G) Img f inv).
  - exact: fposG_support.
  - exact: invK.
  - by move=> x _; rewrite inv_fK.
have reindex_fneg :
    psum (fneg G) = psum (fun x : T => fneg G (f x)).
  apply: (@reindex_psum_onto R U T (fneg G) Img f inv).
  - exact: fnegG_support.
  - exact: invK.
  - by move=> x _; rewrite inv_fK.
have GF x : G (f x) = F x.
  by rewrite /G /F !dmargin_injectiveE.
rewrite /δ_KL /esp.
rewrite (eq_sum (F2 := G)); last by move=> y; rewrite /G mulrC.
rewrite (eq_sum (F2 := F)); last by move=> x; rewrite /F mulrC.
rewrite /sum reindex_fpos reindex_fneg.
congr (_ - _).
- by apply/eq_psum=> x; rewrite /fpos GF.
- by apply/eq_psum=> x; rewrite /fneg GF.
Qed.

Lemma ln_lower_exp_ratio_core (r h : R) :
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

Lemma kl_integrand_variational_pointwise_core (p q h : R) :
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
have Hineq := ln_lower_exp_ratio_core r h Hrpos.
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

Lemma log_sum_inequality_finite {T : choiceType} (p q : T -> R) :
  (forall x, 0 <= p x) ->
  (forall x, 0 <= q x) ->
  summable p ->
  summable q ->
  summable (fun x => p x * ln (p x / q x)) ->
  (forall x, q x = 0 -> p x = 0) ->
  psum p * ln (psum p / psum q) <=
  sum (fun x => p x * ln (p x / q x)).
Proof.
move=> Hp Hq Hpsm Hqsm Hkl Hac.
pose A := psum p.
pose B := psum q.
case HB0: (B == 0).
  have HA0 : A = 0.
    rewrite /A.
    apply: psum_eq0=> x.
    have Hqx0 : q x = 0.
      apply: (eq0_psum Hqsm).
      exact: (eqP HB0).
    exact: (Hac x Hqx0).
  rewrite /A in HA0.
  rewrite HA0 mul0r.
  rewrite (eq_sum (F2 := fun _ : T => 0)); last first.
    move=> x.
    have Hpx0 : p x = 0.
      apply: (eq0_psum Hpsm).
      exact: HA0.
    by rewrite Hpx0 mul0r.
  by rewrite sum0.
case HA0: (A == 0).
  have HA0' : psum p = 0 by exact: (eqP HA0).
  rewrite HA0' mul0r.
  rewrite (eq_sum (F2 := fun _ : T => 0)); last first.
    move=> x.
    have Hpx0 : p x = 0.
      apply: (eq0_psum Hpsm).
      exact: HA0'.
    by rewrite Hpx0 mul0r.
  by rewrite sum0.
have HApos : 0 < A by rewrite lt_def ge0_psum HA0.
have HBpos : 0 < B by rewrite lt_def ge0_psum HB0.
pose h := ln (A / B).
pose F := fun x : T => p x * h - q x * (sequences.expR h - 1).
pose G := fun x : T => p x * ln (p x / q x) - p x + q x.
have HFsm : summable F.
  apply: (eq_summable
    (S1 := (fun x : T => h * p x) \+
      (fun x : T => - ((sequences.expR h - 1) * q x)))).
    by move=> x; rewrite /F /=; ring.
  apply: summableD.
  - apply: summableZ; exact: Hpsm.
  - apply: summableN.
    apply: summableZ; exact: Hqsm.
have HGsm : summable G.
  apply: (eq_summable
    (S1 := (fun x : T => p x * ln (p x / q x)) \+
      ((fun x : T => - p x) \+ q))).
    by move=> x; rewrite /G /=; ring.
  apply: summableD; first exact: Hkl.
  apply: summableD; first exact: summableN.
  exact: Hqsm.
have Hpoint x : F x <= G x.
  rewrite /F /G.
  exact: (kl_integrand_variational_pointwise_core
    (p x) (q x) h (Hp x) (Hq x) (Hac x)).
have Hle := le_sum HFsm HGsm Hpoint.
rewrite /F /G in Hle.
have HFsum :
    sum F = h * sum p - (sequences.expR h - 1) * sum q.
  have Hhp : summable (fun x : T => h * p x).
    apply: summableZ; exact: Hpsm.
  have Hnq : summable (fun x : T => - ((sequences.expR h - 1) * q x)).
    apply: summableN.
    apply: summableZ; exact: Hqsm.
  rewrite (eq_sum (F2 := (fun x : T => h * p x) \+
      (fun x : T => - ((sequences.expR h - 1) * q x)))); last first.
    by move=> x; rewrite /= /F; ring.
  rewrite (@sumD R T (fun x : T => h * p x)
    (fun x : T => - ((sequences.expR h - 1) * q x)) Hhp Hnq).
  rewrite sumN.
  have -> : sum (fun x : T => h * p x) = h * sum p.
    exact: sumZ.
  have -> : sum (fun x : T => (sequences.expR h - 1) * q x) =
      (sequences.expR h - 1) * sum q.
    exact: sumZ.
  ring.
have HGsum :
    sum G =
    sum (fun x : T => p x * ln (p x / q x)) - sum p + sum q.
  have Hnpq : summable ((fun x : T => - p x) \+ q).
    apply: summableD; first exact: summableN.
    exact: Hqsm.
  rewrite (eq_sum (F2 := (fun x : T => p x * ln (p x / q x)) \+
      ((fun x : T => - p x) \+ q))); last first.
    by move=> x; rewrite /= /G; ring.
  rewrite (@sumD R T (fun x : T => p x * ln (p x / q x))
    ((fun x : T => - p x) \+ q) Hkl Hnpq).
  rewrite (@sumD R T (fun x : T => - p x) q
    (summableN Hpsm) Hqsm).
  rewrite sumN.
  ring.
rewrite HFsum HGsum in Hle.
have Hsum_p : sum p = A.
  rewrite /A.
  symmetry.
  exact: (@psum_sum R T p Hp).
have Hsum_q : sum q = B.
  rewrite /B.
  symmetry.
  exact: (@psum_sum R T q Hq).
rewrite Hsum_p Hsum_q in Hle.
rewrite /h.
have Hexp : sequences.expR (ln (A / B)) = A / B.
  rewrite lnK //.
  by rewrite qualifE /= divr_gt0.
have Hcancel : (A / B) * B = A by rewrite divfK ?lt0r_neq0.
rewrite Hexp in Hle.
have Hleft :
    ln (A / B) * A - (A / B - 1) * B =
    A * ln (A / B) - A + B.
  rewrite mulrBl Hcancel.
  ring.
rewrite Hleft in Hle.
rewrite -/A -/B in Hle.
set K := sum (fun x : T => p x * ln (p x / q x)).
rewrite -/K in Hle.
have Hfinal :
    (A * ln (A / B) - A + B) + (A - B) <=
    (K - A + B) + (A - B).
  exact: (lerD Hle (lexx (A - B))).
have HfinalL :
    (A * ln (A / B) - A + B) + (A - B) =
    A * ln (A / B) by ring.
have HfinalR :
    (K - A + B) + (A - B) = K by ring.
by rewrite HfinalL HfinalR in Hfinal.
Qed.

End KL_Core.
