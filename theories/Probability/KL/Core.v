Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format,-notation-incompatible-prefix".
From mathcomp Require Import all_boot all_order all_algebra all_reals distr.
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

Lemma mass1_kl_left {T : choiceType} (P Q : {distr T / R}) :
  dweight P = 1 ->
  δ_KL P Q =
    \E_[P] (fun x => ln (P x / Q x)).
Proof. by []. Qed.

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

Lemma summable_kernel_weighted_pair {T U : choiceType}
    (F : T -> R) (K : T -> {distr U / R}) :
  summable F ->
  summable (fun xy : T * U => K xy.1 xy.2 * F xy.1).
Proof.
move=> smF.
apply/summable_abs.
apply: (eq_summable
  (S1 := fun xy : T * U => K xy.1 xy.2 * `|F xy.1|)).
  move=> xy.
  by rewrite normrM ger0_norm ?ge0_mu.
apply: (@summable_kernel_weighted_pair_nonneg T U
  (fun x => `|F x|) K).
- move=> x; exact: normr_ge0.
- exact: (proj2 (summable_abs F) smF).
Qed.

Lemma kl_dmargin_injective {T U : choiceType}
    (f : T -> U) (P Q : {distr T / R}) :
  injective f ->
  δ_KL (dmargin f P) (dmargin f Q) = δ_KL P Q.
Admitted.

Lemma dmargin_absolute_continuous {T U : choiceType}
    (f : T -> U) (P Q : {distr T / R}) :
  absolute_continuous P Q ->
  absolute_continuous (dmargin f P) (dmargin f Q).
Proof.
move=> Hac y.
rewrite !dmargin_psumE=> HQy0.
apply: psum_eq0=> x.
case Hfx : (f x == y); last by rewrite mul0r.
rewrite mul1r.
have Hfiber_summable : summable (fun x => (f x == y)%:R * Q x).
  exact: summable_condl.
have HQx0 : Q x = 0.
  have := eq0_psum Hfiber_summable HQy0 x.
  by rewrite Hfx mul1r.
by rewrite (Hac x HQx0).
Qed.

Lemma log_sum_inequality_partition {T U : choiceType}
    (f : T -> U) (p q : T -> R) :
  (forall x, 0 <= p x) ->
  (forall x, 0 <= q x) ->
  summable p ->
  summable q ->
  (forall x, q x = 0 -> p x = 0) ->
  sum (fun y =>
    psum (fun x => (f x == y)%:R * p x) *
      ln (psum (fun x => (f x == y)%:R * p x) /
          psum (fun x => (f x == y)%:R * q x))) <=
  sum (fun x => p x * ln (p x / q x)).
Admitted.

Lemma ln_weighted_average (a b c d : R) :
  0 < a -> 0 < b -> 0 < c -> 0 < d ->
  (a / (a + c)) * ln (b / a) +
  (c / (a + c)) * ln (d / c) <=
  ln ((b + d) / (a + c)).
Proof.
move=> Ha Hb Hc Hd.
have Hac : 0 < a + c by rewrite addr_gt0.
have Ht_le1 : a / (a + c) <= 1.
  by rewrite (@ler_pdivrMr R (a + c) 1 a Hac) mul1r lerDl ltW.
pose t : {i01 R} := Itv01 (divr_ge0 (ltW Ha) (ltW Hac)) Ht_le1.
have HtE : t%:num = a / (a + c) by [].
have HtCE : unstable.onem t%:num = c / (a + c).
  rewrite /unstable.onem HtE.
  rewrite -{1}(divff (lt0r_neq0 Hac)) -mulrBl.
  congr (_ / _).
  ring.
have Havg :
    (b / a : R^o) <| t |> (d / c : R^o) = (b + d) / (a + c).
  rewrite convRE HtE HtCE.
  rewrite [a / _]mulrC [c / _]mulrC -!mulrA.
  rewrite [a * (b / a)]mulrC [c * (d / c)]mulrC.
  rewrite !divfK ?lt0r_neq0 //.
  rewrite -mulrDr.
  by rewrite mulrC.
have Hconc := @concave_ln R t (b / a : R^o) (d / c : R^o)
  (divr_gt0 Hb Ha) (divr_gt0 Hd Hc).
by rewrite convRE HtE HtCE Havg in Hconc.
Qed.

Lemma log_sum_inequality2_pos (a b c d : R) :
  0 < a -> 0 < b -> 0 < c -> 0 < d ->
  (a + c) * ln ((a + c) / (b + d)) <=
  a * ln (a / b) + c * ln (c / d).
Proof.
move=> Ha Hb Hc Hd.
have Hac : 0 < a + c by rewrite addr_gt0.
have Hbd : 0 < b + d by rewrite addr_gt0.
have Havg := ln_weighted_average a b c d Ha Hb Hc Hd.
have Hneg :
    - ln ((b + d) / (a + c)) <=
    - ((a / (a + c)) * ln (b / a) +
       (c / (a + c)) * ln (d / c)).
  by rewrite lerN2.
have Hscaled :
    (a + c) * (- ln ((b + d) / (a + c))) <=
    (a + c) *
      (- ((a / (a + c)) * ln (b / a) +
          (c / (a + c)) * ln (d / c))).
  by apply: ler_wpM2l; rewrite // ltW.
have Hleft :
  (a + c) * ln ((a + c) / (b + d)) =
  (a + c) * (- ln ((b + d) / (a + c))).
  rewrite !ln_div ?addr_gt0 //.
  ring.
rewrite Hleft.
apply: (le_trans Hscaled).
rewrite !ln_div ?divr_gt0 //.
rewrite mulrN mulrDr opprD !mulrA.
rewrite [(a + c) * a]mulrC [(a + c) * c]mulrC.
rewrite -[a * (a + c) / (a + c)]mulrA divff ?lt0r_neq0 // mulr1.
rewrite -[c * (a + c) / (a + c)]mulrA divff ?lt0r_neq0 // mulr1.
rewrite le_eqVlt.
apply/orP; left; apply/eqP.
ring.
Qed.

Lemma sum_seq_ge0 {T : eqType} (s : seq T) (a : T -> R) :
  (forall x, x \in s -> 0 <= a x) ->
  0 <= \sum_(x <- s) a x.
Proof.
elim: s=> [|x s IH] Ha; first by rewrite big_nil.
rewrite big_cons.
apply: ler_wpDl; first exact: Ha x (mem_head _ _).
apply: IH=> y Hy.
apply: Ha.
by rewrite inE Hy orbT.
Qed.

Lemma sum_seq_gt0 {T : eqType} (s : seq T) (a : T -> R) :
  s != [::] ->
  (forall x, x \in s -> 0 < a x) ->
  0 < \sum_(x <- s) a x.
Proof.
case: s=> [|x s] // _ Ha.
rewrite big_cons.
apply: ltr_pwDl; first exact: Ha x (mem_head _ _).
apply: sum_seq_ge0=> y Hy.
apply: ltW; apply: Ha.
by rewrite inE Hy orbT.
Qed.

Lemma log_sum_inequality_seq_pos {T : eqType} (s : seq T) (p q : T -> R) :
  s != [::] ->
  (forall x, x \in s -> 0 < p x) ->
  (forall x, x \in s -> 0 < q x) ->
  (\sum_(x <- s) p x) *
    ln ((\sum_(x <- s) p x) / (\sum_(x <- s) q x)) <=
  \sum_(x <- s) p x * ln (p x / q x).
Proof.
elim: s=> [|x s IH] //.
case: s IH=> [|y s] IH _ Hp Hq.
  by rewrite !big_cons !big_nil !addr0.
rewrite !big_cons.
set sp := \sum_(z <- y :: s) p z.
set sq := \sum_(z <- y :: s) q z.
have Hpx : 0 < p x by exact: Hp x (mem_head _ _).
have Hqx : 0 < q x by exact: Hq x (mem_head _ _).
have Hsp : 0 < sp.
  apply: sum_seq_gt0=> // z Hz.
  apply: Hp.
  by rewrite inE Hz orbT.
have Hsq : 0 < sq.
  apply: sum_seq_gt0=> // z Hz.
  apply: Hq.
  by rewrite inE Hz orbT.
have Hbin := log_sum_inequality2_pos (p x) (q x) sp sq
  Hpx Hqx Hsp Hsq.
have Htail : sp * ln (sp / sq) <=
    \sum_(z <- y :: s) p z * ln (p z / q z).
  apply: IH=> // z Hz.
  - apply: Hp.
    by rewrite inE Hz orbT.
  - apply: Hq.
    by rewrite inE Hz orbT.
rewrite -/sp -/sq.
have HspE : sp = p y + \sum_(z <- s) p z by rewrite /sp big_cons.
have HsqE : sq = q y + \sum_(z <- s) q z by rewrite /sq big_cons.
have HtailE :
    \sum_(z <- y :: s) p z * ln (p z / q z) =
    p y * ln (p y / q y) + \sum_(z <- s) p z * ln (p z / q z).
  by rewrite big_cons.
rewrite -HspE -HsqE -HtailE.
apply: (le_trans Hbin).
by apply: lerD; [exact: lexx | exact: Htail].
Qed.

Lemma kl_dmargin_log_sum_inequality {T U : choiceType}
    (f : T -> U) (P Q : {distr T / R}) :
  absolute_continuous P Q ->
  sum (fun y =>
    dmargin f P y * ln (dmargin f P y / dmargin f Q y)) <=
  sum (fun x => P x * ln (P x / Q x)).
Proof.
move=> Hac.
rewrite (eq_sum (F2 := fun y =>
  psum (fun x => (f x == y)%:R * P x) *
    ln (psum (fun x => (f x == y)%:R * P x) /
        psum (fun x => (f x == y)%:R * Q x)))); last first.
  by move=> y; rewrite !dmargin_psumE.
pose p := fun x : T => P x.
pose q := fun x : T => Q x.
change (sum (fun y : U =>
  psum (fun x => (f x == y)%:R * p x) *
    ln (psum (fun x => (f x == y)%:R * p x) /
        psum (fun x => (f x == y)%:R * q x))) <=
  sum (fun x => p x * ln (p x / q x))).
apply: (log_sum_inequality_partition f p q).
- exact: ge0_mu.
- exact: ge0_mu.
- exact: summable_mu.
- exact: summable_mu.
- exact: Hac.
Qed.

Lemma kl_dmargin_data_processing {T U : choiceType}
    (f : T -> U) (P Q : {distr T / R}) :
  absolute_continuous P Q ->
  δ_KL (dmargin f P) (dmargin f Q) <= δ_KL P Q.
Proof.
move=> Hac.
rewrite /δ_KL /esp.
rewrite (eq_sum (F2 := fun y =>
  dmargin f P y * ln (dmargin f P y / dmargin f Q y))); last first.
  by move=> y; rewrite mulrC.
rewrite (eq_sum (F2 := fun x => P x * ln (P x / Q x))); last first.
  by move=> x; rewrite mulrC.
exact: kl_dmargin_log_sum_inequality.
Qed.

Lemma sum_le_psum_fpos {T : choiceType} (F : T -> R) :
  sum F <= psum (fpos F).
Proof.
rewrite /sum.
have Hneg : 0 <= psum (fneg F) := ge0_psum _.
lra.
Qed.

Lemma kl_dmargin_fpos_le_fiber_fpos {T U : choiceType}
    (f : T -> U) (P Q : {distr T / R}) :
  finite_kl P Q ->
  forall y,
    fpos (fun y =>
      dmargin f P y * ln (dmargin f P y / dmargin f Q y)) y <=
    psum (fun x =>
      (f x == y)%:R * fpos (fun x => P x * ln (P x / Q x)) x).
Proof.
move=> Hfin y.
have Hac := finite_kl_absolute_continuous P Q Hfin.
have Hsrc_fpos_sm :
    summable (fpos (fun x => P x * ln (P x / Q x))) :=
  summable_fpos (finite_kl_summable P Q Hfin).
pose py := fun x : T => (f x == y)%:R * P x.
pose qy := fun x : T => (f x == y)%:R * Q x.
pose lhs := dmargin f P y * ln (dmargin f P y / dmargin f Q y).
have Hpy_ge x : 0 <= py x by rewrite /py mulr_ge0 ?ler0n ?ge0_mu.
have Hqy_ge x : 0 <= qy x by rewrite /qy mulr_ge0 ?ler0n ?ge0_mu.
have Hpy_sm : summable py by apply: summable_condl.
have Hqy_sm : summable qy by apply: summable_condl.
have Hfiber_ac x : qy x = 0 -> py x = 0.
  rewrite /py /qy.
  case Hfx: (f x == y); last by rewrite !mul0r.
  rewrite !mul1r.
  exact: Hac x.
have Hlogsum :
    lhs <= sum (fun x => py x * ln (py x / qy x)).
  have H :=
    log_sum_inequality_partition (fun _ : T => tt) py qy
      Hpy_ge Hqy_ge Hpy_sm Hqy_sm Hfiber_ac.
  apply: (le_trans _ H).
  rewrite /lhs.
  rewrite (sum_seq1 tt).
  - rewrite !eqxx.
    have -> : psum (fun x : T => true%:R * py x) = psum py.
      by apply/eq_psum=> x; rewrite /= mul1r.
    have -> : psum (fun x : T => true%:R * qy x) = psum qy.
      by apply/eq_psum=> x; rewrite /= mul1r.
    by rewrite /py /qy !dmargin_psumE.
  - by move=> z Hnz; case: z Hnz.
have Hrhs :
    sum (fun x => py x * ln (py x / qy x)) <=
    psum (fun x =>
      (f x == y)%:R * fpos (fun x => P x * ln (P x / Q x)) x).
  apply: (le_trans (sum_le_psum_fpos _)).
  apply/le_psum.
    move=> x; apply/andP; split; first exact: ge0_fpos.
      have -> :
        fpos (fun x0 : T => py x0 * ln (py x0 / qy x0)) x =
        (f x == y)%:R *
          fpos (fun x0 : T => P x0 * ln (P x0 / Q x0)) x.
      rewrite /py /qy.
      case Hfx: (f x == y).
        by rewrite /fpos /= Hfx /= !mul1r.
      rewrite /fpos /= Hfx /= !mul0r.
      change (fpos (fun _ : T => (0 : R)) x = 0).
      exact: (@fpos0 R T x).
    exact: lexx.
  exact: (@summable_condl R T
    (fpos (fun x => P x * ln (P x / Q x)))
    (fun x => f x == y) Hsrc_fpos_sm).
pose rhs := psum (fun x =>
  (f x == y)%:R * fpos (fun x => P x * ln (P x / Q x)) x).
have Hbound : lhs <= rhs := le_trans Hlogsum Hrhs.
change (fpos (fun _ : U => lhs) y <= rhs).
have Hposle :
    fpos (fun _ : U => lhs) y <= fpos (fun _ : U => rhs) y :=
  @le_fpos R U (fun _ : U => lhs) (fun _ : U => rhs)
    (fun _ : U => Hbound) y.
apply: (le_trans Hposle).
rewrite fpos_ge0 //.
move=> _.
exact: ge0_psum.
Qed.

Lemma summable_fpos_kl_dmargin {T U : choiceType}
    (f : T -> U) (P Q : {distr T / R}) :
  finite_kl P Q ->
  summable (fpos (fun y =>
    dmargin f P y * ln (dmargin f P y / dmargin f Q y))).
Proof.
move=> Hfin.
have Hsrc := finite_kl_summable P Q Hfin.
apply: (le_summable
  (F2 := fun y => psum (fun x =>
    (f x == y)%:R * fpos (fun x => P x * ln (P x / Q x)) x))).
  move=> y; apply/andP; split; first exact: ge0_fpos.
  exact: (kl_dmargin_fpos_le_fiber_fpos f P Q Hfin y).
apply: summable_fiber_psum.
- exact: ge0_fpos.
- exact: (summable_fpos Hsrc).
Qed.

Lemma summable_kl_dmargin {T U : choiceType}
    (f : T -> U) (P Q : {distr T / R}) :
  finite_kl P Q ->
  summable (fun y =>
    dmargin f P y * ln (dmargin f P y / dmargin f Q y)).
Proof.
move=> Hfin.
apply: summable_from_fpos_fneg.
- exact: summable_fpos_kl_dmargin.
- apply: summable_fneg_kl_integrand.
  exact: (dmargin_absolute_continuous f P Q
    (finite_kl_absolute_continuous P Q Hfin)).
Qed.

Lemma dlet_joint_same_kernelE {T U : choiceType}
    (P : {distr T / R}) (K : T -> {distr U / R}) (x : T) (y : U) :
  (\dlet_(x' <- P) \dlet_(y' <- K x') dunit (x', y')) (x, y) =
  P x * K x y.
Proof.
rewrite dletE.
rewrite (psum_finseq (r := [:: x])).
- rewrite big_seq1.
  rewrite dletE.
  rewrite (psum_finseq (r := [:: y])).
  + by rewrite big_seq1 dunit1E eqxx mulr1 !ger0_norm
      ?mulr_ge0 ?ge0_mu.
  + by [].
  + move=> y'.
    rewrite !inE dunit1E xpair_eqE eqxx /=.
    case Hy : (y' == y); first by rewrite (eqP Hy).
    by rewrite mulr0 eqxx.
- by [].
move=> x'.
rewrite !inE.
case Hx : (x' == x)=> //.
move=> Hnz.
have Hinner0 :
    (\dlet_(y' <- K x') dunit (x', y')) (x, y) = 0.
  apply: dlet_eq0=> y' _.
  by rewrite xpair_eqE Hx.
by move: Hnz; rewrite Hinner0 mulr0 eqxx.
Qed.

Lemma kl_joint_same_kernel {T U : choiceType}
    (P Q : {distr T / R}) (K : T -> {distr U / R}) :
  (forall x, dweight (K x) = 1) ->
  δ_KL
    (\dlet_(x <- P) \dlet_(y <- K x) dunit (x, y))
    (\dlet_(x <- Q) \dlet_(y <- K x) dunit (x, y)) =
  δ_KL P Q.
Admitted.

Lemma dlet_joint_same_kernel_absolute_continuous {T U : choiceType}
    (P Q : {distr T / R}) (K : T -> {distr U / R}) :
  absolute_continuous P Q ->
  absolute_continuous
    (\dlet_(x <- P) \dlet_(y <- K x) dunit (x, y))
    (\dlet_(x <- Q) \dlet_(y <- K x) dunit (x, y)).
Proof.
move=> Hac [x y].
rewrite !dlet_joint_same_kernelE.
move=> HQxy0.
case Kxy0: (K x y == 0).
  by rewrite (eqP Kxy0) mulr0.
have HQx0 : Q x = 0.
  apply/eqP.
  move/eqP: HQxy0.
  by rewrite mulf_eq0 Kxy0 orbF.
by rewrite (Hac x HQx0) mul0r.
Qed.

Lemma kl_joint_same_kernel_integrandE {T U : choiceType}
    (P Q : {distr T / R}) (K : T -> {distr U / R}) (xy : T * U) :
  finite_kl P Q ->
  ((\dlet_(x <- P) \dlet_(y <- K x) dunit (x, y)) xy *
      ln ((\dlet_(x <- P) \dlet_(y <- K x) dunit (x, y)) xy /
          (\dlet_(x <- Q) \dlet_(y <- K x) dunit (x, y)) xy)) =
  K xy.1 xy.2 * (P xy.1 * ln (P xy.1 / Q xy.1)).
Proof.
move=> Hfin.
case: xy=> x y /=.
rewrite !dlet_joint_same_kernelE.
case Kxy0: (K x y == 0).
  by rewrite (eqP Kxy0) !mulr0 !mul0r.
case Qx0: (Q x == 0).
  have Px0 := finite_kl_absolute_continuous P Q Hfin x (eqP Qx0).
  by rewrite (eqP Qx0) Px0 !mul0r !mulr0.
have Kxy_pos : 0 < K x y by rewrite lt_def ge0_mu Kxy0.
have ratioE : P x * K x y / (Q x * K x y) = P x / Q x.
  rewrite [P x * K x y]mulrC [Q x * K x y]mulrC.
  exact: divr_cancel_left_pos.
rewrite ratioE.
by rewrite !mulrA [P x * K x y]mulrC.
Qed.

Lemma dlet_same_kernel_absolute_continuous {T U : choiceType}
    (P Q : {distr T / R}) (K : T -> {distr U / R}) :
  absolute_continuous P Q ->
  absolute_continuous (\dlet_(x <- P) K x) (\dlet_(x <- Q) K x).
Proof.
move=> Hac.
pose JP : {distr (T * U) / R} :=
  \dlet_(x <- P) \dlet_(y <- K x) dunit (x, y).
pose JQ : {distr (T * U) / R} :=
  \dlet_(x <- Q) \dlet_(y <- K x) dunit (x, y).
have Hjoint : absolute_continuous JP JQ.
  exact: dlet_joint_same_kernel_absolute_continuous.
have Hmargin := dmargin_absolute_continuous (fun xy : T * U => xy.2) JP JQ Hjoint.
have HPsnd :
    dmargin (fun xy : T * U => xy.2) JP =1 \dlet_(x <- P) K x.
  move=> y.
  rewrite /JP __deprecated__dmargin_dlet.
  apply: eq_in_dlet=> // x _ z.
  rewrite __deprecated__dmargin_dlet.
  rewrite -(dlet_dunit_id (K x) z).
  apply: eq_in_dlet=> // u _ z'.
  by rewrite dmargin_dunit.
have HQsnd :
    dmargin (fun xy : T * U => xy.2) JQ =1 \dlet_(x <- Q) K x.
  move=> y.
  rewrite /JQ __deprecated__dmargin_dlet.
  apply: eq_in_dlet=> // x _ z.
  rewrite __deprecated__dmargin_dlet.
  rewrite -(dlet_dunit_id (K x) z).
  apply: eq_in_dlet=> // u _ z'.
  by rewrite dmargin_dunit.
move=> y HQy0.
rewrite -HPsnd.
apply: Hmargin.
by rewrite HQsnd.
Qed.

Lemma kl_dlet_data_processing {T U : choiceType}
    (P Q : {distr T / R}) (K : T -> {distr U / R}) :
  absolute_continuous P Q ->
  (forall x, dweight (K x) = 1) ->
  δ_KL (\dlet_(x <- P) K x) (\dlet_(x <- Q) K x) <= δ_KL P Q.
Proof.
move=> Hac HK.
pose JP : {distr (T * U) / R} :=
  \dlet_(x <- P) \dlet_(y <- K x) dunit (x, y).
pose JQ : {distr (T * U) / R} :=
  \dlet_(x <- Q) \dlet_(y <- K x) dunit (x, y).
have HPsnd :
    dmargin (fun xy : T * U => xy.2) JP =1 \dlet_(x <- P) K x.
  move=> y.
  rewrite /JP __deprecated__dmargin_dlet.
  apply: eq_in_dlet=> // x _ z.
  rewrite __deprecated__dmargin_dlet.
  rewrite -(dlet_dunit_id (K x) z).
  apply: eq_in_dlet=> // u _ z'.
  by rewrite dmargin_dunit.
have HQsnd :
    dmargin (fun xy : T * U => xy.2) JQ =1 \dlet_(x <- Q) K x.
  move=> y.
  rewrite /JQ __deprecated__dmargin_dlet.
  apply: eq_in_dlet=> // x _ z.
  rewrite __deprecated__dmargin_dlet.
  rewrite -(dlet_dunit_id (K x) z).
  apply: eq_in_dlet=> // u _ z'.
  by rewrite dmargin_dunit.
rewrite -(kl_ext _ _ _ _ HPsnd HQsnd).
apply: (le_trans (kl_dmargin_data_processing
  (fun xy : T * U => xy.2) JP JQ _)).
by apply: dlet_joint_same_kernel_absolute_continuous.
by rewrite /JP /JQ kl_joint_same_kernel.
Qed.

Lemma summable_kl_joint_same_kernel {T U : choiceType}
    (P Q : {distr T / R}) (K : T -> {distr U / R}) :
  finite_kl P Q ->
  (forall x, dweight (K x) = 1) ->
  summable (fun xy =>
    (\dlet_(x <- P) \dlet_(y <- K x) dunit (x, y)) xy *
      ln ((\dlet_(x <- P) \dlet_(y <- K x) dunit (x, y)) xy /
          (\dlet_(x <- Q) \dlet_(y <- K x) dunit (x, y)) xy)).
Proof.
move=> Hfin _.
apply: (eq_summable
  (S1 := fun xy : T * U =>
    K xy.1 xy.2 * (P xy.1 * ln (P xy.1 / Q xy.1)))).
  move=> xy.
  by rewrite -kl_joint_same_kernel_integrandE.
apply: (@summable_kernel_weighted_pair T U
  (fun x => P x * ln (P x / Q x)) K).
exact: (finite_kl_summable P Q Hfin).
Qed.

Lemma finite_kl_joint_same_kernel {T U : choiceType}
    (P Q : {distr T / R}) (K : T -> {distr U / R}) :
  finite_kl P Q ->
  (forall x, dweight (K x) = 1) ->
  finite_kl
    (\dlet_(x <- P) \dlet_(y <- K x) dunit (x, y))
    (\dlet_(x <- Q) \dlet_(y <- K x) dunit (x, y)).
Proof.
move=> Hfin HK.
split.
- exact: (dlet_joint_same_kernel_absolute_continuous P Q K
    (finite_kl_absolute_continuous P Q Hfin)).
- exact: (summable_kl_joint_same_kernel P Q K Hfin HK).
Qed.

Lemma summable_kl_dlet_same_kernel {T U : choiceType}
    (P Q : {distr T / R}) (K : T -> {distr U / R}) :
  finite_kl P Q ->
  (forall x, dweight (K x) = 1) ->
  summable (fun y =>
    (\dlet_(x <- P) K x) y *
      ln ((\dlet_(x <- P) K x) y / (\dlet_(x <- Q) K x) y)).
Proof.
move=> Hfin HK.
pose JP : {distr (T * U) / R} :=
  \dlet_(x <- P) \dlet_(y <- K x) dunit (x, y).
pose JQ : {distr (T * U) / R} :=
  \dlet_(x <- Q) \dlet_(y <- K x) dunit (x, y).
have Hjointfin : finite_kl JP JQ.
  exact: (finite_kl_joint_same_kernel P Q K Hfin HK).
have Hsumm := summable_kl_dmargin (fun xy : T * U => xy.2) JP JQ Hjointfin.
have HPsnd :
    dmargin (fun xy : T * U => xy.2) JP =1 \dlet_(x <- P) K x.
  move=> y.
  rewrite /JP __deprecated__dmargin_dlet.
  apply: eq_in_dlet=> // x _ z.
  rewrite __deprecated__dmargin_dlet.
  rewrite -(dlet_dunit_id (K x) z).
  apply: eq_in_dlet=> // u _ z'.
  by rewrite dmargin_dunit.
have HQsnd :
    dmargin (fun xy : T * U => xy.2) JQ =1 \dlet_(x <- Q) K x.
  move=> y.
  rewrite /JQ __deprecated__dmargin_dlet.
  apply: eq_in_dlet=> // x _ z.
  rewrite __deprecated__dmargin_dlet.
  rewrite -(dlet_dunit_id (K x) z).
  apply: eq_in_dlet=> // u _ z'.
  by rewrite dmargin_dunit.
apply: (eq_summable (S1 := fun y =>
  dmargin (fun xy : T * U => xy.2) JP y *
    ln (dmargin (fun xy : T * U => xy.2) JP y /
        dmargin (fun xy : T * U => xy.2) JQ y))).
  by move=> y; rewrite HPsnd HQsnd.
exact: Hsumm.
Qed.

Lemma finite_kl_dlet_same_kernel {T U : choiceType}
    (P Q : {distr T / R}) (K : T -> {distr U / R}) :
  finite_kl P Q ->
  (forall x, dweight (K x) = 1) ->
  finite_kl (\dlet_(x <- P) K x) (\dlet_(x <- Q) K x).
Proof.
move=> Hfin HK.
split.
- exact: (dlet_same_kernel_absolute_continuous
    P Q K (finite_kl_absolute_continuous P Q Hfin)).
- exact: (summable_kl_dlet_same_kernel P Q K Hfin HK).
Qed.

Lemma finite_kl_dmargin {T U : choiceType}
    (f : T -> U) (P Q : {distr T / R}) :
  finite_kl P Q ->
  finite_kl (dmargin f P) (dmargin f Q).
Proof.
move=> Hfin.
split.
- exact: (dmargin_absolute_continuous f P Q
    (finite_kl_absolute_continuous P Q Hfin)).
- exact: (summable_kl_dmargin f P Q Hfin).
Qed.

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
  absolute_continuous P Q ->
  dweight P = 1 ->
  0 <= δ_KL P Q.
Proof.
move=> Hac HP.
have Hlogsum :=
  log_sum_inequality_partition (fun _ : T => tt) P Q
    (fun x => ge0_mu P x) (fun x => ge0_mu Q x)
    (summable_mu P) (summable_mu Q) Hac.
rewrite /δ_KL /esp.
rewrite (eq_sum (F2 := fun x => P x * ln (P x / Q x))); last first.
  by move=> x; rewrite mulrC.
apply: (le_trans _ Hlogsum).
rewrite (sum_seq1 tt).
- rewrite !eqxx.
  have -> : psum (fun x : T => true%:R * P x) = psum P.
    by apply/eq_psum=> x; rewrite /= mul1r.
  have -> : psum (fun x : T => true%:R * Q x) = psum Q.
    by apply/eq_psum=> x; rewrite /= mul1r.
  rewrite -!pr_predT HP.
  have HQpos : 0 < dweight Q.
    have [x Hx] := dweight1_dinsupp P HP.
    have HPx_neq : P x != 0 by rewrite -in_dinsupp.
    have HPx_pos : 0 < P x by rewrite lt_def ge0_mu HPx_neq.
    have HQx_pos : 0 < Q x := absolute_continuous_positive P Q x Hac HPx_pos.
    apply: (lt_le_trans HQx_pos _).
    rewrite pr_predT.
    by rewrite -(ger0_norm (ge0_mu Q x)); exact: ger1_psum.
  have HQle1 : dweight Q <= 1 by rewrite pr_predT; exact: le1_mu.
  have Hratio_ge1 : 1 <= 1 / dweight Q.
    rewrite -[1 <= _](@ler_pM2r R (dweight Q)).
      rewrite !mul1r mulVr ?mulr1 ?unitfE ?lt0r_neq0 //.
      exact: HQpos.
  by rewrite mul1r ln_ge0.
- move=> y Hnz.
  by case: y Hnz.
Qed.

End KL_Core.
