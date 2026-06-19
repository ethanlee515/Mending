Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra all_reals distr.
From mathcomp Require Import realseq realsum exp interval_inference convex.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From mathcomp.algebra_tactics Require Import ring.

From Mending.LibExtras.MathcompExtras Require Import DistrExtras.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.
Local Open Scope convex_scope.

Section KL_Core.

Context {R: realType}.

Definition δ_KL {T : choiceType} (P Q : {distr T / R}) : R :=
  \E_[P] (fun x => ln (P x / Q x)).

Definition absolute_continuous {T : choiceType} (P Q : {distr T / R}) : Prop :=
  forall x, Q x = 0 -> P x = 0.

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
