From Stdlib Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice tuple fintype bigop order algebra.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp Require Import reals realsum functions numfun exp sequences realseq distr xfinmap.
Set Warnings "notation-incompatible-prefix".
From mathcomp Require Import arithmetic_tactic.
From mathcomp Require Import ring_tactic ssrZ zify.
Import GRing.Theory Num.Theory Order.Theory.

From Mending.LibExtras.MathcompExtras Require Import RealSumExtras.
Set SsrOldRewriteGoalsOrder.

Open Scope ring_scope.

Section DistrExtras.

Context {R : realType}.

Definition total_variation {T : choiceType} (P Q : {distr T / R}) : R :=
  (1 / 2) * sum (fun x => `| P x - Q x |).

Lemma summable_abs_distr_diff {T : choiceType}
    (P Q : {distr T / R}) :
  summable (fun x => `|P x - Q x|).
Proof.
apply/summable_abs.
apply: (eq_summable (f := fun x : T => P x + - Q x)).
  by move=> x; ring.
apply: summableD; first exact: summable_mu.
exact: summableN; exact: summable_mu.
Qed.

Lemma norm_sum_le_psum {T : choiceType} (F : T -> R) :
  summable F ->
  `|sum F| <= psum F.
Proof.
move=> Hsumm.
rewrite /sum.
set p := psum (funrpos F).
set q := psum (funrneg F).
have Hp : 0 <= p by exact: ge0_psum.
have Hq : 0 <= q by exact: ge0_psum.
have Hpsum : psum F = p + q.
  rewrite -[LHS]psum_abs.
  rewrite (eq_psum (F2 := funrpos F \+ funrneg F)); last first.
    move=> x /=.
    exact: esym (congr1 (fun f => f x) (funrposDneg F)).
  rewrite psumD.
  - by [].
  - move=> x; exact: funrpos_ge0.
  - move=> x; exact: funrneg_ge0.
  - exact: (summable_funrpos Hsumm).
  - exact: (summable_funrneg Hsumm).
rewrite Hpsum.
have Habs : `|p - q| <= p + q.
  have H := ler_normB p q.
  by rewrite (ger0_norm Hp) (ger0_norm Hq) in H.
exact: Habs.
Qed.

(* -- Conditional distributions -- *)

Lemma isdistr_dcond {T : choiceType} (P : {distr T / R}) (p : pred T) :
  isdistr (fun x => \P_[P, p] (pred1 x)).
Proof.
split=> [x|J uniq_J]; first exact: ge0_prc.
rewrite /prc -mulr_suml.
case: (\P_[P] p =P 0) => [p0|pNZ].
  by rewrite p0 invr0 mulr0 ler01.
rewrite ler_pdivrMr ?mul1r; last by rewrite lt_def; apply/andP; split; [apply/eqP | exact: ge0_pr].
rewrite (eq_bigr (fun x => (p x)%:R * P x)); last first.
  move=> x _.
  rewrite /pr.
  rewrite (psum_finseq (r := [:: x])).
  - rewrite big_seq1 !inE eqxx.
    case Hpx: (x \in p); rewrite ?mul1r ?mul0r.
      have -> : p x = true by exact: Hpx.
      by rewrite mul1r ger0_norm ?ge0_mu.
    have -> : p x = false by exact: Hpx.
    by rewrite normr0 mul0r.
  - by [].
  move=> y; rewrite !inE; case: (y == x) => //=.
  by rewrite mul0r eqxx.
rewrite /pr.
have le_sum_psum :
    \sum_(x <- J) `| (p x)%:R * P x | <=
    psum (fun x => (p x)%:R * P x) :=
  gerfinseq_psum uniq_J (summable_pr p P).
apply: (le_trans _ le_sum_psum).
apply/ler_sum=> x _.
by rewrite ger0_norm ?mulr_ge0 ?ler0n ?ge0_mu.
Qed.

Definition dcond {T : choiceType} (P : {distr T / R}) (p : pred T)
  : {distr T / R} :=
  mkdistr (isdistr_dcond P p).

Lemma dcondE {T : choiceType} (P : {distr T / R}) (p : pred T) x :
  dcond P p x = \P_[P, p] (pred1 x).
Proof. by []. Qed.

Lemma dcond_mass1 {T : choiceType} (P : {distr T / R}) (p : pred T) :
  0 < \P_[P] p -> dweight (dcond P p) = 1.
Proof.
move=> gt0_p.
rewrite pr_predT.
rewrite (eq_psum (F2 := fun x => \P_[P, p] (pred1 x))).
  exact: prc_sum.
by move=> x; rewrite dcondE.
Qed.

Lemma pr_dcond {T : choiceType} (mu : {distr T / R})
    (p : pred T) (A : pred T) :
  \P_[dcond mu p] A = \P_[mu, p] A.
Proof.
case Hp0: (\P_[mu] p == 0).
  move/eqP: Hp0=> Hp0.
  rewrite /pr /prc Hp0 invr0 mulr0.
  apply/psum_eq0=> x.
  rewrite dcondE /prc Hp0 invr0 mulr0 mulr0.
  exact/eqP.
rewrite /pr.
rewrite (eq_psum
  (F2 := fun x => (A x)%:R * \P_[mu, p] (pred1 x))).
  rewrite (eq_psum
    (F2 := fun x =>
      ((A x)%:R * \P_[mu] [predI pred1 x & p]) / \P_[mu] p)).
    rewrite psumZr ?invr_ge0 ?ge0_pr //.
    rewrite /prc.
    congr (_ / _).
    rewrite /pr.
    apply/eq_psum=> x.
    rewrite /pr (psum_finseq (r := [:: x])) ?big_seq1 //=.
      rewrite !inE eqxx -!topredE /= ger0_norm
        ?mulr_ge0 ?ler0n ?ge0_mu //.
      by case: (A x); case: (p x); rewrite ?mul0r ?mul1r.
    move=> y.
    rewrite !inE.
    case: (y == x) => //=.
    by rewrite mul0r eqxx.
  move=> x.
  by rewrite /prc mulrA.
move=> x.
by rewrite dcondE.
Qed.

Definition conditional_second {T U : choiceType}
    (P : {distr (T * U) / R}) (x : T) : {distr U / R} :=
  dmargin (fun xy : T * U => xy.2)
    (dcond P (fun xy : T * U => xy.1 == x)).

Lemma conditional_secondE {T U : choiceType}
    (P : {distr (T * U) / R}) (x : T) (y : U) :
  conditional_second P x y =
    if dmargin (fun xy : T * U => xy.1) P x == 0 then 0
    else P (x, y) / dmargin (fun xy : T * U => xy.1) P x.
Proof.
rewrite /conditional_second pr_pred1 pr_dmargin pr_dcond /prc.
have Hnum :
    \P_[P] [predI [pred xy | xy.2 \in pred1 y] &
                  [pred xy | xy.1 == x]] = P (x, y).
  rewrite /pr (psum_finseq (r := [:: (x, y)])).
  - rewrite big_seq1 /predI !inE /= !eqxx mul1r.
    by rewrite ger0_norm ?ge0_mu.
  - by [].
  move=> [x' y'].
  rewrite !inE /predI /=.
  case Hy: (y' == y); last by rewrite /= mul0r eqxx.
  case Hx: (x' == x); last by rewrite /= mul0r eqxx.
  move=> _.
  by rewrite (eqP Hx) (eqP Hy) eqxx.
have Hden :
    \P_[P] [pred xy | xy.1 == x] =
    dmargin (fun xy : T * U => xy.1) P x.
  rewrite pr_pred1 pr_dmargin.
  by apply: eq_pr=> xy; rewrite inE.
rewrite Hnum Hden.
case Hden0: (dmargin (fun xy : T * U => xy.1) P x == 0);
  first by rewrite (eqP Hden0) invr0 mulr0.
by [].
Qed.

Lemma conditional_second_factorization {T U : choiceType}
    (P : {distr (T * U) / R}) (x : T) (y : U) :
  P (x, y) =
    dmargin (fun xy : T * U => xy.1) P x *
    conditional_second P x y.
Proof.
rewrite conditional_secondE.
case Hden0: (dmargin (fun xy : T * U => xy.1) P x == 0).
- rewrite (eqP Hden0) mul0r.
  apply/eqP.
  have Hsum0 :
      psum (fun xy : T * U => (xy.1 == x)%:R * P xy) = 0.
    by move/eqP: Hden0; rewrite dmargin_psumE.
  have Hsumm :
      summable (fun xy : T * U => (xy.1 == x)%:R * P xy).
    exact: summable_condl.
  have Hpoint0 := eq0_psum Hsumm Hsum0 (x, y).
  move: Hpoint0; rewrite /= eqxx mul1r => Hpoint0.
  exact/eqP.
rewrite mulrC.
rewrite divfK //.
by rewrite Hden0.
Qed.

Lemma expectation_ext {T : choiceType} (P : {distr T / R}) (f g : T -> R) :
  f =1 g ->
  \E_[P] f = \E_[P] g.
Proof.
move=> eq_fg.
rewrite /esp.
apply/eq_sum=> x.
by rewrite eq_fg.
Qed.

Lemma expectation_distr_ext {T : choiceType}
    (P Q : {distr T / R}) (f : T -> R) :
  P =1 Q ->
  \E_[P] f = \E_[Q] f.
Proof.
move=> eq_PQ.
rewrite /esp.
apply/eq_sum=> x.
by rewrite eq_PQ.
Qed.

Lemma expectation_dnull {T : choiceType} (f : T -> R) :
  \E_[dnull] f = 0.
Proof.
rewrite /esp (eq_sum (F2 := fun _ : T => 0)).
  exact: sum0.
by move=> x; rewrite dnullE mulr0.
Qed.

Lemma expectation_indicator_eq {T : choiceType}
    (P : {distr T / R}) (x : T) (c : R) :
  \E_[P] (fun y => if y == x then c else 0) = P x * c.
Proof.
rewrite /esp (sum_seq1 x).
- by rewrite eqxx mulrC.
- move=> y Hnz.
  case Hy : (y == x).
    by rewrite eq_sym Hy.
  move: Hnz.
  by rewrite Hy mul0r eqxx.
Qed.

Lemma expectation_const {T : choiceType} (P : {distr T / R}) c :
  dweight P = 1 ->
  \E_[P] (fun _ => c) = c.
Proof.
move=> mass1_P.
by rewrite exp_cst mass1_P mul1r.
Qed.

Lemma sumD {T : choiceType} (F G : T -> R) :
  summable F -> summable G ->
  sum (F \+ G) = sum F + sum G.
Proof.
move=> smF smG.
have smFG : summable (F \+ G) by exact: summableD.
have smFp : summable (funrpos F) by exact: summable_funrpos.
have smFn : summable (funrneg F) by exact: summable_funrneg.
have smGp : summable (funrpos G) by exact: summable_funrpos.
have smGn : summable (funrneg G) by exact: summable_funrneg.
have smFGp : summable (funrpos (F \+ G)) by exact: summable_funrpos.
have smFGn : summable (funrneg (F \+ G)) by exact: summable_funrneg.
have H :
    psum (fun x => funrpos (F \+ G) x + (funrneg F x + funrneg G x)) =
    psum (fun x => (funrpos F x + funrpos G x) + funrneg (F \+ G) x).
  apply/eq_psum=> x.
  have := congr1 (fun f => f x) (funrposBneg (F \+ G)).
  have := congr1 (fun f => f x) (funrposBneg F).
  have := congr1 (fun f => f x) (funrposBneg G).
  rewrite !fctE /=.
  lra.
rewrite psumD in H; try solve [move=> x; rewrite addr_ge0 ?funrpos_ge0 ?funrneg_ge0].
  rewrite psumD in H; try solve [move=> x; rewrite addr_ge0 ?funrpos_ge0 ?funrneg_ge0].
    rewrite !psumD in H; try solve [move=> x; rewrite ?funrpos_ge0 ?funrneg_ge0].
      rewrite /sum.
      lra.
    all: try by move=> x; rewrite ?addr_ge0 ?funrpos_ge0 ?funrneg_ge0.
    all: try by apply: summableD.
    all: try done.
  all: try by move=> x; rewrite ?addr_ge0 ?funrpos_ge0 ?funrneg_ge0.
  all: try by apply: summableD.
  all: try done.
all: try by move=> x; rewrite ?addr_ge0 ?funrpos_ge0 ?funrneg_ge0.
all: try by apply: summableD.
all: done.
Qed.

Lemma total_variation_triangle {T : choiceType}
    (P Q M : {distr T / R}) :
  total_variation P M <= total_variation P Q + total_variation Q M.
Proof.
rewrite /total_variation.
pose FPQ := fun x : T => `|P x - Q x|.
pose FQM := fun x : T => `|Q x - M x|.
pose FPM := fun x : T => `|P x - M x|.
have HsmPQ : summable FPQ by exact: summable_abs_distr_diff.
have HsmQM : summable FQM by exact: summable_abs_distr_diff.
have HsmPM : summable FPM by exact: summable_abs_distr_diff.
have HsmPQQM : summable (FPQ \+ FQM) by exact: summableD.
have Hpoint x : FPM x <= (FPQ \+ FQM) x.
  rewrite /FPM /FPQ /FQM /=.
  have -> : P x - M x = (P x - Q x) + (Q x - M x) by ring.
  exact: ler_normD.
have Hle : sum FPM <= sum (FPQ \+ FQM).
  exact: le_sum.
apply: (le_trans _).
  apply: ler_wpM2l; first by lra.
  exact: Hle.
rewrite (@sumD T FPQ FQM HsmPQ HsmQM).
lra.
Qed.

Lemma summable_fiber_psum_nonneg {T U : choiceType}
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

Lemma dmargin_signed_sumE {T U : choiceType}
    (f : T -> U) (P Q : {distr T / R}) y :
  dmargin f P y - dmargin f Q y =
  sum (fun x : T => (f x == y)%:R * (P x - Q x)).
Proof.
rewrite dmargin_psumE.
rewrite dmargin_psumE.
  rewrite (eq_sum (F2 := fun x : T =>
      (f x == y)%:R * P x + - ((f x == y)%:R * Q x))); last first.
    move=> x.
    by rewrite mulrBr.
  have HsmP : summable (fun x : T => (f x == y)%:R * P x).
    apply: summable_condl.
    exact: summable_mu.
  have HsmQ : summable (fun x : T => (f x == y)%:R * Q x).
    apply: summable_condl.
    exact: summable_mu.
rewrite (@sumD T
  (fun x : T => (f x == y)%:R * P x)
  (fun x : T => - ((f x == y)%:R * Q x))
  HsmP (summableN HsmQ)).
- rewrite sumN.
  rewrite -!psum_sum.
  + by [].
  + move=> x; apply: mulr_ge0; [exact: ler0n | exact: ge0_mu].
  + move=> x; apply: mulr_ge0; [exact: ler0n | exact: ge0_mu].
Qed.

Lemma total_variation_dmargin_le {T U : choiceType}
    (f : T -> U) (P Q : {distr T / R}) :
  total_variation (dmargin f P) (dmargin f Q) <= total_variation P Q.
Proof.
rewrite /total_variation.
apply: ler_wpM2l; first by lra.
  pose S := fun x : T => P x - Q x.
  pose fiber_abs := fun y : U => psum (fun x : T => (f x == y)%:R * S x).
  have Hfiber_summable y :
      summable (fun x : T => (f x == y)%:R * S x).
    apply: (eq_summable (f := fun x : T =>
      (f x == y)%:R * P x + - ((f x == y)%:R * Q x))).
      move=> x.
      by rewrite /S mulrBr.
    apply: summableD.
      apply: summable_condl.
      exact: summable_mu.
    apply: summableN.
    apply: summable_condl.
    exact: summable_mu.
  have Hpoint y :
      `|dmargin f P y - dmargin f Q y| <= fiber_abs y.
    rewrite dmargin_signed_sumE.
    exact: norm_sum_le_psum.
have Habs_summable : summable (fun x : T => `|S x|).
  apply/summable_abs.
  apply: (eq_summable (f := fun x : T => P x + - Q x)).
    by move=> x; rewrite /S.
  apply: summableD; first exact: summable_mu.
  exact: summableN; exact: summable_mu.
have Hfiber_abs_summable : summable fiber_abs.
  rewrite /fiber_abs.
  apply: (eq_summable (f := fun y : U =>
    psum (fun x : T => (f x == y)%:R * `|S x|))).
    move=> y.
    apply/eq_psum_abs=> x.
    case Hfy : (f x == y).
      by rewrite /= !mul1r ger0_norm ?normr_ge0.
    by rewrite /= !mul0r !normr0.
  apply: summable_fiber_psum_nonneg; first by move=> x; exact: normr_ge0.
  exact: Habs_summable.
apply: (le_trans (le_sum _ _ Hpoint)).
  apply: (le_summable (g := fiber_abs)).
    move=> y; apply/andP; split; first exact: normr_ge0.
    exact: Hpoint.
  exact: Hfiber_abs_summable.
  exact: Hfiber_abs_summable.
rewrite /fiber_abs.
rewrite -psum_sum; last by move=> y; exact: ge0_psum.
rewrite (eq_psum (F2 := fun y : U =>
  psum (fun x : T => `|S x| * (f x == y)%:R))); last first.
  move=> y.
  apply/eq_psum_abs=> x.
  case Hfy : (f x == y).
    by rewrite /= !mul1r !mulr1 [RHS]ger0_norm ?normr_ge0.
  by rewrite /= !mul0r !mulr0 !normr0.
rewrite -(@partition_psum R T U f (fun x : T => `|S x|)).
  rewrite -psum_sum; last by move=> x; exact: normr_ge0.
  apply: lexx.
exact: Habs_summable.
Qed.

Lemma expectation_add {T : choiceType} (P : {distr T / R}) (f g : T -> R) :
  \E?_[P] f -> \E?_[P] g ->
  \E_[P] (fun x => f x + g x) = \E_[P] f + \E_[P] g.
Proof.
move=> int_f int_g.
rewrite /esp.
have -> :
  sum (fun x => (f x + g x) * P x) =
  sum ((fun x => f x * P x) \+ (fun x => g x * P x)).
  by apply/eq_sum=> x /=; rewrite mulrDl.
by rewrite sumD.
Qed.

Lemma expectation_scale {T : choiceType} (P : {distr T / R}) c (f : T -> R) :
  \E_[P] (fun x => c * f x) = c * \E_[P] f.
Proof.
exact: expZ.
Qed.

Lemma expectation_scale_right {T : choiceType}
    (P : {distr T / R}) c (f : T -> R) :
  \E_[P] (fun x => f x * c) = \E_[P] f * c.
Proof.
rewrite (expectation_ext P _ (fun x => c * f x)); last by move=> x; rewrite mulrC.
by rewrite expectation_scale mulrC.
Qed.

Lemma dweight1_dinsupp {T : choiceType} (mu : {distr T / R}) :
  dweight mu = 1 ->
  exists x, x \in dinsupp mu.
Proof.
rewrite pr_predT=> Hmass.
have Hnz : psum mu <> 0.
  move=> Hzero.
  move: Hmass.
  rewrite Hzero=> H01.
  by move/eqP: H01; rewrite eq_sym oner_eq0.
have [x Hx] := @neq0_psum R T mu Hnz.
exists x.
exact/dinsuppP.
Qed.

Lemma dmargin_dinsupp_image {T U : choiceType}
    (mu : {distr T / R}) (f : T -> U) (x : T) :
  x \in dinsupp mu ->
  f x \in dinsupp (dmargin f mu).
Proof.
move=> Hx.
rewrite dmarginE.
apply: (@dlet_dinsupp R T U (fun x => dunit (f x)) mu x (f x) Hx).
by rewrite dunit1E eqxx oner_neq0.
Qed.

Lemma dmargin_dinsupp_preimage {T U : choiceType}
    (mu : {distr T / R}) (f : T -> U) (y : U) :
  y \in dinsupp (dmargin f mu) ->
  exists2 x, x \in dinsupp mu & f x = y.
Proof.
rewrite dmarginE=> /dinsupp_dlet [x Hx Hunit].
exists x=> //.
move: Hunit.
by rewrite dunit1E pnatr_eq0 eqb0 negbK=> /eqP.
Qed.

Lemma pr_ext {T : choiceType} (P Q : {distr T / R}) (p : pred T) :
  P =1 Q ->
  \P_[P] p = \P_[Q] p.
Proof.
move=> HP.
rewrite /pr.
apply/eq_psum=> x.
by rewrite HP.
Qed.

Lemma prc_ext {T : choiceType}
    (P Q : {distr T / R}) (A p : pred T) :
  P =1 Q ->
  \P_[P, p] A = \P_[Q, p] A.
Proof.
move=> HP.
rewrite /prc.
by rewrite (pr_ext P Q [predI A & p] HP) (pr_ext P Q p HP).
Qed.

Lemma dcond_ext {T : choiceType}
    (P Q : {distr T / R}) (p : pred T) :
  P =1 Q ->
  dcond P p =1 dcond Q p.
Proof.
move=> HP x.
rewrite !dcondE.
exact: (prc_ext P Q (pred1 x) p HP).
Qed.

Lemma dmargin_ext {T U : choiceType} (f : T -> U) (P Q : {distr T / R}) :
  P =1 Q ->
  dmargin f P =1 dmargin f Q.
Proof.
move=> HPQ y.
rewrite !dmargin_psumE.
apply/eq_psum=> x.
by rewrite HPQ.
Qed.

Lemma dmargin_fun_ext {T U : choiceType} (f g : T -> U)
    (P : {distr T / R}) :
  f =1 g ->
  dmargin f P =1 dmargin g P.
Proof.
move=> Hfg y.
rewrite !dmargin_psumE.
apply/eq_psum=> x.
by rewrite Hfg.
Qed.

Lemma dmargin_fun_ext_in {T U : choiceType} (f g : T -> U)
    (P : {distr T / R}) :
  (forall x, x \in dinsupp P -> f x = g x) ->
  dmargin f P =1 dmargin g P.
Proof.
move=> Hfg y.
rewrite !dmargin_psumE.
apply/eq_psum=> x.
case Hx: (x \in dinsupp P).
  by rewrite (Hfg x Hx).
by move/dinsuppPn: Hx=> ->; rewrite !mulr0.
Qed.

Lemma dunit_dweight {T : choiceType} (x : T) :
  dweight (dunit x : {distr T / R}) = 1.
Proof.
by rewrite pr_dunit.
Qed.

Lemma pr_pred1_eq1_dunit {T : choiceType}
    (D : {distr T / R}) (x : T) :
  \P_[D] (pred1 x) = 1 ->
  D =1 dunit x.
Proof.
move=> Hx y.
case Hyx: (y == x).
  rewrite (eqP Hyx) dunit1E eqxx.
  by rewrite pr_pred1 Hx.
rewrite dunit1E eq_sym Hyx.
apply/eqP.
rewrite eq_le.
apply/andP; split; last exact: ge0_mu.
have Huniq : uniq [:: x; y].
  apply/andP; split; last by [].
  by rewrite inE eq_sym Hyx.
have Hpsum_le : D x + D y <= psum D.
  have H :=
    gerfinseq_psum (S := D) (r := [:: x; y]) Huniq (summable_mu D).
  by rewrite big_cons big_seq1 !ger0_norm ?ge0_mu in H.
have HDx : D x = 1 by rewrite pr_pred1 Hx.
have Hle1 : psum D <= 1 := le1_mu D.
rewrite HDx in Hpsum_le.
change (D y <= 0).
lra.
Qed.

Lemma psum_pair_fst_fiberR
    {T U : choiceType} (S : T * U -> R) (x : T) :
  (forall xy, 0 <= S xy) ->
  psum (fun xy : T * U => S xy * (xy.1 == x)%:R) =
  psum (fun y : U => S (x, y)).
Proof.
move=> HS.
rewrite (@reindex_psum_onto R (T * U)%type U
  (fun xy : T * U => S xy * (xy.1 == x)%:R)
  [pred xy : T * U | xy.1 == x]
  (fun y : U => (x, y))
  (fun xy : T * U => if xy.1 == x then Some xy.2 else None)).
- apply/eq_psum=> y.
  by rewrite eqxx mulr1.
- move=> xy Hxy.
  case Hxyx : (xy.1 == x); first by [].
  by move: Hxy; rewrite Hxyx mulr0 eqxx.
- case=> x' y /= Hx'.
  move: Hx'; rewrite /= => /eqP Hx'.
  change (x' = x) in Hx'.
  by rewrite Hx' eqxx.
- by move=> y _; rewrite eqxx.
Qed.

Lemma dweight_dlet_sum {T U : choiceType}
    (D : {distr T / R}) (K : T -> {distr U / R}) :
  dweight (\dlet_(x <- D) K x) =
  psum (fun x => D x * dweight (K x)).
Proof.
rewrite pr_dlet /esp.
have Hnonneg x : 0 <= dweight (K x) * D x.
  by rewrite mulr_ge0 ?ge0_pr ?ge0_mu.
rewrite -(psum_sum Hnonneg).
apply/eq_psum=> x.
by rewrite mulrC.
Qed.

Lemma dweight_dlet_lossless {T U : choiceType}
    (D : {distr T / R}) (K : T -> {distr U / R}) :
  dweight D = 1 ->
  (forall x, dweight (K x) = 1) ->
  dweight (\dlet_(x <- D) K x) = 1.
Proof.
move=> HD HK.
rewrite dweight_dlet_sum.
transitivity (psum D).
- apply/eq_psum=> x.
  by rewrite HK mulr1.
- by rewrite -pr_predT HD.
Qed.

Lemma dmargin_add_intE center (P : {distr int / R}) x :
  dmargin (GRing.add center) P x = P (x - center).
Proof.
rewrite dmargin_psumE.
pose y := x - center.
rewrite (psum_finseq (r := [:: y])).
- rewrite big_seq1 /y.
  by rewrite addrC subrK eqxx mul1r ger0_norm ?ge0_mu.
- by [].
move=> z.
rewrite !inE.
case H: (center + z == x); last by rewrite mul0r eqxx.
rewrite mul1r => _.
apply/eqP.
move/eqP: H => H.
rewrite /y -H.
ring.
Qed.

Lemma dmargin_sub_intE center (P : {distr int / R}) x :
  dmargin (fun z => z - center) P x = P (x + center).
Proof.
rewrite dmargin_psumE.
pose y := x + center.
rewrite (psum_finseq (r := [:: y])).
- rewrite big_seq1 /y.
  by rewrite addrK eqxx mul1r ger0_norm ?ge0_mu.
- by [].
move=> z.
rewrite !inE.
case H: (z - center == x); last by rewrite mul0r eqxx.
rewrite mul1r => _.
apply/eqP.
move/eqP: H => H.
rewrite /y -H.
ring.
Qed.

Lemma expectation_dmargin_sub_int center (P : {distr int / R})
    (g : int -> R) :
  \E_[dmargin (fun x => x - center) P] g =
  \E_[P] (fun x => g (x - center)).
Proof.
rewrite /esp.
have -> :
  sum (fun x => g x * dmargin (fun x => x - center) P x) =
  sum (fun x => g x * P (x + center)).
  by apply/eq_sum=> x; rewrite dmargin_sub_intE.
rewrite -(sum_shift_add_int
  (fun x => g (x - center) * P x) center).
apply/eq_sum=> x.
congr (_ * _).
by congr g; ring.
Qed.

Lemma dmargin_dweight {T U : choiceType}
    (f : T -> U) (P : {distr T / R}) :
  dweight (dmargin f P) = dweight P.
Proof.
rewrite !pr_predT.
rewrite (partition_psum (S := P) f) ?summable_mu //.
apply/eq_psum=> y.
rewrite dmargin_psumE.
by apply/eq_psum=> x; rewrite mulrC.
Qed.

Lemma conditional_second_mass1_on_support {T U : choiceType}
    (P : {distr (T * U) / R}) (x : T) :
  dweight P = 1 ->
  0 < dmargin (fun xy : T * U => xy.1) P x ->
  dweight (conditional_second P x) = 1.
Proof.
move=> _ Hx.
rewrite /conditional_second dmargin_dweight.
apply: dcond_mass1.
rewrite -(pr_dmargin (pred1 x) (fun xy : T * U => xy.1) P).
by rewrite -pr_pred1.
Qed.

End DistrExtras.
