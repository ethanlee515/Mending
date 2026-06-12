From Stdlib Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice tuple fintype bigop order all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp Require Import reals realsum exp sequences realseq distr.
From mathcomp Require Import lra.
From mathcomp.algebra_tactics Require Import ring.
Import GRing.Theory Num.Theory Order.Theory.

From Mending.LibExtras.MathcompExtras Require Import RealSumExtras.

Open Scope ring_scope.

Section DistrExtras.

Context {R : realType}.

Definition total_variation {T : choiceType} (P Q : {distr T / R}) : R :=
  (1 / 2) * sum (fun x => `| P x - Q x |).

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
Admitted.

Lemma conditional_second_factorization {T U : choiceType}
    (P : {distr (T * U) / R}) (x : T) (y : U) :
  P (x, y) =
    dmargin (fun xy : T * U => xy.1) P x *
    conditional_second P x y.
Admitted.

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
have smFp : summable (fpos F) by exact: summable_fpos.
have smFn : summable (fneg F) by exact: summable_fneg.
have smGp : summable (fpos G) by exact: summable_fpos.
have smGn : summable (fneg G) by exact: summable_fneg.
have smFGp : summable (fpos (F \+ G)) by exact: summable_fpos.
have smFGn : summable (fneg (F \+ G)) by exact: summable_fneg.
have H :
    psum (fun x => fpos (F \+ G) x + (fneg F x + fneg G x)) =
    psum (fun x => (fpos F x + fpos G x) + fneg (F \+ G) x).
  apply/eq_psum=> x.
  have := fposBfneg (F \+ G) x.
  have := fposBfneg F x.
  have := fposBfneg G x.
  rewrite /=.
  lra.
rewrite psumD in H; try solve [move=> x; rewrite addr_ge0 ?ge0_fpos ?ge0_fneg].
  rewrite psumD in H; try solve [move=> x; rewrite addr_ge0 ?ge0_fpos ?ge0_fneg].
    rewrite !psumD in H; try solve [move=> x; rewrite ?ge0_fpos ?ge0_fneg].
      rewrite /sum.
      lra.
    all: try by move=> x; rewrite ?addr_ge0 ?ge0_fpos ?ge0_fneg.
    all: try by apply: summableD.
    all: try done.
  all: try by move=> x; rewrite ?addr_ge0 ?ge0_fpos ?ge0_fneg.
  all: try by apply: summableD.
  all: try done.
all: try by move=> x; rewrite ?addr_ge0 ?ge0_fpos ?ge0_fneg.
all: try by apply: summableD.
all: done.
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

Lemma dunit_dweight {T : choiceType} (x : T) :
  dweight (dunit x : {distr T / R}) = 1.
Proof.
by rewrite pr_dunit.
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
