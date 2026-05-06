From Stdlib Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice bigop order all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp Require Import reals realsum exp sequences realseq distr.
From mathcomp Require Import lra.
From mathcomp.algebra_tactics Require Import ring.
Import GRing.Theory Num.Theory Order.Theory.

From Mending Require Import RealSumExtras.

Open Scope ring_scope.

Section DistrExtras.

Context {R : realType}.

Definition statistical_distance {T : choiceType} (P Q : {distr T / R}) : R :=
  sum (fun x => `| P x - Q x |).

(* -- Conditional distributions -- *)
(* Will adapt from EasyCrypt *)

Definition dcond {T : choiceType} (P : {distr T / R}) (p : pred T)
  : {distr T / R}.
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
rewrite -(sum_shift_add_int R
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

End DistrExtras.

