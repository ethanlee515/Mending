Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot all_order all_algebra reals distr.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp Require Import realsum.

From Mending.LibExtras.MathcompExtras Require Import DistrExtras.

Import GRing.Theory Num.Theory Order.Theory.

Section DTuple.

Context {R : realType}.

Fixpoint dtuple {n : nat} {t: choiceType} :
    n.-tuple (distr R t) -> distr R (n.-tuple t) :=
  match n with
  | 0 => fun _ => dunit [tuple]
  | S i => fun ds =>
    \dlet_(x <- thead ds)
    \dlet_(xs <- (dtuple (behead_tuple ds)))
      dunit (cons_tuple x xs)
  end.

Definition nfold_distr (n : nat) {t: choiceType} (d: distr R t) :
  distr R (n.-tuple t) :=
  dtuple (nseq_tuple n d).

Lemma dtuple_mass1 {n : nat} {t : choiceType}
    (ds : n.-tuple (distr R t)) :
  (forall i : 'I_n, dweight (tnth ds i) = 1) ->
  dweight (dtuple ds) = 1.
Proof.
elim: n ds=> [|n IH] ds Hmass.
- by rewrite /= dunit_dweight.
rewrite /= dweight_dlet_sum.
rewrite (eq_psum
  (F2 := fun x : t => thead ds x * 1)); last first.
  move=> x.
  congr (_ * _).
  rewrite dweight_dlet_sum.
  rewrite (eq_psum
    (F2 := fun xs : n.-tuple t => dtuple (behead_tuple ds) xs * 1));
    last by move=> xs; rewrite dunit_dweight.
  rewrite (eq_psum (F2 := dtuple (behead_tuple ds))); last
    by move=> xs; rewrite mulr1.
  rewrite -pr_predT.
  apply: IH=> i.
  by rewrite tnth_behead; exact: Hmass.
rewrite (eq_psum (F2 := thead ds)); last by move=> x; rewrite mulr1.
rewrite -pr_predT.
exact: (Hmass ord0).
Qed.

Lemma nfold_distr_mass1 (n : nat) {t : choiceType} (d : distr R t) :
  dweight d = 1 ->
  dweight (nfold_distr n d) = 1.
Proof.
move=> Hd.
apply: dtuple_mass1=> i.
by rewrite tnth_nseq.
Qed.

End DTuple.
