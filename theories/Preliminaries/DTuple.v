Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr.
Set Warnings "notation-overridden,ambiguous-paths".

Section DTuple.

Context (R: realType).

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

End DTuple.
