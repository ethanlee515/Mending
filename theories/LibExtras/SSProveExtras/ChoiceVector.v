From Stdlib Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot all_order choice tuple.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
Import PackageNotation.
Local Open Scope form_scope.
Local Open Scope package_scope.
Local Open Scope seq_scope.

Set Bullet Behavior "Strict Subproofs".

(* SSProve compatible vectors *)

Fixpoint chVec (t: choice_type) (n: nat) :=
  match n with
  | 0 => chUnit
  | S i => chProd t (chVec t i)
  end.

Fixpoint toVec {t : choice_type} {n : nat}
    : n.-tuple t -> chVec t n :=
  match n with
  | 0 => fun _ => tt
  | S i => fun w => (thead w, toVec (behead_tuple w))
  end.

Fixpoint fromVec {t : choice_type} {n: nat}
    : chVec t n -> n.-tuple t :=
  match n with
  | 0 => fun _ => [tuple]
  | S i => fun w => let '(h, t) := w in cons_tuple h (fromVec t)
  end.

Lemma toVecK {t : choice_type} {n : nat} (v : chVec t n) :
  toVec (fromVec v) = v.
Proof.
elim: n v.
- move => v.
  by case: v.
- move => n IH v /=.
  admit.
Admitted.

Lemma fromVecK {t : choice_type} {n : nat} (v : n.-tuple t) :
  fromVec (toVec v) = v.
Proof.
elim: n v.
- rewrite /fromVec /toVec /=.
  move => v.
  symmetry.
  exact: tuple0.
- admit.
Admitted.

(* Non-uniform tuples *)
Fixpoint chHVec {n : nat} : ('I_n -> choiceType) -> choiceType :=
  match n with
  | 0 => fun _ => (unit : choiceType)
  | S n' =>
      fun X =>
        ((X ord0 * chHVec (fun i : 'I_n' => X (lift ord0 i)))%type
          : choiceType)
  end.

Fixpoint hget {n : nat} :
    forall (X : 'I_n -> choiceType), chHVec X -> forall i : 'I_n, X i :=
  match n return
      forall (X : 'I_n -> choiceType), chHVec X -> forall i : 'I_n, X i
  with
  | 0 =>
      fun _ _ i =>
        let '(Ordinal m p) := i in
        False_rect _ (elimF idP (ltn0 m) p)
  | S n' =>
      fun X v i =>
        match unliftP ord0 i with
        | UnliftSome j Hi =>
            eq_rect (lift ord0 j) X
              (hget (fun k : 'I_n' => X (lift ord0 k)) v.2 j) i
              (esym Hi)
        | UnliftNone Hi =>
            eq_rect ord0 X v.1 i (esym Hi)
        end
  end.
