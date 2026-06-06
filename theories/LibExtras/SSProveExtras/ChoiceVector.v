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
Definition rcons_choice {n : nat}
    (X : 'I_n -> choiceType) (A : choiceType)
    (i : 'I_n.+1) : choiceType :=
  if unlift ord_max i is Some j then X j else A.

Fixpoint chHVec {n : nat} : ('I_n -> choiceType) -> choiceType :=
  match n with
  | 0 => fun _ => (unit : choiceType)
  | S n' =>
      fun X =>
        ((X ord0 * chHVec (fun i : 'I_n' => X (lift ord0 i)))%type
          : choiceType)
  end.

Definition absurd_ord0 {T : Type} (i : 'I_0) : T :=
  let '(Ordinal m p) := i in False_rect _ (elimF idP (ltn0 m) p).

Definition hcast {n : nat} {X : 'I_n -> choiceType}
    {i j : 'I_n} (Hij : i = j) : X i -> X j :=
  fun x => eq_rect i X x j Hij.

Definition hhead {n : nat} {X : 'I_n.+1 -> choiceType}
    (v : chHVec X) : X ord0 :=
  v.1.

Definition htail {n : nat} {X : 'I_n.+1 -> choiceType}
    (v : chHVec X) : chHVec (fun i : 'I_n => X (lift ord0 i)) :=
  v.2.

Fixpoint hget {n : nat} :
    forall (X : 'I_n -> choiceType), chHVec X -> forall i : 'I_n, X i :=
  match n return
      forall (X : 'I_n -> choiceType), chHVec X -> forall i : 'I_n, X i
  with
  | 0 => fun _ _ i => absurd_ord0 i
  | S n' =>
      fun X v i =>
        match unliftP ord0 i with
        | UnliftSome j Hi =>
            hcast (esym Hi)
              (hget (fun k : 'I_n' => X (lift ord0 k)) (htail v) j)
        | UnliftNone Hi => hcast (esym Hi) (hhead v)
        end
  end.

Definition hget_rcons_coord {n : nat}
    (X : 'I_n -> choiceType) (A : choiceType)
    (omega : chHVec (rcons_choice X A)) (i : 'I_n) : X i.
Proof.
have v := hget (rcons_choice X A) omega (lift ord_max i).
rewrite /rcons_choice in v.
case E: (unlift ord_max (lift ord_max i)) v => [j|] v.
- have Hj : j = i.
    have Hsome : Some j = Some i by rewrite -E liftK.
    by inversion Hsome.
  by subst j.
- by rewrite liftK in E.
Defined.

Definition hget_rcons_final {n : nat}
    (X : 'I_n -> choiceType) (A : choiceType)
    (omega : chHVec (rcons_choice X A)) : A.
Proof.
have v := hget (rcons_choice X A) omega ord_max.
rewrite /rcons_choice in v.
case E: (unlift ord_max ord_max) v => [j|] v.
- by rewrite unlift_none in E.
- exact: v.
Defined.
