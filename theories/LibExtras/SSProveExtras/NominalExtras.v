From Stdlib Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
From SSProve Require Import NominalPrelude.

Import PackageNotation.

Local Open Scope package_scope.
Local Open Scope sep_scope.
Local Open Scope seq_scope.

Set Bullet Behavior "Strict Subproofs".

Lemma moved_package_valid
    (I E : Interface) (P A : nom_package) :
  Package I E A ->
  Package I E (move P A).
Proof.
  move=> A_valid.
  rewrite /move.
  by apply: rename_valid.
Qed.

Lemma moved_resolve_bind_valid
    (I E : Interface) (P A : nom_package)
    (B : choiceType) (o : opsig) (x : src o)
    (k : tgt o -> raw_code B) :
  Package I E A ->
  fhas E o ->
  (forall y, ValidCode (loc (move P A)) I (k y)) ->
  ValidCode (loc (move P A)) I
    (bind (resolve (move P A) o x) k).
Proof.
  move=> A_valid Ho Hk.
  have moved_valid : Package I E (move P A).
    exact: (moved_package_valid I E P A A_valid).
  apply: valid_bind.
  apply: (@valid_resolve
    (loc (move P A)) I E (val (move P A)) o x).
  exact: Ho.
Qed.

Lemma moved_resolve_ret_valid
    (I E : Interface) (P A : nom_package)
    (B : choiceType) (o : opsig) (x : src o)
    (f : tgt o -> B) :
  Package I E A ->
  fhas E o ->
  ValidCode (loc (move P A)) I
    (bind (resolve (move P A) o x) (fun y => ret (f y))).
Proof.
  move=> A_valid Ho.
  apply: (@moved_resolve_bind_valid I E P A B o x (fun y => ret (f y))).
  - exact: Ho.
  - move=> y.
    apply: valid_ret.
Qed.
