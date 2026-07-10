From Stdlib Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot all_order all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp Require Import reals distr.
From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Crypt Require Import ChoiceAsOrd Axioms SubDistr.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

Lemma SDistr_assoc_clean :
  forall (A B C : ord_choiceType)
    (f : OrderEnrichedRelativeMonadExamples.TypeCat
           ⦅ choice_incl B; SDistr_carrier C ⦆)
    (g : OrderEnrichedRelativeMonadExamples.TypeCat
           ⦅ choice_incl A; SDistr_carrier B ⦆),
  SDistr_bind A C (SDistr_bind B C f ∙ g) =
  SDistr_bind B C f ∙ SDistr_bind A B g.
Proof.
move=> A B C f g.
simpl in f. simpl in g. simpl.
apply boolp.funext=> de. symmetry.
apply distr_ext=> c. simpl.
exact: dlet_dlet_clean.
Qed.

Program Definition SDistr_clean : ord_relativeMonad choice_incl :=
  mkOrdRelativeMonad SDistr_carrier _ _ _ _ _ _.
Next Obligation. exact (SDistr_unit). Defined.
Next Obligation. exact (SDistr_bind). Defined.
Next Obligation.
  move=> A B f1 f2 H a.
  have -> : f1 = f2 by apply boolp.funext.
  reflexivity.
Qed.
Next Obligation. exact SDistr_rightneutral. Qed.
Next Obligation. exact SDistr_leftneutral. Qed.
Next Obligation. exact SDistr_assoc_clean. Qed.

Lemma SDistr_bind_pairC {X Y : choiceType}
    (p : SDistr_carrier X) (q : SDistr_carrier Y) :
  SDistr_bind X (X * Y)%type
    (fun x => SDistr_bind Y (X * Y)%type
      (fun y => SDistr_unit (X * Y)%type (x, y)) q) p =
  SDistr_bind Y (X * Y)%type
    (fun y => SDistr_bind X (X * Y)%type
      (fun x => SDistr_unit (X * Y)%type (x, y)) p) q.
Proof.
rewrite /SDistr_bind /SDistr_unit.
apply: distr_ext=> xy.
exact: dlet_pairC.
Qed.

Lemma SDistr_bind_commut_clean {X Y Z : choiceType}
    (p : SDistr_carrier X) (q : SDistr_carrier Y)
    (g : X -> Y -> SDistr_carrier Z) :
  SDistr_bind X Z (fun x =>
    SDistr_bind Y Z (fun y => g x y) q) p =
  SDistr_bind Y Z (fun y =>
    SDistr_bind X Z (fun x => g x y) p) q.
Proof.
rewrite /SDistr_bind.
apply: distr_ext=> z.
exact: dlet_commut_indep_clean.
Qed.

Lemma SDistr_bind_lossless {X Y : choiceType}
    (p : SDistr_carrier X) (k : X -> SDistr_carrier Y) :
  dweight p = 1 ->
  (forall x, dweight (k x) = 1) ->
  dweight (SDistr_bind X Y k p) = 1.
Proof.
rewrite /SDistr_bind.
exact: dweight_dlet_lossless.
Qed.
