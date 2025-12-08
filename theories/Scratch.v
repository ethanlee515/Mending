Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From SSProve Require Import NominalPrelude.

Import PackageNotation.
Local Open Scope package_scope.

(*
Import Num.Def Num.Theory Order.POrderTheory.
#[local] Open Scope ring_scope.
Import GroupScope GRing.Theory.

Import GroupScope.
*)

Definition GETA := 50%N.
Definition GETBC := 51%N.

Definition I_LDDH :=
  [interface
    [ GETA  ] : { 'unit ~> 'nat } ;
    [ GETBC ] : { 'unit ~> 'nat × 'nat }
  ].
  
Check I_LDDH.
Print I_LDDH.

