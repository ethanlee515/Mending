From Stdlib Require Import Utf8 Lia.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".

(* Questionable boilerplate *)
(*
Program Definition oget_valid {t: choiceType} (ox: option t) (H: ox != None) :=
  match ox with
  | Some x => x
  | None => _
  end.
  *)
