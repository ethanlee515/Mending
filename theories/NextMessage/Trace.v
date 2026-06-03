From Stdlib Require Import Unicode.Utf8.
From extructures Require Import ord fset fmap.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals distr ssrZ realseq realsum.
From mathcomp Require Import lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Crypt Require Import ChoiceAsOrd Couplings StateTransformingLaxMorph.
From SSProve.Crypt Require Import Axioms StateTransfThetaDens.
From SSProve.Crypt Require Import choice_type SubDistr.
From SSProve.Crypt.nominal Require Import Pr.
From SSProve Require Import pkg_core_definition pkg_advantage pkg_notation.

Import PackageNotation.
Local Open Scope package_scope.

Definition trace_t : choice_type := 'list 'nat.

Definition decode_sample_entry (op : Op)
    (e : 'nat) : option (Arit op) :=
  unpickle e.

Definition decode_call_entry (o : opsig)
    (e : 'nat) : option (tgt o) :=
  unpickle e.

Definition decode_get_entry (l : Location)
    (e : 'nat) : option l :=
  unpickle e.

(** [continue_from_trace p t] consumes the trace [t] as a prefix of [p].

  Heap reads, external calls, and random samples each consume one entry. Heap
  writes consume no entry because their continuation does not depend on an
  external outcome. When successful, the result is the residual program after
  the traced prefix. Failure means that the trace is inconsistent with [p]: a
  payload cannot be unpickled at the type expected by the current [raw_code]
  node, or the trace is longer than the remaining effectful events in the
  program.
*)
Fixpoint continue_from_trace {A : choice_type}
    (p : raw_code A) (t : trace_t) : option (raw_code A) :=
  match t with
  | nil => Some p
  | e :: t' =>
      match p with
      | ret _ => None
      | opr o x k =>
          match decode_call_entry o e with
          | Some y => continue_from_trace (k y) t'
          | None => None
          end
      | getr l k =>
          match decode_get_entry l e with
          | Some y => continue_from_trace (k y) t'
          | None => None
          end
      | putr l v k =>
          continue_from_trace k t
      | sampler op k =>
          match decode_sample_entry op e with
          | Some y => continue_from_trace (k y) t'
          | None => None
          end
      end
  end.

