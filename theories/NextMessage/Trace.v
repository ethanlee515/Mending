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

(** A trace entry records the outcome of one effectful [raw_code] node.

  The trace itself is an SSProve [choice_type]. Since SSProve lists are
  homogeneous, every entry is a [nat], with the underlying value pickled into
  that common representation.

  Entries are intentionally untagged: the [raw_code] being continued tells us
  whether the next entry should be decoded as a heap-read result, random sample
  result, or external call result.
*)
Definition trace_entry_t : choice_type := chNat.

Definition trace_t : choice_type := chList trace_entry_t.

Definition trace_entry : choiceType := trace_entry_t.

Definition trace : choiceType := trace_t.

Definition sample_trace_entry {op : Op} (x : Arit op) : trace_entry :=
  pickle x.

Definition call_trace_entry {o : opsig} (x : tgt o) : trace_entry :=
  pickle x.

Definition get_trace_entry {l : Location} (x : l) : trace_entry :=
  pickle x.

Definition decode_sample_trace_entry (op : Op)
    (e : trace_entry) : option (Arit op) :=
  unpickle e.

Definition decode_call_trace_entry (o : opsig)
    (e : trace_entry) : option (tgt o) :=
  unpickle e.

Definition decode_get_trace_entry (l : Location)
    (e : trace_entry) : option l :=
  unpickle e.

Lemma decode_sample_trace_entryK {op : Op} (x : Arit op) :
  decode_sample_trace_entry op (sample_trace_entry x) = Some x.
Proof. by rewrite /decode_sample_trace_entry /sample_trace_entry pickleK. Qed.

Lemma decode_call_trace_entryK {o : opsig} (x : tgt o) :
  decode_call_trace_entry o (call_trace_entry x) = Some x.
Proof. by rewrite /decode_call_trace_entry /call_trace_entry pickleK. Qed.

Lemma decode_get_trace_entryK {l : Location} (x : l) :
  decode_get_trace_entry l (get_trace_entry x) = Some x.
Proof. by rewrite /decode_get_trace_entry /get_trace_entry pickleK. Qed.

Section ContinueFromTrace.

Context {Loc : Locations}.
Context {Import : Interface}.

(** [continue_from_trace p t] consumes the trace [t] as a prefix of [p].

  Heap reads, external calls, and random samples each consume one entry. Heap
  writes consume no entry because their continuation does not depend on an
  external outcome. When successful, the result is the residual program after
  the traced prefix. Failure means that the trace is inconsistent with [p]: a
  payload cannot be unpickled at the type expected by the current [raw_code]
  node, or the trace is longer than the remaining effectful events in the
  program.
*)
Fixpoint continue_from_trace {A : choiceType}
    (p : raw_code A) (t : trace) : option (raw_code A) :=
  match t with
  | [::] => Some p
  | e :: t' =>
      match p with
      | ret _ => None
      | opr o x k =>
          match decode_call_trace_entry o e with
          | Some y => continue_from_trace (k y) t'
          | None => None
          end
      | getr l k =>
          match decode_get_trace_entry l e with
          | Some y => continue_from_trace (k y) t'
          | None => None
          end
      | putr l v k =>
          continue_from_trace k t
      | sampler op k =>
          match decode_sample_trace_entry op e with
          | Some y => continue_from_trace (k y) t'
          | None => None
          end
      end
  end.

End ContinueFromTrace.
