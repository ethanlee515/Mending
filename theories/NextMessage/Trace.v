From Stdlib Require Import Unicode.Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssreflect eqtype ssrnat seq choice.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From SSProve Require Import NominalPrelude.

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

Definition packed_input := 'nat.

(* left = suspended; right = done *)
Definition suspended_program {A : choice_type} : choice_type :=
  (packed_input * trace_t) + A.

Fixpoint run_until_next_call_aux {T : choice_type} (prog : raw_code T) (fn : ident) (trace : trace_t) :
  raw_code suspended_program :=
  match prog with
  | ret v => ret (inr v)
  | opr o x k =>
    let '(f, _) := o in
    if f == fn then
      ret (inl (pickle x, trace))
    else (
      y ← op o ⋅ x ;;
      run_until_next_call_aux (k y) fn (rcons trace (pickle y))
    )
  | getr l k =>
      y ← getr l (fun y => ret y) ;;
      run_until_next_call_aux (k y) fn (rcons trace (pickle y))
  | putr l v k =>
      putr l v (run_until_next_call_aux k fn trace)
  | sampler op k =>
      y <$ op ;;
      run_until_next_call_aux (k y) fn (rcons trace (pickle y))
  end.

Definition run_until_next_call {T : choice_type} (prog : raw_code T) (fn : ident)
  : raw_code suspended_program :=
  run_until_next_call_aux prog fn nil.

Print resolve.

Definition call_from_package {X Y : choice_type} (p : raw_package) (fn : 'nat) (x : packed_input)
  : option (raw_code Y).
Admitted.

