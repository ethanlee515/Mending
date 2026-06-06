From Stdlib Require Import Unicode.Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssreflect eqtype ssrnat seq choice.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From extructures Require Import ord fset fmap.
From SSProve Require Import NominalPrelude.

Import PackageNotation.
Local Open Scope package_scope.

Inductive trace_entry :=
| call_entry (out : nat)
| get_entry (res : nat)
| put_entry
| sample_entry (res : nat).

Definition trace_t := seq trace_entry.

Definition packed_trace_entry_t : choice_type :=
  'nat + ('nat + ('unit + 'nat)).

Definition packed_trace_t : choice_type := 'list packed_trace_entry_t.

Definition pack_trace_entry (e : trace_entry) : packed_trace_entry_t :=
  match e with
  | call_entry out => inl out
  | get_entry res => inr (inl res)
  | put_entry => inr (inr (inl tt))
  | sample_entry res => inr (inr (inr res))
  end.

Definition unpack_trace_entry (e : packed_trace_entry_t) : trace_entry :=
  match e with
  | inl out => call_entry out
  | inr (inl res) => get_entry res
  | inr (inr (inl tt)) => put_entry
  | inr (inr (inr res)) => sample_entry res
  end.

Definition pack_trace (t : trace_t) : packed_trace_t :=
  map pack_trace_entry t.

Definition unpack_trace (t : packed_trace_t) : trace_t :=
  map unpack_trace_entry t.

Lemma unpack_pack_trace_entry (e : trace_entry) :
  unpack_trace_entry (pack_trace_entry e) = e.
Proof. by case: e. Qed.

Lemma unpack_pack_trace (t : trace_t) :
  unpack_trace (pack_trace t) = t.
Proof. by elim: t => //= e t ->; rewrite unpack_pack_trace_entry. Qed.

Lemma map_unpack_pack_trace (t : trace_t) :
  map unpack_trace_entry (map pack_trace_entry t) = t.
Proof. exact: unpack_pack_trace. Qed.

Definition decode_sample_entry (op : Op)
    (e : trace_entry) : option (Arit op) :=
  match e with
  | sample_entry res => unpickle res
  | _ => None
  end.

Definition decode_call_entry (o : opsig)
    (e : trace_entry) : option (tgt o) :=
  match e with
  | call_entry out => unpickle out
  | _ => None
  end.

Definition decode_get_entry (l : Location)
    (e : trace_entry) : option l :=
  match e with
  | get_entry res => unpickle res
  | _ => None
  end.

(** [continue_from_trace p t] consumes the trace [t] as a prefix of [p].

  Heap reads, heap writes, external calls, and random samples each consume one
  tagged entry. Write entries carry no payload, but their tag is still needed:
  when resuming from a suspended trace, the write has already happened in the
  suspended run, so replay must skip exactly that write in the original program.

  When successful, the result is the residual program after the traced prefix.
  Failure means that the trace is inconsistent with [p]: an entry has the wrong
  tag, a payload cannot be unpickled at the type expected by the current
  [raw_code] node, or the trace is longer than the remaining effectful events in
  the program.
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
          match e with
          | put_entry => continue_from_trace k t'
          | _ => None
          end
      | sampler op k =>
          match decode_sample_entry op e with
          | Some y => continue_from_trace (k y) t'
          | None => None
          end
      end
  end.

Lemma continue_from_trace_nil {A : choice_type} (p : raw_code A) :
  continue_from_trace p nil = Some p.
Proof. by case: p. Qed.

Lemma continue_from_trace_cat {A : choice_type}
    (p p' : raw_code A) (t1 t2 : trace_t) :
  continue_from_trace p t1 = Some p' ->
  continue_from_trace p (t1 ++ t2) = continue_from_trace p' t2.
Proof.
  elim: t1 p => [|e t1 IH] p /=.
  - move=> H.
    rewrite continue_from_trace_nil in H.
    by inversion H; subst.
  - case: p => //=.
    + move=> o x k.
      case Hdec: (decode_call_entry o e) => [y|] //=.
      exact: IH.
    + move=> l k.
      case Hdec: (decode_get_entry l e) => [y|] //=.
      exact: IH.
    + move=> l v k.
      case: e => //=.
      exact: IH.
    + move=> op k.
      case Hdec: (decode_sample_entry op e) => [y|] //=.
      exact: IH.
Qed.

Lemma continue_from_trace_rcons {A : choice_type}
    (p p' : raw_code A) (t : trace_t) (e : trace_entry) :
  continue_from_trace p t = Some p' ->
  continue_from_trace p (rcons t e) = continue_from_trace p' [:: e].
Proof.
  move=> H.
  rewrite -cats1.
  exact: continue_from_trace_cat H.
Qed.

Definition packed_input := 'nat.

(* left = suspended at the next call; right = done *)
Definition suspended_program {A : choice_type} : choice_type :=
  (packed_input + A) * packed_trace_t.

Fixpoint run_until_next_call_aux {T : choice_type} (prog : raw_code T) (fn : ident) (trace : trace_t) :
  raw_code suspended_program :=
  match prog with
  | ret v => ret (inr v, pack_trace trace)
  | opr o x k =>
    let '(f, _) := o in
    if f == fn then
      ret (inl (pickle x), pack_trace trace)
    else (
      y ← op o ⋅ x ;;
      run_until_next_call_aux (k y) fn (rcons trace (call_entry (pickle y)))
    )
  | getr l k =>
      y ← getr l (fun y => ret y) ;;
      run_until_next_call_aux (k y) fn (rcons trace (get_entry (pickle y)))
  | putr l v k =>
      putr l v (run_until_next_call_aux k fn (rcons trace put_entry))
  | sampler op k =>
      y <$ op ;;
      run_until_next_call_aux (k y) fn (rcons trace (sample_entry (pickle y)))
  end.

Definition run_until_next_call {T : choice_type} (prog : raw_code T) (fn : ident)
  : raw_code suspended_program :=
  run_until_next_call_aux prog fn nil.

Definition call_from_package {X Y : choice_type} (p : raw_package) (fn : ident) (x : packed_input)
  : option (raw_code Y) :=
  match unpickle x : option X with
  | Some x' => Some (resolve p (mkopsig fn X Y) x')
  | None => None
  end.

Definition invalid_trace_code {A : choice_type} : raw_code A :=
  sampler (A; distr.dnull) (@ret _).

Definition continue_after_call {A Y : choice_type}
    (prog : raw_code A) (local_trace : trace_t) (y : Y) : raw_code A :=
  match continue_from_trace prog (rcons local_trace (call_entry (pickle y))) with
  | Some prog' => prog'
  | None => invalid_trace_code
  end.

Lemma continue_after_call_here
    (X Y A : choice_type) (fn : ident) (x : X)
    (k : Y -> raw_code A) (y : Y) :
  continue_after_call (opr (mkopsig fn X Y) x k) nil y = k y.
Proof.
  rewrite /continue_after_call /= /decode_call_entry.
  by rewrite pickleK continue_from_trace_nil.
Qed.

Lemma continue_after_call_at_trace
    (X Y A : choice_type) (fn : ident) (prog : raw_code A)
    (local_trace : trace_t) (x : X) (k : Y -> raw_code A) (y : Y) :
  continue_from_trace prog local_trace =
    Some (opr (mkopsig fn X Y) x k) ->
  continue_after_call prog local_trace y = k y.
Proof.
  move=> Hlocal.
  rewrite /continue_after_call.
  rewrite (@continue_from_trace_rcons A prog
    (opr (mkopsig fn X Y) x k) local_trace
    (call_entry (pickle y)) Hlocal) /= /decode_call_entry.
  by rewrite pickleK continue_from_trace_nil.
Qed.

Lemma continue_from_trace_after_call_at_trace
    (X Y A : choice_type) (fn : ident)
    (root prog : raw_code A) (trace_prefix local_trace : trace_t)
    (x : X) (k : Y -> raw_code A) (y : Y) :
  continue_from_trace root trace_prefix = Some prog ->
  continue_from_trace prog local_trace =
    Some (opr (mkopsig fn X Y) x k) ->
  continue_from_trace root
    (rcons (trace_prefix ++ local_trace) (call_entry (pickle y))) =
  Some (k y).
Proof.
  move=> Hroot Hlocal.
  rewrite rcons_cat.
  rewrite (@continue_from_trace_cat A root prog trace_prefix
    (rcons local_trace (call_entry (pickle y))) Hroot).
  rewrite (@continue_from_trace_rcons A prog
    (opr (mkopsig fn X Y) x k) local_trace
    (call_entry (pickle y)) Hlocal) /= /decode_call_entry.
  by rewrite pickleK continue_from_trace_nil.
Qed.

(** [factor_calls_aux q p fn root trace_prefix] starts from [trace_prefix] in
  [root] and factors the next [q] calls to [fn] through [p].

  The prefix is the cursor into [root].  Each factored call extends it by the
  trace to the call and the call result returned by [p].
*)
Fixpoint factor_calls_aux (q : nat) {X Y A : choice_type}
    (p : raw_package) (fn : ident)
    (root : raw_code A) (trace_prefix : trace_t) : raw_code packed_trace_t :=
  match q with
  | 0 => ret (pack_trace trace_prefix)
  | S q' =>
      match continue_from_trace root trace_prefix with
      | Some prog =>
          s ← run_until_next_call prog fn ;;
          let '(status, packed_local_trace) := s in
          let local_trace := unpack_trace packed_local_trace in
          match status with
          | inr _ =>
              ret (pack_trace (trace_prefix ++ local_trace))
          | inl x =>
              match call_from_package (X := X) (Y := Y) p fn x with
              | Some body =>
                  y ← body ;;
                  factor_calls_aux q' (X := X) (Y := Y) p fn root
                    (rcons (trace_prefix ++ local_trace)
                      (call_entry (pickle y)))
              | None => invalid_trace_code
              end
          end
      | None => invalid_trace_code
      end
  end.

Definition factor_calls (q : nat) {X Y A : choice_type}
    (p : raw_package) (fn : ident) (prog : raw_code A)
    : raw_code packed_trace_t :=
  factor_calls_aux q (X := X) (Y := Y) p fn prog nil.

Definition compile_calls (q : nat) {X Y A : choice_type}
    (p : raw_package) (fn : ident) (prog : raw_code A) : raw_code A :=
  packed_trace ← factor_calls q (X := X) (Y := Y) p fn prog ;;
  match continue_from_trace prog (unpack_trace packed_trace) with
  | Some prog' => prog'
  | None => invalid_trace_code
  end.

Definition compile_next_call {X Y A : choice_type}
    (p : raw_package) (fn : ident) (prog : raw_code A) : raw_code A :=
  compile_calls 1 (X := X) (Y := Y) p fn prog.

Lemma fhas_same_ident_opsig
    (M : Interface) (fn : ident) (X Y : choice_type) (o : opsig) :
  fhas M (mkopsig fn X Y) ->
  fhas M o ->
  fst o = fn ->
  o = mkopsig fn X Y.
Proof.
  case: o => id [S T] Hfn Ho /= Hid; subst id.
  rewrite /fhas /mkopsig /= in Hfn Ho.
  by rewrite Hfn in Ho; inversion Ho.
Qed.

Lemma ident_eqb_eq (f fn : ident) :
  (f == fn)%bool = true -> f = fn.
Proof.
  elim: f fn => [|f IH] [|fn] //= H.
  by f_equal; exact: IH.
Qed.

Lemma code_link_closed
    (A : choice_type) (L : Locations) (p : raw_package)
    (prog : raw_code A) :
  ValidCode L [interface] prog ->
  code_link prog p = prog.
Proof.
  move=> Hvalid.
  induction Hvalid.
  - reflexivity.
  - exfalso.
    exact: (fhas_empty _ H).
  - simpl.
    f_equal.
    apply functional_extensionality => v.
    auto.
  - simpl.
    by rewrite IHHvalid.
  - simpl.
    f_equal.
    apply functional_extensionality => v.
    auto.
Qed.

Lemma code_link_resolve_closed
    (X Y : choice_type) (L : Locations) (M : Interface)
    (p : raw_package) (fn : ident) (x : X) :
  ValidPackage L [interface] M p ->
  fhas M (mkopsig fn X Y) ->
  code_link (resolve p (mkopsig fn X Y) x) p =
  resolve p (mkopsig fn X Y) x.
Proof.
  move=> Hp Hfn.
  have [body Hbody] : exists body, p fn = Some (X; Y; body).
  - have [body Hbody] : exists body, fhas p (fn, (X; Y; body)).
    + move: (valid_exports Hp (mkopsig fn X Y)) => [HM _].
      exact: HM.
    + by exists body.
  apply: code_link_closed.
  rewrite /resolve Hbody coerce_kleisliE.
  exact: (valid_imports Hp fn (X; Y; body) x Hbody).
Qed.

Lemma run_until_next_call_aux_correct_code_link
    (q : nat) (X Y A : choice_type)
    (L Lp : Locations) (M : Interface)
    (p : raw_package) (fn : ident)
    (root prog : raw_code A) (trace_prefix local_trace : trace_t) :
  ValidPackage Lp [interface] M p ->
  fhas M (mkopsig fn X Y) ->
  (forall (prog : raw_code A) (trace_prefix : trace_t),
    ValidCode L M prog ->
    continue_from_trace root trace_prefix = Some prog ->
    code_link
      (packed_trace ← factor_calls_aux q (X := X) (Y := Y) p fn
              root trace_prefix ;;
       match continue_from_trace root (unpack_trace packed_trace) with
       | Some prog' => prog'
       | None => invalid_trace_code
       end)
      p =
    code_link prog p) ->
  ValidCode L M prog ->
  continue_from_trace root (trace_prefix ++ local_trace) = Some prog ->
  code_link
    (packed_trace ←
       (s ← run_until_next_call_aux prog fn local_trace ;;
        match s with
        | (inl x, packed_local_trace) =>
            match call_from_package (X := X) (Y := Y) p fn x with
            | Some body =>
                y ← body ;;
                factor_calls_aux q (X := X) (Y := Y) p fn root
                  (rcons (trace_prefix ++ unpack_trace packed_local_trace)
                    (call_entry (pickle y)))
            | None => invalid_trace_code
            end
        | (inr _, packed_local_trace) =>
            ret (pack_trace (trace_prefix ++ unpack_trace packed_local_trace))
        end) ;;
     match continue_from_trace root (unpack_trace packed_trace) with
     | Some prog' => prog'
     | None => invalid_trace_code
     end)
    p =
  code_link prog p.
Proof.
  move=> Hp Hfn Hfactor Hvalid.
  move: trace_prefix local_trace.
  elim: Hvalid => [v|o x k Ho Hk IH|l k Hl Hk IH|l v k Hl Hk IH|op k Hk IH]
    tp lt Hcur /=.
  - by rewrite !unpack_pack_trace Hcur.
  - case: o Ho x k Hk IH Hcur => f [S T] Ho x k Hk IH Hcur /=.
    destruct ((f == fn)%bool) eqn:Hid; simpl.
    + have Hid_eq : f = fn := ident_eqb_eq f fn Hid.
      have Hop :
        (f, (S, T)) = mkopsig fn X Y.
      - apply: (fhas_same_ident_opsig M fn X Y).
        * exact: Hfn.
        * exact: Ho.
        * exact: Hid_eq.
      subst f.
      move: Hop x k Hk IH Hcur.
      rewrite /mkopsig /=.
      move=> [= -> ->] x k Hk IH Hcur.
      rewrite /call_from_package pickleK.
      rewrite unpack_pack_trace.
      rewrite code_link_bind.
      rewrite (@code_link_bind Y packed_trace_t
        (resolve p (mkopsig fn X Y) x)
        (fun y => factor_calls_aux q (X := X) (Y := Y) p fn root
          (rcons (tp ++ lt) (call_entry (pickle y)))) p).
      rewrite (@code_link_resolve_closed X Y Lp M p fn x Hp Hfn).
      rewrite bind_assoc.
      f_equal.
      apply functional_extensionality => y.
      rewrite -code_link_bind.
      have Hnext :
        continue_from_trace root
          (rcons (tp ++ lt) (call_entry (pickle y))) =
        Some (k y).
      {
        rewrite -cats1.
        rewrite (@continue_from_trace_cat A root
          (opr (mkopsig fn X Y) x k)
          (tp ++ lt) [:: call_entry (pickle y)] Hcur)
          /= /decode_call_entry.
        by rewrite pickleK continue_from_trace_nil.
      }
      exact: (Hfactor (k y)
        (rcons (tp ++ lt) (call_entry (pickle y))) (Hk y) Hnext).
    + f_equal.
      apply functional_extensionality => y.
      have Hnext :
        continue_from_trace root
          (tp ++ rcons lt (call_entry (pickle y))) =
        Some (k y).
      {
        rewrite -rcons_cat -cats1.
        rewrite (@continue_from_trace_cat A root
          (opr (f, (S, T)) x k)
          (tp ++ lt) [:: call_entry (pickle y)] Hcur)
          /= /decode_call_entry.
        by rewrite pickleK continue_from_trace_nil.
      }
      exact: (IH y tp (rcons lt (call_entry (pickle y))) Hnext).
  - f_equal.
    apply functional_extensionality => y.
    have Hnext :
      continue_from_trace root
        (tp ++ rcons lt (get_entry (pickle y))) =
      Some (k y).
    {
      rewrite -rcons_cat -cats1.
      rewrite (@continue_from_trace_cat A root (getr l k)
        (tp ++ lt) [:: get_entry (pickle y)] Hcur)
        /= /decode_get_entry.
      by rewrite pickleK continue_from_trace_nil.
    }
    exact: (IH y tp (rcons lt (get_entry (pickle y))) Hnext).
  - have Hnext :
      continue_from_trace root (tp ++ rcons lt put_entry) = Some k.
    {
      rewrite -rcons_cat -cats1.
      by rewrite (@continue_from_trace_cat A root (putr l v k)
        (tp ++ lt) [:: put_entry] Hcur) /= continue_from_trace_nil.
    }
    f_equal.
    exact: (IH tp (rcons lt put_entry) Hnext).
  - f_equal.
    apply functional_extensionality => y.
    have Hnext :
      continue_from_trace root
        (tp ++ rcons lt (sample_entry (pickle y))) =
      Some (k y).
    {
      rewrite -rcons_cat -cats1.
      rewrite (@continue_from_trace_cat A root (sampler op k)
        (tp ++ lt) [:: sample_entry (pickle y)] Hcur)
        /= /decode_sample_entry.
      by rewrite pickleK continue_from_trace_nil.
    }
    exact: (IH y tp (rcons lt (sample_entry (pickle y))) Hnext).
Qed.

Lemma factor_calls_aux_correct_code_link
    (q : nat) (X Y A : choice_type)
    (L Lp : Locations) (M : Interface)
    (p : raw_package) (fn : ident)
    (root prog : raw_code A) (trace_prefix : trace_t) :
  ValidPackage Lp [interface] M p ->
  fhas M (mkopsig fn X Y) ->
  ValidCode L M prog ->
  continue_from_trace root trace_prefix = Some prog ->
  code_link
    (packed_trace ← factor_calls_aux q (X := X) (Y := Y) p fn
            root trace_prefix ;;
     match continue_from_trace root (unpack_trace packed_trace) with
     | Some prog' => prog'
     | None => invalid_trace_code
     end)
    p =
  code_link prog p.
Proof.
  elim: q X Y A L Lp M p fn root prog trace_prefix
    => [|q IHq] X Y A L Lp M p fn root prog trace_prefix Hp Hfn Hvalid Htrace.
  - simpl.
    by rewrite unpack_pack_trace Htrace.
  - simpl.
    rewrite Htrace.
    rewrite /run_until_next_call.
    rewrite -[trace_prefix]cats0 in Htrace.
    exact: (@run_until_next_call_aux_correct_code_link
      q X Y A L Lp M p fn root prog trace_prefix nil
      Hp Hfn
      (fun prog trace_prefix Hvalid Htrace =>
        @IHq X Y A L Lp M p fn root prog trace_prefix
          Hp Hfn Hvalid Htrace)
      Hvalid Htrace).
Qed.

Lemma compile_calls_correct_code_link
    (q : nat) (X Y A : choice_type)
    (L Lp : Locations) (M : Interface)
    (p : raw_package) (fn : ident) (prog : raw_code A) :
  ValidPackage Lp [interface] M p ->
  fhas M (mkopsig fn X Y) ->
  ValidCode L M prog ->
  code_link
    (compile_calls q (X := X) (Y := Y) p fn prog)
    p =
  code_link prog p.
Proof.
  move=> Hp Hfn Hvalid.
  rewrite /compile_calls /factor_calls.
  eapply (@factor_calls_aux_correct_code_link q X Y A L Lp M p fn prog prog nil).
  - exact: Hp.
  - exact: Hfn.
  - exact: Hvalid.
  exact: continue_from_trace_nil.
Qed.

Theorem compile_calls_correct
  (q : nat) (X Y : choice_type)
  (L L' : Locations) (M E : Interface)
  (P P' : raw_package) (fn : ident)
  (o : opsig) (x : src o) h :
ValidPackage L M E P ->
ValidPackage L' [interface] M P' ->
fcompat L L' ->
fhas E o ->
fhas M (mkopsig fn X Y) ->
Pr_code
  (code_link
    (compile_calls q (X := X) (Y := Y) P' fn (resolve P o x))
    P')
  h =
Pr_op (P ∘ P') o x h.
Proof.
  move=> HP HP' _ Ho Hfn.
  rewrite /Pr_op.
  have Hcompile :
    code_link
      (compile_calls q (X := X) (Y := Y) P' fn (resolve P o x))
      P' =
    code_link (resolve P o x) P'.
  {
    apply: compile_calls_correct_code_link.
    - exact: HP'.
    - exact: Hfn.
    - exact: (@valid_resolve L M E P o x HP Ho).
  }
  rewrite Hcompile.
  by rewrite resolve_link.
Qed.
