(* Pythagorean call-compilation rules. *)

From Stdlib Require Import Unicode.Utf8.
From extructures Require Import ord fset fmap fperm.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals distr ssrZ realseq realsum exp lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".
From SSProve.Relational Require Import OrderEnrichedCategory.
From SSProve.Crypt Require Import ChoiceAsOrd Couplings StateTransformingLaxMorph.
From SSProve.Crypt Require Import Axioms StateTransfThetaDens.
From SSProve.Crypt Require Import choice_type fmap_extra SubDistr.
From SSProve.Crypt.nominal Require Import Pr.
From SSProve Require Import pkg_core_definition pkg_advantage pkg_composition
  pkg_notation.
From Mending.NextMessage Require Import Trace.
From Mending.Probability.KL Require Import Core.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras TupleExtras.
From Mending.Probability Require Import Ae OutputHeap PythSeq.
From Mending.Probability.KL Require Import Pyth.
From Mending.ProgramLogics Require Import Ae Hoare Pyth.
Local Open Scope AeNotations.
Local Open Scope HoareNotations.
Local Open Scope PythNotations.

Import PackageNotation.
Import pkg_heap.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope package_scope.
Local Open Scope ring_scope.

Definition heap_eq_on (K : Locations) (mem0 mem1 : heap) : Prop :=
  forall l, fhas K l -> get_heap mem0 l = get_heap mem1 l.

Lemma heap_eq_on_refl K mem :
  heap_eq_on K mem mem.
Proof. by move=> l _. Qed.

Lemma heap_eq_on_sym K mem0 mem1 :
  heap_eq_on K mem0 mem1 ->
  heap_eq_on K mem1 mem0.
Proof.
move=> H l Hl.
by rewrite H.
Qed.

Lemma heap_eq_on_trans K mem0 mem1 mem2 :
  heap_eq_on K mem0 mem1 ->
  heap_eq_on K mem1 mem2 ->
  heap_eq_on K mem0 mem2.
Proof.
move=> H01 H12 l Hl.
by rewrite H01 // H12.
Qed.

Lemma heap_eq_on_rename
    (π : {fperm Nominal.Nominal_atom__canonical__Ord_Ord})
    K mem0 mem1 :
  heap_eq_on K mem0 mem1 ->
  heap_eq_on
    (Nominal.rename π K)
    (Nominal.rename π mem0)
    (Nominal.rename π mem1).
Proof.
move=> Heq l Hl.
have Hpre : fhas K (Nominal.rename (π^-1)%fperm l : Location).
  have H := @fhas_rename (π^-1)%fperm (Nominal.rename π K) l Hl.
  by rewrite Nominal.renameK in H.
have -> : l =
    (Nominal.rename π
      (Nominal.rename (π^-1)%fperm l : Location) : Location).
  by rewrite Nominal.renameKV.
by rewrite !get_heap_rename Heq.
Qed.

Definition heap_eq_on_renamed
    (π : {fperm Nominal.Nominal_atom__canonical__Ord_Ord})
    (K : Locations)
    (memL memR : heap) : Prop :=
  heap_eq_on (Nominal.rename π K) (Nominal.rename π memL) memR.

Lemma heap_eq_on_renamed_refl
    (π : {fperm Nominal.Nominal_atom__canonical__Ord_Ord})
    K mem :
  heap_eq_on_renamed π K mem (Nominal.rename π mem).
Proof.
exact: heap_eq_on_refl.
Qed.

Lemma heap_eq_on_renamed_get
    (π : {fperm Nominal.Nominal_atom__canonical__Ord_Ord})
    K memL memR
    (l : Location) :
  heap_eq_on_renamed π K memL memR ->
  fhas K l ->
  get_heap memL l = get_heap memR (Nominal.rename π l : Location).
Proof.
move=> Hren Hl.
have Hloc := Hren (Nominal.rename π l : Location) (fhas_rename Hl).
by rewrite get_heap_rename in Hloc.
Qed.

Definition heap_pred_depends_only_on
  (K : Locations) (p : pred heap) : Prop :=
  forall mem0 mem1, heap_eq_on K mem0 mem1 -> p mem0 = p mem1.

Lemma heap_eq_on_set_heap_separate
  (K L : Locations) (mem : heap) (l : Location) (v : l) :
  fseparate K L ->
  fhas L l ->
  heap_eq_on K mem (set_heap mem l v).
Proof.
move=> HKL Hl k Hk.
rewrite get_set_heap_neq //.
apply/negP=> /eqP Hkl.
have Hnotin := notin_has_separate K L k Hk HKL.
have Hin := fhas_in L l Hl.
by rewrite Hkl Hin in Hnotin.
Qed.

Lemma heap_eq_on_set_heap_same
  (K : Locations) (mem0 mem1 : heap) (l : Location) (v : l) :
  heap_eq_on K mem0 mem1 ->
  heap_eq_on K (set_heap mem0 l v) (set_heap mem1 l v).
Proof.
move=> Heq k Hk.
rewrite /get_heap /set_heap !setmE.
case Hkl: (k.1 == l.1)=> //.
exact: Heq.
Qed.

Lemma heap_eq_on_renamed_set_heap_same
  (π : {fperm Nominal.Nominal_atom__canonical__Ord_Ord})
  (K : Locations) (memL memR : heap) (l : Location) (v : l) :
  heap_eq_on_renamed π K memL memR ->
  heap_eq_on_renamed π K
    (set_heap memL l v)
    (set_heap memR (Nominal.rename π l : Location) v).
Proof.
move=> Hren.
rewrite /heap_eq_on_renamed -set_heap_rename.
exact: (heap_eq_on_set_heap_same (Nominal.rename π K)
  (Nominal.rename π memL) memR (Nominal.rename π l) v Hren).
Qed.

Lemma heap_eq_on_set_heap_left_separate
  (K L : Locations) (mem0 mem1 : heap) (l : Location) (v : l) :
  fseparate K L ->
  fhas L l ->
  heap_eq_on K mem0 mem1 ->
  heap_eq_on K (set_heap mem0 l v) mem1.
Proof.
move=> HKL Hl Heq k Hk.
rewrite get_set_heap_neq.
- exact: Heq.
- apply/negP=> /eqP Hkl.
  have Hnotin := notin_has_separate K L k Hk HKL.
  have Hin := fhas_in L l Hl.
  by rewrite Hkl Hin in Hnotin.
Qed.

Lemma heap_eq_on_set_heap_right_separate
  (K L : Locations) (mem0 mem1 : heap) (l : Location) (v : l) :
  fseparate K L ->
  fhas L l ->
  heap_eq_on K mem0 mem1 ->
  heap_eq_on K mem0 (set_heap mem1 l v).
Proof.
move=> HKL Hl Heq k Hk.
rewrite get_set_heap_neq.
- exact: Heq.
- apply/negP=> /eqP Hkl.
  have Hnotin := notin_has_separate K L k Hk HKL.
  have Hin := fhas_in L l Hl.
  by rewrite Hkl Hin in Hnotin.
Qed.

Lemma heap_eq_on_renamed_set_heap_left_separate
  (π : {fperm Nominal.Nominal_atom__canonical__Ord_Ord})
  (K L : Locations) (memL memR : heap) (l : Location) (v : l) :
  fseparate
    (Nominal.rename π K : Locations)
    (Nominal.rename π L : Locations) ->
  fhas L l ->
  heap_eq_on_renamed π K memL memR ->
  heap_eq_on_renamed π K (set_heap memL l v) memR.
Proof.
move=> Hsep Hl Hren.
rewrite /heap_eq_on_renamed -set_heap_rename.
exact: (heap_eq_on_set_heap_left_separate
  (Nominal.rename π K) (Nominal.rename π L)
  (Nominal.rename π memL) memR
  (Nominal.rename π l : Location) v
  Hsep (fhas_rename Hl) Hren).
Qed.

Lemma heap_eq_on_renamed_set_heap_right_separate
  (π : {fperm Nominal.Nominal_atom__canonical__Ord_Ord})
  (K L : Locations) (memL memR : heap) (l : Location) (v : l) :
  fseparate (Nominal.rename π K : Locations) L ->
  fhas L l ->
  heap_eq_on_renamed π K memL memR ->
  heap_eq_on_renamed π K memL (set_heap memR l v).
Proof.
move=> Hsep Hl Hren.
rewrite /heap_eq_on_renamed.
exact: (heap_eq_on_set_heap_right_separate
  (Nominal.rename π K : Locations) L (Nominal.rename π memL) memR
  l v Hsep Hl Hren).
Qed.

Lemma closed_code_preserves_heap_eq_on
  {A : choice_type} (K L : Locations) (prog : raw_code A) mem out :
  ValidCode L [interface] prog ->
  fseparate K L ->
  out \in dinsupp (Pr_code prog mem) ->
  heap_eq_on K mem out.2.
Proof.
move=> Hvalid HKL.
have Hvc := valid_code_from_class L [interface] A prog Hvalid.
elim: Hvc mem out=> [a|o x k Ho Hk IH|l k Hl Hk IH
    |l v k Hl Hk IH|op k Hk IH] mem out Hout /=.
- rewrite Pr_code_ret in Hout.
  have -> : out = (a, mem).
    exact: in_dunit Hout.
  exact: heap_eq_on_refl.
- exfalso.
  rewrite /fhas /= in Ho.
  by fmap_invert Ho.
- rewrite Pr_code_get in Hout.
  exact: (IH (get_heap mem l) mem out Hout).
- rewrite Pr_code_put in Hout.
  have Htail := IH (set_heap mem l v) out Hout.
  exact: (heap_eq_on_trans K mem (set_heap mem l v) out.2
    (heap_eq_on_set_heap_separate K L mem l v HKL Hl) Htail).
- rewrite Pr_code_sample in Hout.
  have [a _ Hinner] := @dinsupp_dlet R _ _ _ _ _ Hout.
  exact: (IH a mem out Hinner).
Qed.

Lemma linked_code_preserves_heap_eq_on
  {A : choice_type} (K L L' : Locations) (M : Interface)
  (P : raw_package) (prog : raw_code A) mem out :
  ValidCode L M prog ->
  ValidPackage L' [interface] M P ->
  fseparate K L ->
  fseparate K L' ->
  out \in dinsupp (Pr_code (code_link prog P) mem) ->
  heap_eq_on K mem out.2.
Proof.
move=> Hvalid HP HKL HKL'.
have Hvc := valid_code_from_class L M A prog Hvalid.
elim: Hvc mem out=> [a|o x k Ho Hk IH|l k Hl Hk IH
    |l v k Hl Hk IH|op k Hk IH] mem out Hout /=.
- rewrite Pr_code_ret in Hout.
  have -> : out = (a, mem).
    exact: in_dunit Hout.
  exact: heap_eq_on_refl.
- rewrite Pr_code_bind in Hout.
  have [mid Hmid Hinner] := @dinsupp_dlet R _ _ _ _ _ Hout.
  have Hresolve_valid :
      ValidCode L' [interface] (resolve P o x).
    exact: (@valid_resolve L' [interface] M P o x HP Ho).
  have Hmid_eq :
      heap_eq_on K mem mid.2.
    exact: (closed_code_preserves_heap_eq_on
      K L' (resolve P o x) mem mid Hresolve_valid HKL' Hmid).
  have Htail_eq :
      heap_eq_on K mid.2 out.2.
    exact: (IH mid.1 mid.2 out Hinner).
  exact: (heap_eq_on_trans K mem mid.2 out.2 Hmid_eq Htail_eq).
- rewrite Pr_code_get in Hout.
  exact: (IH (get_heap mem l) mem out Hout).
- rewrite Pr_code_put in Hout.
  have Htail_eq :
      heap_eq_on K (set_heap mem l v) out.2.
    exact: (IH (set_heap mem l v) out Hout).
  exact: (heap_eq_on_trans K mem (set_heap mem l v) out.2
    (heap_eq_on_set_heap_separate K L mem l v HKL Hl) Htail_eq).
- rewrite Pr_code_sample in Hout.
  have [a _ Hinner] := @dinsupp_dlet R _ _ _ _ _ Hout.
  exact: (IH a mem out Hinner).
Qed.


Definition package_preserves_heap_pred_except
  (M : Interface) (P : raw_package) (skip : ident)
  (p : pred heap) : Prop :=
  forall (o : opsig) (x : src o),
    fhas M o ->
    fst o != skip ->
    ⊨Hoare ⦃ fun in_mem => p in_mem.2 ⦄
      (fun x => resolve P o x)
    ⦃ fun out_mem => p out_mem.2 ⦄.

Lemma continue_from_trace_valid
  {A : choice_type} (L : Locations) (M : Interface)
  (root prog : raw_code A) (trace_prefix : trace_t) :
  ValidCode L M root ->
  continue_from_trace root trace_prefix = Some prog ->
  ValidCode L M prog.
Proof.
elim: trace_prefix root=> [|e trace_prefix IH] root Hvalid Htrace.
  rewrite continue_from_trace_nil in Htrace.
  by inversion Htrace; subst.
case: root Hvalid Htrace=> //=.
- move=> o x k Hvalid.
  case Hdec: (decode_call_entry o e)=> [y|] //= Htrace.
  have [_ Hk] := @inversion_valid_opr L M A o x k
    (valid_code_from_class L M A (opr o x k) Hvalid).
  exact: (IH (k y) (Hk y) Htrace).
- move=> l k Hvalid.
  case Hdec: (decode_get_entry l e)=> [y|] //= Htrace.
  have [_ Hk] := @inversion_valid_getr L M A l k
    (valid_code_from_class L M A (getr l k) Hvalid).
  exact: (IH (k y) (Hk y) Htrace).
- move=> l v k Hvalid.
  case: e=> //= Htrace.
  have [_ Hk] := @inversion_valid_putr L M A l v k
    (valid_code_from_class L M A (putr l v k) Hvalid).
  exact: (IH k Hk Htrace).
- move=> op k Hvalid.
  case Hdec: (decode_sample_entry op e)=> [y|] //= Htrace.
  have Hk := @inversion_valid_sampler L M A op k
    (valid_code_from_class L M A (sampler op k) Hvalid).
  exact: (IH (k y) (Hk y) Htrace).
Qed.

Lemma linkedRunUntilNextCallAuxPreservesHeapPred
  (X Y B : choice_type)
  (K L L' : Locations) (M : Interface)
  (P' : raw_package) (fn : ident)
  (prog : raw_code B) (trace : trace_t)
  (call_invariant : pred heap) :
  ValidCode L M prog ->
  ValidPackage L' [interface] M P' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Hoare ⦃ fun in_mem => call_invariant in_mem.2 ⦄
    (fun _ : 'unit => code_link
      (run_until_next_call_aux prog fn trace) P')
  ⦃ fun out_mem => call_invariant out_mem.2 ⦄.
Proof.
move=> Hvalid HP' HKL Hdep HP'_pres Hfn.
rewrite /hoareJudgment=> u mem Hinv out.
change (is_true (call_invariant mem)) in Hinv.
clear u.
move: trace mem Hinv out.
have Hvc := valid_code_from_class L M B prog Hvalid.
elim: Hvc=> [b|o x k Ho Hk IH|l k Hl Hk IH|l v k Hl Hk IH|op k Hk IH]
    trace mem Hinv out Hout /=.
- rewrite Pr_code_ret in Hout.
  have -> : out = ((inr b, pack_trace trace), mem).
    exact: (in_dunit Hout).
  exact: Hinv.
- move: out Hout.
  case: o Ho x k Hk IH=> f [S T] Ho x k Hk IH out Hout /=.
  case Hfid: (f == fn)%bool.
  + rewrite /run_until_next_call_aux Hfid /code_link /= in Hout.
    rewrite Pr_code_ret in Hout.
    have -> : out = ((inl (pickle x), pack_trace trace), mem).
      exact: (in_dunit Hout).
    exact: Hinv.
  + rewrite /run_until_next_call_aux Hfid /code_link /= in Hout.
    rewrite Pr_code_bind in Hout.
    have [mid Hmid Hinner] := @dinsupp_dlet R _ _ _ _ _ Hout.
    have Hneq : (f, (S, T)).1 != fn by rewrite /= Hfid.
    have Hpres := HP'_pres (f, (S, T)) x Ho Hneq.
    have Hmid_inv : call_invariant mid.2.
      exact: (Hpres x mem Hinv mid Hmid).
    exact: (IH mid.1 (rcons trace (call_entry (pickle mid.1)))
      mid.2 Hmid_inv out Hinner).
- rewrite Pr_code_get in Hout.
  exact: (IH (get_heap mem l) (rcons trace (get_entry (pickle (get_heap mem l))))
    mem Hinv out Hout).
- rewrite Pr_code_put in Hout.
  have Hinv' : call_invariant (set_heap mem l v).
    move: (Hdep mem (set_heap mem l v)
      (heap_eq_on_set_heap_separate K L mem l v HKL Hl)).
    by move=> <-.
  exact: (IH (rcons trace put_entry) (set_heap mem l v) Hinv' out Hout).
- rewrite Pr_code_sample in Hout.
  have [a _ Hinner] := @dinsupp_dlet R _ _ _ _ _ Hout.
  exact: (IH a (rcons trace (sample_entry (pickle a))) mem Hinv out Hinner).
Qed.

Lemma linkedRunUntilNextCallPreservesHeapPred
  (X Y B : choice_type)
  (K L L' : Locations) (M : Interface)
  (P' : raw_package) (fn : ident)
  (prog : raw_code B)
  (call_invariant : pred heap) :
  ValidCode L M prog ->
  ValidPackage L' [interface] M P' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Hoare ⦃ fun in_mem => call_invariant in_mem.2 ⦄
    (fun _ : 'unit => code_link (run_until_next_call prog fn) P')
  ⦃ fun out_mem => call_invariant out_mem.2 ⦄.
Proof.
move=> Hvalid HP' HKL Hdep HP'_pres Hfn.
rewrite /run_until_next_call.
exact: (linkedRunUntilNextCallAuxPreservesHeapPred X Y B K L L' M P'
  fn prog nil call_invariant Hvalid HP' HKL Hdep HP'_pres Hfn).
Qed.

Lemma pythCompileCallsFromTraceInvalidRule
  (q : nat) (X Y B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root : raw_code B) (trace_prefix : trace_t)
  (eps : R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  continue_from_trace root trace_prefix = None ->
  ⊨Pyth1 ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( eps )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨PythC ⦃ fun mems =>
          let '(memL, memR) := mems in
          (memL == memR) && call_invariant memL ⦄
    (code_link
      (compile_calls_from_trace q.+1 (X := X) (Y := Y) P' fn
        root trace_prefix)
      P')
    ≈( pythCallErrors q eps )
    (code_link
      (compile_calls_from_trace q.+1 (X := X) (Y := Y) P'' fn
        root trace_prefix)
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Htrace Hcall.
have [Heps_nonneg _] := Hcall.
have Heps : 0 <= eps.
  exact: (Heps_nonneg ord0).
rewrite /pythClosedJudgment.
rewrite /compile_calls_from_trace /= Htrace.
apply: pythReflRule.
- exact: (pythCallErrors_nonneg q eps Heps).
- move=> memL memR [] [] Hpre.
  move/andP: Hpre=> [/eqP -> _].
  by split.
- move=> mem [] y Hpre Hy.
  rewrite /= /invalid_trace_code Pr_code_sample dlet_null_ext in Hy.
  by move/dinsuppP: Hy; rewrite dnullE.
Qed.

Lemma pythCompileCallsFromTraceInvalidTupleRule
  {ℓ : nat}
  (q : nat) (X Y B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root : raw_code B) (trace_prefix : trace_t)
  (s : (ℓ.+1).-tuple R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  continue_from_trace root trace_prefix = None ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( s )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨PythC ⦃ fun mems =>
          let '(memL, memR) := mems in
          (memL == memR) && call_invariant memL ⦄
    (code_link
      (compile_calls_from_trace q.+1 (X := X) (Y := Y) P' fn
        root trace_prefix)
      P')
    ≈( pythErrorTupleTuple (pythCallErrorsTuple q s) )
    (code_link
      (compile_calls_from_trace q.+1 (X := X) (Y := Y) P'' fn
        root trace_prefix)
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Htrace Hcall.
have [Hs_nonneg _] := Hcall.
rewrite /pythClosedJudgment.
rewrite /compile_calls_from_trace /= Htrace.
apply: pythReflRule.
- exact: (pythCallErrorsTuple_nonneg q s Hs_nonneg).
- move=> memL memR [] [] Hpre.
  move/andP: Hpre=> [/eqP -> _].
  by split.
- move=> mem [] y Hpre Hy.
  rewrite /= /invalid_trace_code Pr_code_sample dlet_null_ext in Hy.
  by move/dinsuppP: Hy; rewrite dnullE.
Qed.

Definition compile_calls_from_trace_step_cont
    (q : nat) {X Y A : choice_type}
    (p : raw_package) (fn : ident)
    (root : raw_code A) (trace_prefix : trace_t)
    (s : suspended_program (A := A)) : raw_code A :=
  let '(status, packed_local_trace) := s in
  let local_trace := unpack_trace packed_local_trace in
  let resume_from_packed_trace packed_trace :=
    match continue_from_trace root (unpack_trace packed_trace) with
    | Some prog' => prog'
    | None => invalid_trace_code
    end in
  match status with
  | inl x =>
      match call_from_package (X := X) (Y := Y) p fn x with
      | Some body =>
          y ← body ;;
          compile_calls_from_trace q (X := X) (Y := Y) p fn root
            (rcons (trace_prefix ++ local_trace) (call_entry (pickle y)))
      | None =>
          packed_trace ← invalid_trace_code (A := packed_trace_t) ;;
          resume_from_packed_trace packed_trace
      end
  | inr _ =>
      packed_trace ← ret (pack_trace (trace_prefix ++ local_trace)) ;;
      resume_from_packed_trace packed_trace
  end.

Lemma compileCallsFromTraceS_step_cont
    (q : nat) (X Y A : choice_type)
    (p : raw_package) (fn : ident)
    (root prog : raw_code A) (trace_prefix : trace_t) :
  continue_from_trace root trace_prefix = Some prog ->
  compile_calls_from_trace q.+1 (X := X) (Y := Y) p fn root trace_prefix =
  bind (run_until_next_call prog fn)
    (compile_calls_from_trace_step_cont q (X := X) (Y := Y) p fn
      root trace_prefix).
Proof.
move=> Htrace.
rewrite (@compile_calls_from_traceS_decompose q X Y A p fn root prog
  trace_prefix Htrace).
rewrite /compile_calls_from_trace_step_cont bind_assoc.
f_equal.
apply functional_extensionality=> s.
case: s=> [[x|a] packed_local_trace] /=.
- case: (call_from_package (X := X) (Y := Y) p fn x)=> [body|] //=.
  by rewrite bind_assoc.
- by [].
Qed.

Definition prepend_suspended_trace {A : choice_type}
    (trace_prefix : trace_t) (s : suspended_program (A := A)) :
    suspended_program :=
  let '(status, packed_local_trace) := s in
  (status, pack_trace (trace_prefix ++ unpack_trace packed_local_trace)).

Lemma runUntilNextCallAux_prepend_trace
    (A : choice_type) (prog : raw_code A) fn
    (trace_prefix local_trace : trace_t) :
  run_until_next_call_aux prog fn (trace_prefix ++ local_trace) =
  bind (run_until_next_call_aux prog fn local_trace)
    (fun s => ret (prepend_suspended_trace trace_prefix s)).
Proof.
move: trace_prefix local_trace.
elim: prog=> [a|o x k IH|l k IH|l v k IH|op k IH]
    trace_prefix local_trace /=.
- by rewrite /prepend_suspended_trace /= unpack_pack_trace.
- case: o x k IH=> f [S T] x k IH /=.
  case Hfid: (f == fn).
  + by rewrite /prepend_suspended_trace /= unpack_pack_trace.
  + cbn.
    f_equal.
    apply functional_extensionality=> y.
    rewrite rcons_cat.
    exact: IH.
- cbn.
  f_equal.
  apply functional_extensionality=> y.
  rewrite rcons_cat.
  exact: IH.
- cbn.
  f_equal.
  rewrite rcons_cat.
  exact: IH.
- cbn.
  f_equal.
  apply functional_extensionality=> y.
  rewrite rcons_cat.
  exact: IH.
Qed.

Lemma compileCallsFromTraceStepCont_prepend_trace
    (q : nat) (X Y A : choice_type)
    (p : raw_package) (fn : ident) (root : raw_code A)
    (trace_prefix : trace_t) (s : suspended_program (A := A)) :
  compile_calls_from_trace_step_cont q (X := X) (Y := Y) p fn root nil
    (prepend_suspended_trace trace_prefix s) =
  compile_calls_from_trace_step_cont q (X := X) (Y := Y) p fn root
    trace_prefix s.
Proof.
case: s=> [[packed_x|a] packed_local_trace];
  rewrite /compile_calls_from_trace_step_cont /prepend_suspended_trace /=
    !unpack_pack_trace //.
Qed.

Lemma compileCallsFromTraceStepCont_runUntilNextCallAux_prepend
    (q : nat) (X Y A : choice_type)
    (p : raw_package) (fn : ident) (root prog : raw_code A)
    (trace_prefix : trace_t) :
  bind (run_until_next_call_aux prog fn trace_prefix)
    (compile_calls_from_trace_step_cont q (X := X) (Y := Y) p fn root nil) =
  bind (run_until_next_call prog fn)
    (compile_calls_from_trace_step_cont q (X := X) (Y := Y) p fn root
      trace_prefix).
Proof.
rewrite /run_until_next_call.
rewrite -(cats0 trace_prefix).
rewrite runUntilNextCallAux_prepend_trace.
rewrite bind_assoc.
f_equal.
apply functional_extensionality=> s.
rewrite /= cats0.
by rewrite compileCallsFromTraceStepCont_prepend_trace.
Qed.

Lemma code_link_resolve_closed_with
    (X Y : choice_type) (L : Locations) (M : Interface)
    (p P_link : raw_package) (fn : ident) (x : X) :
  ValidPackage L [interface] M p ->
  fhas M (mkopsig fn X Y) ->
  code_link (resolve p (mkopsig fn X Y) x) P_link =
  resolve p (mkopsig fn X Y) x.
Proof.
move=> Hp Hfn.
apply: code_link_closed.
exact: (@valid_resolve L [interface] M p (mkopsig fn X Y) x Hp Hfn).
Qed.

Lemma code_link_rename
    {A : choice_type} {π}
    (c : raw_code A) (p : raw_package) :
  Nominal.rename π (code_link c p) =
  code_link (Nominal.rename π c) (Nominal.rename π p).
Proof.
induction c in p |- *; cbn.
- reflexivity.
- change (Nominal.rename π
    (bind (resolve p o x) (fun b : tgt o => code_link (k b) p)) =
    bind (resolve (Nominal.rename π p) o x)
      (fun b : tgt o =>
        code_link (Nominal.rename π (k b)) (Nominal.rename π p))).
  rewrite mcode_bind resolve_rename.
  f_equal.
  apply functional_extensionality=> y.
  exact: H.
- f_equal.
  apply functional_extensionality=> y.
  exact: H.
- f_equal.
  exact: IHc.
- f_equal.
  apply functional_extensionality=> y.
  exact: H.
Qed.

Lemma code_link_invalid_trace_code
    (A : choice_type) (P_link : raw_package) :
  code_link (invalid_trace_code (A := A)) P_link =
  invalid_trace_code.
Proof.
by rewrite /invalid_trace_code /=.
Qed.

Lemma Pr_code_bind_invalid_trace_code
    (A B : choice_type) (cont : A -> raw_code B) mem :
  Pr_code (x ← invalid_trace_code (A := A) ;; cont x) mem =
  Pr_code (invalid_trace_code (A := B)) mem.
Proof.
rewrite Pr_code_bind /invalid_trace_code !Pr_code_sample.
by rewrite !dlet_null_ext.
Qed.

Lemma Pr_code_bind_invalid_trace_code_ext
    (A B : choice_type) (contL contR : A -> raw_code B) mem :
  Pr_code (x ← invalid_trace_code (A := A) ;; contL x) mem =
  Pr_code (x ← invalid_trace_code (A := A) ;; contR x) mem.
Proof.
rewrite !Pr_code_bind_invalid_trace_code.
by [].
Qed.

Lemma Pr_code_link_bind_invalid_trace_code
    (A B : choice_type) (cont : A -> raw_code B)
    (P_link : raw_package) mem :
  Pr_code (code_link (x ← invalid_trace_code (A := A) ;; cont x) P_link)
    mem =
  Pr_code (invalid_trace_code (A := B)) mem.
Proof.
rewrite code_link_bind.
rewrite Pr_code_bind_invalid_trace_code.
exact: Pr_code_bind_invalid_trace_code.
Qed.

Lemma Pr_code_link_bind_invalid_trace_code_ext
    (A B : choice_type) (contL contR : A -> raw_code B)
    (P_link : raw_package) mem :
  Pr_code (code_link (x ← invalid_trace_code (A := A) ;; contL x) P_link)
    mem =
  Pr_code (code_link (x ← invalid_trace_code (A := A) ;; contR x) P_link)
    mem.
Proof.
rewrite !Pr_code_link_bind_invalid_trace_code.
by [].
Qed.

Lemma pythCallAtRule
  (X Y : choice_type)
  (P' P'' : raw_package) (fn : ident)
  (eps : R) (call_invariant : pred heap) (x : X) :
  ⊨Pyth1 ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( eps )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨Pyth1 ⦃ fun inps =>
          let '((_, memL), (_, memR)) := inps in
          (memL == memR) && call_invariant memL ⦄
    (fun _ : 'unit => resolve P' (mkopsig fn X Y) x)
    ≈( eps )
    (fun _ : 'unit => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> [Hs Hpyth].
split; first exact: Hs.
move=> memL memR [] [] Hpre.
have Hpre_call :
    (let '((xL, memL0), (xR, memR0)) :=
        ((x, memL), (x, memR)) in
      (xL == xR) && (memL0 == memR0) && call_invariant memL0).
  move/andP: Hpre=> [Hmem Hinv].
  by rewrite eqxx Hmem Hinv.
exact: (Hpyth memL memR x x Hpre_call).
Qed.

Lemma pythCallAtTupleRule
  {ℓ : nat}
  (X Y : choice_type)
  (P' P'' : raw_package) (fn : ident)
  (s : (ℓ.+1).-tuple R) (call_invariant : pred heap) (x : X) :
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( s )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨Pyth ⦃ fun inps =>
          let '((_, memL), (_, memR)) := inps in
          (memL == memR) && call_invariant memL ⦄
    (fun _ : 'unit => resolve P' (mkopsig fn X Y) x)
    ≈( s )
    (fun _ : 'unit => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> [Hs Hpyth].
split; first exact: Hs.
move=> memL memR [] [] Hpre.
have Hpre_call :
    (let '((xL, memL0), (xR, memR0)) :=
        ((x, memL), (x, memR)) in
      (xL == xR) && (memL0 == memR0) && call_invariant memL0).
  move/andP: Hpre=> [Hmem Hinv].
  by rewrite eqxx Hmem Hinv.
exact: (Hpyth memL memR x x Hpre_call).
Qed.

(** The left half of a call coupling is an ordinary invariant-preservation
    Hoare fact for the implementation package. *)
Lemma pythCallLeftHoare
  (X Y : choice_type)
  (P' P'' : raw_package) (fn : ident)
  (eps : R) (call_invariant : pred heap) (x : X) :
  ⊨Pyth1 ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( eps )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨Hoare ⦃ fun in_mem => call_invariant in_mem.2 ⦄
    (fun _ : 'unit => resolve P' (mkopsig fn X Y) x)
  ⦃ fun out_mem => call_invariant out_mem.2 ⦄.
Proof.
move=> [_ Hpyth].
rewrite /hoareJudgment=> u mem Hinv out Hout /=.
case: u Hinv Hout=> Hinv Hout.
have Hpre :
    (let '((xL, memL), (xR, memR)) := ((x, mem), (x, mem)) in
      (xL == xR) && (memL == memR) && call_invariant memL).
  by rewrite !eqxx Hinv.
have [P [Q [_ [_ [_ [HpostL _]]]]]] := Hpyth mem mem x x Hpre.
case: out Hout=> y mem' Hout.
exact: (HpostL (y, mem') Hout).
Qed.

Lemma pythCallLeftHoareTuple
  {ℓ : nat}
  (X Y : choice_type)
  (P' P'' : raw_package) (fn : ident)
  (s : (ℓ.+1).-tuple R) (call_invariant : pred heap) (x : X) :
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( s )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨Hoare ⦃ fun in_mem => call_invariant in_mem.2 ⦄
    (fun _ : 'unit => resolve P' (mkopsig fn X Y) x)
  ⦃ fun out_mem => call_invariant out_mem.2 ⦄.
Proof.
move=> [_ Hpyth].
rewrite /hoareJudgment=> u mem Hinv out Hout /=.
case: u Hinv Hout=> Hinv Hout.
have Hpre :
    (let '((xL, memL), (xR, memR)) := ((x, mem), (x, mem)) in
      (xL == xR) && (memL == memR) && call_invariant memL).
  by rewrite !eqxx Hinv.
have [P [Q [_ [_ [_ [HpostL _]]]]]] := Hpyth mem mem x x Hpre.
case: out Hout=> y mem' Hout.
exact: (HpostL (y, mem') Hout).
Qed.

(** General preservation for linked residual code.  The only interesting case
    is an operation with identifier [fn], where [pythCallLeftHoare] supplies
    the missing package-preservation fact. *)
Lemma linkedCodePreservesHeapPred
  (X Y A : choice_type)
  (K L L' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (prog : raw_code A)
  (eps : R)
  (call_invariant : pred heap) :
  ValidCode L M prog ->
  ValidPackage L' [interface] M P' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Pyth1 ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( eps )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨Hoare ⦃ fun in_mem => call_invariant in_mem.2 ⦄
    (fun _ : 'unit => code_link prog P')
  ⦃ fun out_mem => call_invariant out_mem.2 ⦄.
Proof.
move=> Hvalid HP' HKL Hdep HP'_pres Hfn Hcall.
rewrite /hoareJudgment=> u mem Hinv out.
change (is_true (call_invariant mem)) in Hinv.
clear u.
have Hvc := valid_code_from_class L M A prog Hvalid.
elim: Hvc mem Hinv out=> [a|o x k Ho Hk IH|l k Hl Hk IH
    |l v k Hl Hk IH|op k Hk IH] mem Hinv out Hout /=.
- rewrite Pr_code_ret in Hout.
  have -> : out = (a, mem).
    exact: (in_dunit Hout).
  exact: Hinv.
- move: out Hout.
  case: o Ho x k Hk IH=> f [S T] Ho x k Hk IH out Hout /=.
  rewrite Pr_code_bind in Hout.
  have [mid Hmid Hinner] := @dinsupp_dlet R _ _ _ _ _ Hout.
  case Hfid: (f == fn)%bool.
  + have Hid : f = fn := ident_eqb_eq f fn Hfid.
    have Hop : (f, (S, T)) = mkopsig fn X Y.
      exact: (fhas_same_ident_opsig M fn X Y (f, (S, T)) Hfn Ho Hid).
    subst f.
    inversion Hop; subst S T.
    have Hpres := pythCallLeftHoare X Y P' P'' fn eps call_invariant x
      Hcall.
    have Hmid_inv : call_invariant mid.2.
      exact: (Hpres tt mem Hinv mid Hmid).
    exact: (IH mid.1 mid.2 Hmid_inv out Hinner).
  + have Hneq : (f, (S, T)).1 != fn by rewrite /= Hfid.
    have Hpres := HP'_pres (f, (S, T)) x Ho Hneq.
    have Hmid_inv : call_invariant mid.2.
      exact: (Hpres x mem Hinv mid Hmid).
    exact: (IH mid.1 mid.2 Hmid_inv out Hinner).
- rewrite Pr_code_get in Hout.
  exact: (IH (get_heap mem l) mem Hinv out Hout).
- rewrite Pr_code_put in Hout.
  have Hinv' : call_invariant (set_heap mem l v).
    move: (Hdep mem (set_heap mem l v)
      (heap_eq_on_set_heap_separate K L mem l v HKL Hl)).
    by move=> <-.
  exact: (IH (set_heap mem l v) Hinv' out Hout).
- rewrite Pr_code_sample in Hout.
  have [a _ Hinner] := @dinsupp_dlet R _ _ _ _ _ Hout.
  exact: (IH a mem Hinv out Hinner).
Qed.

Lemma linkedCodePreservesHeapPredTuple
  {ℓ : nat}
  (X Y A : choice_type)
  (K L L' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (prog : raw_code A)
  (s : (ℓ.+1).-tuple R)
  (call_invariant : pred heap) :
  ValidCode L M prog ->
  ValidPackage L' [interface] M P' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( s )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨Hoare ⦃ fun in_mem => call_invariant in_mem.2 ⦄
    (fun _ : 'unit => code_link prog P')
  ⦃ fun out_mem => call_invariant out_mem.2 ⦄.
Proof.
move=> Hvalid HP' HKL Hdep HP'_pres Hfn Hcall.
rewrite /hoareJudgment=> u mem Hinv out.
change (is_true (call_invariant mem)) in Hinv.
clear u.
have Hvc := valid_code_from_class L M A prog Hvalid.
elim: Hvc mem Hinv out=> [a|o x k Ho Hk IH|l k Hl Hk IH
    |l v k Hl Hk IH|op k Hk IH] mem Hinv out Hout /=.
- rewrite Pr_code_ret in Hout.
  have -> : out = (a, mem).
    exact: (in_dunit Hout).
  exact: Hinv.
- move: out Hout.
  case: o Ho x k Hk IH=> f [S T] Ho x k Hk IH out Hout /=.
  rewrite Pr_code_bind in Hout.
  have [mid Hmid Hinner] := @dinsupp_dlet R _ _ _ _ _ Hout.
  case Hfid: (f == fn)%bool.
  + have Hid : f = fn := ident_eqb_eq f fn Hfid.
    have Hop : (f, (S, T)) = mkopsig fn X Y.
      exact: (fhas_same_ident_opsig M fn X Y (f, (S, T)) Hfn Ho Hid).
    subst f.
    inversion Hop; subst S T.
    have Hpres := pythCallLeftHoareTuple X Y P' P'' fn s
      call_invariant x Hcall.
    have Hmid_inv : call_invariant mid.2.
      exact: (Hpres tt mem Hinv mid Hmid).
    exact: (IH mid.1 mid.2 Hmid_inv out Hinner).
  + have Hneq : (f, (S, T)).1 != fn by rewrite /= Hfid.
    have Hpres := HP'_pres (f, (S, T)) x Ho Hneq.
    have Hmid_inv : call_invariant mid.2.
      exact: (Hpres x mem Hinv mid Hmid).
    exact: (IH mid.1 mid.2 Hmid_inv out Hinner).
- rewrite Pr_code_get in Hout.
  exact: (IH (get_heap mem l) mem Hinv out Hout).
- rewrite Pr_code_put in Hout.
  have Hinv' : call_invariant (set_heap mem l v).
    move: (Hdep mem (set_heap mem l v)
      (heap_eq_on_set_heap_separate K L mem l v HKL Hl)).
    by move=> <-.
  exact: (IH (set_heap mem l v) Hinv' out Hout).
- rewrite Pr_code_sample in Hout.
  have [a _ Hinner] := @dinsupp_dlet R _ _ _ _ _ Hout.
  exact: (IH a mem Hinv out Hinner).
Qed.

(** Peel one compiled-call step after a valid trace prefix.  The shared
    [run_until_next_call] part is exposed as the first bind. *)
Lemma codeLinkCompileCallsFromTraceS_decompose
    (q : nat) (X Y A : choice_type)
    (p P_link : raw_package) (fn : ident)
    (root prog : raw_code A) (trace_prefix : trace_t) :
  continue_from_trace root trace_prefix = Some prog ->
  code_link
    (@compile_calls_from_trace q.+1 X Y A p fn root trace_prefix)
    P_link =
  bind (code_link (run_until_next_call prog fn) P_link)
    (fun s =>
      code_link
        (compile_calls_from_trace_step_cont q (X := X) (Y := Y) p fn
          root trace_prefix s)
        P_link).
Proof.
move=> Htrace.
rewrite (@compile_calls_from_traceS_decompose q X Y A p fn root prog
  trace_prefix Htrace).
rewrite !code_link_bind bind_assoc.
f_equal.
apply functional_extensionality=> s.
rewrite -code_link_bind.
case: s=> [[x|a] packed_local_trace] /=.
- case: (call_from_package (X := X) (Y := Y) p fn x)=> [body|] //=.
  by rewrite bind_assoc.
- by [].
Qed.

Lemma Pr_code_codeLink_compileCallsFromTrace_cursor
    (q : nat) (X Y A : choice_type)
    (p P_link : raw_package) (fn : ident)
    (root prog : raw_code A) (trace_prefix local_trace : trace_t)
    mem :
  continue_from_trace root trace_prefix = Some prog ->
  Pr_code (code_link
    (compile_calls_from_trace q (X := X) (Y := Y) p fn root
      (trace_prefix ++ local_trace)) P_link) mem =
  Pr_code (code_link
    (compile_calls_from_trace q (X := X) (Y := Y) p fn prog
      local_trace) P_link) mem.
Proof.
move: X Y A p P_link fn root prog trace_prefix local_trace mem.
elim: q=> [|q IH] X Y A p P_link fn root prog
    trace_prefix local_trace mem Htrace.
- rewrite /compile_calls_from_trace /factor_calls_aux /= !unpack_pack_trace.
  by rewrite (@continue_from_trace_cat A root prog trace_prefix local_trace
    Htrace).
- case Hlocal: (continue_from_trace prog local_trace)=> [prog'|].
  + have Hroot_local :
      continue_from_trace root (trace_prefix ++ local_trace) = Some prog'.
      by rewrite (@continue_from_trace_cat A root prog trace_prefix
        local_trace Htrace) Hlocal.
    rewrite (codeLinkCompileCallsFromTraceS_decompose q X Y A p P_link fn
      root prog' (trace_prefix ++ local_trace) Hroot_local).
    rewrite (codeLinkCompileCallsFromTraceS_decompose q X Y A p P_link fn
      prog prog' local_trace Hlocal).
    rewrite !Pr_code_bind.
    apply: distr_ext=> out.
    apply: eq_in_dlet; last by [].
    move=> y _ z.
    case: y=> [[[packed_x|b] packed_local_trace] mem'] /=.
    * case Hx: (call_from_package (X := X) (Y := Y) p fn packed_x)=>
        [body|].
      -- rewrite !code_link_bind !Pr_code_bind.
         apply: eq_in_dlet; last by [].
         move=> ymem _ z'.
         case: ymem=> y mem''.
         rewrite -catA rcons_cat.
         rewrite (IH X Y A p P_link fn root prog trace_prefix
           (rcons (local_trace ++ unpack_trace packed_local_trace)
             (call_entry (pickle y))) mem'' Htrace).
         by [].
      -- rewrite (Pr_code_link_bind_invalid_trace_code_ext
           packed_trace_t A
           (fun packed_trace =>
             match continue_from_trace root (unpack_trace packed_trace) with
             | Some prog'0 => prog'0
             | None => invalid_trace_code
             end)
           (fun packed_trace =>
             match continue_from_trace prog (unpack_trace packed_trace) with
             | Some prog'0 => prog'0
             | None => invalid_trace_code
             end)
           P_link mem').
         by [].
    * rewrite !unpack_pack_trace.
      by rewrite -catA (@continue_from_trace_cat A root prog trace_prefix
        (local_trace ++ unpack_trace packed_local_trace) Htrace).
  + have Hroot_local :
      continue_from_trace root (trace_prefix ++ local_trace) = None.
      by rewrite (@continue_from_trace_cat A root prog trace_prefix
        local_trace Htrace) Hlocal.
    rewrite /compile_calls_from_trace /factor_calls_aux /=.
    rewrite Hroot_local Hlocal.
    rewrite (Pr_code_link_bind_invalid_trace_code_ext
      packed_trace_t A
      (fun packed_trace =>
        match continue_from_trace root (unpack_trace packed_trace) with
        | Some prog'0 => prog'0
        | None => invalid_trace_code
        end)
      (fun packed_trace =>
        match continue_from_trace prog (unpack_trace packed_trace) with
        | Some prog'0 => prog'0
        | None => invalid_trace_code
        end)
      P_link mem).
    by [].
Qed.

Lemma Pr_code_codeLink_compileCallsFromTrace_aux_prepend
    (q : nat) (X Y A : choice_type)
    (p P_link : raw_package) (fn : ident)
    (root prog : raw_code A) (trace_prefix : trace_t) mem :
  continue_from_trace root trace_prefix = Some prog ->
  Pr_code (code_link
    (packed_trace ←
       (s ← run_until_next_call_aux prog fn trace_prefix ;;
        match s with
        | (inl x, packed_local_trace) =>
            match call_from_package (X := X) (Y := Y) p fn x with
            | Some body =>
                y ← body ;;
                factor_calls_aux q (X := X) (Y := Y) p fn root
                  (rcons (unpack_trace packed_local_trace)
                    (call_entry (pickle y)))
            | None => invalid_trace_code
            end
        | (inr _, packed_local_trace) =>
            ret (pack_trace (unpack_trace packed_local_trace))
        end) ;;
     match continue_from_trace root (unpack_trace packed_trace) with
     | Some prog' => prog'
     | None => invalid_trace_code
     end) P_link) mem =
  Pr_code (code_link
    (compile_calls_from_trace q.+1 (X := X) (Y := Y) p fn root
      trace_prefix) P_link) mem.
Proof.
move=> Htrace.
transitivity (Pr_code (code_link
  (bind (run_until_next_call_aux prog fn trace_prefix)
    (compile_calls_from_trace_step_cont q (X := X) (Y := Y) p fn root nil))
  P_link) mem).
- rewrite /compile_calls_from_trace_step_cont /compile_calls_from_trace.
  rewrite bind_assoc.
  f_equal.
  f_equal.
  f_equal.
  apply functional_extensionality=> s.
  case: s=> [[packed_x|a] packed_local_trace] /=.
  + case: (call_from_package (X := X) (Y := Y) p fn packed_x)=>
      [body|] /=.
    * by rewrite bind_assoc.
    * by [].
  + by [].
- rewrite compileCallsFromTraceStepCont_runUntilNextCallAux_prepend.
  rewrite code_link_bind.
  by rewrite -(codeLinkCompileCallsFromTraceS_decompose q X Y A p P_link
    fn root prog trace_prefix Htrace).
Qed.

Lemma codeLinkClosedPrefixBind
    (A B : choice_type) (L : Locations) (P_link : raw_package)
    (prefix : raw_code A) (cont : A -> raw_code B) :
  ValidCode L [interface] prefix ->
  code_link (bind prefix cont) P_link =
  bind prefix (fun x => code_link (cont x) P_link).
Proof.
move=> Hvalid.
move: cont.
elim: Hvalid=> [a|o x k Ho Hk IH|l k Hl Hk IH
    |l v k Hl Hk IH|op k Hk IH] cont /=.
- by [].
- exfalso.
  exact: (fhas_empty _ Ho).
- f_equal.
  apply functional_extensionality=> y.
  exact: (IH y cont).
- f_equal.
  exact: (IH cont).
- f_equal.
  apply functional_extensionality=> y.
  exact: (IH y cont).
Qed.

Lemma codeLinkCompileCalls0
    (X Y A : choice_type) (p P_link : raw_package)
    (fn : ident) (prog : raw_code A) :
  code_link (compile_calls 0 (X := X) (Y := Y) p fn prog) P_link =
  code_link prog P_link.
Proof.
by rewrite /compile_calls /compile_calls_from_trace /factor_calls_aux /=
  continue_from_trace_nil.
Qed.

Lemma codeLinkCompileCallsClosedPrefix0
    (X Y A B : choice_type)
    (L : Locations) (p P_link : raw_package) (fn : ident)
    (prefix : raw_code A) (cont : A -> raw_code B) :
  ValidCode L [interface] prefix ->
  code_link
    (compile_calls 0 (X := X) (Y := Y) p fn
      (bind prefix cont))
    P_link =
  bind prefix (fun x =>
    code_link
      (compile_calls 0 (X := X) (Y := Y) p fn (cont x))
      P_link).
Proof.
move=> Hvalid.
rewrite codeLinkCompileCalls0.
rewrite (codeLinkClosedPrefixBind A B L P_link prefix cont Hvalid).
f_equal.
apply functional_extensionality=> x.
by rewrite codeLinkCompileCalls0.
Qed.

Lemma Pr_code_codeLinkCompileCallsClosedPrefix
    (q : nat) (X Y A B : choice_type)
    (L : Locations) (p P_link : raw_package) (fn : ident)
    (prefix : raw_code A) (cont : A -> raw_code B) mem :
  ValidCode L [interface] prefix ->
  Pr_code (code_link
    (compile_calls q (X := X) (Y := Y) p fn
      (bind prefix cont))
    P_link) mem =
  Pr_code (bind prefix (fun x =>
    code_link
      (compile_calls q (X := X) (Y := Y) p fn (cont x))
      P_link)) mem.
Proof.
move: q X Y B p P_link fn cont mem.
case=> [|q] X Y B p P_link fn cont mem Hvalid.
- rewrite (codeLinkCompileCallsClosedPrefix0 X Y A B L p P_link fn
    prefix cont Hvalid).
  by [].
- move: cont mem.
  elim: Hvalid=> [a|o x k Ho Hk IH|l k Hl Hk IH
      |l v k Hl Hk IH|op k Hk IH] cont mem /=.
  + by [].
  + exfalso.
    exact: (fhas_empty _ Ho).
  + rewrite !Pr_code_get.
    set y := get_heap mem l.
    transitivity (Pr_code (code_link
      (compile_calls_from_trace q.+1 (X := X) (Y := Y) p fn
        (v ← get l ;; x ← k v ;; cont x)
        [:: get_entry (pickle y)]) P_link) mem).
    * apply: Pr_code_codeLink_compileCallsFromTrace_aux_prepend.
      by rewrite /= /decode_get_entry pickleK continue_from_trace_nil.
    * rewrite -(cats0 [:: get_entry (pickle y)]).
      rewrite (Pr_code_codeLink_compileCallsFromTrace_cursor q.+1 X Y B
        p P_link fn
        (v ← get l ;; x ← k v ;; cont x)
        (x ← k y ;; cont x)
        [:: get_entry (pickle y)] [::] mem).
      -- exact: (IH y cont mem).
      -- by rewrite /= /decode_get_entry pickleK continue_from_trace_nil.
  + rewrite !Pr_code_put.
    transitivity (Pr_code (code_link
      (compile_calls_from_trace q.+1 (X := X) (Y := Y) p fn
        (#put l := v ;; x ← k ;; cont x)
        [:: put_entry]) P_link) (set_heap mem l v)).
    * apply: Pr_code_codeLink_compileCallsFromTrace_aux_prepend.
      by rewrite /= continue_from_trace_nil.
    * rewrite -(cats0 [:: put_entry]).
      rewrite (Pr_code_codeLink_compileCallsFromTrace_cursor q.+1 X Y B
        p P_link fn
        (#put l := v ;; x ← k ;; cont x)
        (x ← k ;; cont x)
        [:: put_entry] [::] (set_heap mem l v)).
      -- exact: (IH cont (set_heap mem l v)).
      -- by rewrite /= continue_from_trace_nil.
  + rewrite !Pr_code_sample.
    apply: distr_ext=> z.
    apply: eq_in_dlet=> // y _ z'.
    transitivity (Pr_code (code_link
      (compile_calls_from_trace q.+1 (X := X) (Y := Y) p fn
        (a ← sample op ;; x ← k a ;; cont x)
        [:: sample_entry (pickle y)]) P_link) mem z').
    * rewrite (Pr_code_codeLink_compileCallsFromTrace_aux_prepend q X Y B
        p P_link fn
        (a ← sample op ;; x ← k a ;; cont x)
        (x ← k y ;; cont x)
        [:: sample_entry (pickle y)] mem).
      -- by [].
      -- by rewrite /= /decode_sample_entry pickleK continue_from_trace_nil.
    * rewrite -(cats0 [:: sample_entry (pickle y)]).
      rewrite (Pr_code_codeLink_compileCallsFromTrace_cursor q.+1 X Y B
        p P_link fn
        (a ← sample op ;; x ← k a ;; cont x)
        (x ← k y ;; cont x)
        [:: sample_entry (pickle y)] [::] mem).
      -- rewrite (IH y cont mem).
         by [].
      -- by rewrite /= /decode_sample_entry pickleK continue_from_trace_nil.
Qed.

(** Base-case continuation after the shared search: either no [fn] call remains,
    the packed call input is invalid, or we spend the single call budget and
    resume the traced residual program. *)
Lemma pythCompileCallsFromTraceStepContinuationBaseRule
  (X Y B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root : raw_code B) (trace_prefix : trace_t)
  (eps : R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Pyth1 ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( eps )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun s => code_link
      (compile_calls_from_trace_step_cont 0
        (X := X) (Y := Y) P' fn root trace_prefix s)
      P')
    ≈( cat_tuple [tuple eps] [tuple 0] )
    (fun s => code_link
      (compile_calls_from_trace_step_cont 0
        (X := X) (Y := Y) P'' fn root trace_prefix s)
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Hcall.
have Heps : 0 <= eps := proj1 Hcall ord0.
split.
  move=> i.
  apply: (cat_tuple_nonneg [tuple eps] [tuple 0] i);
    by move=> j; rewrite [j]ord1.
move=> memL memR sL sR Hpre.
move/andP: Hpre=> [/andP [/eqP Hs /eqP Hmem] Hinv].
subst sR.
subst memL.
case: sL=> [[packed_x|b] packed_local_trace] /=.
-
  case Hx: (unpickle packed_x : option X)=> [x|].
  + rewrite /compile_calls_from_trace_step_cont /= /call_from_package Hx.
    rewrite !code_link_bind.
    rewrite (code_link_resolve_closed_with X Y L' M P' P' fn x HP' Hfn).
    rewrite (code_link_resolve_closed_with X Y L'' M P'' P' fn x HP'' Hfn).
    rewrite /compile_calls_from_trace /=.
    have Hbranch :
      ⊨Pyth ⦃ fun inps =>
              let '((_, memL), (_, memR)) := inps in
              (memL == memR) && call_invariant memL ⦄
        (fun _ : 'unit => resolve P' (mkopsig fn X Y) x)
        ≈( [tuple eps] )
        (fun _ : 'unit => resolve P'' (mkopsig fn X Y) x)
      ⦃ fun out =>
        let '(_, mem) := out in call_invariant mem ⦄.
      exact: (pythCallAtRule X Y P' P'' fn eps call_invariant x Hcall).
    have Hcont_hoare :
      ⊨Hoare ⦃ fun out =>
          let '(_, mem) := out in call_invariant mem ⦄
        (fun y : Y => code_link
          (packed_trace ← ret (pack_trace
            (rcons (trace_prefix ++ unpack_trace packed_local_trace)
              (call_entry (pickle y)))) ;;
           match continue_from_trace root (unpack_trace packed_trace) with
           | Some prog' => prog'
           | None => invalid_trace_code
           end)
          P')
      ⦃ fun out =>
        let '(_, mem) := out in call_invariant mem ⦄.
      rewrite /hoareJudgment=> y mem Hinv0 out Hout.
      move: Hout.
      case: out=> z mem' Hout.
      rewrite code_link_bind in Hout.
      rewrite Pr_code_bind Pr_code_ret in Hout.
      have [packed_trace Hpacked Hinner] :=
        @dinsupp_dlet R _ _ _ _ _ Hout.
      have Hpacked_eq : packed_trace =
          (pack_trace (rcons
             (trace_prefix ++ unpack_trace packed_local_trace)
             (call_entry (pickle y))), mem).
        exact: (in_dunit Hpacked).
      move: Hinner.
      rewrite Hpacked_eq /=.
      move=> Hinner.
      rewrite unpack_pack_trace in Hinner.
      case Hcont: (continue_from_trace root
          (rcons (trace_prefix ++ unpack_trace packed_local_trace)
            (call_entry (pickle y))))=> [prog'|].
      * have Hvalid_prog' : ValidCode L M prog'.
          exact: (continue_from_trace_valid L M root prog'
            (rcons (trace_prefix ++ unpack_trace packed_local_trace)
              (call_entry (pickle y))) Hvalid Hcont).
        have Hhoare := linkedCodePreservesHeapPred X Y B K L L' M P' P''
          fn prog' eps call_invariant Hvalid_prog' HP' HKL Hdep HP'_pres
          Hfn Hcall.
        rewrite Hcont in Hinner.
        change (is_true
          ((z, mem') \in dinsupp (Pr_code (code_link prog' P') mem)))
          in Hinner.
        exact: (Hhoare tt mem Hinv0 (z, mem') Hinner).
      * rewrite Hcont in Hinner.
        rewrite /invalid_trace_code Pr_code_sample dlet_null_ext in Hinner.
        by move/dinsuppP: Hinner; rewrite dnullE.
    have Hseq := @pythAeSeqRule 0 'unit 'unit Y B
      (fun _ : 'unit => resolve P' (mkopsig fn X Y) x)
      (fun _ : 'unit => resolve P'' (mkopsig fn X Y) x)
      (fun y : Y => code_link
        (packed_trace ← ret (pack_trace
          (rcons (trace_prefix ++ unpack_trace packed_local_trace)
            (call_entry (pickle y)))) ;;
         match continue_from_trace root (unpack_trace packed_trace) with
         | Some prog' => prog'
         | None => invalid_trace_code
         end)
        P')
      (fun inps =>
        let '((_, memL), (_, memR)) := inps in
        (memL == memR) && call_invariant memL)
      (fun out =>
        let '(_, mem) := out in call_invariant mem)
      (fun out =>
        let '(_, mem) := out in call_invariant mem)
      [tuple eps] Hbranch Hcont_hoare.
    have [_ Hseq'] := Hseq.
    have Hpre_unit : (tt == tt) && (memR == memR) && call_invariant memR.
      by rewrite !eqxx.
    exact: (Hseq' memR memR tt tt Hpre_unit).
  + have Hbranch :
      ⊨Pyth ⦃ fun inps =>
              let '((xL, memL), (xR, memR)) := inps in
              (xL == xR) && (memL == memR) && call_invariant memL ⦄
        (fun _ : suspended_program (A := B) => code_link
          (compile_calls_from_trace_step_cont 0
            (X := X) (Y := Y) P' fn root trace_prefix
            (inl packed_x, packed_local_trace))
          P')
        ≈( cat_tuple [tuple eps] [tuple 0] )
        (fun _ : suspended_program (A := B) => code_link
          (compile_calls_from_trace_step_cont 0
            (X := X) (Y := Y) P'' fn root trace_prefix
            (inl packed_x, packed_local_trace))
          P')
      ⦃ fun out =>
        let '(_, mem) := out in call_invariant mem ⦄.
      rewrite /compile_calls_from_trace_step_cont /= /call_from_package Hx.
      apply: pythReflRule.
      * move=> i.
        apply: (cat_tuple_nonneg [tuple eps] [tuple 0] i);
          by move=> j; rewrite [j]ord1.
      * move=> memL0 memR0 xL0 xR0 Hpre.
        move/andP: Hpre=> [/andP [/eqP -> /eqP ->] _].
        by split.
      * move=> mem s out Hpre Hy.
        change (is_true
          (out \in dinsupp
            (Pr_code
              (code_link
                (x ← invalid_trace_code (A := packed_trace_t) ;;
                 match continue_from_trace root (unpack_trace x) with
                 | Some prog' => prog'
                 | None => invalid_trace_code
                 end) P') mem)))
          in Hy.
        rewrite code_link_bind code_link_invalid_trace_code in Hy.
        rewrite Pr_code_bind in Hy.
        have [mid Hmid _] := @dinsupp_dlet R _ _ _ _ _ Hy.
        rewrite /= /invalid_trace_code Pr_code_sample dlet_null_ext in Hmid.
        by move/dinsuppP: Hmid; rewrite dnullE.
    have [_ Hbranch'] := Hbranch.
    pose s_bad : suspended_program (A := B) :=
      (@inl (chInterp packed_input) (chInterp B) packed_x,
        packed_local_trace).
    have Hpre_s : (s_bad == s_bad) && (memR == memR) && call_invariant memR.
      by rewrite !eqxx Hinv.
    exact: (Hbranch' memR memR s_bad s_bad Hpre_s).
-
  rewrite /compile_calls_from_trace_step_cont /=.
  rewrite unpack_pack_trace.
  case Hcont: (continue_from_trace root
      (trace_prefix ++ unpack_trace packed_local_trace))=> [prog'|].
  + have Hbranch :
      ⊨Pyth ⦃ fun inps =>
              let '((xL, memL), (xR, memR)) := inps in
              (xL == xR) && (memL == memR) && call_invariant memL ⦄
        (fun _ : suspended_program (A := B) => code_link prog' P')
        ≈( cat_tuple [tuple eps] [tuple 0] )
        (fun _ : suspended_program (A := B) => code_link prog' P')
      ⦃ fun out =>
        let '(_, mem) := out in call_invariant mem ⦄.
      apply: pythReflRule.
      * move=> i.
        apply: (cat_tuple_nonneg [tuple eps] [tuple 0] i);
          by move=> j; rewrite [j]ord1.
      * move=> memL0 memR0 xL0 xR0 Hpre.
        move/andP: Hpre=> [/andP [/eqP -> /eqP ->] _].
        by split.
      * move=> mem s out Hpre Hy.
        have Hvalid_prog' : ValidCode L M prog'.
          exact: (continue_from_trace_valid L M root prog'
            (trace_prefix ++ unpack_trace packed_local_trace) Hvalid Hcont).
        have Hhoare := linkedCodePreservesHeapPred X Y B K L L' M P' P''
          fn prog' eps call_invariant Hvalid_prog' HP' HKL Hdep HP'_pres Hfn
          Hcall.
        move/andP: Hpre=> [_ Hinv0].
        case: out Hy=> y mem' Hy.
        exact: (Hhoare tt mem Hinv0 (y, mem') Hy).
    have [_ Hbranch'] := Hbranch.
    pose s_done : suspended_program (A := B) :=
      (@inr (chInterp packed_input) (chInterp B) b, packed_local_trace).
    have Hpre_s :
        (s_done == s_done) && (memR == memR) && call_invariant memR.
      by rewrite !eqxx Hinv.
    exact: (Hbranch' memR memR s_done s_done Hpre_s).
  + have Hbranch :
      ⊨Pyth ⦃ fun inps =>
              let '((xL, memL), (xR, memR)) := inps in
              (xL == xR) && (memL == memR) && call_invariant memL ⦄
        (fun _ : suspended_program (A := B) =>
          code_link (invalid_trace_code (A := B)) P')
        ≈( cat_tuple [tuple eps] [tuple 0] )
        (fun _ : suspended_program (A := B) =>
          code_link (invalid_trace_code (A := B)) P')
      ⦃ fun out =>
        let '(_, mem) := out in call_invariant mem ⦄.
      apply: pythReflRule.
      * move=> i.
        apply: (cat_tuple_nonneg [tuple eps] [tuple 0] i);
          by move=> j; rewrite [j]ord1.
      * move=> memL0 memR0 xL0 xR0 Hpre.
        move/andP: Hpre=> [/andP [/eqP -> /eqP ->] _].
        by split.
      * move=> mem s out Hpre Hy.
        change (is_true
          (out \in dinsupp
            (Pr_code (code_link (invalid_trace_code (A := B)) P') mem)))
          in Hy.
        rewrite code_link_invalid_trace_code in Hy.
        rewrite /= /invalid_trace_code Pr_code_sample dlet_null_ext in Hy.
        by move/dinsuppP: Hy; rewrite dnullE.
    have [_ Hbranch'] := Hbranch.
    pose s_done : suspended_program (A := B) :=
      (@inr (chInterp packed_input) (chInterp B) b, packed_local_trace).
    have Hpre_s :
        (s_done == s_done) && (memR == memR) && call_invariant memR.
      by rewrite !eqxx Hinv.
    exact: (Hbranch' memR memR s_done s_done Hpre_s).
Qed.

Lemma pythCompileCallsFromTraceStepContinuationBaseTupleRule
  {ℓ : nat}
  (X Y B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root : raw_code B) (trace_prefix : trace_t)
  (s : (ℓ.+1).-tuple R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( s )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun sp => code_link
      (compile_calls_from_trace_step_cont 0
        (X := X) (Y := Y) P' fn root trace_prefix sp)
      P')
    ≈( pythCallContErrorBase s )
    (fun sp => code_link
      (compile_calls_from_trace_step_cont 0
        (X := X) (Y := Y) P'' fn root trace_prefix sp)
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Hcall.
have [Hs_nonneg _] := Hcall.
split.
  exact: (pythCallContErrorBase_nonneg s Hs_nonneg).
move=> memL memR sL sR Hpre.
move/andP: Hpre=> [/andP [/eqP Hs_eq /eqP Hmem] Hinv].
subst sR.
subst memL.
case: sL=> [[packed_x|b] packed_local_trace] /=.
-
  case Hx: (unpickle packed_x : option X)=> [x|].
  + rewrite /compile_calls_from_trace_step_cont /= /call_from_package Hx.
    rewrite !code_link_bind.
    rewrite (code_link_resolve_closed_with X Y L' M P' P' fn x HP' Hfn).
    rewrite (code_link_resolve_closed_with X Y L'' M P'' P' fn x HP'' Hfn).
    rewrite /compile_calls_from_trace /=.
    have Hbranch :
      ⊨Pyth ⦃ fun inps =>
              let '((_, memL), (_, memR)) := inps in
              (memL == memR) && call_invariant memL ⦄
        (fun _ : 'unit => resolve P' (mkopsig fn X Y) x)
        ≈( s )
        (fun _ : 'unit => resolve P'' (mkopsig fn X Y) x)
      ⦃ fun out =>
        let '(_, mem) := out in call_invariant mem ⦄.
      exact: (pythCallAtTupleRule X Y P' P'' fn s call_invariant x Hcall).
    have Hcont_hoare :
      ⊨Hoare ⦃ fun out =>
          let '(_, mem) := out in call_invariant mem ⦄
        (fun y : Y => code_link
          (packed_trace ← ret (pack_trace
            (rcons (trace_prefix ++ unpack_trace packed_local_trace)
              (call_entry (pickle y)))) ;;
           match continue_from_trace root (unpack_trace packed_trace) with
           | Some prog' => prog'
           | None => invalid_trace_code
           end)
          P')
      ⦃ fun out =>
        let '(_, mem) := out in call_invariant mem ⦄.
      rewrite /hoareJudgment=> y mem Hinv0 out Hout.
      move: Hout.
      case: out=> z mem' Hout.
      rewrite code_link_bind in Hout.
      rewrite Pr_code_bind Pr_code_ret in Hout.
      have [packed_trace Hpacked Hinner] :=
        @dinsupp_dlet R _ _ _ _ _ Hout.
      have Hpacked_eq : packed_trace =
          (pack_trace (rcons
             (trace_prefix ++ unpack_trace packed_local_trace)
             (call_entry (pickle y))), mem).
        exact: (in_dunit Hpacked).
      move: Hinner.
      rewrite Hpacked_eq /=.
      move=> Hinner.
      rewrite unpack_pack_trace in Hinner.
      case Hcont: (continue_from_trace root
          (rcons (trace_prefix ++ unpack_trace packed_local_trace)
            (call_entry (pickle y))))=> [prog'|].
      * have Hvalid_prog' : ValidCode L M prog'.
          exact: (continue_from_trace_valid L M root prog'
            (rcons (trace_prefix ++ unpack_trace packed_local_trace)
              (call_entry (pickle y))) Hvalid Hcont).
        have Hhoare := linkedCodePreservesHeapPredTuple X Y B K L L' M
          P' P'' fn prog' s call_invariant Hvalid_prog' HP' HKL Hdep
          HP'_pres Hfn Hcall.
        rewrite Hcont in Hinner.
        change (is_true
          ((z, mem') \in dinsupp (Pr_code (code_link prog' P') mem)))
          in Hinner.
        exact: (Hhoare tt mem Hinv0 (z, mem') Hinner).
      * rewrite Hcont in Hinner.
        rewrite /invalid_trace_code Pr_code_sample dlet_null_ext in Hinner.
        by move/dinsuppP: Hinner; rewrite dnullE.
    have Hseq := @pythAeSeqRule ℓ 'unit 'unit Y B
      (fun _ : 'unit => resolve P' (mkopsig fn X Y) x)
      (fun _ : 'unit => resolve P'' (mkopsig fn X Y) x)
      (fun y : Y => code_link
        (packed_trace ← ret (pack_trace
          (rcons (trace_prefix ++ unpack_trace packed_local_trace)
            (call_entry (pickle y)))) ;;
         match continue_from_trace root (unpack_trace packed_trace) with
         | Some prog' => prog'
         | None => invalid_trace_code
         end)
        P')
      (fun inps =>
        let '((_, memL), (_, memR)) := inps in
        (memL == memR) && call_invariant memL)
      (fun out =>
        let '(_, mem) := out in call_invariant mem)
      (fun out =>
        let '(_, mem) := out in call_invariant mem)
      s Hbranch Hcont_hoare.
    have [_ Hseq'] := Hseq.
    have Hpre_unit : (tt == tt) && (memR == memR) && call_invariant memR.
      by rewrite !eqxx.
    exact: (Hseq' memR memR tt tt Hpre_unit).
  + have Hbranch :
      ⊨Pyth ⦃ fun inps =>
              let '((xL, memL), (xR, memR)) := inps in
              (xL == xR) && (memL == memR) && call_invariant memL ⦄
        (fun _ : suspended_program (A := B) => code_link
          (compile_calls_from_trace_step_cont 0
            (X := X) (Y := Y) P' fn root trace_prefix
            (inl packed_x, packed_local_trace))
          P')
        ≈( pythCallContErrorBase s )
        (fun _ : suspended_program (A := B) => code_link
          (compile_calls_from_trace_step_cont 0
            (X := X) (Y := Y) P'' fn root trace_prefix
            (inl packed_x, packed_local_trace))
          P')
      ⦃ fun out =>
        let '(_, mem) := out in call_invariant mem ⦄.
      rewrite /compile_calls_from_trace_step_cont /= /call_from_package Hx.
      apply: pythReflRule.
      * exact: (pythCallContErrorBase_nonneg s Hs_nonneg).
      * move=> memL0 memR0 xL0 xR0 Hpre.
        move/andP: Hpre=> [/andP [/eqP -> /eqP ->] _].
        by split.
      * move=> mem sp out Hpre Hy.
        change (is_true
          (out \in dinsupp
            (Pr_code
              (code_link
                (x ← invalid_trace_code (A := packed_trace_t) ;;
                 match continue_from_trace root (unpack_trace x) with
                 | Some prog' => prog'
                 | None => invalid_trace_code
                 end) P') mem)))
          in Hy.
        rewrite code_link_bind code_link_invalid_trace_code in Hy.
        rewrite Pr_code_bind in Hy.
        have [mid Hmid _] := @dinsupp_dlet R _ _ _ _ _ Hy.
        rewrite /= /invalid_trace_code Pr_code_sample dlet_null_ext in Hmid.
        by move/dinsuppP: Hmid; rewrite dnullE.
    have [_ Hbranch'] := Hbranch.
    pose s_bad : suspended_program (A := B) :=
      (@inl (chInterp packed_input) (chInterp B) packed_x,
        packed_local_trace).
    have Hpre_s : (s_bad == s_bad) && (memR == memR) && call_invariant memR.
      by rewrite !eqxx Hinv.
    exact: (Hbranch' memR memR s_bad s_bad Hpre_s).
-
  rewrite /compile_calls_from_trace_step_cont /=.
  rewrite unpack_pack_trace.
  case Hcont: (continue_from_trace root
      (trace_prefix ++ unpack_trace packed_local_trace))=> [prog'|].
  + have Hbranch :
      ⊨Pyth ⦃ fun inps =>
              let '((xL, memL), (xR, memR)) := inps in
              (xL == xR) && (memL == memR) && call_invariant memL ⦄
        (fun _ : suspended_program (A := B) => code_link prog' P')
        ≈( pythCallContErrorBase s )
        (fun _ : suspended_program (A := B) => code_link prog' P')
      ⦃ fun out =>
        let '(_, mem) := out in call_invariant mem ⦄.
      apply: pythReflRule.
      * exact: (pythCallContErrorBase_nonneg s Hs_nonneg).
      * move=> memL0 memR0 xL0 xR0 Hpre.
        move/andP: Hpre=> [/andP [/eqP -> /eqP ->] _].
        by split.
      * move=> mem sp out Hpre Hy.
        have Hvalid_prog' : ValidCode L M prog'.
          exact: (continue_from_trace_valid L M root prog'
            (trace_prefix ++ unpack_trace packed_local_trace) Hvalid Hcont).
        have Hhoare := linkedCodePreservesHeapPredTuple X Y B K L L' M
          P' P'' fn prog' s call_invariant Hvalid_prog' HP' HKL Hdep
          HP'_pres Hfn Hcall.
        move/andP: Hpre=> [_ Hinv0].
        case: out Hy=> y mem' Hy.
        exact: (Hhoare tt mem Hinv0 (y, mem') Hy).
    have [_ Hbranch'] := Hbranch.
    pose s_done : suspended_program (A := B) :=
      (@inr (chInterp packed_input) (chInterp B) b, packed_local_trace).
    have Hpre_s :
        (s_done == s_done) && (memR == memR) && call_invariant memR.
      by rewrite !eqxx Hinv.
    exact: (Hbranch' memR memR s_done s_done Hpre_s).
  + have Hbranch :
      ⊨Pyth ⦃ fun inps =>
              let '((xL, memL), (xR, memR)) := inps in
              (xL == xR) && (memL == memR) && call_invariant memL ⦄
        (fun _ : suspended_program (A := B) =>
          code_link (invalid_trace_code (A := B)) P')
        ≈( pythCallContErrorBase s )
        (fun _ : suspended_program (A := B) =>
          code_link (invalid_trace_code (A := B)) P')
      ⦃ fun out =>
        let '(_, mem) := out in call_invariant mem ⦄.
      apply: pythReflRule.
      * exact: (pythCallContErrorBase_nonneg s Hs_nonneg).
      * move=> memL0 memR0 xL0 xR0 Hpre.
        move/andP: Hpre=> [/andP [/eqP -> /eqP ->] _].
        by split.
      * move=> mem sp out Hpre Hy.
        change (is_true
          (out \in dinsupp
            (Pr_code (code_link (invalid_trace_code (A := B)) P') mem)))
          in Hy.
        rewrite code_link_invalid_trace_code in Hy.
        rewrite /= /invalid_trace_code Pr_code_sample dlet_null_ext in Hy.
        by move/dinsuppP: Hy; rewrite dnullE.
    have [_ Hbranch'] := Hbranch.
    pose s_done : suspended_program (A := B) :=
      (@inr (chInterp packed_input) (chInterp B) b, packed_local_trace).
    have Hpre_s :
        (s_done == s_done) && (memR == memR) && call_invariant memR.
      by rewrite !eqxx Hinv.
    exact: (Hbranch' memR memR s_done s_done Hpre_s).
Qed.

(* TODO: Re-evaluate whether these three continuation cases should stay as
   standalone lemmas, or whether the easy branches are clearer inline. *)

(** After the shared search, the program finished before another [fn] call.
    The continuation no longer depends on whether calls are compiled via [P'] or [P'']. *)
Lemma pythCompileCallsFromTraceStepContinuationDoneRule
  (q : nat) (X Y B : choice_type)
  (K L L' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root : raw_code B) (trace_prefix : trace_t)
  (packed_local_trace : packed_trace_t) (b : B)
  (eps : R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Pyth1 ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( eps )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun _ : 'unit => code_link
      (compile_calls_from_trace_step_cont q.+1
        (X := X) (Y := Y) P' fn root trace_prefix
        (inr b, packed_local_trace))
      P')
    ≈( cat_tuple [tuple eps] (pythCallErrors q eps) )
    (fun _ : 'unit => code_link
      (compile_calls_from_trace_step_cont q.+1
        (X := X) (Y := Y) P'' fn root trace_prefix
        (inr b, packed_local_trace))
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hvalid HP' HKL Hdep HP'_pres Hfn Hcall.
rewrite /compile_calls_from_trace_step_cont /=.
rewrite unpack_pack_trace.
case Hcont: (continue_from_trace root
    (trace_prefix ++ unpack_trace packed_local_trace))=> [prog'|].
- apply: pythReflRule.
  + move=> i.
    have Heps : 0 <= eps := proj1 Hcall ord0.
    apply: (cat_tuple_nonneg [tuple eps] (pythCallErrors q eps) i).
    * move=> j.
      by rewrite [j]ord1.
    * exact: (pythCallErrors_nonneg q eps Heps).
  + move=> memL memR [] [] Hpre.
    split; first done.
    by move/andP: Hpre=> [/eqP -> _].
  + move=> mem [] out Hpre Hy.
    have Hvalid_prog' :
        ValidCode L M prog'.
      exact: (continue_from_trace_valid L M root prog'
        (trace_prefix ++ unpack_trace packed_local_trace) Hvalid Hcont).
    have Hhoare := linkedCodePreservesHeapPred X Y B K L L' M P' P''
      fn prog' eps call_invariant Hvalid_prog' HP' HKL Hdep HP'_pres Hfn
      Hcall.
    move/andP: Hpre=> [_ Hinv].
    case: out Hy=> y mem' Hy.
    exact: (Hhoare tt mem Hinv (y, mem') Hy).
- apply: pythReflRule.
  + move=> i.
    have Heps : 0 <= eps := proj1 Hcall ord0.
    apply: (cat_tuple_nonneg [tuple eps] (pythCallErrors q eps) i).
    * move=> j.
      by rewrite [j]ord1.
    * exact: (pythCallErrors_nonneg q eps Heps).
  + move=> memL memR [] [] Hpre.
    split; first done.
    by move/andP: Hpre=> [/eqP -> _].
  + move=> mem [] y Hpre Hy.
    rewrite /= /invalid_trace_code Pr_code_sample dlet_null_ext in Hy.
    by move/dinsuppP: Hy; rewrite dnullE.
Qed.

Lemma pythCompileCallsFromTraceStepContinuationDoneTupleRule
  {ℓ : nat}
  (q : nat) (X Y B : choice_type)
  (K L L' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root : raw_code B) (trace_prefix : trace_t)
  (packed_local_trace : packed_trace_t) (b : B)
  (s : (ℓ.+1).-tuple R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( s )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun _ : 'unit => code_link
      (compile_calls_from_trace_step_cont q.+1
        (X := X) (Y := Y) P' fn root trace_prefix
        (inr b, packed_local_trace))
      P')
    ≈( pythCallContErrorStep s
          (pythErrorTupleTuple (pythCallErrorsTuple q s)) )
    (fun _ : 'unit => code_link
      (compile_calls_from_trace_step_cont q.+1
        (X := X) (Y := Y) P'' fn root trace_prefix
        (inr b, packed_local_trace))
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hvalid HP' HKL Hdep HP'_pres Hfn Hcall.
have [Hs_nonneg _] := Hcall.
rewrite /compile_calls_from_trace_step_cont /=.
rewrite unpack_pack_trace.
case Hcont: (continue_from_trace root
    (trace_prefix ++ unpack_trace packed_local_trace))=> [prog'|].
- apply: pythReflRule.
  + exact: (pythCallContErrorStep_nonneg s
      (pythErrorTupleTuple (pythCallErrorsTuple q s))
      Hs_nonneg (pythCallErrorsTuple_nonneg q s Hs_nonneg)).
  + move=> memL memR [] [] Hpre.
    split; first done.
    by move/andP: Hpre=> [/eqP -> _].
  + move=> mem [] out Hpre Hy.
    have Hvalid_prog' :
        ValidCode L M prog'.
      exact: (continue_from_trace_valid L M root prog'
        (trace_prefix ++ unpack_trace packed_local_trace) Hvalid Hcont).
    have Hhoare := linkedCodePreservesHeapPredTuple X Y B K L L' M P' P''
      fn prog' s call_invariant Hvalid_prog' HP' HKL Hdep HP'_pres Hfn
      Hcall.
    move/andP: Hpre=> [_ Hinv].
    case: out Hy=> y mem' Hy.
    exact: (Hhoare tt mem Hinv (y, mem') Hy).
- apply: pythReflRule.
  + exact: (pythCallContErrorStep_nonneg s
      (pythErrorTupleTuple (pythCallErrorsTuple q s))
      Hs_nonneg (pythCallErrorsTuple_nonneg q s Hs_nonneg)).
  + move=> memL memR [] [] Hpre.
    split; first done.
    by move/andP: Hpre=> [/eqP -> _].
  + move=> mem [] y Hpre Hy.
    rewrite /= /invalid_trace_code Pr_code_sample dlet_null_ext in Hy.
    by move/dinsuppP: Hy; rewrite dnullE.
Qed.

(** The suspended call payload could fail to unpickle as an [X].  Then both
    continuations are the empty invalid-trace program. *)
Lemma pythCompileCallsFromTraceStepContinuationBadCallRule
  (q : nat) (X Y B : choice_type)
  (P' P'' : raw_package) (fn : ident)
  (root : raw_code B) (trace_prefix : trace_t)
  (packed_local_trace : packed_trace_t) (packed_x : packed_input)
  (eps : R)
  (call_invariant : pred heap) :
  unpickle packed_x = (None : option X) ->
  0 <= eps ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun _ : 'unit => code_link
      (compile_calls_from_trace_step_cont q.+1
        (X := X) (Y := Y) P' fn root trace_prefix
        (inl packed_x, packed_local_trace))
      P')
    ≈( cat_tuple [tuple eps] (pythCallErrors q eps) )
    (fun _ : 'unit => code_link
      (compile_calls_from_trace_step_cont q.+1
        (X := X) (Y := Y) P'' fn root trace_prefix
        (inl packed_x, packed_local_trace))
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hx Heps.
rewrite /compile_calls_from_trace_step_cont /= /call_from_package Hx.
apply: pythReflRule.
- move=> i.
  apply: (cat_tuple_nonneg [tuple eps] (pythCallErrors q eps) i).
  + move=> j.
    by rewrite [j]ord1.
  + exact: (pythCallErrors_nonneg q eps Heps).
- move=> memL memR [] [] Hpre.
  split; first done.
  by move/andP: Hpre=> [/eqP -> _].
- move=> mem [] y Hpre Hy.
  rewrite /= /invalid_trace_code Pr_code_sample dlet_null_ext in Hy.
  by move/dinsuppP: Hy; rewrite dnullE.
Qed.

Lemma pythCompileCallsFromTraceStepContinuationBadCallTupleRule
  {ℓ : nat}
  (q : nat) (X Y B : choice_type)
  (P' P'' : raw_package) (fn : ident)
  (root : raw_code B) (trace_prefix : trace_t)
  (packed_local_trace : packed_trace_t) (packed_x : packed_input)
  (s : (ℓ.+1).-tuple R)
  (call_invariant : pred heap) :
  unpickle packed_x = (None : option X) ->
  (forall i : 'I_(ℓ.+1), 0 <= tnth s i) ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun _ : 'unit => code_link
      (compile_calls_from_trace_step_cont q.+1
        (X := X) (Y := Y) P' fn root trace_prefix
        (inl packed_x, packed_local_trace))
      P')
    ≈( pythCallContErrorStep s
          (pythErrorTupleTuple (pythCallErrorsTuple q s)) )
    (fun _ : 'unit => code_link
      (compile_calls_from_trace_step_cont q.+1
        (X := X) (Y := Y) P'' fn root trace_prefix
        (inl packed_x, packed_local_trace))
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hx Hs_nonneg.
rewrite /compile_calls_from_trace_step_cont /= /call_from_package Hx.
apply: pythReflRule.
- exact: (pythCallContErrorStep_nonneg s
    (pythErrorTupleTuple (pythCallErrorsTuple q s))
    Hs_nonneg (pythCallErrorsTuple_nonneg q s Hs_nonneg)).
- move=> memL memR [] [] Hpre.
  split; first done.
  by move/andP: Hpre=> [/eqP -> _].
- move=> mem [] y Hpre Hy.
  rewrite /= /invalid_trace_code Pr_code_sample dlet_null_ext in Hy.
  by move/dinsuppP: Hy; rewrite dnullE.
Qed.

(** The real recursive branch: spend [eps] on the package call, then invoke the
    IH at the trace extended with the returned call value. *)
Lemma pythCompileCallsFromTraceStepContinuationTailRule
  (q : nat) (X Y B : choice_type)
  (P' P'' : raw_package) (fn : ident)
  (root : raw_code B) (trace_prefix local_trace : trace_t)
  (eps : R)
  (call_invariant : pred heap) :
  (forall trace_prefix',
    ⊨PythC ⦃ fun mems =>
            let '(memL, memR) := mems in
            (memL == memR) && call_invariant memL ⦄
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P' fn
          root trace_prefix')
        P')
      ≈( pythCallErrors q eps )
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P'' fn
          root trace_prefix')
        P')
    ⦃ fun out =>
      let '(y, mem) := out in
      call_invariant mem ⦄) ->
  ⊨Pyth ⦃ fun inps =>
          let '((yL, memL), (yR, memR)) := inps in
          (yL == yR) && (memL == memR) && call_invariant memL ⦄
    (fun y : Y => code_link
      (compile_calls_from_trace q.+1 (X := X) (Y := Y) P' fn root
        (rcons (trace_prefix ++ local_trace) (call_entry (pickle y))))
      P')
    ≈( pythCallErrors q eps )
    (fun y : Y => code_link
      (compile_calls_from_trace q.+1 (X := X) (Y := Y) P'' fn root
        (rcons (trace_prefix ++ local_trace) (call_entry (pickle y))))
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> HIH.
split.
  move=> i.
  have [Hs _] := HIH nil.
  exact: Hs i.
move=> memL memR yL yR Hpre.
move/andP: Hpre=> [/andP [/eqP -> /eqP ->] Hinv].
have [_ Htail] := HIH
  (rcons (trace_prefix ++ local_trace) (call_entry (pickle (yR : Y)))).
have Hpre_unit : (memR == memR) && call_invariant memR.
  by rewrite eqxx Hinv.
exact: (Htail memR memR tt tt Hpre_unit).
Qed.

Lemma pythCompileCallsFromTraceStepContinuationTailTupleRule
  {ℓtail : nat}
  (q : nat) (X Y B : choice_type)
  (P' P'' : raw_package) (fn : ident)
  (root : raw_code B) (trace_prefix local_trace : trace_t)
  (tail : (ℓtail.+1).-tuple R)
  (call_invariant : pred heap) :
  (forall trace_prefix',
    ⊨PythC ⦃ fun mems =>
            let '(memL, memR) := mems in
            (memL == memR) && call_invariant memL ⦄
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P' fn
          root trace_prefix')
        P')
      ≈( tail )
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P'' fn
          root trace_prefix')
        P')
    ⦃ fun out =>
      let '(y, mem) := out in
      call_invariant mem ⦄) ->
  ⊨Pyth ⦃ fun inps =>
          let '((yL, memL), (yR, memR)) := inps in
          (yL == yR) && (memL == memR) && call_invariant memL ⦄
    (fun y : Y => code_link
      (compile_calls_from_trace q.+1 (X := X) (Y := Y) P' fn root
        (rcons (trace_prefix ++ local_trace) (call_entry (pickle y))))
      P')
    ≈( tail )
    (fun y : Y => code_link
      (compile_calls_from_trace q.+1 (X := X) (Y := Y) P'' fn root
        (rcons (trace_prefix ++ local_trace) (call_entry (pickle y))))
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> HIH.
split.
  move=> i.
  have [Hs _] := HIH nil.
  exact: Hs i.
move=> memL memR yL yR Hpre.
move/andP: Hpre=> [/andP [/eqP -> /eqP ->] Hinv].
have [_ Htail] := HIH
  (rcons (trace_prefix ++ local_trace) (call_entry (pickle (yR : Y)))).
have Hpre_unit : (memR == memR) && call_invariant memR.
  by rewrite eqxx Hinv.
exact: (Htail memR memR tt tt Hpre_unit).
Qed.

Lemma pythCompileCallsFromTraceStepContinuationCallRule
  (q : nat) (X Y B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root prog : raw_code B) (trace_prefix : trace_t)
  (packed_local_trace : packed_trace_t) (packed_x : packed_input) (x : X)
  (eps : R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  continue_from_trace root trace_prefix = Some prog ->
  unpickle packed_x = Some x ->
  ⊨Pyth1 ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( eps )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  (forall trace_prefix',
    ⊨PythC ⦃ fun mems =>
            let '(memL, memR) := mems in
            (memL == memR) && call_invariant memL ⦄
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P' fn
          root trace_prefix')
        P')
      ≈( pythCallErrors q eps )
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P'' fn
          root trace_prefix')
        P')
    ⦃ fun out =>
      let '(y, mem) := out in
      call_invariant mem ⦄) ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun _ : 'unit => code_link
      (compile_calls_from_trace_step_cont q.+1
        (X := X) (Y := Y) P' fn root trace_prefix
        (inl packed_x, packed_local_trace))
      P')
    ≈( cat_tuple [tuple eps] (pythCallErrors q eps) )
    (fun _ : 'unit => code_link
      (compile_calls_from_trace_step_cont q.+1
        (X := X) (Y := Y) P'' fn root trace_prefix
        (inl packed_x, packed_local_trace))
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Htrace Hx Hcall HIH.
rewrite /compile_calls_from_trace_step_cont /=.
rewrite /call_from_package Hx.
rewrite !code_link_bind.
rewrite (code_link_resolve_closed_with X Y L' M P' P' fn x HP' Hfn).
rewrite (code_link_resolve_closed_with X Y L'' M P'' P' fn x HP'' Hfn).
eapply (@pythSeqRule 0 (q.*2).+2 'unit 'unit Y B
  (fun _ : 'unit => resolve P' (mkopsig fn X Y) x)
  (fun _ : 'unit => resolve P'' (mkopsig fn X Y) x)
  (fun y => code_link
    (compile_calls_from_trace q.+1 (X := X) (Y := Y) P' fn root
      (rcons (trace_prefix ++ unpack_trace packed_local_trace)
        (call_entry (pickle y))))
    P')
  (fun y => code_link
    (compile_calls_from_trace q.+1 (X := X) (Y := Y) P'' fn root
      (rcons (trace_prefix ++ unpack_trace packed_local_trace)
        (call_entry (pickle y))))
    P')
  (fun inps =>
    let '((_, memL), (_, memR)) := inps in
    (memL == memR) && call_invariant memL)
  (fun out =>
    let '(_, mem) := out in call_invariant mem)
  (fun out =>
    let '(_, mem) := out in call_invariant mem)
  [tuple eps]
  (pythCallErrors q eps)).
- exact: (pythCallAtRule X Y P' P'' fn eps call_invariant x Hcall).
- exact: (pythCompileCallsFromTraceStepContinuationTailRule q X Y B P'
    P'' fn root trace_prefix (unpack_trace packed_local_trace) eps
    call_invariant HIH).
Qed.

Lemma pythCompileCallsFromTraceStepContinuationCallTupleRule
  {ℓ : nat}
  (q : nat) (X Y B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root prog : raw_code B) (trace_prefix : trace_t)
  (packed_local_trace : packed_trace_t) (packed_x : packed_input) (x : X)
  (s : (ℓ.+1).-tuple R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  continue_from_trace root trace_prefix = Some prog ->
  unpickle packed_x = Some x ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( s )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  (forall trace_prefix',
    ⊨PythC ⦃ fun mems =>
            let '(memL, memR) := mems in
            (memL == memR) && call_invariant memL ⦄
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P' fn
          root trace_prefix')
        P')
      ≈( pythErrorTupleTuple (pythCallErrorsTuple q s) )
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P'' fn
          root trace_prefix')
        P')
    ⦃ fun out =>
      let '(y, mem) := out in
      call_invariant mem ⦄) ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun _ : 'unit => code_link
      (compile_calls_from_trace_step_cont q.+1
        (X := X) (Y := Y) P' fn root trace_prefix
        (inl packed_x, packed_local_trace))
      P')
    ≈( pythCallContErrorStep s
          (pythErrorTupleTuple (pythCallErrorsTuple q s)) )
    (fun _ : 'unit => code_link
      (compile_calls_from_trace_step_cont q.+1
        (X := X) (Y := Y) P'' fn root trace_prefix
        (inl packed_x, packed_local_trace))
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Htrace Hx Hcall HIH.
rewrite /compile_calls_from_trace_step_cont /=.
rewrite /call_from_package Hx.
rewrite !code_link_bind.
rewrite (code_link_resolve_closed_with X Y L' M P' P' fn x HP' Hfn).
rewrite (code_link_resolve_closed_with X Y L'' M P'' P' fn x HP'' Hfn).
eapply (@pythSeqRule ℓ (pythErrorTupleIndex (pythCallErrorsTuple q s))
  'unit 'unit Y B
  (fun _ : 'unit => resolve P' (mkopsig fn X Y) x)
  (fun _ : 'unit => resolve P'' (mkopsig fn X Y) x)
  (fun y => code_link
    (compile_calls_from_trace q.+1 (X := X) (Y := Y) P' fn root
      (rcons (trace_prefix ++ unpack_trace packed_local_trace)
        (call_entry (pickle y))))
    P')
  (fun y => code_link
    (compile_calls_from_trace q.+1 (X := X) (Y := Y) P'' fn root
      (rcons (trace_prefix ++ unpack_trace packed_local_trace)
        (call_entry (pickle y))))
    P')
  (fun inps =>
    let '((_, memL), (_, memR)) := inps in
    (memL == memR) && call_invariant memL)
  (fun out =>
    let '(_, mem) := out in call_invariant mem)
  (fun out =>
    let '(_, mem) := out in call_invariant mem)
  s
  (pythErrorTupleTuple (pythCallErrorsTuple q s))).
- exact: (pythCallAtTupleRule X Y P' P'' fn s call_invariant x Hcall).
- exact: (pythCompileCallsFromTraceStepContinuationTailTupleRule q X Y B
    P' P'' fn root trace_prefix (unpack_trace packed_local_trace)
    (pythErrorTupleTuple (pythCallErrorsTuple q s)) call_invariant HIH).
Qed.

(** Continuation case split after [run_until_next_call]: finished, bad packed
    call input, or a real call followed by the inductive hypothesis. *)
Lemma pythCompileCallsFromTraceStepContinuationRule
  (q : nat) (X Y B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root prog : raw_code B) (trace_prefix : trace_t)
  (eps : R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  continue_from_trace root trace_prefix = Some prog ->
  ⊨Pyth1 ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( eps )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  (forall trace_prefix',
    ⊨PythC ⦃ fun mems =>
            let '(memL, memR) := mems in
            (memL == memR) && call_invariant memL ⦄
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P' fn
          root trace_prefix')
        P')
      ≈( pythCallErrors q eps )
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P'' fn
          root trace_prefix')
        P')
    ⦃ fun out =>
      let '(y, mem) := out in
      call_invariant mem ⦄) ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun s => code_link
      (compile_calls_from_trace_step_cont q.+1
        (X := X) (Y := Y) P' fn root trace_prefix s)
      P')
    ≈( cat_tuple [tuple eps] (pythCallErrors q eps) )
    (fun s => code_link
      (compile_calls_from_trace_step_cont q.+1
        (X := X) (Y := Y) P'' fn root trace_prefix s)
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Htrace Hcall HIH.
have Heps : 0 <= eps := proj1 Hcall ord0.
split.
  move=> i.
  apply: (cat_tuple_nonneg [tuple eps] (pythCallErrors q eps) i).
  - move=> j.
    by rewrite [j]ord1.
  - exact: (pythCallErrors_nonneg q eps Heps).
move=> memL memR sL sR Hpre.
move/andP: Hpre=> [/andP [/eqP Hs /eqP Hmem] Hinv].
subst sR.
subst memL.
case: sL=> [[packed_x|b] packed_local_trace] /=.
-
  case Hx: (unpickle packed_x : option X)=> [x|].
  + have Hbranch :=
      pythCompileCallsFromTraceStepContinuationCallRule q X Y B K L L' L''
        M P' P'' fn root prog trace_prefix packed_local_trace packed_x x eps
        call_invariant Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Htrace Hx
        Hcall HIH.
    have [_ Hbranch'] := Hbranch.
    have Hpre_unit : (tt == tt) && (memR == memR) && call_invariant memR.
      by rewrite !eqxx.
    exact: (Hbranch' memR memR tt tt Hpre_unit).
  + have Hbranch :=
      pythCompileCallsFromTraceStepContinuationBadCallRule q X Y B P' P''
        fn root trace_prefix packed_local_trace packed_x eps call_invariant
        Hx Heps.
    have [_ Hbranch'] := Hbranch.
    have Hpre_unit : (tt == tt) && (memR == memR) && call_invariant memR.
      by rewrite !eqxx.
    exact: (Hbranch' memR memR tt tt Hpre_unit).
-
  have Hbranch :=
    pythCompileCallsFromTraceStepContinuationDoneRule q X Y B K L L' M
      P' P'' fn root trace_prefix packed_local_trace b eps call_invariant
      Hvalid HP' HKL Hdep HP'_pres Hfn Hcall.
  have [_ Hbranch'] := Hbranch.
  have Hpre_unit : (tt == tt) && (memR == memR) && call_invariant memR.
    by rewrite !eqxx.
  exact: (Hbranch' memR memR tt tt Hpre_unit).
Qed.

Lemma pythCompileCallsFromTraceStepContinuationTupleRule
  {ℓ : nat}
  (q : nat) (X Y B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root prog : raw_code B) (trace_prefix : trace_t)
  (s : (ℓ.+1).-tuple R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  continue_from_trace root trace_prefix = Some prog ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( s )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  (forall trace_prefix',
    ⊨PythC ⦃ fun mems =>
            let '(memL, memR) := mems in
            (memL == memR) && call_invariant memL ⦄
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P' fn
          root trace_prefix')
        P')
      ≈( pythErrorTupleTuple (pythCallErrorsTuple q s) )
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P'' fn
          root trace_prefix')
        P')
    ⦃ fun out =>
      let '(y, mem) := out in
      call_invariant mem ⦄) ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun s0 => code_link
      (compile_calls_from_trace_step_cont q.+1
        (X := X) (Y := Y) P' fn root trace_prefix s0)
      P')
    ≈( pythCallContErrorStep s
          (pythErrorTupleTuple (pythCallErrorsTuple q s)) )
    (fun s0 => code_link
      (compile_calls_from_trace_step_cont q.+1
        (X := X) (Y := Y) P'' fn root trace_prefix s0)
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Htrace Hcall HIH.
have [Hs_nonneg _] := Hcall.
split.
  exact: (pythCallContErrorStep_nonneg s
    (pythErrorTupleTuple (pythCallErrorsTuple q s))
    Hs_nonneg (pythCallErrorsTuple_nonneg q s Hs_nonneg)).
move=> memL memR sL sR Hpre.
move/andP: Hpre=> [/andP [/eqP Hs_eq /eqP Hmem] Hinv].
subst sR.
subst memL.
case: sL=> [[packed_x|b] packed_local_trace] /=.
-
  case Hx: (unpickle packed_x : option X)=> [x|].
  + have Hbranch :=
      pythCompileCallsFromTraceStepContinuationCallTupleRule q X Y B K L L' L''
        M P' P'' fn root prog trace_prefix packed_local_trace packed_x x s
        call_invariant Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Htrace Hx
        Hcall HIH.
    have [_ Hbranch'] := Hbranch.
    have Hpre_unit : (tt == tt) && (memR == memR) && call_invariant memR.
      by rewrite !eqxx.
    exact: (Hbranch' memR memR tt tt Hpre_unit).
  + have Hbranch :=
      pythCompileCallsFromTraceStepContinuationBadCallTupleRule q X Y B P' P''
        fn root trace_prefix packed_local_trace packed_x s call_invariant
        Hx Hs_nonneg.
    have [_ Hbranch'] := Hbranch.
    have Hpre_unit : (tt == tt) && (memR == memR) && call_invariant memR.
      by rewrite !eqxx.
    exact: (Hbranch' memR memR tt tt Hpre_unit).
-
  have Hbranch :=
    pythCompileCallsFromTraceStepContinuationDoneTupleRule q X Y B K L L' M
      P' P'' fn root trace_prefix packed_local_trace b s call_invariant
      Hvalid HP' HKL Hdep HP'_pres Hfn Hcall.
  have [_ Hbranch'] := Hbranch.
  have Hpre_unit : (tt == tt) && (memR == memR) && call_invariant memR.
    by rewrite !eqxx.
  exact: (Hbranch' memR memR tt tt Hpre_unit).
Qed.

(** Closed sequencing is just [pythSeqRule] with the unit inputs hidden by
    [pythClosedJudgment]. *)
Lemma pythClosedSeqRule
  {ℓ1 ℓ2 : nat}
  {mid_t out_t : choice_type}
  (progL progR : raw_code mid_t)
  (contL contR : mid_t -> raw_code out_t)
  (pre : pred (heap * heap))
  (mid : pred (mid_t * heap))
  (post : pred (out_t * heap))
  (s1 : (ℓ1.+1).-tuple R)
  (s2 : (ℓ2.+1).-tuple R) :
  ⊨PythC ⦃ pre ⦄ progL ≈( s1 ) progR ⦃ mid ⦄ ->
  ⊨Pyth ⦃
    fun xs =>
      let '((xL, memL), (xR, memR)) := xs in
      (xL == xR) && (memL == memR) && mid (xL, memL)
  ⦄ contL ≈( s2 ) contR ⦃ post ⦄ ->
  ⊨PythC ⦃ pre ⦄
    (yL ← progL ;; contL yL)
    ≈( cat_tuple s1 s2 )
    (yR ← progR ;; contR yR)
  ⦃ post ⦄.
Proof.
move=> Hfirst Hsecond.
rewrite /pythClosedJudgment.
exact: (pythSeqRule
  (fun _ : 'unit => progL)
  (fun _ : 'unit => progR)
  contL contR
  (fun inps =>
    let '((_, memL), (_, memR)) := inps in pre (memL, memR))
  mid post s1 s2 Hfirst Hsecond).
Qed.

Lemma pythCompileCallsFromTraceBaseRule
  (X Y B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root : raw_code B) (trace_prefix : trace_t)
  (eps : R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Pyth1 ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( eps )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨PythC ⦃ fun mems =>
          let '(memL, memR) := mems in
          (memL == memR) && call_invariant memL ⦄
    (code_link
      (compile_calls_from_trace 1 (X := X) (Y := Y) P' fn
        root trace_prefix)
      P')
    ≈( pythCallErrors 0 eps )
    (code_link
      (compile_calls_from_trace 1 (X := X) (Y := Y) P'' fn
        root trace_prefix)
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Hcall.
case Htrace: (continue_from_trace root trace_prefix)=> [prog|].
- have Hprog_valid : ValidCode L M prog.
    exact: (continue_from_trace_valid L M root prog trace_prefix Hvalid Htrace).
  rewrite (pythCallErrors0 eps).
  have -> :
      [tuple 0; eps; 0] =
      cat_tuple [tuple 0] (cat_tuple [tuple eps] [tuple 0])
    by apply/val_inj.
  rewrite (codeLinkCompileCallsFromTraceS_decompose 0 X Y B P' P'
    fn root prog trace_prefix Htrace).
  rewrite (codeLinkCompileCallsFromTraceS_decompose 0 X Y B P'' P'
    fn root prog trace_prefix Htrace).
  eapply (@pythClosedHoareSeqRule 1
    (suspended_program (A := B)) B
    (code_link (run_until_next_call prog fn) P')
    (fun s => code_link
      (compile_calls_from_trace_step_cont 0
        (X := X) (Y := Y) P' fn root trace_prefix s)
      P')
    (fun s => code_link
      (compile_calls_from_trace_step_cont 0
        (X := X) (Y := Y) P'' fn root trace_prefix s)
      P')
    call_invariant
    (fun mems =>
      let '(memL, memR) := mems in
      (memL == memR) && call_invariant memL)
    (fun out =>
      let '(_, mem) := out in call_invariant mem)
    (fun out =>
      let '(_, mem) := out in call_invariant mem)
    (cat_tuple [tuple eps] [tuple 0])).
  + move=> memL memR Hpre.
    move/andP: Hpre=> [/eqP -> Hinv].
    by split.
  + have Hrun := linkedRunUntilNextCallPreservesHeapPred X Y B K L L' M
      P' fn prog call_invariant Hprog_valid HP' HKL Hdep HP'_pres Hfn.
    rewrite /hoareJudgment=> u mem Hinv out Hout.
    have Hout_inv := Hrun u mem Hinv out Hout.
    clear Hout.
    by case: out Hout_inv=> [[status trace] mem'].
  + exact: (pythCompileCallsFromTraceStepContinuationBaseRule X Y B K L L'
      L'' M P' P'' fn root trace_prefix eps call_invariant Hvalid HP'
      HP'' HKL Hdep HP'_pres Hfn Hcall).
- rewrite /pythClosedJudgment.
  rewrite /compile_calls_from_trace /= Htrace.
  apply: pythReflRule.
  + have [Heps_nonneg _] := Hcall.
    have Heps : 0 <= eps := Heps_nonneg ord0.
    by move=> i; case: i=> [[|[|[|n]]]].
  + move=> memL memR [] [] Hpre.
    move/andP: Hpre=> [/eqP -> _].
    by split.
  + move=> mem [] y Hpre Hy.
  rewrite /= /invalid_trace_code Pr_code_sample dlet_null_ext in Hy.
    by move/dinsuppP: Hy; rewrite dnullE.
Qed.

Lemma pythCompileCallsFromTraceBaseTupleRule
  {ℓ : nat}
  (X Y B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root : raw_code B) (trace_prefix : trace_t)
  (s : (ℓ.+1).-tuple R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( s )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨PythC ⦃ fun mems =>
          let '(memL, memR) := mems in
          (memL == memR) && call_invariant memL ⦄
    (code_link
      (compile_calls_from_trace 1 (X := X) (Y := Y) P' fn
        root trace_prefix)
      P')
    ≈( pythErrorTupleTuple (pythCallErrorsTuple 0 s) )
    (code_link
      (compile_calls_from_trace 1 (X := X) (Y := Y) P'' fn
        root trace_prefix)
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Hcall.
have [Hs_nonneg _] := Hcall.
case Htrace: (continue_from_trace root trace_prefix)=> [prog|].
- have Hprog_valid : ValidCode L M prog.
    exact: (continue_from_trace_valid L M root prog trace_prefix Hvalid Htrace).
  rewrite /pythClosedJudgment.
  change (pythErrorTupleTuple (pythCallErrorsTuple 0 s))
    with (pythCallErrorBase s).
  rewrite (pythCallErrorBaseE s).
  rewrite (codeLinkCompileCallsFromTraceS_decompose 0 X Y B P' P'
    fn root prog trace_prefix Htrace).
  rewrite (codeLinkCompileCallsFromTraceS_decompose 0 X Y B P'' P'
    fn root prog trace_prefix Htrace).
  eapply (@pythClosedHoareSeqRule (ℓ + 1)%N
    (suspended_program (A := B)) B
    (code_link (run_until_next_call prog fn) P')
    (fun sp => code_link
      (compile_calls_from_trace_step_cont 0
        (X := X) (Y := Y) P' fn root trace_prefix sp)
      P')
    (fun sp => code_link
      (compile_calls_from_trace_step_cont 0
        (X := X) (Y := Y) P'' fn root trace_prefix sp)
      P')
    call_invariant
    (fun mems =>
      let '(memL, memR) := mems in
      (memL == memR) && call_invariant memL)
    (fun out =>
      let '(_, mem) := out in call_invariant mem)
    (fun out =>
      let '(_, mem) := out in call_invariant mem)
    (pythCallContErrorBase s)).
  + move=> memL memR Hpre.
    move/andP: Hpre=> [/eqP -> Hinv].
    by split.
  + have Hrun := linkedRunUntilNextCallPreservesHeapPred X Y B K L L' M
      P' fn prog call_invariant Hprog_valid HP' HKL Hdep HP'_pres Hfn.
    rewrite /hoareJudgment=> u mem Hinv out Hout.
    have Hout_inv := Hrun u mem Hinv out Hout.
    clear Hout.
    by case: out Hout_inv=> [[status trace] mem'].
  + exact: (pythCompileCallsFromTraceStepContinuationBaseTupleRule X Y B
      K L L' L'' M P' P'' fn root trace_prefix s call_invariant Hvalid HP'
      HP'' HKL Hdep HP'_pres Hfn Hcall).
- rewrite /pythClosedJudgment.
  rewrite /compile_calls_from_trace /= Htrace.
  apply: pythReflRule.
  + exact: (pythCallErrorsTuple_nonneg 0 s Hs_nonneg).
  + move=> memL memR [] [] Hpre.
    move/andP: Hpre=> [/eqP -> _].
    by split.
  + move=> mem [] y Hpre Hy.
    rewrite /= /invalid_trace_code Pr_code_sample dlet_null_ext in Hy.
    by move/dinsuppP: Hy; rewrite dnullE.
Qed.

Lemma pythCompileCallsFromTraceStepValidRule
  (q : nat) (X Y B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root prog : raw_code B) (trace_prefix : trace_t)
  (eps : R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  continue_from_trace root trace_prefix = Some prog ->
  ⊨Pyth1 ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( eps )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  (forall trace_prefix',
    ⊨PythC ⦃ fun mems =>
            let '(memL, memR) := mems in
            (memL == memR) && call_invariant memL ⦄
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P' fn
          root trace_prefix')
        P')
      ≈( pythCallErrors q eps )
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P'' fn
          root trace_prefix')
        P')
    ⦃ fun out =>
      let '(y, mem) := out in
      call_invariant mem ⦄) ->
  ⊨PythC ⦃ fun mems =>
          let '(memL, memR) := mems in
          (memL == memR) && call_invariant memL ⦄
    (code_link
      (compile_calls_from_trace q.+2 (X := X) (Y := Y) P' fn
        root trace_prefix)
      P')
    ≈( pythCallErrors q.+1 eps )
    (code_link
      (compile_calls_from_trace q.+2 (X := X) (Y := Y) P'' fn
        root trace_prefix)
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Htrace Hcall HIH.
have Hprog_valid : ValidCode L M prog.
  exact: (continue_from_trace_valid L M root prog trace_prefix Hvalid Htrace).
rewrite /pythClosedJudgment.
rewrite (pythCallErrorsS q eps).
have -> :
    cat_tuple [tuple 0; eps] (pythCallErrors q eps) =
    cat_tuple [tuple 0] (cat_tuple [tuple eps] (pythCallErrors q eps))
  by apply/val_inj.
rewrite (codeLinkCompileCallsFromTraceS_decompose q.+1 X Y B P' P'
  fn root prog trace_prefix Htrace).
rewrite (codeLinkCompileCallsFromTraceS_decompose q.+1 X Y B P'' P'
  fn root prog trace_prefix Htrace).
eapply (@pythClosedHoareSeqRule (q.*2).+3
  (suspended_program (A := B)) B
  (code_link (run_until_next_call prog fn) P')
  (fun s => code_link
    (compile_calls_from_trace_step_cont q.+1
      (X := X) (Y := Y) P' fn root trace_prefix s)
    P')
  (fun s => code_link
    (compile_calls_from_trace_step_cont q.+1
      (X := X) (Y := Y) P'' fn root trace_prefix s)
    P')
  call_invariant
  (fun mems =>
    let '(memL, memR) := mems in
    (memL == memR) && call_invariant memL)
  (fun out =>
    let '(_, mem) := out in call_invariant mem)
  (fun out =>
    let '(_, mem) := out in call_invariant mem)
  (cat_tuple [tuple eps] (pythCallErrors q eps))).
- move=> memL memR Hpre.
  move/andP: Hpre=> [/eqP -> Hinv].
  by split.
- have Hrun := linkedRunUntilNextCallPreservesHeapPred X Y B K L L' M
    P' fn prog call_invariant Hprog_valid HP' HKL Hdep HP'_pres Hfn.
  rewrite /hoareJudgment=> u mem Hinv out Hout.
  have Hout_inv := Hrun u mem Hinv out Hout.
  clear Hout.
  by case: out Hout_inv=> [[status trace] mem'].
- exact: (pythCompileCallsFromTraceStepContinuationRule q X Y B K L L' L''
    M P' P'' fn root prog trace_prefix eps call_invariant Hvalid HP'
    HP'' HKL Hdep HP'_pres Hfn Htrace Hcall HIH).
Qed.

Lemma pythCompileCallsFromTraceStepValidTupleRule
  {ℓ : nat}
  (q : nat) (X Y B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root prog : raw_code B) (trace_prefix : trace_t)
  (s : (ℓ.+1).-tuple R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  continue_from_trace root trace_prefix = Some prog ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( s )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  (forall trace_prefix',
    ⊨PythC ⦃ fun mems =>
            let '(memL, memR) := mems in
            (memL == memR) && call_invariant memL ⦄
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P' fn
          root trace_prefix')
        P')
      ≈( pythErrorTupleTuple (pythCallErrorsTuple q s) )
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P'' fn
          root trace_prefix')
        P')
    ⦃ fun out =>
      let '(y, mem) := out in
      call_invariant mem ⦄) ->
  ⊨PythC ⦃ fun mems =>
          let '(memL, memR) := mems in
          (memL == memR) && call_invariant memL ⦄
    (code_link
      (compile_calls_from_trace q.+2 (X := X) (Y := Y) P' fn
        root trace_prefix)
      P')
    ≈( pythErrorTupleTuple (pythCallErrorsTuple q.+1 s) )
    (code_link
      (compile_calls_from_trace q.+2 (X := X) (Y := Y) P'' fn
        root trace_prefix)
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Htrace Hcall HIH.
have Hprog_valid : ValidCode L M prog.
  exact: (continue_from_trace_valid L M root prog trace_prefix Hvalid Htrace).
rewrite /pythClosedJudgment.
change (pythErrorTupleTuple (pythCallErrorsTuple q.+1 s)) with
  (pythCallErrorStep s (pythErrorTupleTuple (pythCallErrorsTuple q s))).
rewrite (pythCallErrorStepE s
  (pythErrorTupleTuple (pythCallErrorsTuple q s))).
rewrite (codeLinkCompileCallsFromTraceS_decompose q.+1 X Y B P' P'
  fn root prog trace_prefix Htrace).
rewrite (codeLinkCompileCallsFromTraceS_decompose q.+1 X Y B P'' P'
  fn root prog trace_prefix Htrace).
eapply (@pythClosedHoareSeqRule _
  (suspended_program (A := B)) B
  (code_link (run_until_next_call prog fn) P')
  (fun sp => code_link
    (compile_calls_from_trace_step_cont q.+1
      (X := X) (Y := Y) P' fn root trace_prefix sp)
    P')
  (fun sp => code_link
    (compile_calls_from_trace_step_cont q.+1
      (X := X) (Y := Y) P'' fn root trace_prefix sp)
    P')
  call_invariant
  (fun mems =>
    let '(memL, memR) := mems in
    (memL == memR) && call_invariant memL)
  (fun out =>
    let '(_, mem) := out in call_invariant mem)
  (fun out =>
    let '(_, mem) := out in call_invariant mem)
  (pythCallContErrorStep s
    (pythErrorTupleTuple (pythCallErrorsTuple q s)))).
- move=> memL memR Hpre.
  move/andP: Hpre=> [/eqP -> Hinv].
  by split.
- have Hrun := linkedRunUntilNextCallPreservesHeapPred X Y B K L L' M
    P' fn prog call_invariant Hprog_valid HP' HKL Hdep HP'_pres Hfn.
  rewrite /hoareJudgment=> u mem Hinv out Hout.
  have Hout_inv := Hrun u mem Hinv out Hout.
  clear Hout.
  by case: out Hout_inv=> [[status trace] mem'].
- exact: (pythCompileCallsFromTraceStepContinuationTupleRule q X Y B K L L' L''
    M P' P'' fn root prog trace_prefix s call_invariant Hvalid HP'
    HP'' HKL Hdep HP'_pres Hfn Htrace Hcall HIH).
Qed.

Lemma pythCompileCallsFromTraceStepRule
  (q : nat) (X Y B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root : raw_code B) (trace_prefix : trace_t)
  (eps : R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Pyth1 ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( eps )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  (forall trace_prefix',
    ⊨PythC ⦃ fun mems =>
            let '(memL, memR) := mems in
            (memL == memR) && call_invariant memL ⦄
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P' fn
          root trace_prefix')
        P')
      ≈( pythCallErrors q eps )
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P'' fn
          root trace_prefix')
        P')
    ⦃ fun out =>
      let '(y, mem) := out in
      call_invariant mem ⦄) ->
  ⊨PythC ⦃ fun mems =>
          let '(memL, memR) := mems in
          (memL == memR) && call_invariant memL ⦄
    (code_link
      (compile_calls_from_trace q.+2 (X := X) (Y := Y) P' fn
        root trace_prefix)
      P')
    ≈( pythCallErrors q.+1 eps )
    (code_link
      (compile_calls_from_trace q.+2 (X := X) (Y := Y) P'' fn
        root trace_prefix)
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Hcall HIH.
case Htrace: (continue_from_trace root trace_prefix)=> [prog|].
- exact: (pythCompileCallsFromTraceStepValidRule q X Y B K L L' L'' M
    P' P'' fn root prog trace_prefix eps call_invariant Hvalid HP' HP''
    HKL Hdep HP'_pres Hfn Htrace Hcall HIH).
- exact: (pythCompileCallsFromTraceInvalidRule q.+1 X Y B K L L' L'' M
    P' P'' fn root trace_prefix eps call_invariant Hvalid HP' HP''
    HKL Hdep HP'_pres Hfn Htrace Hcall).
Qed.

Lemma pythCompileCallsFromTraceStepTupleRule
  {ℓ : nat}
  (q : nat) (X Y B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root : raw_code B) (trace_prefix : trace_t)
  (s : (ℓ.+1).-tuple R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( s )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  (forall trace_prefix',
    ⊨PythC ⦃ fun mems =>
            let '(memL, memR) := mems in
            (memL == memR) && call_invariant memL ⦄
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P' fn
          root trace_prefix')
        P')
      ≈( pythErrorTupleTuple (pythCallErrorsTuple q s) )
      (code_link
        (compile_calls_from_trace q.+1 (X := X) (Y := Y) P'' fn
          root trace_prefix')
        P')
    ⦃ fun out =>
      let '(y, mem) := out in
      call_invariant mem ⦄) ->
  ⊨PythC ⦃ fun mems =>
          let '(memL, memR) := mems in
          (memL == memR) && call_invariant memL ⦄
    (code_link
      (compile_calls_from_trace q.+2 (X := X) (Y := Y) P' fn
        root trace_prefix)
      P')
    ≈( pythErrorTupleTuple (pythCallErrorsTuple q.+1 s) )
    (code_link
      (compile_calls_from_trace q.+2 (X := X) (Y := Y) P'' fn
        root trace_prefix)
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Hcall HIH.
case Htrace: (continue_from_trace root trace_prefix)=> [prog|].
- exact: (pythCompileCallsFromTraceStepValidTupleRule q X Y B K L L' L'' M
    P' P'' fn root prog trace_prefix s call_invariant Hvalid HP' HP''
    HKL Hdep HP'_pres Hfn Htrace Hcall HIH).
- exact: (pythCompileCallsFromTraceInvalidTupleRule q.+1 X Y B K L L' L'' M
    P' P'' fn root trace_prefix s call_invariant Hvalid HP' HP''
    HKL Hdep HP'_pres Hfn Htrace Hcall).
Qed.

Lemma pythCompileCallsFromTraceRule
  (q : nat) (X Y B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root : raw_code B) (trace_prefix : trace_t)
  (eps : R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Pyth1 ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( eps )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨PythC ⦃ fun mems =>
          let '(memL, memR) := mems in
          (memL == memR) && call_invariant memL ⦄
    (code_link
      (compile_calls_from_trace q.+1 (X := X) (Y := Y) P' fn
        root trace_prefix)
      P')
    ≈( pythCallErrors q eps )
    (code_link
      (compile_calls_from_trace q.+1 (X := X) (Y := Y) P'' fn
        root trace_prefix)
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
elim: q X Y B K L L' L'' M P' P'' fn root trace_prefix eps call_invariant
  => [|q IH] X Y B K L L' L'' M P' P'' fn root trace_prefix eps
     call_invariant Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Hcall.
- exact: (pythCompileCallsFromTraceBaseRule X Y B K L L' L'' M P' P''
    fn root trace_prefix eps call_invariant Hvalid HP' HP'' HKL Hdep
    HP'_pres Hfn Hcall).
- apply: (pythCompileCallsFromTraceStepRule q X Y B K L L' L'' M P' P''
    fn root trace_prefix eps call_invariant Hvalid HP' HP'' HKL Hdep
    HP'_pres Hfn Hcall).
  move=> trace_prefix'.
  exact: (IH X Y B K L L' L'' M P' P'' fn root trace_prefix' eps
    call_invariant Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Hcall).
Qed.

Lemma pythCompileCallsFromTraceTupleRule
  {ℓ : nat}
  (q : nat) (X Y B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (root : raw_code B) (trace_prefix : trace_t)
  (s : (ℓ.+1).-tuple R)
  (call_invariant : pred heap) :
  ValidCode L M root ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( s )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨PythC ⦃ fun mems =>
          let '(memL, memR) := mems in
          (memL == memR) && call_invariant memL ⦄
    (code_link
      (compile_calls_from_trace q.+1 (X := X) (Y := Y) P' fn
        root trace_prefix)
      P')
    ≈( pythErrorTupleTuple (pythCallErrorsTuple q s) )
    (code_link
      (compile_calls_from_trace q.+1 (X := X) (Y := Y) P'' fn
        root trace_prefix)
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
elim: q X Y B K L L' L'' M P' P'' fn root trace_prefix s call_invariant
  => [|q IH] X Y B K L L' L'' M P' P'' fn root trace_prefix s
     call_invariant Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Hcall.
- exact: (pythCompileCallsFromTraceBaseTupleRule X Y B K L L' L'' M P' P''
    fn root trace_prefix s call_invariant Hvalid HP' HP'' HKL Hdep
    HP'_pres Hfn Hcall).
- apply: (pythCompileCallsFromTraceStepTupleRule q X Y B K L L' L'' M P' P''
    fn root trace_prefix s call_invariant Hvalid HP' HP'' HKL Hdep
    HP'_pres Hfn Hcall).
  move=> trace_prefix'.
  exact: (IH X Y B K L L' L'' M P' P'' fn root trace_prefix' s
    call_invariant Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Hcall).
Qed.

Lemma pythCompileCallsRule
  (q : nat) (X Y A B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (prog : A -> raw_code B)
  (eps : R)
  (call_invariant : pred heap) :
  (forall x, ValidCode L M (prog x)) ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Pyth1 ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( eps )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => code_link
      (compile_calls q.+1 (X := X) (Y := Y) P' fn (prog x))
      P')
    ≈( pythCallErrors q eps )
    (fun x => code_link
      (compile_calls q.+1 (X := X) (Y := Y) P'' fn (prog x))
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Hcall.
have [Heps_nonneg _] := Hcall.
have Heps : 0 <= eps.
  exact: (Heps_nonneg ord0).
split.
- exact: (pythCallErrors_nonneg q eps Heps).
- move=> memL memR xL xR Hpre.
  move/andP: Hpre=> [/andP [/eqP -> /eqP ->] Hinv].
  have Htrace :=
    pythCompileCallsFromTraceRule q X Y B K L L' L'' M P' P'' fn
      (prog xR) nil eps call_invariant
      (Hvalid xR) HP' HP'' HKL Hdep HP'_pres Hfn Hcall.
  have [_ Hpyth] := Htrace.
  have Hpre_unit :
      (let '((_, memL0), (_, memR0)) := ((tt, memR), (tt, memR)) in
        (memL0 == memR0) && call_invariant memL0).
    by rewrite eqxx.
  have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
    Hpyth memR memR tt tt Hpre_unit.
  exists P, Q.
  rewrite -!compile_calls_from_trace_nil.
  split; first exact: Hdist.
  split; first exact: HmarginL.
  split; first exact: HmarginR.
  by split.
Qed.

Lemma pythCompileCallsTupleRule
  {ℓ : nat}
  (q : nat) (X Y A B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (prog : A -> raw_code B)
  (s : (ℓ.+1).-tuple R)
  (call_invariant : pred heap) :
  (forall x, ValidCode L M (prog x)) ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( s )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => code_link
      (compile_calls q.+1 (X := X) (Y := Y) P' fn (prog x))
      P')
    ≈( pythErrorTupleTuple (pythCallErrorsTuple q s) )
    (fun x => code_link
      (compile_calls q.+1 (X := X) (Y := Y) P'' fn (prog x))
      P')
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄.
Proof.
move=> Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Hcall.
have [Hs_nonneg _] := Hcall.
split.
- exact: (pythCallErrorsTuple_nonneg q s Hs_nonneg).
- move=> memL memR xL xR Hpre.
  move/andP: Hpre=> [/andP [/eqP -> /eqP ->] Hinv].
  have Htrace :=
    pythCompileCallsFromTraceTupleRule q X Y B K L L' L'' M P' P'' fn
      (prog xR) nil s call_invariant
      (Hvalid xR) HP' HP'' HKL Hdep HP'_pres Hfn Hcall.
  have [_ Hpyth] := Htrace.
  have Hpre_unit :
      (let '((_, memL0), (_, memR0)) := ((tt, memR), (tt, memR)) in
        (memL0 == memR0) && call_invariant memL0).
    by rewrite eqxx.
  have [P [Q [Hdist [HmarginL [HmarginR [HpostL HpostR]]]]]] :=
    Hpyth memR memR tt tt Hpre_unit.
  exists P, Q.
  rewrite -!compile_calls_from_trace_nil.
  split; first exact: Hdist.
  split; first exact: HmarginL.
  split; first exact: HmarginR.
  by split.
Qed.

Lemma diagonalCoupling
  (A : ord_choiceType) (D : {distr A / R}) :
  clean_coupling (\dlet_(z <- D) dunit (z, z)) D D.
Proof.
split.
- move=> x.
  rewrite dmargin_dlet_partition.
  rewrite (eq_dlet (m := D) (g := fun y => dunit y)); last first.
    move=> y.
    apply: distr_ext=> z.
    by rewrite dmargin_dunit.
  by rewrite dlet_dunit_id.
- move=> x.
  rewrite dmargin_dlet_partition.
  rewrite (eq_dlet (m := D) (g := fun y => dunit y)); last first.
    move=> y.
    apply: distr_ext=> z.
    by rewrite dmargin_dunit.
  by rewrite dlet_dunit_id.
Qed.

Lemma diagonalDletPrEq1
  {A : ord_choiceType} (D : {distr A / R}) :
  dweight D = 1 ->
  \P_[\dlet_(z <- D) dunit (z, z)]
    (fun outs =>
      let '(outL, outR) := outs in outL == outR) = 1.
Proof.
move=> HD.
apply: pr_eq1_of_support.
- rewrite dweight_dlet_sum -HD.
  apply/eq_psum=> z.
  by rewrite dunit_dweight mulr1 mul1r.
- move=> xy Hxy.
have [z Hz Hunit] := @dinsupp_dlet R _ _
  (fun z => dunit (z, z)) D xy Hxy.
have -> : xy = (z, z) by exact: in_dunit Hunit.
by rewrite eqxx.
Qed.

Lemma compileRule
  {ℓ : nat}
  (q : nat) (X Y A B : choice_type)
  (K L L' L'' : Locations) (M : Interface)
  (P' P'' : raw_package) (fn : ident)
  (prog : A -> raw_code B)
  (s : (ℓ.+1).-tuple R)
  (call_invariant : pred heap) :
  (forall x, ValidCode L M (prog x)) ->
  ValidPackage L' [interface] M P' ->
  ValidPackage L'' [interface] M P'' ->
  fseparate K L ->
  heap_pred_depends_only_on K call_invariant ->
  package_preserves_heap_pred_except M P' fn call_invariant ->
  fhas M (mkopsig fn X Y) ->
  ⊨Pyth ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => resolve P' (mkopsig fn X Y) x)
    ≈( s )
    (fun x => resolve P'' (mkopsig fn X Y) x)
  ⦃ fun out =>
    let '(y, mem) := out in
    call_invariant mem ⦄ ->
  ⊨AE ⦃ fun inps =>
          let '((xL, memL), (xR, memR)) := inps in
          (xL == xR) && (memL == memR) &&
          call_invariant memL ⦄
    (fun x => code_link
      (compile_calls q (X := X) (Y := Y) P' fn (prog x))
      P')
    ≈( Num.sqrt ((q%:R * tuple_sum s) / 2) )
    (fun x => code_link
      (compile_calls q (X := X) (Y := Y) P'' fn (prog x))
      P')
  ⦃ fun outs =>
    let '(outL, outR) := outs in
    outL == outR ⦄.
Proof.
move=> Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Hcall.
case: q=> [|q].
- rewrite /compile_calls /compile_calls_from_trace /=.
  split; first exact: Num.Theory.sqrtr_ge0.
  move=> memL memR xL xR Hpre.
  move/andP: Hpre=> [/andP [/eqP -> /eqP ->] _].
  rewrite continue_from_trace_nil.
  set D := complete (Pr_code (code_link (prog xR) P') memR).
  exists (\dlet_(z <- D) dunit (z, z)).
  split; first exact: diagonalCoupling.
  rewrite (_ : \P_[\dlet_(z <- D) dunit (z, z)]
      (fun outs =>
        let '(outL, outR) := outs in outL == outR) = 1).
    have -> : Num.sqrt ((0%:R * tuple_sum s) / 2) = 0.
      by rewrite mul0r mul0r sqrtr0.
    by rewrite subr0 lexx.
  by rewrite diagonalDletPrEq1 // /D complete_dweight.
rewrite -pythagorean_tv_bound_pythCallErrorsTuple.
exact: (MicciancioWalterRule _ _ _ _ _
  (pythCompileCallsTupleRule q X Y A B K L L' L'' M P' P'' fn prog s
    call_invariant Hvalid HP' HP'' HKL Hdep HP'_pres Hfn Hcall)).
Qed.
