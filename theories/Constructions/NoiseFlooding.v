(* This converts an IND-CPA scheme to an IND-CPA-D one *)

From Stdlib Require Import Utf8 BinInt.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot all_order all_algebra reals distr realsum.
Set Warnings "notation-overridden,ambiguous-paths".
From SSProve.Crypt Require Import Axioms Package Prelude.
From SSProve Require Import NominalPrelude.
From Mending.Schemes Require Import ApproxFHE Indcpa Indcpad.
From Mending.Schemes.Utils Require Import IntVec.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras DTuple
  TupleExtras.
From Mending.Probability.DiscreteGaussians Require Import
  DiscreteGaussian DiscreteGaussianKL.
From Mending.Probability.KL Require Import Core.
From extructures Require Import ord fset fmap.
Import PackageNotation.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope package_scope.
Local Open Scope sep_scope.
Local Open Scope ring_scope.

Definition n_dg (n : nat) (s : R) : distr R (n.-tuple int) :=
  nfold_distr n (centered_discrete_gaussian s).

Lemma cons_tuple_thead_behead {n : nat} {A : choiceType}
    (y : n.+1.-tuple A) :
  cons_tuple (thead y) (behead_tuple y) = y.
Proof.
by rewrite [RHS](tuple_eta y).
Qed.

Lemma behead_tuple_cons {n : nat} {A : choiceType}
    (x : A) (xs : n.-tuple A) :
  behead_tuple (cons_tuple x xs) = xs.
Proof.
by apply: val_inj.
Qed.

Lemma dlet_cons_tupleE {n : nat} {A : choiceType}
    (P : distr R A) (Q : distr R (n.-tuple A))
    (y : n.+1.-tuple A) :
  (\dlet_(x <- P)
   \dlet_(xs <- Q)
     dunit (cons_tuple x xs)) y =
    P (thead y) * Q (behead_tuple y).
Proof.
rewrite !dletE.
rewrite (psum_finseq (r := [:: thead y])).
- rewrite big_seq1 ger0_norm ?mulr_ge0 ?ge0_mu //.
  congr (_ * _).
  rewrite dletE.
  rewrite (psum_finseq (r := [:: behead_tuple y])).
  + rewrite big_seq1 dunit1E cons_tuple_thead_behead eqxx mulr1.
    by rewrite ger0_norm ?ge0_mu.
  + by [].
  move=> xs Hnz.
  rewrite inE.
  apply/eqP.
  move: Hnz.
  rewrite !inE dunit1E.
  rewrite mulf_eq0 negb_or=> /andP[_ Hunit].
  move: Hunit.
  rewrite pnatr_eq0 eqb0 negbK=> /eqP Hcons.
  by rewrite -Hcons behead_tuple_cons.
- by [].
move=> x Hnz.
rewrite inE.
case: (x =P thead y)=> [Hx_eq|Hx].
  by [].
move: Hnz.
rewrite !inE dletE.
have Hinner0 : psum
    (fun xs : n.-tuple A => Q xs * dunit (cons_tuple x xs) y) = 0.
  apply: psum_eq0=> xs.
  rewrite dunit1E.
  apply/eqP.
  rewrite mulf_eq0.
  apply/orP; right.
  rewrite pnatr_eq0 eqb0.
  apply/negP=> /eqP Hcons.
  have Hx_eq : x = thead y.
    by rewrite -Hcons theadE.
  by case: Hx.
by rewrite Hinner0 mulr0 eqxx.
Qed.

Fixpoint n_dg_shifted {n : nat}
    : n.-tuple int -> R -> distr R (n.-tuple int) :=
  match n with
  | 0 => fun _ _ => dunit [tuple]
  | S n' => fun center s =>
    \dlet_(x <- discrete_gaussian (thead center) s)
    \dlet_(xs <- n_dg_shifted (behead_tuple center) s)
      dunit (cons_tuple x xs)
  end.

Lemma n_dg_shifted_cons_cat {n : nat}
    (c : int) (center : n.-tuple int) (s : R) :
  n_dg_shifted [tuple of c :: center] s =1
    \dlet_(x <- discrete_gaussian c s)
    \dlet_(xs <- n_dg_shifted center s)
      dunit (cat_tuple [tuple x] xs).
Proof.
move=> y.
rewrite /= theadE.
have Hbehead : behead_tuple [tuple of c :: center] = center.
  by apply: val_inj.
rewrite Hbehead.
apply: eq_in_dlet=> // x _ z.
apply: eq_in_dlet=> // xs _ w.
by rewrite cat_tuple_singleton_cons.
Qed.

Lemma centered_discrete_gaussian_shift_add (center : int) (s : R) :
  dmargin (fun x : int => x + center) (centered_discrete_gaussian s) =1
    discrete_gaussian center s.
Proof.
move=> y.
rewrite /discrete_gaussian !dmargin_psumE.
apply: eq_psum=> x.
by rewrite addrC.
Qed.

Lemma discrete_gaussian_centered_subE (center : int) (s : R) (x : int) :
  discrete_gaussian center s x =
    centered_discrete_gaussian s (x - center).
Proof.
by rewrite /discrete_gaussian dmargin_add_intE.
Qed.

Lemma n_dg_consE {n : nat} (s : R) (y : n.+1.-tuple int) :
  n_dg n.+1 s y =
    centered_discrete_gaussian s (thead y) *
    n_dg n s (behead_tuple y).
Proof.
rewrite /n_dg /nfold_distr /=.
rewrite dlet_cons_tupleE.
have Hbehead :
    behead_tuple (nseq_tuple n.+1 (centered_discrete_gaussian s)) =
    nseq_tuple n (centered_discrete_gaussian s).
  by apply: val_inj.
by rewrite Hbehead.
Qed.

Lemma n_dg_shifted_consE {n : nat}
    (c : int) (center : n.-tuple int) (s : R)
    (y : n.+1.-tuple int) :
  n_dg_shifted [tuple of c :: center] s y =
    discrete_gaussian c s (thead y) *
    n_dg_shifted center s (behead_tuple y).
Proof.
rewrite /= theadE.
have Hbehead : behead_tuple [tuple of c :: center] = center.
  by apply: val_inj.
by rewrite Hbehead dlet_cons_tupleE.
Qed.

Lemma n_dg_shifted_pointE {n : nat} (center y : n.-tuple int) s :
  n_dg_shifted center s y = n_dg n s (ivec_sub y center).
Proof.
elim: n center y=> [|n IH] center y.
- rewrite [center](tuple0 center) [y](tuple0 y) /=.
  rewrite [ivec_sub [tuple] [tuple]](tuple0 (ivec_sub [tuple] [tuple])).
  by rewrite /n_dg /nfold_distr /=.
case/tupleP: center=> c center.
case/tupleP: y=> x xs.
rewrite n_dg_shifted_consE.
rewrite ivec_sub_cons n_dg_consE theadE behead_tuple_cons.
rewrite discrete_gaussian_centered_subE.
rewrite theadE behead_tuple_cons.
by rewrite (IH center xs).
Qed.

Lemma n_dg_shiftedE {n : nat} (center : n.-tuple int) s :
  dmargin (fun noise => ivec_add noise center) (n_dg n s) =1
    n_dg_shifted center s.
Proof.
move=> y.
transitivity (n_dg n s (ivec_sub y center)).
- transitivity
    (dmargin (fun noise : n.-tuple int => ivec_add noise center)
      (n_dg n s) (ivec_add (ivec_sub y center) center)).
  + by rewrite ivec_add_subK.
  rewrite (dmargin_injectiveE
    (fun noise : n.-tuple int => ivec_add noise center)
    (n_dg n s) (ivec_add_inj_r center) (ivec_sub y center)).
  by [].
by rewrite -n_dg_shifted_pointE.
Qed.

Lemma n_dg_shifted_mass1 {n : nat} (center : n.-tuple int) s :
  0 < s ->
  dweight (n_dg_shifted center s) = 1.
Proof.
elim: n center=> [|n IH] center Hs.
- by rewrite /= dunit_dweight.
case/tupleP: center=> c center.
rewrite /= dweight_dlet_sum.
rewrite (eq_psum
  (F2 := fun x : int => discrete_gaussian c s x * 1)); last first.
  move=> x.
  congr (_ * _).
  rewrite dweight_dlet_sum.
  rewrite (eq_psum
    (F2 := fun xs : n.-tuple int => n_dg_shifted center s xs * 1));
    last first.
      move=> xs.
      have Hbehead : behead_tuple [tuple of c :: center] = center.
        by apply: val_inj.
      by rewrite Hbehead dunit_dweight.
  rewrite (eq_psum (F2 := n_dg_shifted center s)); last
    by move=> xs; rewrite mulr1.
  by rewrite -pr_predT IH.
rewrite (eq_psum (F2 := discrete_gaussian c s)); last
  by move=> x; rewrite mulr1.
by rewrite -pr_predT discrete_gaussian_mass1.
Qed.

Lemma n_dg_shifted_dinsupp {n : nat} (center y : n.-tuple int) s :
  0 < s ->
  y \in dinsupp (n_dg_shifted center s).
Proof.
elim: n center y=> [|n IH] center y Hs.
- rewrite [center](tuple0 center) [y](tuple0 y) /=.
  by rewrite in_dinsupp dunit1E eqxx oner_neq0.
case/tupleP: center=> c center.
case/tupleP: y=> x xs.
rewrite /= theadE.
have Hbehead : behead_tuple [tuple of c :: center] = center.
  by apply: val_inj.
rewrite Hbehead.
apply: (@dlet_dinsupp R int (n.+1.-tuple int)
  (fun x0 : int =>
    \dlet_(xs0 <- n_dg_shifted center s) dunit (cons_tuple x0 xs0))
  (discrete_gaussian c s) x (cons_tuple x xs)).
- apply/dinsuppP.
  move=> Hx0.
  have Hxgt := discrete_gaussian_gt0 c s x Hs.
  by rewrite Hx0 ltxx in Hxgt.
apply: (@dlet_dinsupp R (n.-tuple int) (n.+1.-tuple int)
  (fun xs0 : n.-tuple int => dunit (cons_tuple x xs0))
  (n_dg_shifted center s) xs (cons_tuple x xs)).
- exact: IH.
by rewrite dunit1E eqxx oner_neq0.
Qed.

Lemma n_dg_mass1 n s :
  0 < s ->
  dweight (n_dg n s) = 1.
Proof.
move=> Hs.
rewrite /n_dg.
apply: nfold_distr_mass1.
exact: centered_discrete_gaussian_mass1.
Qed.

Definition noise_flooding_dg_stdev
    (gaussian_width_multiplier : R) (error_bound : nat) : R :=
  (error_bound * error_bound + 1)%:~R * gaussian_width_multiplier.

Module Type NoiseFloodingParams.
Parameter gaussian_width_multiplier : R.
Axiom gt0_gaussian_width_multiplier :
  gaussian_width_multiplier > 0.
End NoiseFloodingParams.

Module NoiseFlooding
  (Import Scheme : ApproxFheScheme)
  (Import Metric : ApproxFheMetric(Scheme))
  (Import Params : NoiseFloodingParams)
  <: ApproxFheScheme.
Definition pk_t := Scheme.pk_t.
Definition evk_t := Scheme.evk_t.
Definition sk_t := Scheme.sk_t.
Definition Scheme_t := Scheme.Scheme_t.
Definition message := Scheme.message.
Definition encryption := Scheme.encryption.
Definition ciphertext := Scheme.ciphertext.
Definition unary_gate := Scheme.unary_gate.
Definition binary_gate := Scheme.binary_gate.
Definition interpret_unary := Scheme.interpret_unary.
Definition interpret_binary := Scheme.interpret_binary.
Definition keygen := Scheme.keygen.
Lemma keygen_lossless : dweight keygen = 1.
Proof. exact: Scheme.keygen_lossless. Qed.
Definition encrypt := Scheme.encrypt.
Definition eval1 := Scheme.eval1.
Definition eval2 := Scheme.eval2.
(* TODO find out if this is the "right" amount of noise. *)
Definition dg_stdev (error_bound : nat) : R :=
  noise_flooding_dg_stdev gaussian_width_multiplier error_bound.
(* Maybe it's not ideal that decrypting an invalid ciphertext crashes the entire experiment.
 * This makes any sense only if invalid ciphertexts result only from misuse. *)
Definition decrypt (sk: sk_t) (c: ciphertext) : distr R message :=
  match c with
  | None => dnull
  | Some (_, e) =>
    \dlet_(m <- Scheme.decrypt sk c)
    \dlet_(noise <- n_dg dim (dg_stdev e))
    dunit (inverse_isometry m (ivec_add noise (isometry m m)))
  end.

  Definition Scheme : Scheme_t := [package emptym ;
    #def #[keygen_l] (_: 'unit) : ('pk_t × 'evk_t) × 'sk_t
    {
      keys <$ ((pk_t × evk_t) × sk_t ; keygen) ;;
      let '(pk, evk, sk) := keys in
      ret (pk, evk, sk)
    } ;
    #def #[enc_l] ('(pk, m) : ('pk_t × 'message_t)) : 'ciphertext
    {
      c <$ (ciphertext; encrypt pk m) ;;
      ret c
    } ;
    #def #[eval1_l] ('(evk, g, c) : (('evk_t × 'unary_gate) × 'ciphertext)) : 'ciphertext
    {
      c' <$ (ciphertext; eval1 evk g c) ;;
      ret c'
    } ;
    #def #[eval2_l] ('(evk, g, c1, c2) : (('evk_t × 'binary_gate) × 'ciphertext) × 'ciphertext) : 'ciphertext
    {
      c <$ (ciphertext; eval2 evk g c1 c2) ;;
      ret c
    } ;
    #def #[dec_l] ('(sk, c) : 'sk_t ×'ciphertext) : 'message_t
    {
      m <$ (message; decrypt sk c) ;;
      ret m
    }
  ].

End NoiseFlooding.
