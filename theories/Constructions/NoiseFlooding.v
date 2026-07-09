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
From extructures Require Import ord fset fmap.
Import PackageNotation.
Import GRing.Theory Order.Theory.
Local Open Scope package_scope.
Local Open Scope sep_scope.
Local Open Scope ring_scope.

Definition n_dg (n : nat) (s : R) : distr R (n.-tuple int) :=
  nfold_distr n (centered_discrete_gaussian s).

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

Lemma n_dg_shiftedE {n : nat} (center : n.-tuple int) s :
  dmargin (fun noise => ivec_add noise center) (n_dg n s) =1
    n_dg_shifted center s.
Proof.
elim: n center=> [|n IH] center y.
- rewrite /n_dg /nfold_distr /=.
  rewrite [center](tuple0 center) [y](tuple0 y).
  rewrite dmargin_dunit.
  rewrite [ivec_add [tuple] [tuple]](tuple0 (ivec_add [tuple] [tuple])).
  by [].
case/tupleP: center=> c center.
rewrite /n_dg /nfold_distr /=.
transitivity
  ((\dlet_(x <- discrete_gaussian c s)
    \dlet_(xs <- n_dg_shifted center s)
      dunit (cons_tuple x xs)) y).
- rewrite dmargin_dlet.
  transitivity
    ((\dlet_(x <- centered_discrete_gaussian s)
      \dlet_(xs <- n_dg_shifted center s)
        dunit (cons_tuple (x + c) xs)) y).
  + apply: eq_in_dlet=> // x _ z.
    rewrite dmargin_dlet.
    transitivity
      ((\dlet_(xs <- dmargin (fun noise => ivec_add noise center)
          (n_dg n s))
        dunit (cons_tuple (x + c) xs)) z).
    * transitivity
        ((\dlet_(xs <- n_dg n s)
          dunit (cons_tuple (x + c) (ivec_add xs center))) z).
      -- apply: eq_in_dlet.
         ++ move=> xs _ w.
            by rewrite dmargin_dunit ivec_add_cons.
         rewrite /n_dg /nfold_distr /=.
         have Hbehead :
             behead_tuple (nseq_tuple n.+1 (centered_discrete_gaussian s)) =
             nseq_tuple n (centered_discrete_gaussian s).
           by apply: val_inj.
         by rewrite Hbehead.
      rewrite -(dlet_dmargin (n_dg n s)
        (fun noise => ivec_add noise center)
        (fun xs => dunit (cons_tuple (x + c) xs)) z).
      by [].
    apply: eq_in_dlet.
    * by move=> xs _ w.
    exact: IH.
  rewrite -(dlet_dmargin (centered_discrete_gaussian s)
    (fun x : int => x + c)
    (fun x => \dlet_(xs <- n_dg_shifted center s)
      dunit (cons_tuple x xs)) y).
  apply: eq_in_dlet.
  + by move=> x _ z.
  exact: centered_discrete_gaussian_shift_add.
rewrite theadE.
have Hbehead : behead_tuple [tuple of c :: center] = center.
  by apply: val_inj.
by rewrite Hbehead.
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
