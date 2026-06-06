(* Distribution facts for Pythagorean errors. *)

Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals realsum exp distr.
From mathcomp Require Import lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From Mending.Probability Require Import Ae.
From Mending.Probability.KL Require Import Core Conditional Pinsker.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras RealTupleExtras.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

Section PythagoreanDistributionJudgments.

Context {R : realType}.

Theorem pythagorean_probability_preservation
    {n : nat} {Ω : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i)
    (P Q : {distr Ω / R}) (eps : n.-tuple R) :
  coordinates_separate coord ->
  (forall i : 'I_n, 0 <= tnth eps i) ->
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  (forall (i : 'I_n) (a : forall j : 'I_n, X j),
    δ_KL (conditional_coordinate coord P i a)
         (conditional_coordinate coord Q i a) <= tnth eps i) ->
  total_variation P Q <= Num.sqrt ((\sum_(i < n) tnth eps i) / 2).
Proof.
move=> Hsep Heps Hac HP HQ Hcond.
have Hpin := pinsker P Q Hac HP HQ.
apply: (le_trans Hpin).
apply: ler_wsqrtr.
have Hkl :
    δ_KL P Q <= \sum_(i < n) tnth eps i :=
  iterated_kl_chain_bound coord P Q eps Hsep Heps Hac HP HQ Hcond.
lra.
Qed.

Corollary pythagorean_probability_preservation_sup_pinsker
    {n : nat} {Ω : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i)
    (P Q : {distr Ω / R}) (eps : R) :
  coordinates_separate coord ->
  0 <= eps ->
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  (forall (i : 'I_n) (a : forall j : 'I_n, X j),
    δ_KL (conditional_coordinate coord P i a)
         (conditional_coordinate coord Q i a) <= eps) ->
  total_variation P Q <= Num.sqrt ((n%:R * eps) / 2).
Proof.
move=> Hsep Heps Hac HP HQ Hcond.
pose eps_tuple : n.-tuple R := [tuple eps | i < n].
have Heps_tuple : forall i : 'I_n, 0 <= tnth eps_tuple i.
  by move=> i; rewrite /eps_tuple tnth_mktuple.
have Hcond_tuple : forall (i : 'I_n) (a : forall j : 'I_n, X j),
    δ_KL (conditional_coordinate coord P i a)
         (conditional_coordinate coord Q i a) <= tnth eps_tuple i.
  by move=> i a; rewrite /eps_tuple tnth_mktuple; apply: Hcond.
have Htv :=
  pythagorean_probability_preservation coord P Q eps_tuple
    Hsep Heps_tuple Hac HP HQ Hcond_tuple.
apply: (le_trans Htv).
apply: ler_wsqrtr.
rewrite (eq_bigr (fun _ : 'I_n => eps)); last first.
  by move=> i _; rewrite /eps_tuple tnth_mktuple.
by rewrite big_const_ord iter_addr_0 mulr_natl.
Qed.

Definition pythDist
    {n : nat} {Ω : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i)
    (P Q : {distr Ω / R}) (eps : n.-tuple R) : Prop :=
  coordinates_separate coord /\
  (forall i : 'I_n, 0 <= tnth eps i) /\
  absolute_continuous P Q /\
  dweight P = 1 /\
  dweight Q = 1 /\
  forall (i : 'I_n) (a : forall j : 'I_n, X j),
    δ_KL (conditional_coordinate coord P i a)
         (conditional_coordinate coord Q i a) <= tnth eps i.

Lemma pythDist_total_variation
    {n : nat} {Ω : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i)
    (P Q : {distr Ω / R}) (eps : n.-tuple R) :
  pythDist coord P Q eps ->
  total_variation P Q <= Num.sqrt ((\sum_(i < n) tnth eps i) / 2).
Proof.
move=> [Hsep [Heps [Hac [HP [HQ Hcond]]]]].
exact: (pythagorean_probability_preservation coord P Q eps
          Hsep Heps Hac HP HQ Hcond).
Qed.


Definition rcons_choice {n : nat}
    (X : 'I_n -> choiceType) (A : choiceType)
    (i : 'I_n.+1) : choiceType :=
  if unlift ord_max i is Some j then X j else A.

Definition rcons_coord {n : nat} {Ω : choiceType}
    {X : 'I_n -> choiceType} {A : choiceType}
    (coord : forall i : 'I_n, Ω -> X i) (final : Ω -> A)
    (i : 'I_n.+1) : Ω -> rcons_choice X A i :=
  match unlift ord_max i as u return
      Ω -> (if u is Some j then X j else A) with
  | Some j => coord j
  | None => final
  end.

Definition pythDistWithFinal
    {n : nat} {Ω A : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i) (final : Ω -> A)
    (P Q : {distr Ω / R}) (eps : n.+1.-tuple R) : Prop :=
  pythDist (rcons_coord coord final) P Q eps.

Definition singleton_pyth_choice (A : choiceType) (_ : 'I_1) : choiceType := A.

Definition singleton_pyth_coord {A : choiceType}
    (i : 'I_1) : A -> singleton_pyth_choice A i :=
  fun x => x.

Lemma pythDist_kl_singleton
    {A : choiceType} (P Q : {distr A / R}) (eps : R) :
  0 <= eps ->
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  δ_KL P Q <= eps ->
  pythDist (@singleton_pyth_coord A) P Q [tuple eps].
Proof.
move=> Heps Hac HP HQ Hkl.
split.
- move=> x y Hxy.
  exact: (Hxy ord0).
split; first by move=> i; rewrite ord1 tnth0.
split; first exact: Hac.
split; first exact: HP.
split; first exact: HQ.
move=> i a.
rewrite ord1 tnth0.
have Hdcond (D : {distr A / R}) (HD : dweight D = 1) x :
    dcond D (fun y => tuple_prefix_eq
      (@singleton_pyth_coord A) ord0 a y) x = D x.
  rewrite dcondE /prc.
  have -> : \P_[D] [predI pred1 x & fun y =>
      tuple_prefix_eq (@singleton_pyth_coord A) ord0 a y] =
      \P_[D] (pred1 x).
    apply: eq_pr=> y.
    rewrite !inE /tuple_prefix_eq.
    rewrite andb_idr // => _.
    by apply/forallP=> j; rewrite /=.
  have -> : \P_[D] (fun y =>
      tuple_prefix_eq (@singleton_pyth_coord A) ord0 a y) =
      \P_[D] predT.
    apply: eq_pr=> y.
    rewrite !inE /tuple_prefix_eq.
    by apply/forallP=> j; rewrite /=.
  by rewrite -pr_pred1 HD divr1.
have Hconditional (D : {distr A / R}) (HD : dweight D = 1) x :
    conditional_coordinate (@singleton_pyth_coord A) D ord0 a x = D x.
  rewrite /conditional_coordinate dmargin_psumE.
  rewrite (realsum.psum_finseq (r := [:: x])).
  - by rewrite big_seq1 (Hdcond D HD) /singleton_pyth_coord eqxx mul1r
      ger0_norm ?ge0_mu.
  - by [].
  move=> y.
  rewrite !inE /singleton_pyth_coord.
  case Hxy: (y == x); first by rewrite (eqP Hxy).
  by rewrite mul0r eqxx.
rewrite /δ_KL /esp in Hkl *.
rewrite (realsum.eq_sum (F2 := fun x => ln (P x / Q x) * P x));
  first exact: Hkl.
by move=> x; rewrite !Hconditional.
Qed.

Definition empty_pyth_coord (_ : 'I_0) : choiceType := unit.

Lemma pythDistWithFinal_kl_final
    {Ω A : choiceType} (final : Ω -> A)
    (P Q : {distr Ω / R}) (eps : R) :
  injective final ->
  0 <= eps ->
  absolute_continuous P Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  δ_KL P Q <= eps ->
  pythDistWithFinal (X := empty_pyth_coord) (fun i : 'I_0 => fun _ => tt)
    final P Q [tuple eps].
Proof.
move=> Hfinal Heps Hac HP HQ Hkl.
split.
- move=> x y Hxy.
  apply: Hfinal.
  have := Hxy ord_max.
  rewrite /rcons_coord /rcons_choice.
  case E: (unlift ord_max ord_max) => [j|] /=.
  - by clear E; case: j.
  - by [].
split; first by move=> i; rewrite ord1 tnth0.
split; first exact: Hac.
split; first exact: HP.
split; first exact: HQ.
move=> i a.
have -> : i = ord_max by rewrite [i]ord1 [ord_max]ord1.
have -> : tnth [tuple eps] ord_max = eps by rewrite [ord_max]ord1 tnth0.
have Hdcond (D : {distr Ω / R}) (HD : dweight D = 1) x :
    dcond D (fun y => tuple_prefix_eq
      (rcons_coord (fun i : 'I_0 => fun _ => tt) final) ord_max a y) x =
      D x.
  rewrite dcondE /prc.
  have -> : \P_[D] [predI pred1 x & fun y => tuple_prefix_eq
      (rcons_coord (fun i : 'I_0 => fun _ => tt) final) ord_max a y] =
      \P_[D] (pred1 x).
    apply: eq_pr=> y.
    rewrite !inE /tuple_prefix_eq.
    rewrite andb_idr // => _.
    by apply/forallP=> j; rewrite /=.
  have -> : \P_[D] (fun y => tuple_prefix_eq
      (rcons_coord (fun i : 'I_0 => fun _ => tt) final) ord_max a y) =
      \P_[D] predT.
    apply: eq_pr=> y.
    rewrite !inE /tuple_prefix_eq.
    by apply/forallP=> j; rewrite /=.
  by rewrite -pr_pred1 HD divr1.
have Hconditional (D : {distr Ω / R}) (HD : dweight D = 1) (x : A) :
    dmargin final (dcond D (fun y => tuple_prefix_eq
      (rcons_coord (fun i : 'I_0 => fun _ => tt) final) ord_max a y)) x =
      dmargin final D x.
  rewrite !dmargin_psumE.
  apply: eq_psum=> y.
  by rewrite Hdcond.
have Hmargin : δ_KL (dmargin final P) (dmargin final Q) <= eps.
  by rewrite (kl_dmargin_injective final P Q Hfinal).
rewrite /conditional_coordinate /rcons_coord /rcons_choice unlift_none /=.
rewrite /δ_KL /esp in Hmargin *.
rewrite (realsum.eq_sum
  (F2 := fun x => ln (dmargin final P x / dmargin final Q x) *
    dmargin final P x)); first exact: Hmargin.
by move=> x; rewrite !Hconditional.
Qed.

Lemma pythDistWithFinal_total_variation
    {n : nat} {Ω A : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i) (final : Ω -> A)
    (P Q : {distr Ω / R}) (eps : n.+1.-tuple R) :
  pythDistWithFinal coord final P Q eps ->
  total_variation (dmargin final P) (dmargin final Q) <=
    pythagorean_tv_bound eps.
Admitted.

Lemma pythDistWithFinal_postprocess
    {n : nat} {Ω A B : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i) (final : Ω -> A)
    (P Q : {distr Ω / R}) (eps : n.+1.-tuple R)
    (K : A -> {distr B / R}) :
  pythDistWithFinal coord final P Q eps ->
  exists
  (Ω' : choiceType)
  (X' : 'I_n -> choiceType)
  (coord' : forall i : 'I_n, Ω' -> X' i)
  (final' : Ω' -> B)
  (P' Q' : {distr Ω' / R}),
    pythDistWithFinal coord' final' P' Q' eps /\
    dmargin final' P' =1 \dlet_(x <- dmargin final P) K x /\
    dmargin final' Q' =1 \dlet_(x <- dmargin final Q) K x.
Admitted.

Lemma pythDistWithFinal_bind
    {n m : nat} {Ω A B : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i) (final : Ω -> A)
    (P Q : {distr Ω / R}) (eps : n.+1.-tuple R) (eps' : m.+1.-tuple R)
    (KL KR : A -> {distr B / R}) :
  pythDistWithFinal coord final P Q eps ->
  (forall aL aR,
    aL \in dinsupp (dmargin final P) ->
    aR \in dinsupp (dmargin final Q) ->
    exists
    (Ω' : choiceType)
    (X' : 'I_m -> choiceType)
    (coord' : forall i : 'I_m, Ω' -> X' i)
    (final' : Ω' -> B)
    (P' Q' : {distr Ω' / R}),
      pythDistWithFinal coord' final' P' Q' eps' /\
      dmargin final' P' =1 KL aL /\
      dmargin final' Q' =1 KR aR) ->
  exists
  (Ωc : choiceType)
  (Xc : 'I_(n + m.+1) -> choiceType)
  (coordc : forall i : 'I_(n + m.+1), Ωc -> Xc i)
  (finalc : Ωc -> B)
  (Pc Qc : {distr Ωc / R}),
    pythDistWithFinal coordc finalc Pc Qc (cat_tuple eps eps') /\
    dmargin finalc Pc =1 \dlet_(a <- dmargin final P) KL a /\
    dmargin finalc Qc =1 \dlet_(a <- dmargin final Q) KR a.
Admitted.

(*
TODO: Restate the diagonal bind lemma with uniform continuation witnesses.

The tempting pointwise-existential shape

  forall a, exists Ω' X' coord' final' P' Q', ...

is not useful for constructing the composed choiceType Ωc: the continuation
choice space is hidden behind a Prop-level existential and may vary with [a].
The replacement should expose a fixed Ω'/X'/coord'/final' and kernels
P' Q' : A -> {distr Ω' / R}.
*)

Lemma pythDistWithFinal_bind_coupling
    {n : nat} {A B C : choiceType}
    (ML : {distr A / R}) (MR : {distr B / R})
    (KL : A -> {distr C / R}) (KR : B -> {distr C / R})
    (mid : pred (A * B)) (d0 : {distr (A * B) / R})
    (eps : n.+1.-tuple R) :
  coupling_with_loss d0 ML MR ->
  \P_[ d0 ] mid >= 1 ->
  (forall a b,
    mid (a, b) ->
    exists
    (Ω : choiceType)
    (X : 'I_n -> choiceType)
    (coord : forall i : 'I_n, Ω -> X i)
    (final : Ω -> C)
    (P Q : {distr Ω / R}),
      pythDistWithFinal coord final P Q eps /\
      dmargin final P =1 KL a /\
      dmargin final Q =1 KR b) ->
  exists
  (Ωc : choiceType)
  (Xc : 'I_n -> choiceType)
  (coordc : forall i : 'I_n, Ωc -> Xc i)
  (finalc : Ωc -> C)
  (Pc Qc : {distr Ωc / R}),
    pythDistWithFinal coordc finalc Pc Qc eps /\
    dmargin finalc Pc =1 \dlet_(a <- ML) KL a /\
    dmargin finalc Qc =1 \dlet_(b <- MR) KR b.
Admitted.

Lemma coupling_with_loss_prob1_left_support
    {A B : choiceType}
    (ML : {distr A / R}) (MR : {distr B / R})
    (mid : pred (A * B)) (d0 : {distr (A * B) / R}) :
  coupling_with_loss d0 ML MR ->
  \P_[ d0 ] mid >= 1 ->
  forall a, a \in dinsupp ML -> exists b, mid (a, b).
Admitted.

Lemma coupling_with_loss_prob1_right_support
    {A B : choiceType}
    (ML : {distr A / R}) (MR : {distr B / R})
    (mid : pred (A * B)) (d0 : {distr (A * B) / R}) :
  coupling_with_loss d0 ML MR ->
  \P_[ d0 ] mid >= 1 ->
  forall b, b \in dinsupp MR -> exists a, mid (a, b).
Admitted.

End PythagoreanDistributionJudgments.
