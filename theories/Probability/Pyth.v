(* Distribution facts for Pythagorean errors. *)

Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals realsum exp distr.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From Mending.Probability Require Import Ae KL.
From Mending.LibExtras.MathcompExtras Require Import DistrExtras RealListExtras.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

Section PythagoreanDistributionJudgments.

Context {R : realType}.

Definition pythDist
    {n : nat} {Ω : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i)
    (P Q : {distr Ω / R}) (eps : list R) : Prop :=
  size eps = n /\
  coordinates_separate coord /\
  (forall i : 'I_n, 0 <= nth 0 eps i) /\
  absolute_continuous P Q /\
  dweight P = 1 /\
  dweight Q = 1 /\
  forall (i : 'I_n) (a : forall j : 'I_n, X j),
    δ_KL (conditional_coordinate coord P i a)
         (conditional_coordinate coord Q i a) <= nth 0 eps i.

Lemma pythDist_total_variation
    {n : nat} {Ω : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i)
    (P Q : {distr Ω / R}) (eps : list R) :
  pythDist coord P Q eps ->
  total_variation P Q <= pythagorean_tv_bound eps.
Proof.
move=> [Hsize [Hsep [Heps [Hac [HP [HQ Hcond]]]]]].
exact: (pythagorean_probability_preservation coord P Q eps
          Hsize Hsep Heps Hac HP HQ Hcond).
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
    (P Q : {distr Ω / R}) (eps : list R) : Prop :=
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
  pythDist (@singleton_pyth_coord A) P Q [:: eps].
Admitted.

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
    final P Q [:: eps].
Admitted.

Lemma pythDistWithFinal_total_variation
    {n : nat} {Ω A : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i) (final : Ω -> A)
    (P Q : {distr Ω / R}) (eps : list R) :
  pythDistWithFinal coord final P Q eps ->
  total_variation (dmargin final P) (dmargin final Q) <=
    pythagorean_tv_bound eps.
Admitted.

Lemma pythDistWithFinal_postprocess
    {n : nat} {Ω A B : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i) (final : Ω -> A)
    (P Q : {distr Ω / R}) (eps : list R)
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
    (P Q : {distr Ω / R}) (eps eps' : list R)
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
    pythDistWithFinal coordc finalc Pc Qc (eps ++ eps') /\
    dmargin finalc Pc =1 \dlet_(a <- dmargin final P) KL a /\
    dmargin finalc Qc =1 \dlet_(a <- dmargin final Q) KR a.
Admitted.

Lemma pythDistWithFinal_bind_exists
    {n : nat} {Ω A B : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i) (final : Ω -> A)
    (P Q : {distr Ω / R}) (eps eps' : list R)
    (KL KR : A -> {distr B / R}) :
  pythDistWithFinal coord final P Q eps ->
  (forall aL aR,
    aL \in dinsupp (dmargin final P) ->
    aR \in dinsupp (dmargin final Q) ->
    exists
    (m : nat)
    (Ω' : choiceType)
    (X' : 'I_m -> choiceType)
    (coord' : forall i : 'I_m, Ω' -> X' i)
    (final' : Ω' -> B)
    (P' Q' : {distr Ω' / R}),
      pythDistWithFinal coord' final' P' Q' eps' /\
      dmargin final' P' =1 KL aL /\
      dmargin final' Q' =1 KR aR) ->
  exists
  (m : nat)
  (Ωc : choiceType)
  (Xc : 'I_m -> choiceType)
  (coordc : forall i : 'I_m, Ωc -> Xc i)
  (finalc : Ωc -> B)
  (Pc Qc : {distr Ωc / R}),
    pythDistWithFinal coordc finalc Pc Qc (eps ++ eps') /\
    dmargin finalc Pc =1 \dlet_(a <- dmargin final P) KL a /\
    dmargin finalc Qc =1 \dlet_(a <- dmargin final Q) KR a.
Admitted.

Lemma pythDistWithFinal_bind_coupling
    {n : nat} {A B C : choiceType}
    (ML : {distr A / R}) (MR : {distr B / R})
    (KL : A -> {distr C / R}) (KR : B -> {distr C / R})
    (mid : pred (A * B)) (d0 : {distr (A * B) / R})
    (eps : list R) :
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
