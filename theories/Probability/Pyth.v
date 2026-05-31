(* Distribution facts for Pythagorean errors. *)

Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals realsum exp distr.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From SSProve.Crypt Require Import Axioms.
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

Record pythDistWithFinalWitness (A : choiceType) (eps : list R) := {
  pyth_wit_n : nat;
  pyth_wit_Ω : choiceType;
  pyth_wit_X : 'I_pyth_wit_n -> choiceType;
  pyth_wit_coord : forall i : 'I_pyth_wit_n, pyth_wit_Ω -> pyth_wit_X i;
  pyth_wit_final : pyth_wit_Ω -> A;
  pyth_wit_P : {distr pyth_wit_Ω / R};
  pyth_wit_Q : {distr pyth_wit_Ω / R};
  pyth_wit_dist :
    pythDistWithFinal pyth_wit_coord pyth_wit_final pyth_wit_P pyth_wit_Q eps;
}.

Arguments pyth_wit_n {A eps}.
Arguments pyth_wit_Ω {A eps}.
Arguments pyth_wit_X {A eps}.
Arguments pyth_wit_coord {A eps}.
Arguments pyth_wit_final {A eps}.
Arguments pyth_wit_P {A eps}.
Arguments pyth_wit_Q {A eps}.
Arguments pyth_wit_dist {A eps}.

Definition pythBindMargins {A B : choiceType}
    (KL KR : A -> {distr B / R}) (aL aR : A)
    {eps : list R} (wit : pythDistWithFinalWitness B eps) : Prop :=
  dmargin wit.(pyth_wit_final) wit.(pyth_wit_P) =1 KL aL /\
  dmargin wit.(pyth_wit_final) wit.(pyth_wit_Q) =1 KR aR.

Lemma dinsupp_dmargin_image {A B : choiceType} (f : A -> B)
    (P : {distr A / R}) a :
  a \in dinsupp P -> f a \in dinsupp (dmargin f P).
Proof.
move=> Ha.
rewrite dmarginE.
apply: dlet_dinsupp; first exact: Ha.
by rewrite dunit1E eqxx pnatr_eq0.
Qed.

Lemma absolute_continuous_dinsupp {A : choiceType} (P Q : {distr A / R}) a :
  absolute_continuous P Q ->
  a \in dinsupp P ->
  a \in dinsupp Q.
Proof.
move=> Hac /dinsuppP Ha.
apply/dinsuppP=> HQ.
exact: Ha (Hac a HQ).
Qed.

Lemma dweight1_dinsupp_nonempty {A : choiceType} (P : {distr A / R}) :
  dweight P = 1 -> exists a, a \in dinsupp P.
Proof.
move=> HP.
have Hnz : \P_[P] predT <> 0 by rewrite HP; apply/eqP; rewrite oner_eq0.
rewrite /pr in Hnz.
have [a Ha] := neq0_psum Hnz.
exists a.
apply/dinsuppP=> Pa0.
apply: Ha.
by rewrite Pa0 mulr0.
Qed.

Lemma pyth_wit_absolute_continuous {A : choiceType} {eps : list R}
    (wit : pythDistWithFinalWitness A eps) :
  absolute_continuous wit.(pyth_wit_P) wit.(pyth_wit_Q).
Proof.
by have [_ [_ [_ [Hac _]]]] := wit.(pyth_wit_dist).
Qed.

Lemma pyth_wit_mass1_P {A : choiceType} {eps : list R}
    (wit : pythDistWithFinalWitness A eps) :
  dweight wit.(pyth_wit_P) = 1.
Proof.
by have [_ [_ [_ [_ [HP _]]]]] := wit.(pyth_wit_dist).
Qed.

Lemma pyth_wit_mass1_Q {A : choiceType} {eps : list R}
    (wit : pythDistWithFinalWitness A eps) :
  dweight wit.(pyth_wit_Q) = 1.
Proof.
by have [_ [_ [_ [_ [_ [HQ _]]]]]] := wit.(pyth_wit_dist).
Qed.

Definition dlet_tagged {I : choiceType} (F : I -> choiceType)
    (P : {distr I / R}) (K : forall i, {distr (F i) / R}) :
    {distr ({i : I & F i}) / R} :=
  \dlet_(i <- P) dmargin (fun x => Tagged F x) (K i).

Definition pythFamilyP {A B : choiceType} {eps eps' : list R}
    (base : pythDistWithFinalWitness A eps)
    (next : base.(pyth_wit_Ω) -> pythDistWithFinalWitness B eps') :=
  dlet_tagged (fun omega => (next omega).(pyth_wit_Ω))
    base.(pyth_wit_P) (fun omega => (next omega).(pyth_wit_P)).

Definition pythFamilyQ {A B : choiceType} {eps eps' : list R}
    (base : pythDistWithFinalWitness A eps)
    (next : base.(pyth_wit_Ω) -> pythDistWithFinalWitness B eps') :=
  dlet_tagged (fun omega => (next omega).(pyth_wit_Ω))
    base.(pyth_wit_Q) (fun omega => (next omega).(pyth_wit_Q)).

Definition pythFamilyFinal {A B : choiceType} {eps eps' : list R}
    (base : pythDistWithFinalWitness A eps)
    (next : base.(pyth_wit_Ω) -> pythDistWithFinalWitness B eps')
    (out : {omega : base.(pyth_wit_Ω) & (next omega).(pyth_wit_Ω)})
    : (A * B)%type :=
  (base.(pyth_wit_final) (tag out),
   (next (tag out)).(pyth_wit_final) (tagged out)).

Lemma pythFamilyP_margin {A B : choiceType} {eps eps' : list R}
    (base : pythDistWithFinalWitness A eps)
    (KL : A -> {distr B / R})
    (next : base.(pyth_wit_Ω) -> pythDistWithFinalWitness B eps') :
  (forall omega,
    omega \in dinsupp base.(pyth_wit_P) ->
    dmargin (next omega).(pyth_wit_final) (next omega).(pyth_wit_P) =1
      KL (base.(pyth_wit_final) omega)) ->
  dmargin (pythFamilyFinal base next) (pythFamilyP base next) =1
    \dlet_(a <- dmargin base.(pyth_wit_final) base.(pyth_wit_P))
      \dlet_(b <- KL a) dunit (a, b).
Proof.
move=> Hnext out.
rewrite /pythFamilyP /dlet_tagged dmarginE.
rewrite __deprecated__dlet_dlet.
rewrite (__deprecated__dlet_dmargin base.(pyth_wit_P)
  base.(pyth_wit_final) (fun a => \dlet_(b <- KL a) dunit (a, b))).
apply: eq_in_dlet; last by [].
move=> omega Homega out'.
rewrite (__deprecated__dlet_dmargin (next omega).(pyth_wit_P)
  (fun x => Tagged (fun omega => (next omega).(pyth_wit_Ω)) x)
  (fun x => dunit (pythFamilyFinal base next x))).
rewrite /= -(__deprecated__dlet_dmargin (next omega).(pyth_wit_P)
  (next omega).(pyth_wit_final)
  (fun b => dunit (base.(pyth_wit_final) omega, b))).
apply: eq_in_dlet; last exact: Hnext omega Homega.
by move=> b _ out''.
Qed.

Lemma pythFamilyQ_margin {A B : choiceType} {eps eps' : list R}
    (base : pythDistWithFinalWitness A eps)
    (KR : A -> {distr B / R})
    (next : base.(pyth_wit_Ω) -> pythDistWithFinalWitness B eps') :
  (forall omega,
    omega \in dinsupp base.(pyth_wit_Q) ->
    dmargin (next omega).(pyth_wit_final) (next omega).(pyth_wit_Q) =1
      KR (base.(pyth_wit_final) omega)) ->
  dmargin (pythFamilyFinal base next) (pythFamilyQ base next) =1
    \dlet_(a <- dmargin base.(pyth_wit_final) base.(pyth_wit_Q))
      \dlet_(b <- KR a) dunit (a, b).
Proof.
move=> Hnext out.
rewrite /pythFamilyQ /dlet_tagged dmarginE.
rewrite __deprecated__dlet_dlet.
rewrite (__deprecated__dlet_dmargin base.(pyth_wit_Q)
  base.(pyth_wit_final) (fun a => \dlet_(b <- KR a) dunit (a, b))).
apply: eq_in_dlet; last by [].
move=> omega Homega out'.
rewrite (__deprecated__dlet_dmargin (next omega).(pyth_wit_Q)
  (fun x => Tagged (fun omega => (next omega).(pyth_wit_Ω)) x)
  (fun x => dunit (pythFamilyFinal base next x))).
rewrite /= -(__deprecated__dlet_dmargin (next omega).(pyth_wit_Q)
  (next omega).(pyth_wit_final)
  (fun b => dunit (base.(pyth_wit_final) omega, b))).
apply: eq_in_dlet; last exact: Hnext omega Homega.
by move=> b _ out''.
Qed.

Definition taggedChoice (I : choiceType) (F : I -> choiceType) : choiceType :=
  @Choice.Pack {i : I & F i} (Choice.on {i : I & F i}).

Definition pythAppendChoice {n n' : nat} {Ω A : choiceType}
    (X : 'I_n -> choiceType) (Ω' : Ω -> choiceType)
    (X' : forall omega, 'I_n' -> choiceType)
    (i : 'I_(n.+1 + n')) : choiceType :=
  match split i with
  | inl j => rcons_choice X A j
  | inr k => taggedChoice Ω (fun omega => X' omega k)
  end.

Definition pythAppendCoord {n n' : nat} {Ω A : choiceType}
    {X : 'I_n -> choiceType} {Ω' : Ω -> choiceType}
    {X' : forall omega, 'I_n' -> choiceType}
    (coord : forall i, Ω -> X i) (final : Ω -> A)
    (coord' : forall omega i, Ω' omega -> X' omega i)
    (i : 'I_(n.+1 + n'))
    (out : {omega : Ω & Ω' omega}) :
    Choice.sort (match split i with
    | inl j => rcons_choice X A j
    | inr k => taggedChoice Ω (fun omega => X' omega k)
    end) :=
  match split i as s return
      Choice.sort (match s with
      | inl j => rcons_choice X A j
      | inr k => taggedChoice Ω (fun omega => X' omega k)
      end)
  with
  | inl j => rcons_coord coord final j (tag out)
  | inr k => Tagged (fun omega => X' omega k)
      (coord' (tag out) k (tagged out))
  end.

Definition pythAppendFinal {Ω A B : choiceType} {Ω' : Ω -> choiceType}
    (final : Ω -> A) (final' : forall omega, Ω' omega -> B)
    (out : {omega : Ω & Ω' omega}) : (A * B)%type :=
  (final (tag out), final' (tag out) (tagged out)).

Lemma pythDistWithFinal_bind_dependent_fixed_size_nonnegative
    {n n' : nat} {Ω A B : choiceType}
    {X : 'I_n -> choiceType} {Ω' : Ω -> choiceType}
    {X' : forall omega, 'I_n' -> choiceType}
    (coord : forall i, Ω -> X i) (final : Ω -> A)
    (P Q : {distr Ω / R}) (eps : list R)
    (coord' : forall omega i, Ω' omega -> X' omega i)
    (final' : forall omega, Ω' omega -> B)
    (P' Q' : forall omega, {distr (Ω' omega) / R}) (eps' : list R) :
  pythDistWithFinal coord final P Q eps ->
  (forall omega,
    pythDistWithFinal (coord' omega) (final' omega) (P' omega) (Q' omega)
      eps') ->
  size (eps ++ eps') = (n.+1 + n').+1 /\
  forall i : 'I_(n.+1 + n').+1, 0 <= nth 0 (eps ++ eps') i.
Proof.
move=> [Hsize [_ [Hnonneg [_ [HP _]]]]] Hdist'.
have [omega _] := dweight1_dinsupp_nonempty P HP.
have [Hsize' [_ [Hnonneg' _]]] := Hdist' omega.
split.
- by rewrite size_cat Hsize Hsize' addnS.
- move=> i.
  rewrite nth_cat.
  case Hlt: (val i < size eps)%N.
  - change (0 <= nth 0 eps (val i)).
    have Hlt' : (val i < n.+1)%N.
      by move: Hlt; rewrite Hsize.
    exact: (Hnonneg (Ordinal Hlt')).
  - have Hge : (size eps <= val i)%N by rewrite leqNgt Hlt.
    have Hi : (val i < (n.+1 + n').+1)%N := ltn_ord i.
    have Hi' : (val i - size eps < size eps')%N.
      rewrite ltn_subLR // -size_cat.
      by move: Hi; rewrite size_cat Hsize Hsize' addnS.
    change (0 <= nth 0 eps' (val i - size eps)).
    have Hi'' : (val i - size eps < n'.+1)%N.
      by move: Hi'; rewrite Hsize'.
    exact: (Hnonneg' (Ordinal Hi'')).
Qed.

Lemma pythDistWithFinal_bind_dependent_fixed_separate
    {n n' : nat} {Ω A B : choiceType}
    {X : 'I_n -> choiceType} {Ω' : Ω -> choiceType}
    {X' : forall omega, 'I_n' -> choiceType}
    (coord : forall i, Ω -> X i) (final : Ω -> A)
    (P Q : {distr Ω / R}) (eps : list R)
    (coord' : forall omega i, Ω' omega -> X' omega i)
    (final' : forall omega, Ω' omega -> B)
    (P' Q' : forall omega, {distr (Ω' omega) / R}) (eps' : list R) :
  pythDistWithFinal coord final P Q eps ->
  (forall omega,
    pythDistWithFinal (coord' omega) (final' omega) (P' omega) (Q' omega)
      eps') ->
  coordinates_separate
    (rcons_coord (pythAppendCoord coord final coord')
      (pythAppendFinal final final')).
Proof.
move=> [_ [Hsep _]] Hdist'.
move=> [omega1 omega1'] [omega2 omega2'] Heq /=.
have Homega : omega1 = omega2.
  apply: Hsep=> i.
  remember (lift ord_max (lshift n' i)) as ii eqn:Eii.
  move: (Heq ii).
  rewrite /rcons_coord /rcons_choice.
  case: unliftP => [k Hii|Hii].
  - move: Eii; rewrite Hii.
    move/(@lift_inj _ ord_max)=> ->.
    by rewrite /pythAppendCoord (unsplitK (inl _ _)).
  - by move: Eii; rewrite Hii => /eqP; rewrite eq_liftF.
subst omega2.
congr (Tagged (fun omega => Ω' omega) _).
have [_ [Hsep' _]] := Hdist' omega1.
have Hcoord' j : coord' omega1 j omega1' = coord' omega1 j omega2'.
  remember (lift ord_max (rshift n.+1 j)) as ii eqn:Eii.
  move: (Heq ii).
  rewrite /rcons_coord /rcons_choice.
  case: unliftP => [k Hii|Hii].
  - move: Eii; rewrite Hii.
    move/(@lift_inj _ ord_max)=> ->.
    rewrite /pythAppendCoord (unsplitK (inr _ _)) => H.
    exact: (eq_from_Tagged H).
  - by move: Eii; rewrite Hii => /eqP; rewrite eq_liftF.
have Hfinal' : final' omega1 omega1' = final' omega1 omega2'.
  have := Heq ord_max.
  by rewrite /rcons_coord /rcons_choice unlift_none => -[H].
apply: Hsep'=> i.
rewrite /rcons_coord /rcons_choice.
by case: unliftP => [j _|_]; [apply: Hcoord' | apply: Hfinal'].
Qed.

Lemma absolute_continuous_dlet {A B : choiceType}
    (P Q : {distr A / R}) (F G : A -> {distr B / R}) :
  absolute_continuous P Q ->
  (forall x, x \in dinsupp P -> absolute_continuous (F x) (G x)) ->
  absolute_continuous (\dlet_(x <- P) F x) (\dlet_(x <- Q) G x).
Proof.
move=> Hac HFG y HQ.
rewrite dletE.
apply: psum_eq0=> x.
case Px0: (P x == 0).
- by rewrite (eqP Px0) mul0r.
- have HxP : x \in dinsupp P by rewrite in_dinsupp Px0.
  have HxQ := absolute_continuous_dinsupp P Q x Hac HxP.
  have Gy0 := eq0_dlet HQ HxQ.
  have Fy0 := HFG x HxP y Gy0.
  by rewrite Fy0 mulr0.
Qed.

Lemma absolute_continuous_dmargin {A B : choiceType} (f : A -> B)
    (P Q : {distr A / R}) :
  absolute_continuous P Q ->
  absolute_continuous (dmargin f P) (dmargin f Q).
Proof.
move=> Hac.
change (absolute_continuous
  (dlet (fun x => dunit (f x)) P) (dlet (fun x => dunit (f x)) Q)).
apply: (absolute_continuous_dlet P Q
  (fun x => dunit (f x)) (fun x => dunit (f x))).
- exact: Hac.
by move=> x _ y.
Qed.

Lemma dweightE {A : choiceType} (P : {distr A / R}) :
  dweight P = psum P.
Proof.
rewrite /pr.
by apply: eq_psum=> x; rewrite mul1r.
Qed.

Lemma dweight_dlet_mass1 {A B : choiceType}
    (P : {distr A / R}) (F : A -> {distr B / R}) :
  dweight P = 1 ->
  (forall x, x \in dinsupp P -> dweight (F x) = 1) ->
  dweight (\dlet_(x <- P) F x) = 1.
Proof.
move=> HP HF.
rewrite dweightE.
rewrite (eq_psum (F2 := fun y => psum (fun x => P x * F x y))).
  rewrite -__admitted__interchange_psum.
  - rewrite (eq_psum (F2 := P)); last first.
      move=> x.
      rewrite psumZ //.
      case Hx: (x \in dinsupp P).
      + by rewrite -(dweightE (F x)) HF // mulr1.
      + by move/dinsuppPn: Hx => ->; rewrite mul0r.
    by rewrite -dweightE.
  - by move=> x; apply: summableZ; exact: (summable_mu (F x)).
  - apply: (le_summable (F2 := P)).
    + move=> x.
      rewrite psumZ //.
      apply/andP; split.
      * by rewrite mulr_ge0 ?ge0_mu ?ge0_psum.
      * rewrite -{2}[P x]mulr1.
        by rewrite mulr1 mulrC ler_piMl // le1_mu.
    + exact: (summable_mu P).
move=> y.
by rewrite dletE.
Qed.

Lemma pythDistWithFinal_bind_dependent_fixed_measure
    {n n' : nat} {Ω A B : choiceType}
    {X : 'I_n -> choiceType} {Ω' : Ω -> choiceType}
    {X' : forall omega, 'I_n' -> choiceType}
    (coord : forall i, Ω -> X i) (final : Ω -> A)
    (P Q : {distr Ω / R}) (eps : list R)
    (coord' : forall omega i, Ω' omega -> X' omega i)
    (final' : forall omega, Ω' omega -> B)
    (P' Q' : forall omega, {distr (Ω' omega) / R}) (eps' : list R) :
  pythDistWithFinal coord final P Q eps ->
  (forall omega,
    pythDistWithFinal (coord' omega) (final' omega) (P' omega) (Q' omega)
      eps') ->
  absolute_continuous (dlet_tagged Ω' P P') (dlet_tagged Ω' Q Q') /\
  dweight (dlet_tagged Ω' P P') = 1 /\
  dweight (dlet_tagged Ω' Q Q') = 1.
Proof.
move=> Hdist Hdist'.
have [_ [_ [_ [Hac [HP [HQ _]]]]]] := Hdist.
rewrite /dlet_tagged.
split.
- apply: (absolute_continuous_dlet P Q
    (fun omega => dmargin (fun x => Tagged Ω' x) (P' omega))
    (fun omega => dmargin (fun x => Tagged Ω' x) (Q' omega))).
  - exact: Hac.
  move=> omega Homega.
  apply: absolute_continuous_dmargin.
  by have [_ [_ [_ [Hac' _]]]] := Hdist' omega.
split.
- apply: (dweight_dlet_mass1 P
    (fun omega => dmargin (fun x => Tagged Ω' x) (P' omega))).
  - exact: HP.
  move=> omega _.
  rewrite dmargin_dweight.
  by have [_ [_ [_ [_ [HP' _]]]]] := Hdist' omega.
- apply: (dweight_dlet_mass1 Q
    (fun omega => dmargin (fun x => Tagged Ω' x) (Q' omega))).
  - exact: HQ.
  move=> omega _.
  rewrite dmargin_dweight.
  by have [_ [_ [_ [_ [_ [HQ' _]]]]]] := Hdist' omega.
Qed.

Definition pythAppendConditionalKL
    {n n' : nat} {Ω A B : choiceType}
    {X : 'I_n -> choiceType} {Ω' : Ω -> choiceType}
    {X' : forall omega, 'I_n' -> choiceType}
    (coord : forall i, Ω -> X i) (final : Ω -> A)
    (P Q : {distr Ω / R})
    (coord' : forall omega i, Ω' omega -> X' omega i)
    (final' : forall omega, Ω' omega -> B)
    (P' Q' : forall omega, {distr (Ω' omega) / R})
    (i : 'I_(n.+1 + n').+1)
    (a : forall j : 'I_(n.+1 + n').+1,
      rcons_choice (pythAppendChoice X Ω' X') (A * B)%type j) : R :=
  δ_KL
    (conditional_coordinate
      (rcons_coord (pythAppendCoord coord final coord')
        (pythAppendFinal final final'))
      (dlet_tagged Ω' P P') i a)
    (conditional_coordinate
      (rcons_coord (pythAppendCoord coord final coord')
        (pythAppendFinal final final'))
      (dlet_tagged Ω' Q Q') i a).

Definition pythAppendRightIndex {n n' : nat} (i : 'I_n'.+1) :
    'I_(n.+1 + n').+1 :=
  match unlift ord_max i with
  | Some j => lift ord_max (rshift n.+1 j)
  | None => ord_max
  end.

Lemma pythDistWithFinal_bind_dependent_fixed_conditional_old
    {n n' : nat} {Ω A B : choiceType}
    {X : 'I_n -> choiceType} {Ω' : Ω -> choiceType}
    {X' : forall omega, 'I_n' -> choiceType}
    (coord : forall i, Ω -> X i) (final : Ω -> A)
    (P Q : {distr Ω / R}) (eps : list R)
    (coord' : forall omega i, Ω' omega -> X' omega i)
    (final' : forall omega, Ω' omega -> B)
    (P' Q' : forall omega, {distr (Ω' omega) / R}) (eps' : list R) :
  pythDistWithFinal coord final P Q eps ->
  (forall omega,
    pythDistWithFinal (coord' omega) (final' omega) (P' omega) (Q' omega)
      eps') ->
  forall
    (i : 'I_n.+1)
    (a : forall j : 'I_(n.+1 + n').+1,
      rcons_choice (pythAppendChoice X Ω' X') (A * B)%type j),
    pythAppendConditionalKL coord final P Q coord' final' P' Q'
      (lift ord_max (lshift n' i)) a <= nth 0 eps i.
Admitted.

Lemma pythDistWithFinal_bind_dependent_fixed_conditional_right
    {n n' : nat} {Ω A B : choiceType}
    {X : 'I_n -> choiceType} {Ω' : Ω -> choiceType}
    {X' : forall omega, 'I_n' -> choiceType}
    (coord : forall i, Ω -> X i) (final : Ω -> A)
    (P Q : {distr Ω / R}) (eps : list R)
    (coord' : forall omega i, Ω' omega -> X' omega i)
    (final' : forall omega, Ω' omega -> B)
    (P' Q' : forall omega, {distr (Ω' omega) / R}) (eps' : list R) :
  pythDistWithFinal coord final P Q eps ->
  (forall omega,
    pythDistWithFinal (coord' omega) (final' omega) (P' omega) (Q' omega)
      eps') ->
  forall
    (i : 'I_n'.+1)
    (a : forall j : 'I_(n.+1 + n').+1,
      rcons_choice (pythAppendChoice X Ω' X') (A * B)%type j),
    pythAppendConditionalKL coord final P Q coord' final' P' Q'
      (pythAppendRightIndex i) a <= nth 0 eps' i.
Admitted.

Lemma pythDistWithFinal_bind_dependent_fixed_conditional
    {n n' : nat} {Ω A B : choiceType}
    {X : 'I_n -> choiceType} {Ω' : Ω -> choiceType}
    {X' : forall omega, 'I_n' -> choiceType}
    (coord : forall i, Ω -> X i) (final : Ω -> A)
    (P Q : {distr Ω / R}) (eps : list R)
    (coord' : forall omega i, Ω' omega -> X' omega i)
    (final' : forall omega, Ω' omega -> B)
    (P' Q' : forall omega, {distr (Ω' omega) / R}) (eps' : list R) :
  pythDistWithFinal coord final P Q eps ->
  (forall omega,
    pythDistWithFinal (coord' omega) (final' omega) (P' omega) (Q' omega)
      eps') ->
  forall
    (i : 'I_(n.+1 + n').+1)
    (a : forall j : 'I_(n.+1 + n').+1,
      rcons_choice (pythAppendChoice X Ω' X') (A * B)%type j),
    pythAppendConditionalKL coord final P Q coord' final' P' Q' i a <=
      nth 0 (eps ++ eps') i.
Proof.
move=> Hdist Hdist' i a.
have [Hsize _] := Hdist.
case: (unliftP ord_max i) => [k|] ->.
- case: (split_ordP k) => [j|j] ->.
  - have := pythDistWithFinal_bind_dependent_fixed_conditional_old
      coord final P Q eps coord' final' P' Q' eps' Hdist Hdist' j a.
    rewrite nth_cat Hsize /= /bump.
    have Hj : (j < n.+1 + n')%N :=
      leq_trans (ltn_ord j) (leq_addr n' n.+1).
    have -> : (n.+1 + n' <= j)%N = false by rewrite leqNgt Hj.
    by rewrite /= ltn_ord.
  - have := pythDistWithFinal_bind_dependent_fixed_conditional_right
      coord final P Q eps coord' final' P' Q' eps' Hdist Hdist'
      (lift ord_max j) a.
    rewrite /pythAppendRightIndex liftK.
    rewrite nth_cat Hsize /= /bump.
    have -> : (n.+1 + n' <= n.+1 + j)%N = false.
      by rewrite leq_add2l leqNgt ltn_ord.
    rewrite /=.
    rewrite ltnNge leq_addr /=.
    have -> : (n' <= j)%N = false by rewrite leqNgt ltn_ord.
    by rewrite /= !add0n addKn.
- have := pythDistWithFinal_bind_dependent_fixed_conditional_right
    coord final P Q eps coord' final' P' Q' eps' Hdist Hdist' ord_max a.
  rewrite /pythAppendRightIndex unlift_none.
  rewrite nth_cat Hsize /= ltnNge leq_addr /=.
  by rewrite addKn.
Qed.

(* Mathematical core at fixed dimensions.  This is the conditional-KL append
   theorem: old coordinates, the old final coordinate, continuation
   coordinates, and finally the pair of observable finals. *)
Lemma pythDistWithFinal_bind_dependent_fixed
    {n n' : nat} {Ω A B : choiceType}
    {X : 'I_n -> choiceType} {Ω' : Ω -> choiceType}
    {X' : forall omega, 'I_n' -> choiceType}
    (coord : forall i, Ω -> X i) (final : Ω -> A)
    (P Q : {distr Ω / R}) (eps : list R)
    (coord' : forall omega i, Ω' omega -> X' omega i)
    (final' : forall omega, Ω' omega -> B)
    (P' Q' : forall omega, {distr (Ω' omega) / R}) (eps' : list R) :
  pythDistWithFinal coord final P Q eps ->
  (forall omega,
    pythDistWithFinal (coord' omega) (final' omega) (P' omega) (Q' omega)
      eps') ->
  pythDistWithFinal (pythAppendCoord coord final coord')
    (pythAppendFinal final final')
    (dlet_tagged Ω' P P') (dlet_tagged Ω' Q Q') (eps ++ eps').
Proof.
move=> Hdist Hdist'.
have [Hsize Hnonneg] :=
  pythDistWithFinal_bind_dependent_fixed_size_nonnegative
    coord final P Q eps coord' final' P' Q' eps' Hdist Hdist'.
have Hsep :=
  pythDistWithFinal_bind_dependent_fixed_separate
    coord final P Q eps coord' final' P' Q' eps' Hdist Hdist'.
have [Hac [HP HQ]] :=
  pythDistWithFinal_bind_dependent_fixed_measure
    coord final P Q eps coord' final' P' Q' eps' Hdist Hdist'.
split; first exact: Hsize.
split; first exact: Hsep.
split; first exact: Hnonneg.
split; first exact: Hac.
split; first exact: HP.
split; first exact: HQ.
exact: (pythDistWithFinal_bind_dependent_fixed_conditional
  coord final P Q eps coord' final' P' Q' eps' Hdist Hdist').
Qed.

Definition transportOrdBack {n n' : nat} (Hn : n = n') : 'I_n' -> 'I_n :=
  match Hn with
  | erefl => fun i => i
  end.

Lemma pythDistWithFinal_cast_coord
    {n n' : nat} {Ω A : choiceType} {X : 'I_n -> choiceType}
    (Hn : n = n') (coord : forall i, Ω -> X i) (final : Ω -> A)
    (P Q : {distr Ω / R}) (eps : list R) :
  pythDistWithFinal coord final P Q eps ->
  pythDistWithFinal (fun i => coord (transportOrdBack Hn i)) final P Q eps.
Proof.
move=> Hdist.
destruct Hn.
exact: Hdist.
Qed.

(* Transport-only normalization.  Each continuation witness stores its own
   coordinate count, but every count is propositionally equal to [n'] because
   every witness uses the same [eps']. *)
Lemma pythDistWithFinalWitness_family_normalize
    {A B : choiceType} {eps eps' : list R}
    (base : pythDistWithFinalWitness A eps)
    (next : base.(pyth_wit_Ω) -> pythDistWithFinalWitness B eps') :
  exists
  (n' : nat)
  (X' : forall omega, 'I_n' -> choiceType)
  (coord' : forall omega i, (next omega).(pyth_wit_Ω) -> X' omega i),
    (forall omega,
      pythDistWithFinal (coord' omega) (next omega).(pyth_wit_final)
        (next omega).(pyth_wit_P) (next omega).(pyth_wit_Q) eps').
Proof.
have Hn omega : (next omega).(pyth_wit_n) = (size eps').-1.
  have [Hsize _] := (next omega).(pyth_wit_dist).
  by rewrite Hsize.
exists (size eps').-1,
  (fun omega i => (next omega).(pyth_wit_X) (transportOrdBack (Hn omega) i)),
  (fun omega i => (next omega).(pyth_wit_coord) (transportOrdBack (Hn omega) i)).
move=> omega.
exact: (pythDistWithFinal_cast_coord (Hn omega)
  (next omega).(pyth_wit_coord) (next omega).(pyth_wit_final)
  (next omega).(pyth_wit_P) (next omega).(pyth_wit_Q) eps'
  (next omega).(pyth_wit_dist)).
Qed.

Lemma pythDistWithFinalWitness_bind_family_coordinates
    {A B : choiceType} {eps eps' : list R}
    (base : pythDistWithFinalWitness A eps)
    (next : base.(pyth_wit_Ω) -> pythDistWithFinalWitness B eps') :
  exists
  (m : nat)
  (X : 'I_m -> choiceType)
  (coord : forall i : 'I_m,
    {omega : base.(pyth_wit_Ω) & (next omega).(pyth_wit_Ω)} -> X i),
    pythDistWithFinal coord (pythFamilyFinal base next)
      (pythFamilyP base next) (pythFamilyQ base next) (eps ++ eps').
Proof.
have [n' [X' [coord' Hdist']]] :=
  pythDistWithFinalWitness_family_normalize base next.
exists (base.(pyth_wit_n).+1 + n'), (pythAppendChoice
  base.(pyth_wit_X) (fun omega => (next omega).(pyth_wit_Ω)) X'),
  (pythAppendCoord base.(pyth_wit_coord) base.(pyth_wit_final) coord').
exact: (pythDistWithFinal_bind_dependent_fixed
  base.(pyth_wit_coord) base.(pyth_wit_final)
  base.(pyth_wit_P) base.(pyth_wit_Q) eps coord'
  (fun omega => (next omega).(pyth_wit_final))
  (fun omega => (next omega).(pyth_wit_P))
  (fun omega => (next omega).(pyth_wit_Q)) eps'
  base.(pyth_wit_dist) Hdist').
Qed.

(* The remaining coordinate proof is now concrete: the old coordinates, the
   old final coordinate, and the dependent continuation coordinates are
   concatenated, while [pythFamilyFinal] becomes the new final coordinate. *)
Lemma pythDistWithFinalWitness_bind_family_core
    {A B : choiceType} {eps eps' : list R}
    (base : pythDistWithFinalWitness A eps)
    (KL KR : A -> {distr B / R})
    (next : base.(pyth_wit_Ω) -> pythDistWithFinalWitness B eps') :
  (forall omega,
    omega \in dinsupp base.(pyth_wit_P) ->
    dmargin (next omega).(pyth_wit_final) (next omega).(pyth_wit_P) =1
      KL (base.(pyth_wit_final) omega)) ->
  (forall omega,
    omega \in dinsupp base.(pyth_wit_Q) ->
    dmargin (next omega).(pyth_wit_final) (next omega).(pyth_wit_Q) =1
      KR (base.(pyth_wit_final) omega)) ->
  exists
  (m : nat)
  (X : 'I_m -> choiceType)
  (coord : forall i : 'I_m,
    {omega : base.(pyth_wit_Ω) & (next omega).(pyth_wit_Ω)} -> X i),
    pythDistWithFinal coord (pythFamilyFinal base next)
      (pythFamilyP base next) (pythFamilyQ base next) (eps ++ eps') /\
    dmargin (pythFamilyFinal base next) (pythFamilyP base next) =1
      \dlet_(a <- dmargin base.(pyth_wit_final) base.(pyth_wit_P))
        \dlet_(b <- KL a) dunit (a, b) /\
    dmargin (pythFamilyFinal base next) (pythFamilyQ base next) =1
      \dlet_(a <- dmargin base.(pyth_wit_final) base.(pyth_wit_Q))
        \dlet_(b <- KR a) dunit (a, b).
Proof.
move=> HnextP HnextQ.
have [m [X [coord Hdist]]] :=
  pythDistWithFinalWitness_bind_family_coordinates base next.
exists m, X, coord.
split; first exact: Hdist.
split.
- exact: pythFamilyP_margin HnextP.
- exact: pythFamilyQ_margin HnextQ.
Qed.

(* Mathematical core: concatenate the coordinates of a base witness with a
   witness family indexed by its latent points. *)
Lemma pythDistWithFinalWitness_bind_family
    {A B : choiceType} {eps eps' : list R}
    (base : pythDistWithFinalWitness A eps)
    (KL KR : A -> {distr B / R})
    (next : base.(pyth_wit_Ω) -> pythDistWithFinalWitness B eps') :
  (forall omega,
    omega \in dinsupp base.(pyth_wit_P) ->
    dmargin (next omega).(pyth_wit_final) (next omega).(pyth_wit_P) =1
      KL (base.(pyth_wit_final) omega)) ->
  (forall omega,
    omega \in dinsupp base.(pyth_wit_Q) ->
    dmargin (next omega).(pyth_wit_final) (next omega).(pyth_wit_Q) =1
      KR (base.(pyth_wit_final) omega)) ->
  exists wit : pythDistWithFinalWitness (A * B)%type (eps ++ eps'),
    dmargin wit.(pyth_wit_final) wit.(pyth_wit_P) =1
      \dlet_(a <- dmargin base.(pyth_wit_final) base.(pyth_wit_P))
        \dlet_(b <- KL a) dunit (a, b) /\
    dmargin wit.(pyth_wit_final) wit.(pyth_wit_Q) =1
      \dlet_(a <- dmargin base.(pyth_wit_final) base.(pyth_wit_Q))
        \dlet_(b <- KR a) dunit (a, b).
Proof.
move=> HnextP HnextQ.
have [m [X [coord [Hdist [HP HQ]]]]] :=
  pythDistWithFinalWitness_bind_family_core base KL KR next HnextP HnextQ.
exists {| pyth_wit_n := m;
          pyth_wit_Ω :=
            {omega : base.(pyth_wit_Ω) & (next omega).(pyth_wit_Ω)};
          pyth_wit_X := X;
          pyth_wit_coord := coord;
          pyth_wit_final := pythFamilyFinal base next;
          pyth_wit_P := pythFamilyP base next;
          pyth_wit_Q := pythFamilyQ base next;
          pyth_wit_dist := Hdist |}.
by split.
Qed.

(* Probability-level chain construction.  The witness packaging keeps the
   dependent latent spaces internal to the probability layer.

   The composed latent space is a dependent sum over the base latent space.
   At a base point [omega] with positive [P]-mass, absolute continuity gives
   positive [Q]-mass too, so the continuation witness can be selected
   diagonally at [(final omega, final omega)].  At a [Q]-only point, select a
   witness using any fixed point in the [P]-support on the left and
   [final omega] on the right; its left branch is multiplied by zero anyway.
   The new coordinates are the old coordinates, the old final coordinate, and
   the continuation coordinates.  The new final value retains both finals. *)
Lemma pythDistWithFinalWitness_bind_pair
    {A B : choiceType} {eps eps' : list R}
    (base : pythDistWithFinalWitness A eps)
    (KL KR : A -> {distr B / R})
    (select : forall aL aR,
      aL \in dinsupp (dmargin base.(pyth_wit_final) base.(pyth_wit_P)) ->
      aR \in dinsupp (dmargin base.(pyth_wit_final) base.(pyth_wit_Q)) ->
      { wit : pythDistWithFinalWitness B eps' |
        pythBindMargins KL KR aL aR wit }) :
  exists wit : pythDistWithFinalWitness (A * B)%type (eps ++ eps'),
    dmargin wit.(pyth_wit_final) wit.(pyth_wit_P) =1
      \dlet_(a <- dmargin base.(pyth_wit_final) base.(pyth_wit_P))
        \dlet_(b <- KL a) dunit (a, b) /\
    dmargin wit.(pyth_wit_final) wit.(pyth_wit_Q) =1
      \dlet_(a <- dmargin base.(pyth_wit_final) base.(pyth_wit_Q))
        \dlet_(b <- KR a) dunit (a, b).
Proof.
have Hac := pyth_wit_absolute_continuous base.
have [omegaL HomegaL] :=
  dweight1_dinsupp_nonempty base.(pyth_wit_P) (pyth_wit_mass1_P base).
have [omegaR HomegaR] :=
  dweight1_dinsupp_nonempty base.(pyth_wit_Q) (pyth_wit_mass1_Q base).
pose next_ok omega (wit : pythDistWithFinalWitness B eps') :=
  (omega \in dinsupp base.(pyth_wit_P) ->
    dmargin wit.(pyth_wit_final) wit.(pyth_wit_P) =1
      KL (base.(pyth_wit_final) omega)) /\
  (omega \in dinsupp base.(pyth_wit_Q) ->
    dmargin wit.(pyth_wit_final) wit.(pyth_wit_Q) =1
      KR (base.(pyth_wit_final) omega)).
have Hnext_exists omega : exists wit, next_ok omega wit.
  case HomegaP: (omega \in dinsupp base.(pyth_wit_P)).
  - have HomegaQ :=
      absolute_continuous_dinsupp base.(pyth_wit_P) base.(pyth_wit_Q)
        omega Hac HomegaP.
    have [wit [HP HQ]] :=
      select (base.(pyth_wit_final) omega) (base.(pyth_wit_final) omega)
        (dinsupp_dmargin_image base.(pyth_wit_final) base.(pyth_wit_P)
          omega HomegaP)
        (dinsupp_dmargin_image base.(pyth_wit_final) base.(pyth_wit_Q)
          omega HomegaQ).
    by exists wit; split.
  - case HomegaQ: (omega \in dinsupp base.(pyth_wit_Q)).
    + have [wit [HP HQ]] :=
        select (base.(pyth_wit_final) omegaL) (base.(pyth_wit_final) omega)
          (dinsupp_dmargin_image base.(pyth_wit_final) base.(pyth_wit_P)
            omegaL HomegaL)
          (dinsupp_dmargin_image base.(pyth_wit_final) base.(pyth_wit_Q)
            omega HomegaQ).
      exists wit; split; last by [].
      by rewrite HomegaP.
    + have [wit [HP HQ]] :=
        select (base.(pyth_wit_final) omegaL) (base.(pyth_wit_final) omegaR)
          (dinsupp_dmargin_image base.(pyth_wit_final) base.(pyth_wit_P)
            omegaL HomegaL)
          (dinsupp_dmargin_image base.(pyth_wit_final) base.(pyth_wit_Q)
            omegaR HomegaR).
      exists wit; split.
      * by rewrite HomegaP.
      * by rewrite HomegaQ.
have [next Hnext] := schoice _ _ next_ok Hnext_exists.
apply: (pythDistWithFinalWitness_bind_family base KL KR next).
- by move=> omega Homega; exact: (Hnext omega).1 Homega.
- by move=> omega Homega; exact: (Hnext omega).2 Homega.
Qed.

Lemma dlet_finish_pairs {A B C : choiceType}
    (mu : {distr A / R}) (K : A -> {distr B / R}) (finish : A -> B -> C) :
  \dlet_(ab <- \dlet_(a <- mu) \dlet_(b <- K a) dunit (a, b))
    dunit (finish ab.1 ab.2) =1
  \dlet_(a <- mu) \dlet_(b <- K a) dunit (finish a b).
Proof.
move=> out.
rewrite __deprecated__dlet_dlet.
apply: eq_in_dlet; last by [].
move=> a _ out'.
rewrite __deprecated__dlet_dlet.
apply: eq_in_dlet; last by [].
move=> b _ out''.
by rewrite dlet_unit.
Qed.

(* Core chain construction.  Keeping the selected witness proof-relevant makes
   the dependent latent-space construction explicit.  The stateful finalizer
   is deliberately absent here: it is handled by postprocessing below. *)
Lemma pythDistWithFinal_bind_pair_selected
    {n : nat} {Ω A B : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i) (final : Ω -> A)
    (P Q : {distr Ω / R}) (eps eps' : list R)
    (KL KR : A -> {distr B / R})
    (select : forall aL aR,
      aL \in dinsupp (dmargin final P) ->
      aR \in dinsupp (dmargin final Q) ->
      { wit : pythDistWithFinalWitness B eps' |
        pythBindMargins KL KR aL aR wit }) :
  pythDistWithFinal coord final P Q eps ->
  exists
  (m : nat)
  (Ωc : choiceType)
  (Xc : 'I_m -> choiceType)
  (coordc : forall i : 'I_m, Ωc -> Xc i)
  (finalc : Ωc -> A * B)
  (Pc Qc : {distr Ωc / R}),
    pythDistWithFinal coordc finalc Pc Qc (eps ++ eps') /\
    dmargin finalc Pc =1
      \dlet_(a <- dmargin final P) \dlet_(b <- KL a) dunit (a, b) /\
    dmargin finalc Qc =1
      \dlet_(a <- dmargin final Q) \dlet_(b <- KR a) dunit (a, b).
Proof.
move=> Hdist.
pose base :=
  {| pyth_wit_n := n;
     pyth_wit_Ω := Ω;
     pyth_wit_X := X;
     pyth_wit_coord := coord;
     pyth_wit_final := final;
     pyth_wit_P := P;
     pyth_wit_Q := Q;
     pyth_wit_dist := Hdist |}.
have [wit [HP HQ]] :=
  pythDistWithFinalWitness_bind_pair base KL KR select.
exists wit.(pyth_wit_n), wit.(pyth_wit_Ω), wit.(pyth_wit_X),
  wit.(pyth_wit_coord), wit.(pyth_wit_final), wit.(pyth_wit_P),
  wit.(pyth_wit_Q).
by split; [exact: wit.(pyth_wit_dist) | split].
Qed.

Lemma pythDistWithFinal_bind_selected
    {n : nat} {Ω A B C : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i) (final : Ω -> A)
    (P Q : {distr Ω / R}) (eps eps' : list R)
    (KL KR : A -> {distr B / R}) (finish : A -> B -> C)
    (select : forall aL aR,
      aL \in dinsupp (dmargin final P) ->
      aR \in dinsupp (dmargin final Q) ->
      { wit : pythDistWithFinalWitness B eps' |
        pythBindMargins KL KR aL aR wit }) :
  pythDistWithFinal coord final P Q eps ->
  exists
  (m : nat)
  (Ωc : choiceType)
  (Xc : 'I_m -> choiceType)
  (coordc : forall i : 'I_m, Ωc -> Xc i)
  (finalc : Ωc -> C)
  (Pc Qc : {distr Ωc / R}),
    pythDistWithFinal coordc finalc Pc Qc (eps ++ eps') /\
    dmargin finalc Pc =1
      \dlet_(a <- dmargin final P) \dlet_(b <- KL a) dunit (finish a b) /\
    dmargin finalc Qc =1
      \dlet_(a <- dmargin final Q) \dlet_(b <- KR a) dunit (finish a b).
Proof.
move=> Hdist.
have [m [Ωc [Xc [coordc [finalc [Pc [Qc [Hdistc [HPc HQc]]]]]]]]] :=
  pythDistWithFinal_bind_pair_selected coord final P Q eps eps' KL KR
    select Hdist.
have [Ω' [X' [coord' [final' [P' [Q' [Hdist' [HP' HQ']]]]]]]] :=
  pythDistWithFinal_postprocess coordc finalc Pc Qc (eps ++ eps')
    (fun ab => dunit (finish ab.1 ab.2)) Hdistc.
exists _, Ω', X', coord', final', P', Q'.
split; first exact: Hdist'.
split.
- move=> out.
  rewrite HP'.
  transitivity
    ((\dlet_(ab <-
       \dlet_(a <- dmargin final P) \dlet_(b <- KL a) dunit (a, b))
       dunit (finish ab.1 ab.2)) out).
  - apply: eq_in_dlet; last exact: HPc.
    by move=> ab _ out'; reflexivity.
  - exact: dlet_finish_pairs _ _ _ out.
- move=> out.
  rewrite HQ'.
  transitivity
    ((\dlet_(ab <-
       \dlet_(a <- dmargin final Q) \dlet_(b <- KR a) dunit (a, b))
       dunit (finish ab.1 ab.2)) out).
  - apply: eq_in_dlet; last exact: HQc.
    by move=> ab _ out'; reflexivity.
  - exact: dlet_finish_pairs _ _ _ out.
Qed.

Lemma pythDistWithFinal_bind
    {n : nat} {Ω A B C : choiceType} {X : 'I_n -> choiceType}
    (coord : forall i : 'I_n, Ω -> X i) (final : Ω -> A)
    (P Q : {distr Ω / R}) (eps eps' : list R)
    (KL KR : A -> {distr B / R}) (finish : A -> B -> C) :
  pythDistWithFinal coord final P Q eps ->
  (forall aL aR,
    aL \in dinsupp (dmargin final P) ->
    aR \in dinsupp (dmargin final Q) ->
    exists wit : pythDistWithFinalWitness B eps',
      pythBindMargins KL KR aL aR wit) ->
  exists
  (m : nat)
  (Ωc : choiceType)
  (Xc : 'I_m -> choiceType)
  (coordc : forall i : 'I_m, Ωc -> Xc i)
  (finalc : Ωc -> C)
  (Pc Qc : {distr Ωc / R}),
    pythDistWithFinal coordc finalc Pc Qc (eps ++ eps') /\
    dmargin finalc Pc =1
      \dlet_(a <- dmargin final P) \dlet_(b <- KL a) dunit (finish a b) /\
    dmargin finalc Qc =1
      \dlet_(a <- dmargin final Q) \dlet_(b <- KR a) dunit (finish a b).
Proof.
move=> Hdist Hwit.
apply: (pythDistWithFinal_bind_selected coord final P Q eps eps'
          KL KR finish _ Hdist).
move=> aL aR HaL HaR.
apply: boolp.constructive_indefinite_description.
exact: Hwit aL aR HaL HaR.
Qed.

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
