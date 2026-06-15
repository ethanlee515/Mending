Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra all_reals distr.
From mathcomp Require Import realseq realsum exp.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From Mending.LibExtras.MathcompExtras Require Import DistrExtras.

Import GRing.Theory Num.Theory Order.Theory.

Local Open Scope ring_scope.

Section KL_Core.

Context {R: realType}.

Definition δ_KL {T : choiceType} (P Q : {distr T / R}) : R :=
  \E_[P] (fun x => ln (P x / Q x)).

Definition absolute_continuous {T : choiceType} (P Q : {distr T / R}) : Prop :=
  forall x, Q x = 0 -> P x = 0.

Lemma mass1_kl_left {T : choiceType} (P Q : {distr T / R}) :
  dweight P = 1 ->
  δ_KL P Q =
    \E_[P] (fun x => ln (P x / Q x)).
Proof. by []. Qed.

Lemma kl_ext {T : choiceType} (P P' Q Q' : {distr T / R}) :
  P =1 P' ->
  Q =1 Q' ->
  δ_KL P Q = δ_KL P' Q'.
Proof.
move=> HP HQ.
rewrite /δ_KL.
rewrite (expectation_distr_ext P P' _ HP).
apply: expectation_ext=> x.
by rewrite -HP -HQ.
Qed.

Lemma kl_left_dnull {T : choiceType} (P Q : {distr T / R}) :
  P =1 dnull ->
  δ_KL P Q = 0.
Proof.
move=> HP.
rewrite /δ_KL.
rewrite (expectation_distr_ext P dnull _ HP).
exact: expectation_dnull.
Qed.

Lemma kl_self {T : choiceType} (P : {distr T / R}) :
  δ_KL P P = 0.
Proof.
rewrite /δ_KL /esp.
rewrite (eq_sum (F2 := fun _ : T => 0)).
  exact: sum0.
move=> x.
case Px0: (P x == 0).
  by rewrite (eqP Px0) mulr0.
have HPx : P x != 0 by rewrite Px0.
have -> : P x / P x = 1 by rewrite divff ?unitfE ?HPx.
by rewrite ln1 mul0r.
Qed.

Lemma absolute_continuous_positive {T : choiceType}
    (P Q : {distr T / R}) (x : T) :
  absolute_continuous P Q ->
  0 < P x -> 0 < Q x.
Proof.
move=> Hac HPx.
rewrite lt_def ge0_mu andbT.
apply/negP=> /eqP HQx0.
have HPx0 := Hac x HQx0.
by rewrite HPx0 ltxx in HPx.
Qed.

Lemma kl_dmargin_injective {T U : choiceType}
    (f : T -> U) (P Q : {distr T / R}) :
  injective f ->
  δ_KL (dmargin f P) (dmargin f Q) = δ_KL P Q.
Admitted.

Lemma kl_dmargin_data_processing {T U : choiceType}
    (f : T -> U) (P Q : {distr T / R}) :
  absolute_continuous P Q ->
  δ_KL (dmargin f P) (dmargin f Q) <= δ_KL P Q.
Admitted.

Lemma dlet_joint_same_kernelE {T U : choiceType}
    (P : {distr T / R}) (K : T -> {distr U / R}) (x : T) (y : U) :
  (\dlet_(x' <- P) \dlet_(y' <- K x') dunit (x', y')) (x, y) =
  P x * K x y.
Proof.
rewrite dletE.
rewrite (psum_finseq (r := [:: x])).
- rewrite big_seq1.
  rewrite dletE.
  rewrite (psum_finseq (r := [:: y])).
  + by rewrite big_seq1 dunit1E eqxx mulr1 !ger0_norm
      ?mulr_ge0 ?ge0_mu.
  + by [].
  + move=> y'.
    rewrite !inE dunit1E xpair_eqE eqxx /=.
    case Hy : (y' == y); first by rewrite (eqP Hy).
    by rewrite mulr0 eqxx.
- by [].
move=> x'.
rewrite !inE.
case Hx : (x' == x)=> //.
move=> Hnz.
have Hinner0 :
    (\dlet_(y' <- K x') dunit (x', y')) (x, y) = 0.
  apply: dlet_eq0=> y' _.
  by rewrite xpair_eqE Hx.
by move: Hnz; rewrite Hinner0 mulr0 eqxx.
Qed.

Lemma kl_joint_same_kernel {T U : choiceType}
    (P Q : {distr T / R}) (K : T -> {distr U / R}) :
  (forall x, dweight (K x) = 1) ->
  δ_KL
    (\dlet_(x <- P) \dlet_(y <- K x) dunit (x, y))
    (\dlet_(x <- Q) \dlet_(y <- K x) dunit (x, y)) =
  δ_KL P Q.
Admitted.

Lemma dlet_joint_same_kernel_absolute_continuous {T U : choiceType}
    (P Q : {distr T / R}) (K : T -> {distr U / R}) :
  absolute_continuous P Q ->
  absolute_continuous
    (\dlet_(x <- P) \dlet_(y <- K x) dunit (x, y))
    (\dlet_(x <- Q) \dlet_(y <- K x) dunit (x, y)).
Proof.
move=> Hac [x y].
rewrite !dlet_joint_same_kernelE.
move=> HQxy0.
case Kxy0: (K x y == 0).
  by rewrite (eqP Kxy0) mulr0.
have HQx0 : Q x = 0.
  apply/eqP.
  move/eqP: HQxy0.
  by rewrite mulf_eq0 Kxy0 orbF.
by rewrite (Hac x HQx0) mul0r.
Qed.

Lemma kl_dlet_data_processing {T U : choiceType}
    (P Q : {distr T / R}) (K : T -> {distr U / R}) :
  absolute_continuous P Q ->
  (forall x, dweight (K x) = 1) ->
  δ_KL (\dlet_(x <- P) K x) (\dlet_(x <- Q) K x) <= δ_KL P Q.
Proof.
move=> Hac HK.
pose JP : {distr (T * U) / R} :=
  \dlet_(x <- P) \dlet_(y <- K x) dunit (x, y).
pose JQ : {distr (T * U) / R} :=
  \dlet_(x <- Q) \dlet_(y <- K x) dunit (x, y).
have HPsnd :
    dmargin (fun xy : T * U => xy.2) JP =1 \dlet_(x <- P) K x.
  move=> y.
  rewrite /JP __deprecated__dmargin_dlet.
  apply: eq_in_dlet=> // x _ z.
  rewrite __deprecated__dmargin_dlet.
  rewrite -(dlet_dunit_id (K x) z).
  apply: eq_in_dlet=> // u _ z'.
  by rewrite dmargin_dunit.
have HQsnd :
    dmargin (fun xy : T * U => xy.2) JQ =1 \dlet_(x <- Q) K x.
  move=> y.
  rewrite /JQ __deprecated__dmargin_dlet.
  apply: eq_in_dlet=> // x _ z.
  rewrite __deprecated__dmargin_dlet.
  rewrite -(dlet_dunit_id (K x) z).
  apply: eq_in_dlet=> // u _ z'.
  by rewrite dmargin_dunit.
rewrite -(kl_ext _ _ _ _ HPsnd HQsnd).
apply: (le_trans (kl_dmargin_data_processing
  (fun xy : T * U => xy.2) JP JQ _)).
by apply: dlet_joint_same_kernel_absolute_continuous.
by rewrite /JP /JQ kl_joint_same_kernel.
Qed.

Lemma expectation_le_const_on_support {T : choiceType}
    (P : {distr T / R}) (f : T -> R) (c : R) :
  dweight P = 1 ->
  0 <= c ->
  (forall x, 0 <= f x) ->
  (forall x, 0 < P x -> f x <= c) ->
  \E_[P] f <= c.
Proof.
move=> HP Hc Hf Hbound.
rewrite /esp.
have Hpoint x : 0 <= f x * P x <= c * P x.
  apply/andP; split.
  - by rewrite mulr_ge0 ?Hf ?ge0_mu.
  - case Px0: (P x == 0).
    + by rewrite (eqP Px0) !mulr0.
    + apply: ler_wpM2r; first exact: ge0_mu.
      apply: Hbound.
      by rewrite lt_def Px0 ge0_mu.
have smG : summable (fun x : T => c * P x).
  change (summable (c \*o P)).
  exact: summableZ.
have smF : summable (fun x : T => f x * P x).
  apply: (le_summable (F2 := fun x : T => c * P x)); first exact: Hpoint.
  exact: smG.
apply: (le_trans (le_sum smF smG _)).
  by move=> x; have /andP[_ hx] := Hpoint x.
change (\E_[P] (fun=> c) <= c).
by rewrite exp_cst HP mul1r.
Qed.

Lemma kl_nonnegative {T : choiceType} (P Q : {distr T / R}) :
  absolute_continuous P Q ->
  dweight P = 1 ->
  0 <= δ_KL P Q.
Admitted.

End KL_Core.
