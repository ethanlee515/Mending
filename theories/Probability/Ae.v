(* Distribution facts for additive-error couplings. *)

Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals distr.
From mathcomp Require Import realseq realsum exp lra.
Set Warnings "ambiguous-paths,notation-overridden,notation-incompatible-format".

From Mending.LibExtras.MathcompExtras Require Import DistrExtras RealSumExtras.

Import GRing.Theory Num.Theory Order.Theory Order.POrderTheory.

Local Open Scope ring_scope.

Section AdditiveErrorCouplings.

Context {R : realType}.

Definition complete_mass {T : choiceType} (D : {distr T / R}) : option T -> R :=
  fun x =>
    match x with
    | Some y => D y
    | None => 1 - dweight D
    end.

Lemma isdistr_complete_mass {T : choiceType} (D : {distr T / R}) :
  isdistr (complete_mass D).
Proof.
split.
- case=> [x|]; first exact: ge0_mu.
  rewrite subr_ge0 pr_predT.
  exact: le1_mu.
- move=> J uniq_J.
  pose get (x : option T) := x.
  have getK : ocancel get (@Some T) by case.
  have Hsplit :
      \sum_(j <- J) complete_mass D j =
      \sum_(x <- pmap get J) D x +
        (if None \in J then 1 - dweight D else 0).
    elim: J uniq_J => [|j J IH] /=.
      by rewrite !big_nil addr0.
    rewrite in_cons => /andP [Hnotin Huniq].
    rewrite !big_cons.
    case: j Hnotin => [y|] Hnotin /=.
      rewrite IH // big_cons addrA.
      by [].
    rewrite IH //.
    move/negbTE: Hnotin => ->.
    by rewrite addr0 addrC.
  rewrite Hsplit.
  have Hsomes_uniq : uniq (pmap get J).
    exact: (pmap_uniq getK uniq_J).
  have Hsomes_le : \sum_(x <- pmap get J) D x <= dweight D.
    rewrite pr_predT.
    apply: (le_trans _ (gerfinseq_psum Hsomes_uniq (summable_mu D))).
    apply/ler_sum=> x _.
    by rewrite ger0_norm ?ge0_mu.
  have Hmass_le1 : dweight D <= 1 by rewrite pr_predT; exact: le1_mu.
  have Hloss_ge0 : 0 <= 1 - dweight D by lra.
  case: ifP => _; lra.
Qed.

Definition complete {T : choiceType} (D : {distr T / R})
    : {distr (option T) / R} :=
  mkdistr (isdistr_complete_mass D).

Lemma completeE {T : choiceType} (D : {distr T / R}) x :
  complete D x = complete_mass D x.
Proof. by []. Qed.

Lemma complete_dweight {T : choiceType} (D : {distr T / R}) :
  dweight (complete D) = 1.
Proof.
rewrite pr_predT.
rewrite (psum_option_split (complete D)).
- rewrite (eq_psum (F2 := D)); last by move=> x; rewrite completeE.
  rewrite completeE /=.
  rewrite -pr_predT.
  by rewrite addrC subrK.
- move=> x; exact: ge0_mu.
- exact: summable_mu.
Qed.

Definition coupling_with_loss
  {outL_t outR_t : choiceType}
  (d : {distr (outL_t * outR_t) / R})
  (outL : {distr outL_t / R})
  (outR : {distr outR_t / R}) : Prop :=
  dmargin fst d <=1 outL /\ dmargin snd d <=1 outR.

Definition overlap_mass {T : choiceType}
    (P Q : {distr T / R}) : T -> R :=
  fun x => Num.min (P x) (Q x).

Lemma isdistr_overlap_mass {T : choiceType}
    (P Q : {distr T / R}) :
  isdistr (overlap_mass P Q).
Proof.
split.
- move=> x.
  rewrite /overlap_mass.
  apply: minr_ge0; exact: ge0_mu.
- move=> J uniq_J.
  apply: (le_trans _ (le1_mu P)).
  apply: (le_trans _ (gerfinseq_psum uniq_J (summable_mu P))).
  apply/ler_sum=> x _.
  rewrite /overlap_mass.
  have Hmin_ge0 : 0 <= Num.min (P x) (Q x).
    apply: minr_ge0; exact: ge0_mu.
  by rewrite ger0_norm ?minr_lel.
Qed.

Definition overlap_distr {T : choiceType}
    (P Q : {distr T / R}) : {distr T / R} :=
  mkdistr (isdistr_overlap_mass P Q).

Lemma overlap_distrE {T : choiceType}
    (P Q : {distr T / R}) x :
  overlap_distr P Q x = Num.min (P x) (Q x).
Proof. by []. Qed.

Definition residual_mass {T : choiceType}
    (P Q : {distr T / R}) : T -> R :=
  fun x => P x - overlap_distr P Q x.

Lemma residual_mass_ge0 {T : choiceType}
    (P Q : {distr T / R}) x :
  0 <= residual_mass P Q x.
Proof.
rewrite /residual_mass overlap_distrE subr_ge0.
exact: minr_lel.
Qed.

Lemma residual_mass_le {T : choiceType}
    (P Q : {distr T / R}) x :
  residual_mass P Q x <= P x.
Proof.
rewrite /residual_mass.
have Hoverlap_ge0 : 0 <= overlap_distr P Q x.
  rewrite overlap_distrE.
  apply: minr_ge0; exact: ge0_mu.
lra.
Qed.

Lemma isdistr_residual_mass {T : choiceType}
    (P Q : {distr T / R}) :
  isdistr (residual_mass P Q).
Proof.
split.
- move=> x.
  exact: (residual_mass_ge0 P Q x).
- move=> J uniq_J.
  apply: (le_trans _ (le1_mu P)).
  apply: (le_trans _ (gerfinseq_psum uniq_J (summable_mu P))).
  apply: ler_sum=> x _.
  have -> : `|P x| = P x by rewrite ger0_norm ?ge0_mu.
  exact: residual_mass_le.
Qed.

Definition residual_distr {T : choiceType}
    (P Q : {distr T / R}) : {distr T / R} :=
  mkdistr (isdistr_residual_mass P Q).

Lemma residual_distrE {T : choiceType}
    (P Q : {distr T / R}) x :
  residual_distr P Q x = P x - overlap_distr P Q x.
Proof. by []. Qed.

Lemma big_seq_divr {T : choiceType} (J : seq T) (F : T -> R) c :
  \sum_(x <- J) F x / c = (\sum_(x <- J) F x) / c.
Proof.
elim: J => [|j J IH] //=.
  by rewrite !big_nil mul0r.
rewrite !big_cons IH.
lra.
Qed.

Definition normalize_mass {T : choiceType} (D : {distr T / R}) : T -> R :=
  fun x => if dweight D == 0 then 0 else D x / dweight D.

Lemma isdistr_normalize_mass {T : choiceType} (D : {distr T / R}) :
  isdistr (normalize_mass D).
Proof.
split.
- move=> x.
  rewrite /normalize_mass.
  case: ifP=> // HDnz.
  rewrite divr_ge0 //.
  rewrite ltW // lt_def.
  apply/andP; split.
    by apply/eqP; move=> HD0; move/negbT: HDnz; rewrite HD0 eqxx.
  rewrite pr_predT.
  exact: ge0_psum.
- move=> J uniq_J.
  rewrite /normalize_mass.
  case HD0: (dweight D == 0).
    by rewrite big1 ?ler01 // => x _; rewrite HD0.
  rewrite big_seq_divr.
  have HDpos : 0 < dweight D.
    rewrite lt_def.
    apply/andP; split.
      by apply/eqP; move=> HD0'; move: HD0; rewrite HD0' eqxx.
  rewrite pr_predT.
  exact: ge0_psum.
  rewrite ler_pdivrMr ?mul1r //.
  have Hsum_le : \sum_(x <- J) D x <= dweight D.
    rewrite pr_predT.
    apply: (le_trans _ (gerfinseq_psum uniq_J (summable_mu D))).
    apply/ler_sum=> x _.
    by rewrite ger0_norm ?ge0_mu.
  exact: Hsum_le.
Qed.

Definition normalize_distr {T : choiceType}
    (D : {distr T / R}) : {distr T / R} :=
  mkdistr (isdistr_normalize_mass D).

Lemma normalize_distrE {T : choiceType}
    (D : {distr T / R}) x :
  normalize_distr D x = normalize_mass D x.
Proof. by []. Qed.

Lemma dweight_normalize_distr {T : choiceType}
    (D : {distr T / R}) :
  0 < dweight D ->
  dweight (normalize_distr D) = 1.
Proof.
move=> HDpos.
rewrite pr_predT.
rewrite (eq_psum (F2 := fun x => (dweight D)^-1 * D x)); last first.
  move=> x.
  rewrite normalize_distrE /normalize_mass.
  case: ifP=> [/eqP HD0|_]; last by rewrite mulrC.
  move: HDpos; by rewrite HD0 ltxx.
rewrite psumZ; last first.
  rewrite invr_ge0 ltW //.
rewrite pr_predT.
rewrite mulVf //.
by apply/eqP=> HD0; move: HDpos; rewrite pr_predT HD0 ltxx.
Qed.

Lemma overlap_distrC {T : choiceType}
    (P Q : {distr T / R}) :
  overlap_distr P Q =1 overlap_distr Q P.
Proof.
move=> x.
by rewrite !overlap_distrE minC.
Qed.

Lemma dweight_residual_distr {T : choiceType}
    (P Q : {distr T / R}) :
  dweight (residual_distr P Q) =
    dweight P - dweight (overlap_distr P Q).
Proof.
rewrite !pr_predT.
rewrite (eq_psum (F2 := fun x => P x - overlap_distr P Q x)); last first.
  by move=> x; rewrite residual_distrE.
rewrite (@psumB R T P (overlap_distr P Q)).
- by [].
- move=> x.
  apply/andP; split; first exact: ge0_mu.
  rewrite overlap_distrE.
  exact: minr_lel.
- exact: summable_mu.
Qed.

Lemma dweight_residual_distr_eq {T : choiceType}
    (P Q : {distr T / R}) :
  dweight P = dweight Q ->
  dweight (residual_distr P Q) = dweight (residual_distr Q P).
Proof.
move=> HPQ.
rewrite !dweight_residual_distr HPQ.
have Hoverlap :
    dweight (overlap_distr P Q) = dweight (overlap_distr Q P).
  rewrite !pr_predT.
  apply/eq_psum=> x.
  by rewrite !overlap_distrE minC.
by rewrite Hoverlap.
Qed.

Lemma dlet_const_dunit {T U : choiceType}
    (D : {distr T / R}) (x : U) :
  dweight D = 1 ->
  \dlet_(y <- D) dunit x =1 dunit x.
Proof.
move=> HD z.
rewrite dletE.
rewrite psumZr; last exact: ge0_mu.
by rewrite -pr_predT HD mul1r.
Qed.

Lemma dlet_const_kernelE {T U : choiceType}
    (D : {distr T / R}) (E : {distr U / R}) z :
  (\dlet_(x <- D) E) z = dweight D * E z.
Proof.
rewrite dletE.
rewrite psumZr; last exact: ge0_mu.
by rewrite pr_predT.
Qed.

Definition distr_plus_mass {T : choiceType}
    (D E : {distr T / R}) : T -> R :=
  fun x => D x + E x.

Lemma isdistr_plus_mass {T : choiceType}
    (D E : {distr T / R}) :
  dweight D + dweight E <= 1 ->
  isdistr (distr_plus_mass D E).
Proof.
move=> Hweight.
split.
- move=> x.
  rewrite /distr_plus_mass.
  exact: addr_ge0; exact: ge0_mu.
- move=> J uniq_J.
  rewrite /distr_plus_mass big_split /=.
  apply: (le_trans _ Hweight).
  apply: lerD.
  - rewrite pr_predT.
    apply: (le_trans _ (gerfinseq_psum uniq_J (summable_mu D))).
    apply/ler_sum=> x _.
    by rewrite ger0_norm ?ge0_mu.
  - rewrite pr_predT.
    apply: (le_trans _ (gerfinseq_psum uniq_J (summable_mu E))).
    apply/ler_sum=> x _.
    by rewrite ger0_norm ?ge0_mu.
Qed.

Definition distr_plus {T : choiceType}
    (D E : {distr T / R})
    (Hweight : dweight D + dweight E <= 1) : {distr T / R} :=
  mkdistr (isdistr_plus_mass D E Hweight).

Lemma distr_plusE {T : choiceType}
    (D E : {distr T / R})
    (Hweight : dweight D + dweight E <= 1) x :
  distr_plus D E Hweight x = D x + E x.
Proof. by []. Qed.

Lemma dmargin_distr_plus {T U : choiceType}
    (D E : {distr T / R})
    (Hweight : dweight D + dweight E <= 1)
    (f : T -> U) :
  dmargin f (distr_plus D E Hweight) =1
    distr_plus (dmargin f D) (dmargin f E)
      (ltac:(rewrite !dmargin_dweight; exact: Hweight)).
Proof.
move=> y.
rewrite dmargin_psumE distr_plusE.
rewrite (eq_psum
  (F2 := fun x => (f x == y)%:R * D x + (f x == y)%:R * E x)).
  rewrite psumD.
  - by rewrite !dmargin_psumE.
  - move=> x; apply: mulr_ge0; first exact: ler0n.
    exact: ge0_mu.
  - move=> x; apply: mulr_ge0; first exact: ler0n.
    exact: ge0_mu.
  - exact: summable_pr.
  - exact: summable_pr.
move=> x.
by rewrite mulrDr.
Qed.

Definition residual_product {T : choiceType}
    (P Q : {distr T / R}) : {distr (T * T) / R} :=
  \dlet_(x <- residual_distr P Q)
    \dlet_(y <- normalize_distr (residual_distr Q P))
      dunit (x, y).

Lemma residual_product_margin_l {T : choiceType}
    (P Q : {distr T / R}) :
  0 < dweight (residual_distr Q P) ->
  dmargin fst (residual_product P Q) =1 residual_distr P Q.
Proof.
move=> HQpos z.
rewrite /residual_product __deprecated__dmargin_dlet.
transitivity ((\dlet_(x <- residual_distr P Q) dunit x) z).
  apply: eq_in_dlet=> // x _ z'.
  rewrite dmarginE __deprecated__dlet_dlet.
  transitivity ((\dlet_(y <- normalize_distr (residual_distr Q P)) dunit x) z').
    apply: eq_in_dlet=> // y _ w.
    by rewrite dlet_unit.
  exact: dlet_const_dunit (dweight_normalize_distr _ HQpos) z'.
by rewrite dlet_dunit_id.
Qed.

Lemma residual_product_margin_r {T : choiceType}
    (P Q : {distr T / R}) :
  dweight (residual_distr P Q) = dweight (residual_distr Q P) ->
  0 < dweight (residual_distr Q P) ->
  dmargin snd (residual_product P Q) =1 residual_distr Q P.
Proof.
move=> Hweights HQpos z.
rewrite /residual_product __deprecated__dmargin_dlet.
transitivity
  ((\dlet_(x <- residual_distr P Q)
      normalize_distr (residual_distr Q P)) z).
  apply: eq_in_dlet=> // x _ z'.
  rewrite dmarginE __deprecated__dlet_dlet.
  transitivity
    ((\dlet_(y <- normalize_distr (residual_distr Q P)) dunit y) z').
    apply: eq_in_dlet=> // y _ w.
    by rewrite dlet_unit.
  by rewrite dlet_dunit_id.
rewrite dlet_const_kernelE normalize_distrE /normalize_mass.
case: ifP=> [/eqP HQ0|_].
  move: HQpos; by rewrite HQ0 ltxx.
rewrite Hweights.
rewrite mulrC.
rewrite divfK //.
by apply/eqP=> HQ0; move: HQpos; rewrite HQ0 ltxx.
Qed.

Definition diagonal_overlap {T : choiceType}
    (P Q : {distr T / R}) : {distr (T * T) / R} :=
  \dlet_(x <- overlap_distr P Q) dunit (x, x).

Lemma diagonal_overlap_margin_l {T : choiceType}
    (P Q : {distr T / R}) :
  dmargin fst (diagonal_overlap P Q) =1 overlap_distr P Q.
Proof.
move=> x.
rewrite /diagonal_overlap dmarginE __deprecated__dlet_dlet.
transitivity ((\dlet_(y <- overlap_distr P Q) dunit y) x).
  apply: eq_in_dlet=> // y _ z.
  by rewrite dlet_unit.
by rewrite dlet_dunit_id.
Qed.

Lemma diagonal_overlap_margin_r {T : choiceType}
    (P Q : {distr T / R}) :
  dmargin snd (diagonal_overlap P Q) =1 overlap_distr P Q.
Proof.
move=> x.
rewrite /diagonal_overlap dmarginE __deprecated__dlet_dlet.
transitivity ((\dlet_(y <- overlap_distr P Q) dunit y) x).
  apply: eq_in_dlet=> // y _ z.
  by rewrite dlet_unit.
by rewrite dlet_dunit_id.
Qed.

Lemma diagonal_overlap_coupling_with_loss {T : choiceType}
    (P Q : {distr T / R}) :
  coupling_with_loss (diagonal_overlap P Q) P Q.
Proof.
split=> x.
- rewrite diagonal_overlap_margin_l overlap_distrE.
  exact: minr_lel.
- rewrite diagonal_overlap_margin_r overlap_distrE.
  exact: minr_ler.
Qed.

Lemma dweight_diagonal_overlap {T : choiceType}
    (P Q : {distr T / R}) :
  dweight (diagonal_overlap P Q) = dweight (overlap_distr P Q).
Proof.
rewrite -(dmargin_dweight fst (diagonal_overlap P Q)) !pr_predT.
rewrite (eq_psum (F2 := fun x => overlap_distr P Q x)); first by [].
move=> x.
exact: (diagonal_overlap_margin_l P Q x).
Qed.

Lemma dweight_residual_product {T : choiceType}
    (P Q : {distr T / R}) :
  0 < dweight (residual_distr Q P) ->
  dweight (residual_product P Q) = dweight (residual_distr P Q).
Proof.
move=> HQpos.
rewrite -(dmargin_dweight fst (residual_product P Q)) !pr_predT.
rewrite (eq_psum (F2 := fun x => residual_distr P Q x)); first by [].
move=> x.
exact: (residual_product_margin_l P Q HQpos x).
Qed.

Lemma dweight_overlap_residual {T : choiceType}
    (P Q : {distr T / R}) :
  dweight (overlap_distr P Q) + dweight (residual_distr P Q) =
  dweight P.
Proof.
rewrite dweight_residual_distr.
lra.
Qed.

Lemma maximal_coupling_positive_weight {T : choiceType}
    (P Q : {distr T / R}) :
  dweight P = 1 ->
  0 < dweight (residual_distr Q P) ->
  dweight (diagonal_overlap P Q) + dweight (residual_product P Q) <= 1.
Proof.
move=> HP HQpos.
rewrite dweight_diagonal_overlap dweight_residual_product //.
rewrite dweight_overlap_residual HP.
exact: lexx.
Qed.

Lemma maximal_coupling_positive_margin_l {T : choiceType}
    (P Q : {distr T / R})
    (Hweight : dweight (diagonal_overlap P Q) +
               dweight (residual_product P Q) <= 1) :
  0 < dweight (residual_distr Q P) ->
  dmargin fst
    (distr_plus (diagonal_overlap P Q) (residual_product P Q) Hweight)
  =1 P.
Proof.
move=> HQpos x.
rewrite dmargin_distr_plus distr_plusE.
rewrite diagonal_overlap_margin_l residual_product_margin_l //.
rewrite residual_distrE !overlap_distrE.
lra.
Qed.

Lemma maximal_coupling_positive_margin_r {T : choiceType}
    (P Q : {distr T / R})
    (Hweight : dweight (diagonal_overlap P Q) +
               dweight (residual_product P Q) <= 1) :
  dweight P = dweight Q ->
  0 < dweight (residual_distr Q P) ->
  dmargin snd
    (distr_plus (diagonal_overlap P Q) (residual_product P Q) Hweight)
  =1 Q.
Proof.
move=> HPQ HQpos x.
have Hres_weight := dweight_residual_distr_eq P Q HPQ.
rewrite dmargin_distr_plus distr_plusE.
rewrite diagonal_overlap_margin_r.
rewrite (residual_product_margin_r P Q Hres_weight HQpos).
rewrite residual_distrE.
rewrite (overlap_distrC P Q x).
rewrite !overlap_distrE.
lra.
Qed.

Lemma dweight0_distr0 {T : choiceType} (D : {distr T / R}) :
  dweight D = 0 ->
  D =1 dnull.
Proof.
move=> HD0 x.
rewrite dnullE.
apply: (eq0_psum (summable_mu D)).
by rewrite -pr_predT.
Qed.

Lemma diagonal_overlap_zero_residual_margin_l {T : choiceType}
    (P Q : {distr T / R}) :
  dweight (residual_distr P Q) = 0 ->
  dmargin fst (diagonal_overlap P Q) =1 P.
Proof.
move=> Hres0 x.
have Hzero := dweight0_distr0 (residual_distr P Q) Hres0 x.
move: Hzero.
rewrite dnullE residual_distrE.
rewrite diagonal_overlap_margin_l.
lra.
Qed.

Lemma diagonal_overlap_zero_residual_margin_r {T : choiceType}
    (P Q : {distr T / R}) :
  dweight (residual_distr Q P) = 0 ->
  dmargin snd (diagonal_overlap P Q) =1 Q.
Proof.
move=> Hres0 x.
have Hzero := dweight0_distr0 (residual_distr Q P) Hres0 x.
move: Hzero.
rewrite dnullE residual_distrE.
rewrite diagonal_overlap_margin_r.
rewrite (overlap_distrC P Q x).
lra.
Qed.

Lemma abs_diff_residual_sum {T : choiceType}
    (P Q : {distr T / R}) x :
  `|P x - Q x| = residual_distr P Q x + residual_distr Q P x.
Proof.
rewrite !residual_distrE !overlap_distrE !minr_absE.
rewrite -opprB normrN.
lra.
Qed.

Lemma summable_abs_diff {T : choiceType}
    (P Q : {distr T / R}) :
  summable (fun x => `|P x - Q x|).
Proof.
apply: le_summable.
- move=> x.
  apply/andP; split; first exact: normr_ge0.
  have Hnorm := ler_normB (P x) (Q x).
  have HPge : 0 <= P x := ge0_mu P x.
  have HQge : 0 <= Q x := ge0_mu Q x.
  rewrite (ger0_norm HPge) (ger0_norm HQge) in Hnorm.
  exact: Hnorm.
- apply: summableD; exact: summable_mu.
Qed.

Lemma total_variation_residual {T : choiceType}
    (P Q : {distr T / R}) :
  dweight P = dweight Q ->
  total_variation P Q = dweight (residual_distr P Q).
Proof.
move=> HPQ.
rewrite /total_variation.
rewrite -(@psum_sum R T (fun x => `|P x - Q x|)).
- rewrite (eq_psum
    (F2 := fun x => residual_distr P Q x + residual_distr Q P x)).
    rewrite psumD.
    + rewrite -!pr_predT.
      have Hres := dweight_residual_distr_eq P Q HPQ.
      rewrite Hres.
      lra.
    + move=> x; exact: ge0_mu.
    + move=> x; exact: ge0_mu.
    + exact: summable_mu.
    + exact: summable_mu.
  move=> x.
  exact: abs_diff_residual_sum.
- move=> x; exact: normr_ge0.
Qed.

Lemma total_variation_overlap {T : choiceType}
    (P Q : {distr T / R}) :
  dweight P = 1 ->
  dweight Q = 1 ->
  total_variation P Q = 1 - dweight (overlap_distr P Q).
Proof.
move=> HP HQ.
rewrite total_variation_residual; last by rewrite HP HQ.
rewrite dweight_residual_distr HP.
by [].
Qed.

Lemma overlap_weight_ge_of_total_variation_le {T : choiceType}
    (P Q : {distr T / R}) ε :
  dweight P = 1 ->
  dweight Q = 1 ->
  total_variation P Q <= ε ->
  dweight (overlap_distr P Q) >= 1 - ε.
Proof.
move=> HP HQ Htv.
rewrite (total_variation_overlap P Q HP HQ) in Htv.
lra.
Qed.

Lemma pr_pointwise_le {A : choiceType}
    (D E : {distr A / R}) (p : pred A) :
  D <=1 E ->
  \P_[D] p <= \P_[E] p.
Proof.
move=> HDE.
rewrite /pr.
apply: le_psum; last exact: summable_pr.
move=> x.
apply/andP; split.
  rewrite mulr_ge0 ?ler0n ?ge0_mu //.
case Hpx: (p x).
  by rewrite !mul1r HDE.
by rewrite !mul0r.
Qed.

Lemma diagonal_overlap_eq_pr {T : choiceType}
    (P Q : {distr T / R}) :
  \P_[diagonal_overlap P Q] (fun xy => xy.1 == xy.2) =
  dweight (overlap_distr P Q).
Proof.
rewrite /diagonal_overlap __deprecated__pr_dlet.
rewrite (expectation_ext (overlap_distr P Q)
  (fun x => \P_[dunit (x, x)] (fun xy => xy.1 == xy.2))
  (fun _ => 1)); last first.
  move=> x.
  by rewrite pr_dunit /= eqxx.
by rewrite exp_cst mulr1.
Qed.

Lemma maximal_coupling_total_variation
    {T : choiceType} (P Q : {distr T / R}) ε :
  dweight P = 1 ->
  dweight Q = 1 ->
  total_variation P Q <= ε ->
  exists d : {distr (T * T) / R},
    dmargin fst d =1 P /\
    dmargin snd d =1 Q /\
    \P_[d] (fun xy => xy.1 == xy.2) >= 1 - ε.
Proof.
move=> HP HQ Htv.
have Hoverlap_ge := overlap_weight_ge_of_total_variation_le P Q ε HP HQ Htv.
case HQres0: (dweight (residual_distr Q P) == 0).
- exists (diagonal_overlap P Q).
  move/eqP: HQres0=> HQres0.
  have Hres_weight := dweight_residual_distr_eq P Q.
  have HPQ : dweight P = dweight Q by rewrite HP HQ.
  have HPres0 : dweight (residual_distr P Q) = 0.
    by rewrite (Hres_weight HPQ) HQres0.
  split; first exact: diagonal_overlap_zero_residual_margin_l.
  split; first exact: diagonal_overlap_zero_residual_margin_r.
  rewrite diagonal_overlap_eq_pr.
  exact: Hoverlap_ge.
- have HQpos : 0 < dweight (residual_distr Q P).
    rewrite lt_def.
    apply/andP; split.
      by apply/eqP; move=> H0; move: HQres0; rewrite H0 eqxx.
    rewrite pr_predT.
    exact: ge0_psum.
  pose Hweight := maximal_coupling_positive_weight P Q HP HQpos.
  exists (distr_plus (diagonal_overlap P Q) (residual_product P Q) Hweight).
  split.
    exact: maximal_coupling_positive_margin_l.
  split.
    apply: maximal_coupling_positive_margin_r=> //.
    by rewrite HP HQ.
  have Hdiag_le :
      \P_[diagonal_overlap P Q] (fun xy => xy.1 == xy.2) <=
      \P_[distr_plus (diagonal_overlap P Q) (residual_product P Q) Hweight]
        (fun xy => xy.1 == xy.2).
    apply: pr_pointwise_le=> xy.
    rewrite distr_plusE.
    have Hres_ge : 0 <= residual_product P Q xy := ge0_mu _ _.
    lra.
  apply: (le_trans _ Hdiag_le).
  rewrite diagonal_overlap_eq_pr.
  exact: Hoverlap_ge.
Qed.

Lemma pr_le_dweight {A : choiceType} (D : {distr A / R}) (p : pred A) :
  \P_[D] p <= dweight D.
Proof.
have H : \P_[D] p <= \P_[D] predT.
  apply: subset_pr => x _.
  by [].
exact: H.
Qed.

Lemma dweight_le_pointwise {A : choiceType} (D E : {distr A / R}) :
  D <=1 E ->
  dweight D <= dweight E.
Proof.
move=> HDE.
rewrite !pr_predT.
apply: le_psum; last exact: summable_mu.
move=> x.
apply/andP; split.
- exact: ge0_mu.
- exact: HDE x.
Qed.

Lemma coupling_with_loss_left_mass1
  {outL_t outR_t : choiceType}
  (d : {distr (outL_t * outR_t) / R})
  (outL : {distr outL_t / R})
  (outR : {distr outR_t / R})
  (post : pred (outL_t * outR_t)) :
  coupling_with_loss d outL outR ->
  \P_[ d ] post >= 1 ->
  dweight outL = 1.
Proof.
move=> [HdL _] Hpost.
have Hprob_le : \P_[ d ] post <= dweight d.
  exact: pr_le_dweight.
have Hd_ge1 : 1 <= dweight d := le_trans Hpost Hprob_le.
have Hd_le1 : dweight d <= 1 by rewrite pr_predT; exact: le1_mu.
have Hd_weight : dweight d = 1.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - exact: Hd_le1.
  - exact: Hd_ge1.
have Hout_ge1 : 1 <= dweight outL.
  have := dweight_le_pointwise (dmargin fst d) outL HdL.
  by rewrite dmargin_dweight Hd_weight.
have Hout_le1 : dweight outL <= 1 by rewrite pr_predT; exact: le1_mu.
apply/eqP; rewrite eq_le; apply/andP; split.
- exact: Hout_le1.
- exact: Hout_ge1.
Qed.

Lemma coupling_with_loss_eq_output_heaps
  {out_t mem_t : choiceType}
  (d : {distr ((out_t * mem_t) * (out_t * mem_t)) / R})
  (outL outR : {distr (out_t * mem_t) / R})
  (post : pred (out_t * mem_t)) :
  coupling_with_loss d outL outR ->
  \P_[ d ] (fun outs =>
    let '((yL, memL'), (yR, memR')) := outs in
    (yL == yR) && (memL' == memR') && post (yL, memL')) >= 1 ->
  outL =1 outR.
Admitted.

Lemma coupling_with_loss_eq_output_heap_post_support
  {out_t mem_t : choiceType}
  (d : {distr ((out_t * mem_t) * (out_t * mem_t)) / R})
  (outL outR : {distr (out_t * mem_t) / R})
  (post : pred (out_t * mem_t)) :
  coupling_with_loss d outL outR ->
  \P_[ d ] (fun outs =>
    let '((yL, memL'), (yR, memR')) := outs in
    (yL == yR) && (memL' == memR') && post (yL, memL')) >= 1 ->
  (forall y, y \in dinsupp outL -> post y) /\
  (forall y, y \in dinsupp outR -> post y).
Admitted.

Definition lift_loss_post
  {outL_t outR_t : choiceType}
  (post : pred (outL_t * outR_t)) : pred (option outL_t * option outR_t) :=
  fun outs =>
    match outs with
    | (Some outL, Some outR) => post (outL, outR)
    | _ => false
    end.

Lemma coupling_with_loss_total_variation_dmargin_match
  {outL_t outR_t A : choiceType}
  (fL : outL_t -> A) (fR : outR_t -> A)
  (d : {distr (outL_t * outR_t) / R})
  (outL : {distr outL_t / R})
  (outR : {distr outR_t / R})
  (ε : R) :
  coupling_with_loss d outL outR ->
  \P_[ d ] (fun xy => fL xy.1 == fR xy.2) >= 1 - ε ->
  total_variation (dmargin fL outL) (dmargin fR outR) <= ε.
Admitted.

Lemma coupling_with_loss_bind
  {midL_t midR_t outL_t outR_t : choiceType}
  (ML : {distr midL_t / R})
  (MR : {distr midR_t / R})
  (KL : midL_t -> {distr outL_t / R})
  (KR : midR_t -> {distr outR_t / R})
  (mid : pred (midL_t * midR_t))
  (post : pred (outL_t * outR_t))
  (ε ε' : R)
  (d0 : {distr (midL_t * midR_t) / R}) :
  0 <= ε ->
  0 <= ε' ->
  coupling_with_loss d0 ML MR ->
  \P_[ d0 ] mid >= 1 - ε ->
  (forall xL xR,
    mid (xL, xR) ->
    exists d1,
      coupling_with_loss d1 (KL xL) (KR xR) /\
      \P_[ d1 ] post >= 1 - ε') ->
  exists d,
    coupling_with_loss d
      (\dlet_(xL <- ML) KL xL)
      (\dlet_(xR <- MR) KR xR) /\
    \P_[ d ] post >= 1 - (ε + ε').
Admitted.

End AdditiveErrorCouplings.
