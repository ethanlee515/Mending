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

Lemma complete_distr_ext {T : choiceType} (D E : {distr T / R}) :
  D =1 E ->
  complete D =1 complete E.
Proof.
move=> HDE [x|].
- by rewrite !completeE /= HDE.
rewrite !completeE /=.
have Hdweight : dweight D = dweight E.
  rewrite !pr_predT.
  apply: eq_psum=> x.
  exact: HDE.
by rewrite Hdweight.
Qed.

Lemma complete_dnull {T : choiceType} :
  complete (dnull : {distr T / R}) =1 dunit None.
Proof.
case=> [x|].
- by rewrite completeE /= dnullE dunit1E.
- rewrite completeE /= dunit1E eqxx.
  rewrite (_ : dweight (dnull : {distr T / R}) = 0); first by rewrite subr0.
  rewrite pr_predT.
  rewrite (eq_psum (F2 := fun _ : T => 0)); first exact: psum0.
  by move=> x; rewrite dnullE.
Qed.

Lemma dmargin_dnull {T U : choiceType} (f : T -> U) :
  dmargin f (dnull : {distr T / R}) =1 dnull.
Proof.
move=> y.
rewrite dmarginE dletE dnullE.
rewrite (eq_psum (F2 := fun _ : T => 0)); first exact: psum0.
by move=> x; rewrite dnullE mul0r.
Qed.

Lemma complete_dmargin_dnull {T U : choiceType} (f : T -> U) :
  complete (dmargin f (dnull : {distr T / R})) =1 dunit None.
Proof.
move=> z.
rewrite (complete_distr_ext
  (dmargin f (dnull : {distr T / R})) dnull (dmargin_dnull f) z).
exact: complete_dnull.
Qed.

Lemma dflip_dweight (p : R) :
  dweight (dflip p : {distr bool / R}) = 1.
Proof.
rewrite pr_predT psum_fin.
rewrite /index_enum !unlock /=.
rewrite !dflip1E /mflip /=.
rewrite ger0_norm ?cp01_clamp //.
rewrite ger0_norm ?subr_ge0 ?cp01_clamp //.
by rewrite addr0 addrC subrK.
Qed.

Lemma dmargin_omap_complete
    {T U : choiceType} (f : T -> U) (D : {distr T / R}) :
  dmargin (omap f) (complete D) =1 complete (dmargin f D).
Proof.
case=> [y|].
- rewrite completeE /= !dmargin_psumE.
  rewrite (psum_option_some_zero
    (fun x : option T => (omap f x == Some y)%:R * complete D x)).
    apply/eq_psum=> x.
    by rewrite completeE /=.
  by rewrite mul0r.
rewrite completeE /= dmargin_psumE.
rewrite (psum_finseq (r := [:: None])).
- rewrite big_seq1 /= mul1r.
  rewrite ger0_norm; last by rewrite subr_ge0 pr_predT; exact: le1_mu.
  by rewrite dmargin_dweight.
- by [].
move=> x.
rewrite !inE.
case: x=> [x|] /=; last by [].
by rewrite mul0r eqxx.
Qed.

Definition complete_bind_kernel
    {T U : choiceType} (K : T -> {distr U / R})
    (x : option T) : {distr (option U) / R} :=
  match x with
  | Some y => complete (K y)
  | None => dunit None
  end.

Lemma dweight_dlet {T U : choiceType}
    (D : {distr T / R}) (K : T -> {distr U / R}) :
  dweight (\dlet_(x <- D) K x) =
  psum (fun x => D x * dweight (K x)).
Proof.
exact: dweight_dlet_sum.
Qed.

Lemma complete_bind_some
    {T U : choiceType} (D : {distr T / R})
    (K : T -> {distr U / R}) z :
  (\dlet_(x <- complete D) complete_bind_kernel K x) (Some z) =
  complete (\dlet_(x <- D) K x) (Some z).
Proof.
rewrite completeE /=.
rewrite !dletE.
rewrite (psum_option_some_zero
  (fun x : option T =>
    complete D x * complete_bind_kernel K x (Some z))).
  apply: eq_psum=> x.
  by rewrite /complete_bind_kernel completeE /=.
by rewrite /complete_bind_kernel dunit1E /= mulr0.
Qed.

Lemma complete_bind_none
    {T U : choiceType} (D : {distr T / R})
    (K : T -> {distr U / R}) :
  (\dlet_(x <- complete D) complete_bind_kernel K x) None =
  complete (\dlet_(x <- D) K x) None.
Proof.
rewrite completeE /= dletE.
rewrite (psum_option_split (fun x : option T =>
  complete D x * complete_bind_kernel K x None)).
- rewrite /complete_bind_kernel dunit1E eqxx mulr1 completeE /=.
  rewrite (eq_psum
    (F2 := fun x : T => D x - D x * dweight (K x))).
    rewrite (@psum_sub_bounded_nonneg R T D
      (fun x => D x * dweight (K x))).
    + rewrite -pr_predT -dweight_dlet.
      lra.
    + move=> x.
      apply/andP; split.
      * rewrite mulr_ge0 ?ge0_mu //.
        rewrite pr_predT.
        exact: ge0_psum.
      rewrite -[leRHS]mulr1.
      apply: ler_wpM2l; first exact: ge0_mu.
      rewrite pr_predT.
      exact: le1_mu.
    + exact: summable_mu.
  move=> x.
  by rewrite mulrBr mulr1.
- case=> [x|].
  + rewrite /complete_bind_kernel completeE /=.
    apply: mulr_ge0; first exact: ge0_mu.
    rewrite subr_ge0 pr_predT.
    exact: le1_mu.
  + rewrite /complete_bind_kernel dunit1E eqxx mulr1 completeE /=.
    rewrite subr_ge0 pr_predT.
    exact: le1_mu.
- apply: summable_mlet.
Qed.

Lemma complete_bind
    {T U : choiceType} (D : {distr T / R})
    (K : T -> {distr U / R}) :
  \dlet_(x <- complete D) complete_bind_kernel K x
  =1 complete (\dlet_(x <- D) K x).
Proof.
case=> [z|].
- exact: complete_bind_some.
- exact: complete_bind_none.
Qed.

Lemma total_variation_eq_le0
    {T : choiceType} (P Q : {distr T / R}) :
  P =1 Q -> total_variation P Q <= 0.
Proof.
move=> HPQ.
rewrite /total_variation.
rewrite (_ : sum (fun y => `|P y - Q y|) = 0).
  by rewrite mulr0 lexx.
rewrite -(@sum0 R T).
apply/eq_sum=> y.
by rewrite HPQ subrr normr0.
Qed.

Lemma total_variation_refl_le0
    {T : choiceType} (P : {distr T / R}) :
  total_variation P P <= 0.
Proof.
apply: total_variation_eq_le0.
by [].
Qed.

Lemma total_variation_ext
    {T : choiceType} (P P' Q Q' : {distr T / R}) :
  P =1 P' -> Q =1 Q' ->
  total_variation P Q = total_variation P' Q'.
Proof.
move=> HP HQ.
rewrite /total_variation.
congr (_ * _).
apply/eq_sum=> y.
by rewrite HP HQ.
Qed.

Lemma total_variation_point_bound2
    {T : choiceType} (P Q : {distr T / R}) (x : T) :
  `|P x - Q x| <= 2 * total_variation P Q.
Proof.
rewrite /total_variation.
have Hsummable : summable (fun y => P y - Q y).
  apply: summableD; first exact: summable_mu.
  by apply: summableN; exact: summable_mu.
have Hpoint :=
  gerfinseq_psum (S := fun y => P y - Q y) (r := [:: x])
    _ Hsummable.
rewrite big_seq1 in Hpoint.
rewrite -(psum_abs (fun y => P y - Q y)) in Hpoint.
have Hpsum_sum :
  psum (fun y => `|P y - Q y|) =
  sum (fun y => `|P y - Q y|).
  by apply: psum_sum=> y; exact: normr_ge0.
rewrite Hpsum_sum in Hpoint.
apply: (@le_trans _ _ (sum (fun y => `|P y - Q y|))).
  exact: Hpoint.
lra.
Qed.

Lemma dmargin_dunit_fst_pair {T U : choiceType} (x : T) (y : U) :
  dmargin fst (dunit (x, y) : {distr (T * U) / R}) =1 dunit x.
Proof.
move=> z.
rewrite dmarginE dlet_unit.
by [].
Qed.

Lemma dmargin_dunit_snd_pair {T U : choiceType} (x : T) (y : U) :
  dmargin snd (dunit (x, y) : {distr (T * U) / R}) =1 dunit y.
Proof.
move=> z.
rewrite dmarginE dlet_unit.
by [].
Qed.

Definition shared_complete_sample_coupling
    {T U V : choiceType} (D : {distr T / R})
    (f : T -> U) (g : T -> V) :
    {distr (option U * option V) / R} :=
  \dlet_(x <- complete D)
    match x with
    | Some y => dunit (Some (f y), Some (g y))
    | None => dunit (None, None)
    end.

Lemma shared_complete_sample_coupling_margin_l
    {T U V : choiceType} (D : {distr T / R})
    (f : T -> U) (g : T -> V) :
  dmargin fst (shared_complete_sample_coupling D f g) =1
    complete (dmargin f D).
Proof.
move=> z.
rewrite /shared_complete_sample_coupling.
rewrite dmargin_dlet_partition.
transitivity ((\dlet_(x <- complete D) dunit (omap f x)) z).
- apply: eq_in_dlet=> // x _ z'.
  case: x=> [x|].
  + exact: dmargin_dunit_fst_pair.
  + exact: dmargin_dunit_fst_pair.
- by rewrite -dmarginE dmargin_omap_complete.
Qed.

Lemma shared_complete_sample_coupling_margin_r
    {T U V : choiceType} (D : {distr T / R})
    (f : T -> U) (g : T -> V) :
  dmargin snd (shared_complete_sample_coupling D f g) =1
    complete (dmargin g D).
Proof.
move=> z.
rewrite /shared_complete_sample_coupling.
rewrite dmargin_dlet_partition.
transitivity ((\dlet_(x <- complete D) dunit (omap g x)) z).
- apply: eq_in_dlet=> // x _ z'.
  case: x=> [x|].
  + exact: dmargin_dunit_snd_pair.
  + exact: dmargin_dunit_snd_pair.
- by rewrite -dmarginE dmargin_omap_complete.
Qed.

Lemma shared_complete_sample_coupling_margins
    {T U V : choiceType} (D : {distr T / R})
    (f : T -> U) (g : T -> V) :
  dmargin fst (shared_complete_sample_coupling D f g) =1
    complete (dmargin f D) /\
  dmargin snd (shared_complete_sample_coupling D f g) =1
    complete (dmargin g D).
Proof.
split.
- exact: shared_complete_sample_coupling_margin_l.
- exact: shared_complete_sample_coupling_margin_r.
Qed.

Lemma shared_complete_sample_coupling_dweight
    {T U V : choiceType} (D : {distr T / R})
    (f : T -> U) (g : T -> V) :
  dweight (shared_complete_sample_coupling D f g) = 1.
Proof.
rewrite /shared_complete_sample_coupling dweight_dlet.
transitivity (@psum R _ (fun x : option T => complete D x * 1)).
- apply/eq_psum=> x.
  congr (_ * _).
  case: x=> [x|]; exact: dunit_dweight.
- transitivity (@psum R _ (complete D)).
    apply/eq_psum=> x.
    by rewrite mulr1.
  by rewrite -pr_predT complete_dweight.
Qed.

Definition product_coupling
    {T U : choiceType} (P : {distr T / R}) (Q : {distr U / R}) :
    {distr (T * U) / R} :=
  \dlet_(x <- P) \dlet_(y <- Q) dunit (x, y).

Lemma product_coupling_margin_l
    {T U : choiceType} (P : {distr T / R}) (Q : {distr U / R}) :
  dweight Q = 1 ->
  dmargin fst (product_coupling P Q) =1 P.
Proof.
move=> HQ x0.
rewrite /product_coupling dmargin_dlet_partition.
transitivity ((\dlet_(x <- P) dunit x) x0).
- apply: eq_in_dlet=> // x _ z.
  rewrite dmargin_dlet_partition.
  transitivity ((\dlet_(y <- Q) dunit x) z).
  + apply: eq_in_dlet=> // y _ z'.
    exact: dmargin_dunit_fst_pair.
  + rewrite dletE.
    rewrite psumZr; last exact: ge0_mu.
    by rewrite -pr_predT HQ mul1r.
- by rewrite dlet_dunit_id.
Qed.

Lemma product_coupling_margin_r
    {T U : choiceType} (P : {distr T / R}) (Q : {distr U / R}) :
  dweight P = 1 ->
  dmargin snd (product_coupling P Q) =1 Q.
Proof.
move=> HP y0.
rewrite /product_coupling dmargin_dlet_partition.
transitivity ((\dlet_(x <- P) Q) y0).
- apply: eq_in_dlet=> // x _ z.
  rewrite dmargin_dlet_partition.
  transitivity ((\dlet_(y <- Q) dunit y) z).
  + apply: eq_in_dlet=> // y _ z'.
    exact: dmargin_dunit_snd_pair.
  + by rewrite dlet_dunit_id.
- rewrite dletE.
  rewrite psumZr; last exact: ge0_mu.
  by rewrite -pr_predT HP mul1r.
Qed.

Lemma product_coupling_margins
    {T U : choiceType} (P : {distr T / R}) (Q : {distr U / R}) :
  dweight P = 1 ->
  dweight Q = 1 ->
  dmargin fst (product_coupling P Q) =1 P /\
  dmargin snd (product_coupling P Q) =1 Q.
Proof.
move=> HP HQ.
split.
- exact: product_coupling_margin_l.
- exact: product_coupling_margin_r.
Qed.

Definition completed_fallback_coupling
    {T U : choiceType} (P : {distr T / R}) (Q : {distr U / R}) :
    {distr (option T * option U) / R} :=
  product_coupling (complete P) (complete Q).

Lemma completed_fallback_coupling_margins
    {T U : choiceType} (P : {distr T / R}) (Q : {distr U / R}) :
  dmargin fst (completed_fallback_coupling P Q) =1 complete P /\
  dmargin snd (completed_fallback_coupling P Q) =1 complete Q.
Proof.
apply: product_coupling_margins;
  exact: complete_dweight.
Qed.

Definition complete_bind_fallback_coupling
    {midL_t midR_t outL_t outR_t : choiceType}
    (KL : midL_t -> {distr outL_t / R})
    (KR : midR_t -> {distr outR_t / R})
    (xy : option midL_t * option midR_t) :
    {distr (option outL_t * option outR_t) / R} :=
  product_coupling
    (complete_bind_kernel KL xy.1)
    (complete_bind_kernel KR xy.2).

Lemma complete_bind_kernel_dweight
    {T U : choiceType} (K : T -> {distr U / R}) x :
  dweight (complete_bind_kernel K x) = 1.
Proof.
case: x=> [x|].
- exact: complete_dweight.
- exact: dunit_dweight.
Qed.

Lemma complete_bind_fallback_coupling_margins
    {midL_t midR_t outL_t outR_t : choiceType}
    (KL : midL_t -> {distr outL_t / R})
    (KR : midR_t -> {distr outR_t / R})
    (xy : option midL_t * option midR_t) :
  dmargin fst (complete_bind_fallback_coupling KL KR xy) =1
    complete_bind_kernel KL xy.1 /\
  dmargin snd (complete_bind_fallback_coupling KL KR xy) =1
    complete_bind_kernel KR xy.2.
Proof.
apply: product_coupling_margins;
  exact: complete_bind_kernel_dweight.
Qed.

Lemma pr_dlet_lower_bound_good
    {T U : choiceType} (D : {distr T / R}) (K : T -> {distr U / R})
    (good : pred T) (post : pred U) ε ε' :
  0 <= ε ->
  0 <= ε' ->
  \P_[D] good >= 1 - ε ->
  (forall x, good x -> \P_[K x] post >= 1 - ε') ->
  \P_[\dlet_(x <- D) K x] post >= 1 - (ε + ε').
Proof.
move=> Heps Heps' Hgood HK.
case: (leP ε' 1)=> Heps'le1.
- have Hc : 0 <= 1 - ε' by lra.
  rewrite __deprecated__pr_dlet.
  have Hpoint :
      (fun x => (good x)%:R * (1 - ε')) <=1
      (fun x => \P_[K x] post).
    move=> x.
    case Hx: (good x).
    + by rewrite /= mul1r; exact: HK.
    + by rewrite /= mul0r; exact: ge0_pr.
  have Hle :
      \E_[D] (fun x => (good x)%:R * (1 - ε')) <=
      \E_[D] (fun x => \P_[K x] post).
    apply: le_exp.
    + apply: bounded_has_exp.
      exists `|1 - ε'|=> x.
      case: (good x); rewrite /= ?mul1r ?mul0r ?normr0 //.
    + apply: bounded_has_exp.
      exists 1=> x.
      rewrite ger0_norm; first exact: le1_pr.
      exact: ge0_pr.
    + exact: Hpoint.
  apply: (le_trans _ Hle).
  rewrite expectation_scale_right -pr_exp.
  have Hmul : (1 - ε) * (1 - ε') <= \P_[D] good * (1 - ε').
    apply: ler_wpM2r; first exact: Hc.
    exact: Hgood.
  have Htarget : 1 - (ε + ε') <= (1 - ε) * (1 - ε') by nra.
  exact: (le_trans Htarget Hmul).
- have Htarget : 1 - (ε + ε') <= 0 by lra.
  have Hnonneg : 0 <= \P_[\dlet_(x <- D) K x] post.
    exact: ge0_pr.
  exact: (le_trans Htarget Hnonneg).
Qed.

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
rewrite (@psum_sub_bounded_nonneg R T P (overlap_distr P Q)).
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
rewrite /residual_product dmargin_dlet_partition.
transitivity ((\dlet_(x <- residual_distr P Q) dunit x) z).
  apply: eq_in_dlet=> // x _ z'.
  rewrite dmargin_dlet_partition.
  transitivity ((\dlet_(y <- normalize_distr (residual_distr Q P)) dunit x) z').
    apply: eq_in_dlet=> // y _ w.
    exact: dmargin_dunit_fst_pair.
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
rewrite /residual_product dmargin_dlet_partition.
transitivity
  ((\dlet_(x <- residual_distr P Q)
      normalize_distr (residual_distr Q P)) z).
  apply: eq_in_dlet=> // x _ z'.
  rewrite dmargin_dlet_partition.
  transitivity
    ((\dlet_(y <- normalize_distr (residual_distr Q P)) dunit y) z').
    apply: eq_in_dlet=> // y _ w.
    exact: dmargin_dunit_snd_pair.
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
rewrite /diagonal_overlap dmargin_dlet_partition.
transitivity ((\dlet_(y <- overlap_distr P Q) dunit y) x).
  apply: eq_in_dlet=> // y _ z.
  exact: dmargin_dunit_fst_pair.
by rewrite dlet_dunit_id.
Qed.

Lemma diagonal_overlap_margin_r {T : choiceType}
    (P Q : {distr T / R}) :
  dmargin snd (diagonal_overlap P Q) =1 overlap_distr P Q.
Proof.
move=> x.
rewrite /diagonal_overlap dmargin_dlet_partition.
transitivity ((\dlet_(y <- overlap_distr P Q) dunit y) x).
  apply: eq_in_dlet=> // y _ z.
  exact: dmargin_dunit_snd_pair.
by rewrite dlet_dunit_id.
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

Lemma distr_point_le_dweight {T : choiceType}
    (D : {distr T / R}) (x : T) :
  D x <= dweight D.
Proof.
rewrite pr_predT.
have H := gerfinseq_psum
  (S := D) (r := [:: x]) (erefl true) (summable_mu D).
by rewrite big_seq1 ger0_norm ?ge0_mu in H.
Qed.

Lemma total_variation_point_bound
    {T : choiceType} (P Q : {distr T / R}) (x : T) :
  dweight P = dweight Q ->
  `|P x - Q x| <= total_variation P Q.
Proof.
move=> HPQ.
rewrite (total_variation_residual P Q HPQ).
case: (lerP (P x) (Q x))=> Hle.
- have Hpoint := distr_point_le_dweight (residual_distr Q P) x.
  rewrite residual_distrE overlap_distrE (min_idPr Hle) in Hpoint.
  have Hweights := dweight_residual_distr_eq P Q HPQ.
  rewrite -Hweights in Hpoint.
  lra.
- have Hge : Q x <= P x := ltW Hle.
  have Hpoint := distr_point_le_dweight (residual_distr P Q) x.
  rewrite residual_distrE overlap_distrE (min_idPr Hge) in Hpoint.
  lra.
Qed.

Lemma total_variation_complete_point_bound
    {T : choiceType} (P Q : {distr T / R}) (x : T) :
  `|P x - Q x| <=
    total_variation (complete P) (complete Q).
Proof.
have H := total_variation_point_bound (complete P) (complete Q) (Some x).
rewrite !completeE /= in H.
apply: H.
by rewrite !complete_dweight.
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

Lemma pr_eq1_of_support {A : choiceType}
    (D : {distr A / R}) (p : pred A) :
  dweight D = 1 ->
  (forall x, x \in dinsupp D -> p x) ->
  \P_[D] p = 1.
Proof.
move=> HD Hsupp.
rewrite -HD pr_predT /pr.
apply/eq_psum=> x.
case Hpx: (p x); first by rewrite mul1r.
rewrite mul0r.
apply/esym/dinsuppPn.
apply/negP=> Hx.
by move: (Hsupp x Hx); rewrite Hpx.
Qed.

Lemma pr_eq_dweight_of_support {A : choiceType}
    (D : {distr A / R}) (p : pred A) :
  (forall x, x \in dinsupp D -> p x) ->
  \P_[D] p = dweight D.
Proof.
move=> Hsupp.
rewrite pr_predT /pr.
apply/eq_psum=> x.
case Hpx: (p x); first by rewrite mul1r.
rewrite mul0r.
apply/esym/dinsuppPn.
apply/negP=> Hx.
by move: (Hsupp x Hx); rewrite Hpx.
Qed.

Lemma support_of_pr_ge1 {A : choiceType}
    (D : {distr A / R}) (p : pred A) :
  dweight D = 1 ->
  \P_[D] p >= 1 ->
  forall x, x \in dinsupp D -> p x.
Proof.
move=> HD Hpr x Hx.
case Hpx: (p x); first by [].
exfalso.
have HDx_pos : 0 < D x.
  move: Hx.
  rewrite in_dinsupp=> Hx.
  by rewrite lt_def ge0_mu andbT Hx.
have Hcomp_pos : 0 < \P_[D] (predC p).
  apply: (lt_le_trans HDx_pos).
  rewrite [D x]pr_pred1.
  apply: subset_pr=> y Hy.
  move/eqP: Hy=> Hy.
  subst y.
  by rewrite !inE Hpx.
have Hcomp_nonpos : \P_[D] (predC p) <= 0.
  rewrite pr_predC HD.
  lra.
lra.
Qed.

Lemma shared_complete_sample_coupling_pr_eq1
    {T U V : choiceType} (D : {distr T / R})
    (f : T -> U) (g : T -> V)
    (post : pred (option U * option V)) :
  (forall x, x \in dinsupp D -> post (Some (f x), Some (g x))) ->
  post (None, None) ->
  \P_[shared_complete_sample_coupling D f g] post = 1.
Proof.
move=> Hsome Hnone.
apply: pr_eq1_of_support.
- exact: shared_complete_sample_coupling_dweight.
- move=> xy Hxy.
  rewrite /shared_complete_sample_coupling in Hxy.
  have [ox Hox Hinner] := @dinsupp_dlet R _ _ _ _ _ Hxy.
  case: ox Hox Hinner=> [x|] Hox Hinner.
  + have -> : xy = (Some (f x), Some (g x)).
      exact: in_dunit Hinner.
    apply: Hsome.
    move: Hox.
    by rewrite in_dinsupp completeE /= -in_dinsupp.
  + have -> : xy = (None, None).
      exact: in_dunit Hinner.
    exact: Hnone.
Qed.

Lemma shared_complete_sample_coupling_pr_ge1
    {T U V : choiceType} (D : {distr T / R})
    (f : T -> U) (g : T -> V)
    (post : pred (option U * option V)) :
  (forall x, x \in dinsupp D -> post (Some (f x), Some (g x))) ->
  post (None, None) ->
  \P_[shared_complete_sample_coupling D f g] post >= 1.
Proof.
move=> Hsome Hnone.
by rewrite shared_complete_sample_coupling_pr_eq1.
Qed.

Lemma diagonal_overlap_eq_pr {T : choiceType}
    (P Q : {distr T / R}) :
  \P_[diagonal_overlap P Q] (fun xy => xy.1 == xy.2) =
  dweight (overlap_distr P Q).
Proof.
rewrite (pr_eq_dweight_of_support (diagonal_overlap P Q)); last first.
  move=> [x y] Hxy.
  move: Hxy.
  rewrite /diagonal_overlap=> /dinsupp_dlet [z _ Hz].
  move: Hz.
  rewrite dunit1E pnatr_eq0 eqb0 negbK=> /eqP Hz.
  by move: Hz=> [-> ->]; rewrite eqxx.
exact: dweight_diagonal_overlap.
Qed.

Lemma exact_coupling_eq_pr_le_overlap
    {T : choiceType} (d : {distr (T * T) / R}) (P Q : {distr T / R}) :
  dmargin fst d =1 P ->
  dmargin snd d =1 Q ->
  \P_[d] (fun xy => xy.1 == xy.2) <= dweight (overlap_distr P Q).
Proof.
move=> HdL HdR.
have Hdiag_row x :
    psum (fun y : T => (x == y)%:R * d (x, y)) = d (x, x).
  rewrite (psum_finseq (r := [:: x])).
  - by rewrite big_seq1 eqxx mul1r ger0_norm ?ge0_mu.
  - by [].
  move=> y.
  rewrite !inE.
  case Hxy: (x == y); last by rewrite mul0r eqxx.
  by move/eqP: Hxy=> ->; rewrite eqxx.
have Hpoint_left (a : T) : d (a, a) <= P a.
  have Huniq_a : uniq [:: (a, a)] by [].
  have H :=
    gerfinseq_psum
      (S := fun xy : T * T => (xy.1 == a)%:R * d xy)
      (r := [:: (a, a)]) Huniq_a
      (summable_pr (fun xy : T * T => xy.1 == a) d).
  rewrite big_seq1 eqxx mul1r in H.
  rewrite ger0_norm in H; last exact: ge0_mu.
  rewrite -dmargin_psumE HdL in H.
  exact: H.
have Hpoint_right (b : T) : d (b, b) <= Q b.
  have Huniq_b : uniq [:: (b, b)] by [].
  have H :=
    gerfinseq_psum
      (S := fun xy : T * T => (xy.2 == b)%:R * d xy)
      (r := [:: (b, b)]) Huniq_b
      (summable_pr (fun xy : T * T => xy.2 == b) d).
  rewrite big_seq1 eqxx mul1r in H.
  rewrite ger0_norm in H; last exact: ge0_mu.
  rewrite -dmargin_psumE HdR in H.
  exact: H.
have Hpr_diag :
    \P_[d] (fun xy : T * T => xy.1 == xy.2) =
      psum (fun xy : T * T => (xy.1 == xy.2)%:R * d xy).
  by rewrite /pr.
rewrite Hpr_diag.
rewrite (@psum_pair R T T
  (fun xy : T * T => (xy.1 == xy.2)%:R * d xy)
  (summable_pr (fun xy : T * T => xy.1 == xy.2) d)).
rewrite pr_predT.
apply: le_psum; last exact: summable_mu.
move=> x.
apply/andP; split.
  exact: ge0_psum.
rewrite Hdiag_row overlap_distrE /overlap_mass.
by rewrite le_min Hpoint_left Hpoint_right.
Qed.

Lemma exact_coupling_eq_pr_total_variation
    {T : choiceType} (d : {distr (T * T) / R}) (P Q : {distr T / R}) ε :
  dweight P = 1 ->
  dweight Q = 1 ->
  dmargin fst d =1 P ->
  dmargin snd d =1 Q ->
  \P_[d] (fun xy => xy.1 == xy.2) >= 1 - ε ->
  total_variation P Q <= ε.
Proof.
move=> HP HQ HdL HdR Heq.
have Hoverlap := exact_coupling_eq_pr_le_overlap d P Q HdL HdR.
rewrite (total_variation_overlap P Q HP HQ).
lra.
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

Definition tagged_by {T U : choiceType} (f : T -> U)
    (P : {distr T / R}) : {distr (U * T) / R} :=
  dmargin (fun x => (f x, x)) P.

Lemma tagged_byE {T U : choiceType} (f : T -> U)
    (P : {distr T / R}) (u : U) (x : T) :
  tagged_by f P (u, x) = if f x == u then P x else 0.
Proof.
rewrite /tagged_by dmargin_psumE.
case Hfx: (f x == u).
- rewrite (psum_finseq (r := [:: x])).
  + rewrite big_seq1 (eqP Hfx) eqxx /= mul1r.
    by rewrite ger0_norm ?ge0_mu.
  + by [].
  move=> y.
  rewrite !inE.
  case Hy: (y == x).
    by rewrite (eqP Hy) (eqP Hfx) eqxx.
  case Hpair: ((f y, y) == (u, x)); last by rewrite mul0r eqxx.
  move/eqP: Hpair=> [_ Hyx].
  by move: Hy; rewrite Hyx eqxx.
- rewrite (eq_psum (F2 := fun _ : T => 0)); first exact: psum0.
  move=> y.
  case Hpair: ((f y, y) == (u, x)); last by rewrite mul0r.
  move/eqP: Hpair=> [Hfy Hyx].
  move: Hfx.
  by rewrite -Hfy Hyx eqxx.
Qed.

Lemma tagged_by_margin_l {T U : choiceType} (f : T -> U)
    (P : {distr T / R}) :
  dmargin fst (tagged_by f P) =1 dmargin f P.
Proof.
move=> u.
rewrite /tagged_by dmarginE __deprecated__dlet_dlet.
transitivity ((\dlet_(x <- P) dunit (f x)) u).
- apply: eq_in_dlet=> // x _ z.
  by rewrite dlet_unit.
- by rewrite dmarginE.
Qed.

Definition conditional_fiber {T U : choiceType} (f : T -> U)
    (P : {distr T / R}) (u : U) : {distr T / R} :=
  conditional_second (tagged_by f P) u.

Lemma conditional_fiber_outside {T U : choiceType} (f : T -> U)
    (P : {distr T / R}) (u : U) (x : T) :
  f x != u ->
  conditional_fiber f P u x = 0.
Proof.
move=> Hfx.
rewrite /conditional_fiber conditional_secondE.
case: ifP=> // _.
by rewrite tagged_byE (negbTE Hfx) mul0r.
Qed.

Lemma conditional_fiber_dinsupp {T U : choiceType} (f : T -> U)
    (P : {distr T / R}) (u : U) (x : T) :
  x \in dinsupp (conditional_fiber f P u) ->
  f x = u.
Proof.
move=> Hx.
apply/eqP.
case Hfx: (f x == u); first by [].
have Hneq : f x != u by rewrite Hfx.
move: Hx.
by rewrite in_dinsupp (conditional_fiber_outside f P u x Hneq) eqxx.
Qed.

Lemma conditional_fiber_factorization {T U : choiceType} (f : T -> U)
    (P : {distr T / R}) (x : T) :
  P x = dmargin f P (f x) * conditional_fiber f P (f x) x.
Proof.
rewrite /conditional_fiber.
have H :=
  conditional_second_factorization (tagged_by f P) (f x) x.
move: H.
rewrite tagged_byE eqxx tagged_by_margin_l.
by [].
Qed.

Lemma conditional_fiber_recompose {T U : choiceType} (f : T -> U)
    (P : {distr T / R}) :
  \dlet_(u <- dmargin f P) conditional_fiber f P u =1 P.
Proof.
move=> x.
rewrite dletE.
rewrite (psum_finseq (r := [:: f x])).
- rewrite big_seq1.
  rewrite ger0_norm; last by apply: mulr_ge0; exact: ge0_mu.
  rewrite [RHS](@conditional_fiber_factorization T U f P x).
  by [].
- by [].
- move=> u Hnz.
  case Hfu: (f x == u).
    move/eqP: Hfu=> <-.
    by rewrite inE eqxx.
  have Hneq : f x != u by rewrite Hfu.
  move: Hnz.
  by rewrite inE /= (conditional_fiber_outside f P u x Hneq)
    mulr0 eqxx.
Qed.

Lemma dweight_tagged_by {T U : choiceType} (f : T -> U)
    (P : {distr T / R}) :
  dweight (tagged_by f P) = dweight P.
Proof.
by rewrite /tagged_by dmargin_dweight.
Qed.

Lemma conditional_fiber_mass1_on_support {T U : choiceType} (f : T -> U)
    (P : {distr T / R}) (u : U) :
  dweight P = 1 ->
  0 < dmargin f P u ->
  dweight (conditional_fiber f P u) = 1.
Proof.
move=> HP Hu.
rewrite /conditional_fiber.
apply: conditional_second_mass1_on_support.
- by rewrite dweight_tagged_by.
- by rewrite tagged_by_margin_l.
Qed.

Definition lift_projected_inner
    {T U : choiceType} (f : T -> U)
    (P Q : {distr T / R}) (uv : U * U) :
    {distr (T * T) / R} :=
  \dlet_(x <- conditional_fiber f P uv.1)
    \dlet_(y <- conditional_fiber f Q uv.2)
      dunit (x, y).

Definition projected_pair_event
    {T U : choiceType} (f : T -> U) : pred (T * T) :=
  fun xy => f xy.1 == f xy.2.

Definition lift_projected_inner_event_prob
    {T U : choiceType} (f : T -> U)
    (P Q : {distr T / R}) (uv : U * U) : R :=
  \P_[lift_projected_inner f P Q uv] (projected_pair_event f).

Definition lift_projected_coupling
    {T U : choiceType} (f : T -> U)
    (P Q : {distr T / R}) (d : {distr (U * U) / R}) :
    {distr (T * T) / R} :=
  \dlet_(uv <- d) lift_projected_inner f P Q uv.

Lemma dmargin_dunit_pair_fst {T U : choiceType} (x : T) (y : U) :
  dmargin fst (dunit (x, y) : {distr (T * U) / R}) =1 dunit x.
Proof.
move=> z.
rewrite dmarginE dlet_unit.
by [].
Qed.

Lemma dmargin_dunit_pair_snd {T U : choiceType} (x : T) (y : U) :
  dmargin snd (dunit (x, y) : {distr (T * U) / R}) =1 dunit y.
Proof.
move=> z.
rewrite dmarginE dlet_unit.
by [].
Qed.

Lemma lift_projected_coupling_margin_l
    {T U : choiceType} (f : T -> U)
    (P Q : {distr T / R}) (d : {distr (U * U) / R}) :
  dmargin fst d =1 dmargin f P ->
  dmargin snd d =1 dmargin f Q ->
  dweight Q = 1 ->
  dmargin fst (lift_projected_coupling f P Q d) =1 P.
Proof.
move=> HdL HdR HQ x0.
rewrite /lift_projected_coupling.
rewrite __deprecated__dmargin_dlet.
transitivity ((\dlet_(uv <- d) conditional_fiber f P uv.1) x0).
- apply: eq_in_dlet=> // uv Huv z.
  rewrite __deprecated__dmargin_dlet.
  transitivity ((\dlet_(x <- conditional_fiber f P uv.1) dunit x) z).
  + apply: eq_in_dlet=> // x _ z'.
    rewrite __deprecated__dmargin_dlet.
    transitivity ((\dlet_(y <- conditional_fiber f Q uv.2) dunit x) z').
    * apply: eq_in_dlet=> // y _ w.
      exact: dmargin_dunit_pair_fst.
    * rewrite dlet_const_kernelE.
      have Huv2 : uv.2 \in dinsupp (dmargin snd d).
        exact: dmargin_dinsupp_image Huv.
      have Hqv_pos : 0 < dmargin f Q uv.2.
        rewrite lt_def.
        apply/andP; split.
        + by move: Huv2; rewrite in_dinsupp HdR.
        + exact: ge0_mu.
      rewrite (conditional_fiber_mass1_on_support f Q uv.2 HQ Hqv_pos).
      by rewrite mul1r.
  + by rewrite dlet_dunit_id.
- transitivity ((\dlet_(u <- dmargin fst d) conditional_fiber f P u) x0).
  + rewrite __deprecated__dlet_dmargin.
    by [].
  + transitivity ((\dlet_(u <- dmargin f P) conditional_fiber f P u) x0).
    * rewrite !dletE.
      apply/eq_psum=> u.
      by rewrite HdL.
    * exact: conditional_fiber_recompose.
Qed.

Lemma lift_projected_coupling_margin_r
    {T U : choiceType} (f : T -> U)
    (P Q : {distr T / R}) (d : {distr (U * U) / R}) :
  dmargin fst d =1 dmargin f P ->
  dmargin snd d =1 dmargin f Q ->
  dweight P = 1 ->
  dmargin snd (lift_projected_coupling f P Q d) =1 Q.
Proof.
move=> HdL HdR HP y0.
rewrite /lift_projected_coupling.
rewrite __deprecated__dmargin_dlet.
transitivity ((\dlet_(uv <- d) conditional_fiber f Q uv.2) y0).
- apply: eq_in_dlet=> // uv Huv z.
  rewrite __deprecated__dmargin_dlet.
  transitivity ((\dlet_(x <- conditional_fiber f P uv.1)
      conditional_fiber f Q uv.2) z).
  + apply: eq_in_dlet=> // x _ z'.
    rewrite __deprecated__dmargin_dlet.
    transitivity ((\dlet_(y <- conditional_fiber f Q uv.2) dunit y) z').
    * apply: eq_in_dlet=> // y _ w.
      exact: dmargin_dunit_pair_snd.
    * by rewrite dlet_dunit_id.
  + rewrite dlet_const_kernelE.
    have Huv1 : uv.1 \in dinsupp (dmargin fst d).
      exact: dmargin_dinsupp_image Huv.
    have Hpv_pos : 0 < dmargin f P uv.1.
      rewrite lt_def.
      apply/andP; split.
      * by move: Huv1; rewrite in_dinsupp HdL.
      * exact: ge0_mu.
    rewrite (conditional_fiber_mass1_on_support f P uv.1 HP Hpv_pos).
    by rewrite mul1r.
- transitivity ((\dlet_(u <- dmargin snd d) conditional_fiber f Q u) y0).
  + rewrite __deprecated__dlet_dmargin.
    by [].
  + transitivity ((\dlet_(u <- dmargin f Q) conditional_fiber f Q u) y0).
    * rewrite !dletE.
      apply/eq_psum=> u.
      by rewrite HdR.
    * exact: conditional_fiber_recompose.
Qed.

Lemma lift_projected_coupling_inner_event_ge
    {T U : choiceType} (f : T -> U)
    (P Q : {distr T / R}) (d : {distr (U * U) / R}) :
  dmargin fst d =1 dmargin f P ->
  dmargin snd d =1 dmargin f Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  forall uv,
  uv \in dinsupp d ->
  (uv.1 == uv.2)%:R <=
  \P_[\dlet_(x <- conditional_fiber f P uv.1)
        \dlet_(y <- conditional_fiber f Q uv.2)
          dunit (x, y)]
    (fun xy => f xy.1 == f xy.2).
Proof.
move=> HdL HdR HP HQ uv Huv.
case Huv_eq: (uv.1 == uv.2).
- have Huv1 : uv.1 \in dinsupp (dmargin fst d).
    exact: dmargin_dinsupp_image Huv.
  have Huv2 : uv.2 \in dinsupp (dmargin snd d).
    exact: dmargin_dinsupp_image Huv.
  have Hpu_pos : 0 < dmargin f P uv.1.
    rewrite lt_def.
    apply/andP; split.
    + by move: Huv1; rewrite in_dinsupp HdL.
    + exact: ge0_mu.
  have Hqu_pos : 0 < dmargin f Q uv.2.
    rewrite lt_def.
    apply/andP; split.
    + by move: Huv2; rewrite in_dinsupp HdR.
    + exact: ge0_mu.
  set Pu := conditional_fiber f P uv.1.
  set Qu := conditional_fiber f Q uv.2.
  set inner := \dlet_(x <- Pu) \dlet_(y <- Qu) dunit (x, y).
  have HPu : dweight Pu = 1.
    rewrite /Pu.
    exact: (conditional_fiber_mass1_on_support f P uv.1 HP Hpu_pos).
  have HQu : dweight Qu = 1.
    rewrite /Qu.
    exact: (conditional_fiber_mass1_on_support f Q uv.2 HQ Hqu_pos).
  have Hinner_weight : dweight inner = 1.
    rewrite /inner dweight_dlet_sum.
    transitivity (psum (fun x => Pu x * 1)).
    + apply/eq_psum=> x.
      congr (_ * _).
      rewrite dweight_dlet_sum.
      transitivity (psum (fun y => Qu y * 1)).
      * apply/eq_psum=> y.
        by rewrite dunit_dweight.
      * transitivity (psum Qu).
          apply/eq_psum=> y.
          by rewrite mulr1.
        by rewrite -pr_predT HQu.
    + transitivity (psum Pu).
        apply/eq_psum=> x.
        by rewrite mulr1.
      by rewrite -pr_predT HPu.
  rewrite (pr_eq1_of_support inner); last first.
    move=> xy Hxy.
    have [x Hx Hinner] := @dinsupp_dlet R _ _ _ _ _ Hxy.
    have [y Hy Hunit] := @dinsupp_dlet R _ _ _ _ _ Hinner.
    have Hxy_eq : xy = (x, y) by exact: in_dunit Hunit.
    subst xy.
    have Hfx : f x = uv.1.
      exact: (conditional_fiber_dinsupp f P uv.1 x Hx).
    have Hfy : f y = uv.2.
      exact: (conditional_fiber_dinsupp f Q uv.2 y Hy).
    by rewrite Hfx Hfy (eqP Huv_eq) eqxx.
  by rewrite Hinner_weight.
- move: Huv_eq; case: (uv.1 == uv.2)=> //= _.
  exact: ge0_pr.
Qed.

Lemma lift_projected_coupling_event_ge
    {T U : choiceType} (f : T -> U)
    (P Q : {distr T / R}) (d : {distr (U * U) / R}) :
  dmargin fst d =1 dmargin f P ->
  dmargin snd d =1 dmargin f Q ->
  dweight P = 1 ->
  dweight Q = 1 ->
  \P_[lift_projected_coupling f P Q d]
    (fun xy => f xy.1 == f xy.2) >=
  \P_[d] (fun uv => uv.1 == uv.2).
Proof.
move=> HdL HdR HP HQ.
pose F : U * U -> R := fun uv => lift_projected_inner_event_prob f P Q uv.
pose I : U * U -> R :=
  fun uv => if uv \in dinsupp d then (uv.1 == uv.2)%:R else 0.
rewrite /lift_projected_coupling __deprecated__pr_dlet.
rewrite [X in X <= _]pr_exp.
rewrite (eq_exp (mu := d) (f1 := fun uv => (uv.1 == uv.2)%:R)
  (f2 := I)); last first.
  move=> uv Huv.
  by rewrite /I Huv.
apply: le_exp.
- apply: bounded_has_exp.
  exists 1=> uv.
  rewrite /I.
  case: ifP=> _.
  + by rewrite ger0_norm ?ler0n ?lern1 ?leq_b1.
  + by rewrite normr0 ler01.
- apply: bounded_has_exp.
  exists 1=> uv.
  rewrite /F /lift_projected_inner_event_prob.
  rewrite ger0_norm; first exact: le1_pr.
  exact: ge0_pr.
- move=> uv.
  rewrite /I /F /lift_projected_inner_event_prob.
  case Huv: (uv \in dinsupp d).
  + rewrite /lift_projected_inner /projected_pair_event.
    exact: (lift_projected_coupling_inner_event_ge
      f P Q d HdL HdR HP HQ uv Huv).
  + exact: ge0_pr.
Qed.

(* Disintegrates a maximal coupling of projected marginals into a coupling of
   the original distributions.  The intended construction samples a maximal
   coupling of [dmargin f P] and [dmargin f Q], then samples each full output
   from the corresponding conditional fiber. *)
Lemma projected_total_variation_coupling
    {T U : choiceType} (f : T -> U) (P Q : {distr T / R}) ε :
  dweight P = 1 ->
  dweight Q = 1 ->
  total_variation (dmargin f P) (dmargin f Q) <= ε ->
  exists d : {distr (T * T) / R},
    dmargin fst d =1 P /\
    dmargin snd d =1 Q /\
    \P_[d] (fun xy => f xy.1 == f xy.2) >= 1 - ε.
Proof.
move=> HP HQ Htv.
have HdfP : dweight (dmargin f P) = 1 by rewrite dmargin_dweight.
have HdfQ : dweight (dmargin f Q) = 1 by rewrite dmargin_dweight.
have [d [HdL [HdR Hprob]]] :=
  maximal_coupling_total_variation
    (dmargin f P) (dmargin f Q) ε HdfP HdfQ Htv.
exists (lift_projected_coupling f P Q d).
split.
- exact: lift_projected_coupling_margin_l.
split.
- exact: lift_projected_coupling_margin_r.
- have Hlift :=
    lift_projected_coupling_event_ge f P Q d HdL HdR HP HQ.
  exact: (le_trans Hprob Hlift).
Qed.

Definition lift_loss_post
  {outL_t outR_t : choiceType}
  (post : pred (outL_t * outR_t)) : pred (option outL_t * option outR_t) :=
  fun outs =>
    match outs with
    | (Some outL, Some outR) => post (outL, outR)
    | _ => false
    end.

End AdditiveErrorCouplings.
