Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot all_order all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp Require Import reals realsum exp sequences realseq distr.

Import GRing.Theory.
Local Open Scope ring_scope.

Definition max_norm {n} (v : n.-tuple int) : nat :=
  \big[Order.max/0]_(i < n) absz (tnth v i).

Definition ivec_zero {n} : n.-tuple int :=
  [tuple 0 | i < n].

Lemma max_norm_tnth_le {n : nat} (v : n.-tuple int) (i : 'I_n) :
  (absz (tnth v i) <= max_norm v)%N.
Proof.
rewrite /max_norm.
exact: (bigmax_sup i).
Qed.

Definition ivec_add {n} (v w : n.-tuple int) : n.-tuple int :=
  [tuple (tnth v i + tnth w i) | i < n].

Lemma ivec_add0r {n : nat} (v : n.-tuple int) :
  ivec_add v ivec_zero = v.
Proof.
apply: eq_from_tnth=> i.
by rewrite /ivec_add /ivec_zero !tnth_mktuple addr0.
Qed.

Lemma ivec_add_cons {n : nat} (x y : int) (xs ys : n.-tuple int) :
  ivec_add (cons_tuple x xs) (cons_tuple y ys) =
    cons_tuple (x + y) (ivec_add xs ys).
Proof.
apply: eq_from_tnth=> i.
rewrite /ivec_add !tnth_mktuple.
case: i=> [[|k] Hk] /=.
- have -> : Ordinal Hk = ord0 :> 'I_n.+1 by apply: val_inj.
  by rewrite !tnth0.
have Hkn : (k < n)%N by move: Hk; rewrite ltnS.
have -> : Ordinal Hk = lift ord0 (Ordinal Hkn) :> 'I_n.+1
  by apply: val_inj.
by rewrite !tnthS tnth_mktuple.
Qed.

Definition ivec_sub {n} (v w : n.-tuple int) : n.-tuple int :=
  [tuple (tnth v i - tnth w i) | i < n].

Lemma ivec_sub_cons {n : nat} (x y : int) (xs ys : n.-tuple int) :
  ivec_sub (cons_tuple x xs) (cons_tuple y ys) =
    cons_tuple (x - y) (ivec_sub xs ys).
Proof.
apply: eq_from_tnth=> i.
rewrite /ivec_sub !tnth_mktuple.
case: i=> [[|k] Hk] /=.
- have -> : Ordinal Hk = ord0 :> 'I_n.+1 by apply: val_inj.
  by rewrite !tnth0.
have Hkn : (k < n)%N by move: Hk; rewrite ltnS.
have -> : Ordinal Hk = lift ord0 (Ordinal Hkn) :> 'I_n.+1
  by apply: val_inj.
by rewrite !tnthS tnth_mktuple.
Qed.

Lemma ivec_add_subK {n : nat} (v w : n.-tuple int) :
  ivec_add (ivec_sub v w) w = v.
Proof.
apply: eq_from_tnth=> i.
by rewrite /ivec_add /ivec_sub !tnth_mktuple subrK.
Qed.

Lemma ivec_sub_addK {n : nat} (v w : n.-tuple int) :
  ivec_sub (ivec_add v w) w = v.
Proof.
apply: eq_from_tnth=> i.
by rewrite /ivec_add /ivec_sub !tnth_mktuple addrK.
Qed.

Lemma ivec_add_inj_r {n : nat} (center : n.-tuple int) :
  injective (fun v : n.-tuple int => ivec_add v center).
Proof.
move=> v1 v2 H.
rewrite -(ivec_sub_addK v1 center) -(ivec_sub_addK v2 center).
by rewrite H.
Qed.

Definition ivec_dist {n} (v w : n.-tuple int) : nat :=
  max_norm (ivec_sub v w).

Lemma ivec_dist_refl {n : nat} (v : n.-tuple int) :
  ivec_dist v v = 0%N.
Proof.
apply/eqP.
rewrite eqn_leq leq0n andbT /ivec_dist /max_norm.
apply/bigmax_leqP=> i _.
by rewrite /ivec_sub tnth_mktuple subrr absz0.
Qed.

Lemma ivec_dist_tnth_le {n : nat} (v w : n.-tuple int) (i : 'I_n) :
  (absz (tnth v i - tnth w i) <= ivec_dist v w)%N.
Proof.
rewrite /ivec_dist.
have H := max_norm_tnth_le (ivec_sub v w) i.
by rewrite /ivec_sub tnth_mktuple in H.
Qed.
