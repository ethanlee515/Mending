Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot all_order all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".
From mathcomp Require Import reals realsum exp sequences realseq distr.

Local Open Scope ring_scope.

Definition max_norm {n} (v : n.-tuple int) : nat :=
  \big[Order.max/0]_(i < n) absz (tnth v i).

Lemma max_norm_tnth_le {n : nat} (v : n.-tuple int) (i : 'I_n) :
  (absz (tnth v i) <= max_norm v)%N.
Proof.
rewrite /max_norm.
exact: (bigmax_sup i).
Qed.

Definition ivec_add {n} (v w : n.-tuple int) : n.-tuple int :=
  [tuple (tnth v i + tnth w i) | i < n].

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

Definition ivec_dist {n} (v w : n.-tuple int) : nat :=
  max_norm (ivec_sub v w).

Lemma ivec_dist_tnth_le {n : nat} (v w : n.-tuple int) (i : 'I_n) :
  (absz (tnth v i - tnth w i) <= ivec_dist v w)%N.
Proof.
rewrite /ivec_dist.
have H := max_norm_tnth_le (ivec_sub v w) i.
by rewrite /ivec_sub tnth_mktuple in H.
Qed.
