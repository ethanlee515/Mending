# KL Pythagorean Proof TODO

## Current status

- The coordinate/value-side KL machinery was split out of `KL/Pyth.v` into
  `KL/ChainPointwise.v`, breaking the would-be
  `Conditional.v -> Pyth.v -> Conditional.v` import cycle.
- The public `iterated_kl_chain_bound` in `KL/Conditional.v` is proved by
  calling `iterated_kl_chain_bound_via_pointwise` from `KL/ChainPointwise.v`.
- `iterated_kl_chain_bound_from_pointwise` is now proved top-down in
  `KL/ChainPointwise.v`.
- The coordinate contribution summability obligation is proved: its positive
  part uses the finite positive-part coordinate bound, and its negative part is
  bounded by the weighted conditional `Q` mass.
- The remaining value-side admit is the exact grouping identity
  `sum_coordinate_log_contribution_prefix_weighted`; it now explicitly assumes
  summability of both sides instead of asserting an unconditional totalized-sum
  equality.
- Two reusable grouping helpers are proved: `sum_dmargin_comp` pushes
  expectations through a discrete marginal, and `dmargin_prefix_coordinateE`
  identifies the joint prefix/current-coordinate marginal with
  `Pr[prefix a] * conditional_coordinate P a b`.
- The finite-positive/integrability path still compiles through
  `coordinate_bounded_kl_finite_kl`; the Pythagorean callers are wired through
  the pointwise chain-bound interface.

Checked with:

```sh
coqc -Q theories Mending theories/Probability/KL/ChainPointwise.v
coqc -Q theories Mending theories/Probability/KL/Conditional.v
coqc -Q theories Mending theories/Probability/KL/Pyth.v
```

## Value-side next steps

The remaining admitted value-side obligations are:

```coq
sum_coordinate_log_contribution_prefix_weighted
```

It lives in `KL/ChainPointwise.v` and provides the per-coordinate exact grouping
needed by `iterated_kl_chain_bound_from_pointwise`.

The conceptual proof should be:

1. Rewrite `δ_KL P Q` as the `sum` of `fun x => P x * ln (P x / Q x)`.
2. Use the pointwise chain decomposition to rewrite the integrand as
   `\sum_(i < n) P x * coordinate_log_contribution P Q x i`.
3. Exchange the outer `sum` over `x` with the finite sum over `i`.
4. For each coordinate `i`, group by prefixes `a : i.-tuple A`.
5. Identify each prefix group with
   `Pr[prefix a] * δ_KL (conditional_coordinate P a) (conditional_coordinate Q a)`.
6. Apply `sum_prefix_coordinate_weighted_kl_bound`, then sum over `i`.

## Main proof-engineering obstacles

- `coordinate_finite_kl_absolute_continuous` is still an admitted dependency of
  `pythSeqRule`. Today's summability work gives the summability half of
  ensemble `finite_kl`, but the absolute-continuity half still needs the
  coordinate-to-ensemble support proof.
- `kl_integrand_chain_decomp_pointwise` is still admitted and remains the
  pointwise chain-rule dependency for the value theorem.
- The prefix grouping step should probably use `psum_bigop` or a
  small wrapper around it, analogous to existing uses in `Core.v`.
- The full weighted-prefix KL series is now summable and bounded by `eps_i`;
  the missing exact step is relating each coordinate contribution sum to that
  prefix-weighted KL series.

## Good next target

Prove `sum_coordinate_log_contribution_prefix_weighted` in
`KL/ChainPointwise.v`:

```coq
summable (fun x => P x * coordinate_log_contribution P Q x i) ->
summable (fun a =>
  \P_[P] (fun x => tuple_prefix_eq a x) *
  δ_KL (conditional_coordinate P a) (conditional_coordinate Q a)) ->
...
sum (fun x => P x * coordinate_log_contribution P Q x i) =
sum (fun a =>
  \P_[P] (fun x => tuple_prefix_eq a x) *
  δ_KL (conditional_coordinate P a) (conditional_coordinate Q a))
```

`sum_coordinate_log_contribution_bound` already factors through this identity
and supplies the needed summability facts from the coordinate bound hypotheses,
so proving the identity should immediately remove the last value-side coordinate
admit.
