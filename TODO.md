# KL Pythagorean Proof TODO

## Current status

- `finite_sum_selected_prefix_coordinate_mass_le` is proved directly.
- `point_mass_le_prefix_coordinate_mass` was removed because it is no longer used.
- `prefix_coordinate_pr_factor` is proved:
  `Pr[prefix a and coordinate b] = Pr[prefix a] * conditional_coordinate P a b`.
- The finite-positive/integrability path now compiles through
  `summable_kl_from_coordinate_bounded_kl`.
- A first value-side helper is proved:
  `prefix_coordinate_weighted_kl_bound`.
- `iterated_kl_chain_bound_from_pointwise` and
  `iterated_kl_chain_bound_via_pointwise` now assume `finite_kl P Q` instead of
  only `absolute_continuous P Q`.
- The finite-coordinate summability/interchange helpers are proved:
  `summable_finite_ord_sum` and `sum_finite_ord_sum`.
- The coordinate/value-side KL machinery was split out of `KL/Pyth.v` into
  `KL/ChainPointwise.v`, breaking the would-be
  `Conditional.v -> Pyth.v -> Conditional.v` import cycle.
- The public `iterated_kl_chain_bound` in `KL/Conditional.v` is now proved by
  calling `iterated_kl_chain_bound_via_pointwise` from `KL/ChainPointwise.v`.
- The public `iterated_kl_chain_bound` in `KL/Conditional.v` now also assumes
  `finite_kl P Q`; the `Pyth.v` callers derive it from coordinate-wise
  `finite_kl` using `coordinate_bounded_kl_finite_kl`.
- The `Pyth.v` callers now go through `iterated_kl_chain_bound_via_pointwise`.

Checked with:

```sh
coqc -Q theories Mending theories/Probability/KL/Pyth.v
```

## Value-side next steps

The remaining admitted value theorem is:

```coq
iterated_kl_chain_bound_from_pointwise
```

It now lives in `KL/ChainPointwise.v`, which is the common dependency of both
`KL/Conditional.v` and `KL/Pyth.v`.

The conceptual proof should be:

1. Rewrite `δ_KL P Q` as the `sum` of `fun x => P x * ln (P x / Q x)`.
2. Use the pointwise chain decomposition to rewrite the integrand as
   `\sum_(i < n) P x * coordinate_log_contribution P Q x i`.
3. Exchange the outer `sum` over `x` with the finite sum over `i`.
4. For each coordinate `i`, group by prefixes `a : i.-tuple A`.
5. Identify each prefix group with
   `Pr[prefix a] * δ_KL (conditional_coordinate P a) (conditional_coordinate Q a)`.
6. Apply `prefix_coordinate_weighted_kl_bound`, then sum over `i`.

## Main proof-engineering obstacles

- `coordinate_finite_kl_absolute_continuous` is still an admitted dependency of
  `pythSeqRule`. Today's summability work gives the summability half of
  ensemble `finite_kl`, but the absolute-continuity half still needs the
  coordinate-to-ensemble support proof.
- The remaining proof still needs summability facts for `sumD` and finite-bigop
  linearity.
- The likely central helper is a finite-coordinate linearity/interchange lemma:

```coq
sum (fun x => \sum_(i < n) F i x) =
\sum_(i < n) sum (fun x => F i x)
```

under suitable summability assumptions.

- After that, the prefix grouping step should probably use `psum_bigop` or a
  small wrapper around it, analogous to existing uses in `Core.v`.

## Good next target

Prove `iterated_kl_chain_bound_from_pointwise` in `KL/ChainPointwise.v`.
The import graph is ready now; the remaining work is the actual value-side
proof using `sum_finite_ord_sum`, prefix grouping, and
`prefix_coordinate_weighted_kl_bound`.
