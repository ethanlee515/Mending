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
- The public `iterated_kl_chain_bound` in `KL/Conditional.v` now also assumes
  `finite_kl P Q`; the `Pyth.v` callers derive it from coordinate-wise
  `finite_kl` using `coordinate_bounded_kl_finite_kl`.

Checked with:

```sh
coqc -Q theories Mending theories/Probability/KL/Pyth.v
```

## Value-side next steps

The remaining admitted value theorem is:

```coq
iterated_kl_chain_bound_from_pointwise
```

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

Try proving the central finite-coordinate linearity/interchange lemma, then use
it inside `iterated_kl_chain_bound_from_pointwise`. After that, make the public
`iterated_kl_chain_bound` call `iterated_kl_chain_bound_via_pointwise`.
