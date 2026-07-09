# Noise-Flooding Security Status

Compact handoff for the current formalization state.

## Build Gate

Latest targeted Coq checks after restoring the local-isometry fields and
threading finite encoding as explicit security evidence:

```sh
timeout 600s rocq c -Q theories Mending theories/Schemes/ApproxFHE.v
timeout 600s rocq c -Q theories Mending theories/Schemes/Indcpa.v
timeout 600s rocq c -Q theories Mending theories/Schemes/Indcpad.v
timeout 600s rocq c -Q theories Mending theories/Constructions/NoiseFlooding.v
timeout 600s rocq c -Q theories Mending theories/Security/IndcpadSimulator.v
timeout 600s rocq c -Q theories Mending theories/Security/NoiseFloodingSecurity.v
```

Latest hygiene checks after the current handoff update:

```sh
git diff --check
rg -n "Admitted\.|Axiom |admit" \
  theories/ProgramLogics/PythCompile.v \
  theories/Security/NoiseFloodingSecurity.v \
  theories/Probability/Ae.v
rg -n "inv_isoK|isoK|isometry_radius|iso_correct" \
  theories/Schemes/ApproxFHE.v
rg -n "local_chart_metric_to_ivec_dist|local_chart_center_metric_to_ivec_dist|noise_flooding_vector_pythDist_from_metric_chart" \
  theories/Security/NoiseFloodingSecurity.v
rg -n "Parameter chart_center_dist_le_metric|Axiom chart_center_dist_le_metric" \
  theories
```

The focused admit/axiom scan, removed local-chart-helper scan, and
metric-interface chart-center scan are expected to produce no output. The
local-isometry scan should show the restored active assumptions in
`ApproxFHE.v`.

Keep this focused gate green after local proof edits:

```sh
rocq c -Q theories Mending theories/LibExtras/MathcompExtras/DistrExtras.v
rocq c -Q theories Mending theories/Schemes/Utils/IntVec.v
rocq c -Q theories Mending theories/Probability/KL/Core.v
rocq c -Q theories Mending theories/Schemes/ApproxFHE.v
rocq c -Q theories Mending theories/Probability/KL/Pyth.v
rocq c -Q theories Mending theories/Constructions/NoiseFlooding.v
rocq c -Q theories Mending theories/Security/NoiseFloodingSecurity.v
git diff --check
rg -n "Admitted\.|Axiom |admit" \
  theories/ProgramLogics/PythCompile.v \
  theories/Security/NoiseFloodingSecurity.v \
  theories/Probability/Ae.v
```

Broader gate to keep green before major handoff/merge:

```sh
rocq c -Q theories Mending theories/LibExtras/MathcompExtras/DistrExtras.v
rocq c -Q theories Mending theories/Schemes/Utils/IntVec.v
rocq c -Q theories Mending theories/Probability/KL/Core.v
rocq c -Q theories Mending theories/Probability/KL/Pinsker.v
rocq c -Q theories Mending theories/Schemes/ApproxFHE.v
rocq c -Q theories Mending theories/Schemes/Indcpa.v
rocq c -Q theories Mending theories/Schemes/Indcpad.v
rocq c -Q theories Mending theories/Probability/DiscreteGaussians/DiscreteGaussianKL.v
rocq c -Q theories Mending theories/LibExtras/SSProveExtras/DiscreteGaussian.v
rocq c -Q theories Mending theories/Probability/ConditionalCoordinate.v
rocq c -Q theories Mending theories/Probability/KL/ChainPointwise.v
rocq c -Q theories Mending theories/Probability/DletTuple.v
rocq c -Q theories Mending theories/Probability/KL/Pyth.v
rocq c -Q theories Mending theories/Probability/PythSeq.v
rocq c -Q theories Mending theories/ProgramLogics/Pyth.v
rocq c -Q theories Mending theories/ProgramLogics/PythCompile.v
rocq c -Q theories Mending theories/Constructions/NoiseFlooding.v
rocq c -Q theories Mending theories/Security/IndcpadSimulator.v
rocq c -Q theories Mending theories/LibExtras/SSProveExtras/NominalExtras.v
rocq c -Q theories Mending theories/Probability/Ae.v
rocq c -Q theories Mending theories/Security/NoiseFloodingSecurity.v
git diff --check
rg -n "Admitted\.|Axiom |admit" \
  theories/ProgramLogics/PythCompile.v \
  theories/Security/NoiseFloodingSecurity.v \
  theories/Probability/Ae.v
```

Known warnings remain from existing notation/deprecation warnings in
`Pinsker.v`, `DletTuple.v`, `NoiseFlooding.v`, `IndcpadSimulator.v`,
`PythSeq.v`, `PythCompile.v`, and `Ae.v`.

## Main Chain

Intended loss:

```coq
security_loss max_queries =
  2 * sqrt ((max_queries * (dim / (2 * gaussian_width_multiplier^2))) / 2)

compile_security_error max_queries = security_loss max_queries / 2
```

Current hybrid chain:

```coq
ind_cpad_game_code
  -- compile_security_error max_queries -->
ind_cpad_compiled_sim_decrypt_game_code
  -- 0 -->
ind_cpad_compiled_sim_decrypt_self_link_game_code
  -- 0 -->
ind_cpad_sim_decrypt_game_code
  -- 0, direct/factored reduction bridge -->
ind_cpa_reduction_direct_factored_game_code
  -- 0, unfresh/factored linked bridge -->
ind_cpa_reduction_unfresh_linked_game_code
  -- 0, alpha/freshening bridge -->
ind_cpa_reduction_linked_game_code
  -- 0 -->
ind_cpa_reduction_game_code
```

The chart-route assembly theorem is
`ind_cpa_reduction_additive_error_from_compile`, now with explicit
`finite_encoding_cert` and `chart_center_dist_le_metric_cert` premises. The
direct assembly theorem is
`ind_cpa_reduction_additive_error_from_compile_ready_vector_bound`, with
`finite_encoding_cert` and `decrypt_prefix_ready_vector_bound_cert` premises.
The final endpoint is intentionally result-level via `same_game_result_opt`.
The chain is closed modulo the scheme, correctness, IND-CPA, the metric
interface assumptions, `finite_encoding_cert`, and whichever explicit route
certificate is chosen.

## Current Frontier

Important blocker: the current `finite_encoding_cert` is proof-shaped in a way
that is likely false for the intended origin-centered chart model. In
particular, the fields
`finite_common_inverse_isometry_encoding_left/right` ask for one common
encoding map whose pushforward agrees with both
`encode ∘ inverse_isometry centerL` and
`encode ∘ inverse_isometry centerR` when both tuple Gaussians are centered at
their own chart origins. If the intended chart law includes
`isometry a a = 0` and `isometry b b = 0`, this would force the flooded
message distributions around `a` and `b` to be equal rather than merely close.
That is not the noise-flooding statement, so this certificate should be
replaced before further concrete-instance work.

The same coordinate-system problem affects the current
`chart_center_dist_le_metric_cert` and
`challenge_decrypt_prefix_row_vector_bound` route. They compare
`isometry a a` with `isometry b b`; under origin-centered charts both sides are
the zero vector, so the bound becomes vacuous. The vector KL comparison should
instead happen in one chart, comparing centers `0` and `isometry a b`.

The active security route now uses finite message encodings and direct
vector-center bounds rather than an opaque message-space Gaussian KL axiom.
The local Gaussian KL bound is proved for integer vectors, lifted through
finite-output KL data processing, and then packaged as message-level
`pythDist`/program-logic wrappers.

The direct ready-vector Hoare obligation is now named:

```coq
decrypt_prefix_ready_vector_bound_cert max_queries
```

That alias abbreviates the certificate that `ind_cpad_decrypt_prefix_code`
returns rows satisfying:

```coq
challenge_decrypt_prefix_row_ready_vector_bound
```

The chart-center route instantiates the certificate with:

```coq
ind_cpad_decrypt_prefix_code_readies_row_vector_bound
```

This closed proof derives vector-ready rows from row-ready rows using
`chart_center_dist_le_metric_cert`. For concrete instances that can prove the
vector-center bound directly, the premised route carries
`decrypt_prefix_ready_vector_bound_cert` through code, resolve, compile,
reduction, and the final theorem:

```coq
ind_cpad_decrypt_code_pyth1_from_metric_encoding_ready_vector_bound
ind_cpad_decrypt_resolve_pyth1_from_metric_encoding_ready_vector_bound
ind_cpad_compiled_guess_decrypt_replacement_from_compile_ready_vector_bound
ind_cpad_game_to_compiled_sim_decrypt_additive_error_ready_vector_bound
ind_cpa_reduction_additive_error_from_compile_ready_vector_bound
ind_cpa_reduction_additive_error_ready_vector_bound
ind_cpa_reduction_bound_ready_vector_bound
is_secure_ready_vector_bound
```

The public theorem `is_secure` is now the chart-route theorem and takes
`finite_encoding_cert` and `chart_center_dist_le_metric_cert` explicitly. The
theorem `is_secure_ready_vector_bound` is the direct route and takes
`finite_encoding_cert` and `decrypt_prefix_ready_vector_bound_cert`
explicitly. `NoiseFloodingSecure` no longer ascribes the closed `IsIndCpad`
module type, because chart/encoding evidence is no longer hidden in the metric
interface.

## Useful Proof Surfaces

Finite-encoding/KL bridge:

```coq
kl_dmargin_ord_bound
kl_dmargin_ord_common_bound
kl_dmargin_finite_encoding_common_bound
kl_dmargin_finite_encoding_common_bound_comp
kl_dmargin_finite_encoding_common_bound_comp_eq
kl_dmargin_finite_encoding_common_bound_comp_eq_in
```

Noise-flooding/message bridge:

```coq
noise_flooding_vector_kl_bound
noise_flooding_message_gaussian_kl_from_finite_encoding_vector_bound
noise_flooding_message_gaussian_kl_from_finite_encoding
noise_flooding_message_gaussian_pythDist_from_finite_encoding_vector_bound
noise_flooding_successful_decrypt_code_pyth_from_metric_encoding_vector_bound
noise_flooding_successful_decrypt_code_pyth1_from_metric_encoding_vector_bound
```

Metric-interface helpers:

```coq
shifted_tuple_gaussian_n_dg_shiftedE
shifted_tuple_gaussian_dinsupp
common_inverse_isometry_encoding_left_n_dg_shifted
common_inverse_isometry_encoding_right_n_dg_shifted
```

The local-isometry obligations `inv_isoK`, `isoK`, `isometry_radius`, and
`iso_correct` are restored in `ApproxFheMetric` as active assumptions. The
current finite-encoding/vector-ready security route does not consume them
directly yet, but they remain in the interface as the intended local-isometry
contract. The older local-chart helper lemmas in `NoiseFloodingSecurity.v`
remain removed/unused.
`chart_center_dist_le_metric` was also removed from `ApproxFheMetric`; the
security file now names that route-specific evidence as:

```coq
chart_center_dist_le_metric_cert
```

Finite message encoding is now carried by the security file as:

```coq
finite_encoding_cert
```

This record should be treated as provisional: keep the finite encoding and
injectivity pieces if needed for finite-output KL data processing, but do not
try to prove the current `finite_common_inverse_isometry_encoding*` fields for
the intended `(Z mod q)^n` chart model.

## Remaining Gaps

Before doing more proof work, replace the bad common-encoding certificate with
chart laws that match the intended geometry. A plausible replacement interface
is:

```coq
(* zero denotes the all-zero dim.-tuple int; concrete name TBD. *)
isometry_center0 :
  forall c, isometry c c = zero

metric_chartE :
  forall a b, metric a b = ivec_dist zero (isometry a b)

inverse_isometry_shift :
  forall a b x,
    inverse_isometry b x =
    inverse_isometry a (ivec_add x (isometry a b))
```

With this shape, the right comparison is:

```coq
encode ∘ inverse_isometry a
```

applied to vector Gaussians centered at `zero` and `isometry a b`,
respectively. That matches noise flooding: the distributions are close by the
integer-vector Gaussian KL bound; they are not required to be equal.

After that refactor, final security should use either the chart-law route above
or a concrete proof of the reshaped direct obligation:

```coq
decrypt_prefix_ready_vector_bound_cert max_queries
```

The direct route should also compare vector centers in one chart, not compare
`isometry a a` with `isometry b b`.

## Next Work

1. Refactor the message-KL bridge away from
   `finite_common_inverse_isometry_encoding*` and toward the origin-centered
   chart laws above.
2. Refactor `challenge_decrypt_prefix_row_vector_bound`,
   `chart_center_dist_le_metric_cert`, and their theorem wrappers so the vector
   bound is stated in one chart.
3. Keep only the finite encoding/injectivity assumptions that are actually
   needed for finite-output KL data processing.
4. Decide whether the concrete proof should use the chart-law route or the
   direct `decrypt_prefix_ready_vector_bound_cert` route.
5. Keep the focused gate green after each proof step.
