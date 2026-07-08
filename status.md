# Noise-Flooding Security Status

Compact handoff for the current formalization state.

## Build Gate

- Ethan reported that a clean whole-project rebuild succeeds after the latest
  cleanup.
- Last local targeted checks passed:

  ```sh
  rocq c -Q theories Mending theories/Schemes/ApproxFHE.v
  rocq c -Q theories Mending theories/Schemes/Indcpa.v
  rocq c -Q theories Mending theories/Schemes/Indcpad.v
  rocq c -Q theories Mending theories/Constructions/NoiseFlooding.v
  rocq c -Q theories Mending theories/Security/IndcpadSimulator.v
  rocq c -Q theories Mending theories/Probability/Ae.v
  rocq c -Q theories Mending theories/Probability/OutputHeap.v
  rocq c -Q theories Mending theories/Probability/PythSeq.v
  rocq c -Q theories Mending theories/ProgramLogics/Ae.v
  rocq c -Q theories Mending theories/ProgramLogics/Pyth.v
  rocq c -Q theories Mending theories/ProgramLogics/PythCompile.v
  rocq c -Q theories Mending theories/Security/NoiseFloodingSecurity.v
  rocq c -Q theories Mending -vos theories/Security/NoiseFloodingSecurity.v
  git diff --check
  ```

- Existing deprecation warnings remain in probability/compiler files.
- `Pythagorean-RHL/lmss.tex` builds with `make`, with existing LaTeX warnings.
- `NoiseFloodingSecurity.v` now full proof-checks locally without the previous
  reduction-side decrypt support ssreflect warning.
- The previous `compileRule` frontier is cleared: the decrypt-call replacement
  now has a resolved one-coordinate `⊨Pyth1` judgment, so
  `ind_cpad_compiled_guess_decrypt_replacement_from_compile` checks.

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
  -- 0 -->
ind_cpa_reduction_linked_game_code
  -- 0 -->
ind_cpa_reduction_game_code
```

The Coq assembly theorem is:

```coq
ind_cpa_reduction_additive_error_from_compile
```

The final endpoint is intentionally result-level via `same_game_result_opt`.
It compares only the returned winning bit, matching the security theorem and
avoiding unnecessary heap equality between the sim-decrypt IND-CPAD game and
the IND-CPA reduction presentation.

## Proved Pieces

- `ApproxCorrectnessPerfect` is the active exact correctness assumption for
  keygen/encrypt/eval.
- `ApproxFheScheme` now exposes `keygen_lossless : dweight keygen = 1`.
- IND-CPAD query accounting is by decrypt count, not table size.
- Encrypt/eval table-extension calls no longer assert
  `length updated_table <= max_queries`; the bound is enforced only by the
  decrypt counter.
- `IndCpadSimDecryptOracle` keeps real encrypt/eval behavior and replaces only
  `oracle_decrypt`.
- `challenge_heap_valid` is the main invariant for challenge bit, keys, table
  rows, and `good_keys`.
- Decrypt code is factored through:

  ```coq
  ind_cpad_decrypt_prefix_code
  ind_cpad_real_decrypt_cont
  ind_cpad_sim_decrypt_cont
  ```

- The one-call decrypt replacement is proved:

  ```coq
  ind_cpad_decrypt_code_pyth1
  ind_cpad_decrypt_resolve_pyth1
  ind_cpad_decrypt_code_pyth_short
  ind_cpad_decrypt_resolve_pyth_short
  ind_cpad_decrypt_resolve_additive_error_short
  ```

- The invariant-compatible compile bridge is packaged through the factored open
  challenger:

  ```coq
  ind_cpad_challenge_init_code
  ind_cpad_factored_open_game_code
  ind_cpad_open_game_code_factored
  ind_cpad_challenge_init_code_empty_valid
  ind_cpad_factored_compiled_guess_decrypt_replacement
  ind_cpad_compiled_open_decrypt_replacement_from_guess_factoring
  ind_cpad_game_to_compiled_sim_decrypt_additive_error
  ```

- Result-level AE/TV helpers are in place:

  ```coq
  same_result_opt
  same_game_result_opt
  same_game_output_result_opt
  same_output_heap_game_output_opt
  same_game_output_same_output_heap_opt
  additiveErrorOptSameResultTvdEqRule
  additiveErrorOptSameGameResultTvBound
  additiveErrorOptSameGameResultTvdEqRule
  additiveErrorOptSameGameResultReflRule
  additiveErrorOptSameGameResultTriangleRule
  additiveErrorOptSameGameOutputToResult
  ```

- Exact endpoint presentation helpers now include:

  ```coq
  ind_cpad_compiled_sim_decrypt_self_link_to_sim_decrypt_ae
  ind_cpa_reduction_game_code_linked_ae
  ind_cpa_reduction_linked_game_code_ae
  ```

- Generic moved-package helpers live in
  `theories/LibExtras/SSProveExtras/NominalExtras.v`:

  ```coq
  moved_package_valid
  moved_resolve_bind_valid
  moved_resolve_ret_valid
  ```

## Probability Glue

`projected_total_variation_coupling` is fully proved in
`theories/Probability/Ae.v`.  It lifts a coupling of projected result marginals
back to full completed outputs by conditioning on projected fibers.

Important supporting facts:

```coq
complete_bind_kernel
dweight_dlet
complete_bind_some
complete_bind_none
complete_bind
complete_distr_ext
complete_dmargin_dnull
dmargin_dunit_fst_pair
dmargin_dunit_snd_pair
product_coupling
product_coupling_margins
completed_fallback_coupling
completed_fallback_coupling_margins
complete_bind_fallback_coupling
complete_bind_kernel_dweight
complete_bind_fallback_coupling_margins
shared_complete_sample_coupling
shared_complete_sample_coupling_margins
shared_complete_sample_coupling_dweight
shared_complete_sample_coupling_pr_eq1
shared_complete_sample_coupling_pr_ge1
dflip_dweight
conditional_fiber_factorization
conditional_fiber_recompose
lift_projected_coupling
lift_projected_coupling_margin_l
lift_projected_coupling_margin_r
lift_projected_coupling_event_ge
projected_total_variation_coupling
```

The aggregate event proof avoids raw `psum` normalization by rewriting both
sides as expectations over the projected coupling and applying `le_exp`
pointwise.

## Gaussian/Chart State

- Shifted tuple Gaussian definitions and product Pythagorean bounds are in
  place.
- Successful decrypt is connected to raw oracle code by:

  ```coq
  noise_flooding_successful_decrypt_code_pyth
  noise_flooding_successful_decrypt_code_pyth1
  ```

- Exact-center chart case is axiom-free:

  ```coq
  noise_flooding_message_gaussian_kl_refl
  noise_flooding_message_gaussian_pythDist_refl
  ```

- Metric-to-vector local chart reasoning is proved:

  ```coq
  local_chart_metric_to_ivec_dist
  local_chart_center_metric_to_ivec_dist
  noise_flooding_vector_pythDist_from_metric_chart
  ```

## Sequencing Glue

- `additiveErrorOptSeqRule` in `theories/ProgramLogics/Ae.v` is now proved.
  The proof uses completed-bind margin glue and a generic good-prefix event
  bound:

  ```coq
  complete_bind_kernel
  complete_bind
  total_variation_complete_ge
  total_variation_eq_le0
  total_variation_refl_le0
  total_variation_ext
  total_variation_point_bound2
  total_variation_complete_point_bound2
  dmargin_some
  additiveErrorTvdEqTotalRule
  additiveErrorTvdEqPostTotalRule
  additiveErrorReflTotalRule
  completed_fallback_coupling
  completed_fallback_coupling_margins
  complete_bind_fallback_coupling
  complete_bind_fallback_coupling_margins
  shared_complete_sample_coupling
  shared_complete_sample_coupling_margins
  shared_complete_sample_coupling_dweight
  shared_complete_sample_coupling_pr_eq1
  shared_complete_sample_coupling_pr_ge1
  additiveErrorOptSeqKernel
  additiveErrorOptSeqKernel_margins
  additiveErrorOptSeqKernel_event
  coupling_bind_kernel
  additiveErrorOptSeqRule_coupling
  pr_dlet_lower_bound_good
  additiveErrorOptSeqRule
  additiveErrorSeqRule
  additiveErrorTvBound
  ```

  This proves that completing a subdistribution commutes with semantic bind
  when `None` continues to `None`, and provides an independent completed
  fallback coupling for bad prefix pairs where the middle relation is not
  available.  The dependent kernel that uses continuation AE couplings on good
  prefix pairs and fallback couplings otherwise is also in place, with its
  margins proved.  The generic `coupling_bind_kernel` lemma now binds a prefix
  coupling with any pointwise kernel coupling, and
  `additiveErrorOptSeqRule_coupling` uses it to prove the margin/coupling half
  for sequenced completed programs.  The event side is discharged by
  `pr_dlet_lower_bound_good`, which formalizes the union-bound-style estimate
  for a good prefix event followed by a good continuation.  The non-optional
  sequencing rule is now a wrapper around the optional rule.  The generic
  `additiveErrorTvBound` extraction is also proved by projecting completed
  couplings to optional result values and using `total_variation_complete_ge`
  to drop completion.
- The older raw-TV rules in `theories/ProgramLogics/Ae.v` should be treated
  carefully: non-optional `⊨AE` uses `lift_loss_post`, so raw subdistribution
  TV alone is not enough when either side can fail.  The new
  `additiveErrorTvdEqTotalRule` is the sound total-mass variant for exact
  output equality, and `additiveErrorTvdEqPostTotalRule` is the corresponding
  postcondition-preserving variant.  `additiveErrorReflTotalRule` is the
  corresponding sound reflexivity rule; the older raw reflexivity rule remains
  delicate for partial programs.  The generic zero-TV equality/reflexivity,
  TV extensionality, and pointwise TV-bound lemmas now live in
  `theories/Probability/Ae.v`, so the security file no longer carries local
  copies.  Challenge initialization now uses the total post rule instead of
  the older admitted raw-TV post rule.  The needed
  totality facts are exposed by `keygen_lossless`, `dflip_dweight`, and:

  ```coq
  ind_cpad_challenge_init_code_dweight
  ```

## Remaining Gaps

- `codeLinkCompileCallsClosedPrefix` in
  `theories/ProgramLogics/PythCompile.v`.

  The zero-budget closed-prefix case is proved:

  ```coq
  codeLinkClosedPrefixBind
  codeLinkCompileCallsClosedPrefix0
  ```

  Positive budgets still need a semantic trace-prefix fusion lemma for
  `factor_calls_aux`/`run_until_next_call_aux`.  A raw syntactic rebase lemma is
  too strong because invalid packed trace branches are both null semantically
  but can have different continuations.  The null-branch facts already proved:

  ```coq
  Pr_code_bind_invalid_trace_code
  Pr_code_link_bind_invalid_trace_code
  ```

- Endpoint bridges in `theories/Security/NoiseFloodingSecurity.v`:

  ```coq
  ind_cpad_compiled_sim_decrypt_mixed_to_self_link_ae
  ind_cpad_sim_decrypt_to_ind_cpa_reduction_linked_ae
  ```

  The mixed-to-self bridge is the bounded-query endpoint.  After the first
  `max_queries` selected decrypt calls are compiled, residual uncompiled
  decrypt calls should assert-fail on both sides because real and simulator
  packages share the decrypt counter.  Local over-bound failure facts are
  proved:

  ```coq
  ind_cpad_real_decrypt_code_over_bound_null
  ind_cpad_sim_decrypt_code_over_bound_null
  ind_cpad_real_decrypt_resolve_over_bound_null
  ind_cpad_sim_decrypt_resolve_over_bound_null
  ```

  The linked IND-CPA reduction bridge should remain result-level: the
  sim-decrypt IND-CPAD presentation and the reduction simulator use different
  bookkeeping locations, but should return the same bit.  The intended
  cross-game heap invariant is now named:

  ```coq
  reduction_initialized_heap
  sim_decrypt_reduction_heap_rel
  sim_decrypt_reduction_heap_rel_initialized
  ```

  It relates the two initialized heaps by the sampled bit/keys, ready flag,
  adversary-visible table, and decrypt counter, while allowing the two packages
  to own different internal bookkeeping locations.  Projection lemmas for each
  component are proved, as are the first generic preservation facts:

  ```coq
  sim_decrypt_reduction_heap_rel_set_table
  sim_decrypt_reduction_heap_rel_set_decrypt_count
  sim_decrypt_reduction_heap_rel_set_decrypt_count_valid
  ```

  Table preservation is also specialized to the three adversary-visible row
  append operations:

  ```coq
  sim_decrypt_reduction_heap_rel_set_table_encrypt
  sim_decrypt_reduction_heap_rel_set_table_eval1
  sim_decrypt_reduction_heap_rel_set_table_eval2
  ```

  The rewrite layer from reduction-side table reads to left-table expressions is
  now present:

  ```coq
  sim_decrypt_reduction_heap_rel_eval1_row
  sim_decrypt_reduction_heap_rel_eval2_row_i
  sim_decrypt_reduction_heap_rel_eval2_row_j
  sim_decrypt_reduction_heap_rel_set_table_encrypt_right
  sim_decrypt_reduction_heap_rel_set_table_eval1_right
  sim_decrypt_reduction_heap_rel_set_table_eval2_right
  ```

  The next endpoint-invariant facts should move from heap-update preservation
  to oracle-body simulations: encrypt/eval calls should produce the same
  returned ciphertext and preserve `sim_decrypt_reduction_heap_rel`; decrypt
  calls should produce the same option result distribution and preserve the
  relation after the shared counter increment.

  The reduction simulator's adversary-visible oracle bodies are now exposed as
  raw code with resolve lemmas:

  ```coq
  ind_cpa_reduction_challenge_init_code
  ind_cpa_reduction_challenge_init_code_empty_shape
  ind_cpad_reduction_challenge_init_heaps_rel
  ind_cpa_reduction_sim_encrypt_code
  ind_cpa_reduction_sim_encrypt_resolveE
  ind_cpa_reduction_sim_eval1_code
  ind_cpa_reduction_sim_eval1_resolveE
  ind_cpa_reduction_sim_eval2_code
  ind_cpa_reduction_sim_eval2_resolveE
  ```

  The initialization helper names the right-side heap shape expected by
  `sim_decrypt_reduction_heap_rel`: after the shared challenge bit and keygen
  samples, the IND-CPAD challenge heap and the reduction heap are related.
  The intended relation-preserving oracle postcondition is now named:

  ```coq
  same_result_sim_decrypt_reduction_opt
  same_result_sim_decrypt_reduction_result_opt
  ```

  It strengthens the existing result-only postcondition by additionally
  requiring related heaps on successful outputs while still allowing paired
  failure.
  This should make the upcoming adversary/oracle lifting proof start from a
  named invariant rather than redoing raw bind-support reasoning.  The exposed
  oracle bodies should make the remaining simulations look like direct
  `Pr_code`/Hoare arguments over named programs, matching the existing
  `ind_cpad_real_*_code` exposure on the left.

  The encrypt oracle has the expected linked result comparison:

  ```coq
  ind_cpa_reduction_sim_encrypt_linked_code
  ind_cpad_sim_decrypt_reduction_encrypt_linked_result_eq
  ind_cpa_reduction_sim_encrypt_linked_code_left_support_rel
  ind_cpad_sim_decrypt_reduction_encrypt_resolve_linked_left_support_rel
  ind_cpad_sim_decrypt_reduction_encrypt_linked_result_tv_le0
  ind_cpad_sim_decrypt_reduction_encrypt_resolve_linked_result_tv_le0
  ind_cpad_sim_decrypt_reduction_encrypt_resolve_linked_ae
  ind_cpad_sim_decrypt_reduction_encrypt_resolve_linked_rel_ae
  ```

  The right side is factored through an explicit linked-body raw code because
  the reduction simulator obtains encrypt ciphertexts through the outer
  IND-CPA oracle rather than sampling them internally.  The left-support helper
  strengthens this from result-marginal equality to the witness shape needed by
  a future relation-preserving coupling: every successful linked reduction
  encrypt output has a left sim-decrypt encrypt output with the same ciphertext
  and related heaps.  The AE wrapper packages the oracle call under
  `same_input_sim_decrypt_reduction_pre` and the generic result-only
  postcondition `same_result_opt`.  The stronger relation-preserving AE wrapper
  is also now proved by an explicit shared-sample coupling: when the public key
  is initialized, both sides use the same encrypt sample and update their
  respective table locations in lockstep; when the key is absent, both sides
  fail and the completed null coupling handles the paired `None` branch.  The
  null branch now uses the generic `complete_dmargin_dnull` helper.

  The analogous direct `eval1` relation-preserving proof exposed a dependent
  assertion-normalization issue: unfolding the raw code exposes the
  `#assert ... as r_in_range` continuation proof as a boolean equality, while
  `nth_valid`/the table-row lemmas want the proposition form.  The reusable
  assertion-coupling helper now packages the common same-guard case:

  ```coq
  assertD_same_guard_coupling
  ```

  True branches delegate to a supplied continuation coupling, while false
  branches are coupled as paired `(None, None)` failures under a nonnegative
  error budget.  Using this helper, the `eval1` and `eval2` oracles now also
  have relation-preserving AE wrappers.  The proofs align the range guards with
  the table relation, use proof irrelevance for generated `nth_valid` witnesses,
  couple the shared eval samples, and preserve
  `sim_decrypt_reduction_heap_rel` with
  `sim_decrypt_reduction_heap_rel_set_table_eval1_right` and
  `sim_decrypt_reduction_heap_rel_set_table_eval2_right`.

  A generic shared-sample relation coupling helper is also available:

  ```coq
  shared_sample_relation_coupling
  ```

  It packages the common proof pattern where both programs are margins of the
  same completed sample distribution and the postcondition holds for every
  sample in support plus the paired failure branch.  This is intended to shorten
  the remaining decrypt relation-preserving wrapper, especially the equal-label
  shared-noise branch.

  Support-level simulations for the reduction-side eval oracles now exist:

  ```coq
  ind_cpa_reduction_sim_eval1_code_support_rel
  ind_cpa_reduction_sim_eval1_code_left_support_rel
  ind_cpa_reduction_sim_eval2_code_support_rel
  ind_cpa_reduction_sim_eval2_code_left_support_rel
  ind_cpad_sim_decrypt_reduction_eval1_result_eq
  ind_cpad_sim_decrypt_reduction_eval2_result_eq
  ind_cpad_sim_decrypt_reduction_eval1_result_tv_le0
  ind_cpad_sim_decrypt_reduction_eval2_result_tv_le0
  ind_cpad_sim_decrypt_reduction_eval1_resolve_result_tv_le0
  ind_cpad_sim_decrypt_reduction_eval2_resolve_result_tv_le0
  ind_cpad_sim_decrypt_reduction_eval1_resolve_left_support_rel
  ind_cpad_sim_decrypt_reduction_eval2_resolve_left_support_rel
  ind_cpad_sim_decrypt_reduction_eval1_resolve_ae
  ind_cpad_sim_decrypt_reduction_eval1_resolve_rel_ae
  ind_cpad_sim_decrypt_reduction_eval2_resolve_ae
  ind_cpad_sim_decrypt_reduction_eval2_resolve_rel_ae
  ```

  They say every successful reduction-side eval output can be matched by a
  left-side output with the same returned ciphertext and related heaps.  Both
  eval oracles now also have the left-support strengthening needed for a
  relation-preserving coupling, and those facts are also exposed at the
  resolve/oracle-call boundary.  The result-equality lemmas package the same
  eval comparisons as
  exact equality of returned-ciphertext marginals, and the TV wrappers turn
  those equalities into zero-distance facts over completed result marginals.
  The resolve-level wrappers expose the same facts at the oracle-call
  boundary, and the AE wrappers package them as result-only zero-error oracle
  judgments.

  The reduction simulator's decrypt body is also exposed, and the first
  none-result support case is proved:

  ```coq
  ind_cpa_reduction_sim_decrypt_code
  ind_cpa_reduction_sim_decrypt_resolveE
  sim_decrypt_reduction_heap_rel_decrypt_row
  ind_cpa_reduction_sim_decrypt_code_support_rel_none
  ind_cpa_reduction_sim_decrypt_code_support_rel
  ind_cpa_reduction_sim_decrypt_code_left_support_rel
  ind_cpad_sim_decrypt_reduction_decrypt_result_eq
  ind_cpad_sim_decrypt_reduction_decrypt_result_tv_le0
  ind_cpad_sim_decrypt_reduction_decrypt_resolve_result_tv_le0
  ind_cpad_sim_decrypt_reduction_decrypt_resolve_left_support_rel
  ind_cpad_sim_decrypt_reduction_decrypt_resolve_ae
  ```

  The general support-shape lemma covers both the unequal-label `None` branch
  and the equal-label sampled `Some` branch at the level of matching returned
  option values and related heaps.  The left-support strengthening now also
  shows that the matched output is in the support of the left sim-decrypt code,
  using the same sampled noise in the equal-label branch.  Decrypt is also
  packaged as exact equality of returned-result marginals under
  `sim_decrypt_reduction_heap_rel`, with a zero-TV wrapper for the completed
  result marginals, a resolve-level wrapper for oracle-call use, and a
  result-only zero-error AE wrapper.  The remaining endpoint work is to lift
  these per-oracle encrypt/eval/decrypt AE facts through the adversary
  execution and discharge the mixed compiled/self-link bridge.

- Explicit axiom:

  ```coq
  noise_flooding_message_gaussian_kl
  ```

  Likely replacement: deterministic KL data processing for `dmargin`, plus the
  domain-specific chart translation assumptions.

## Paper State

`Pythagorean-RHL/lmss.tex` mirrors the formal chain, including the linked
endpoint `H_4'`.  It distinguishes the mixed-link and self-link compiled
sim-decrypt games, explains why the final bridge is result-level, and sketches
the projected-marginal disintegration argument behind
`projected_total_variation_coupling`.  The `H_3 -> H_4'` paragraph now spells
out the intended endpoint invariant: the two heaps are not equal, but they
carry the same sampled bit/keys, adversary-visible table, decrypt counter, and
answers to adversary calls.

## Next Work

1. Prove or justify `codeLinkCompileCallsClosedPrefix` without an admit.
2. Prove `ind_cpad_compiled_sim_decrypt_mixed_to_self_link_ae`.
3. Prove `ind_cpad_sim_decrypt_to_ind_cpa_reduction_linked_ae` at
   `same_game_result_opt`.
4. Replace `noise_flooding_message_gaussian_kl` with smaller reusable
   geometric/probabilistic ingredients.
