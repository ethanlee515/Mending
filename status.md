# Noise-Flooding Security Status

Compact handoff for the current formalization state.

## Build Gate

- Ethan reported that a clean whole-project rebuild succeeds after the latest
  cleanup.
- Last local targeted checks passed:

  ```sh
  rocq c -Q theories Mending theories/Probability/Ae.v
  rocq c -Q theories Mending theories/Probability/OutputHeap.v
  rocq c -Q theories Mending theories/Probability/PythSeq.v
  rocq c -Q theories Mending theories/ProgramLogics/Ae.v
  rocq c -Q theories Mending theories/ProgramLogics/Pyth.v
  rocq c -Q theories Mending theories/ProgramLogics/PythCompile.v
  rocq c -Q theories Mending -vos theories/Security/NoiseFloodingSecurity.v
  git diff --check
  ```

- Existing deprecation warnings remain in probability/compiler files.
- `Pythagorean-RHL/lmss.tex` builds with `make`, with existing LaTeX warnings.
- `NoiseFloodingSecurity.v` is still only checked with `-vos`; do not claim the
  full file proof-checks unless that has been rerun and fixed.

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
- IND-CPAD query accounting is by decrypt count, not table size.
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
  same_game_result_opt
  same_game_output_result_opt
  additiveErrorOptResultTvBound
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

## Remaining Gaps

- `additiveErrorOptSeqRule` in `theories/ProgramLogics/Ae.v`, matching the
  existing admitted non-optional sequence rule.
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
  ind_cpa_reduction_sim_encrypt_code
  ind_cpa_reduction_sim_encrypt_resolveE
  ind_cpa_reduction_sim_eval1_code
  ind_cpa_reduction_sim_eval1_resolveE
  ind_cpa_reduction_sim_eval2_code
  ind_cpa_reduction_sim_eval2_resolveE
  ```

  This should make the upcoming oracle-body simulations look like direct
  `Pr_code`/Hoare arguments over named programs, matching the existing
  `ind_cpad_real_*_code` exposure on the left.

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

## Cleanup Note

Encrypt/eval still assert:

```coq
length updated_table <= max_queries
```

These look conceptually extraneous because the reduction tracks decrypt calls.
If removing them, update `theories/Schemes/Indcpad.v`, the simulator mirror in
`theories/Security/IndcpadSimulator.v`, raw-code copies in
`NoiseFloodingSecurity.v`, and affected bridge/preservation proofs together.

## Next Work

1. Prove or justify `codeLinkCompileCallsClosedPrefix`.
2. Prove `ind_cpad_compiled_sim_decrypt_mixed_to_self_link_ae`.
3. Prove `ind_cpad_sim_decrypt_to_ind_cpa_reduction_linked_ae` at
   `same_game_result_opt`.
4. Replace `noise_flooding_message_gaussian_kl` with smaller reusable
   geometric/probabilistic ingredients.
