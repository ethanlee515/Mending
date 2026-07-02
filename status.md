# Noise-Flooding Security Status

This is the short resume note for the current formalization state.

## Build State

- The project has reached a valid state again; Ethan reported a clean rebuild
  succeeds after the latest proof work.
- The last lightweight checks run during cleanup were:

  ```sh
  rocq c -Q theories Mending theories/LibExtras/SSProveExtras/NominalExtras.v
  make -f Makefile.coq theories/LibExtras/SSProveExtras/NominalExtras.vo TIMED=1
  rocq c -Q theories Mending -vos theories/Security/NoiseFloodingSecurity.v
  git diff --check
  ```

## Main Result Shape

The intended security loss is still:

```coq
security_loss max_queries =
  2 * sqrt ((max_queries * (dim / (2 * gaussian_width_multiplier^2))) / 2)
```

The compile step uses:

```coq
compile_security_error max_queries = security_loss max_queries / 2
```

The key remaining theorem is still admitted:

```coq
ind_cpa_reduction_additive_error_from_compile
```

This is the bridge from the currently proved one-call/factored decrypt work to
the full IND-CPA reduction endpoint.

## Current Formal Ingredients

- `ApproxCorrectnessPerfect` is the active correctness assumption in
  `NoiseFloodingSecure`.  It gives exact support-level correctness for
  keygen/encrypt/eval, separate from the original probabilistic
  `ApproxCorrectness` interface.

- The real and simulated IND-CPAD oracles enforce a decryption counter.
  `max_queries` bounds actual decrypt calls, not merely table growth.

- The first closed decrypt-hybrid oracle exists:

  ```coq
  IndCpadSimDecryptOracle
  ```

  It keeps real encrypt/eval behavior and replaces only `oracle_decrypt` with
  the simulator plaintext/noise response.

- The heap invariant is:

  ```coq
  challenge_heap_valid
  ```

  It reads the challenge bit, keys, and table from the heap; rejects partial key
  states; requires `good_keys` when keys are initialized; and requires every row
  to be valid for the selected challenge branch plaintext.

- The main support/preservation atoms are proved:
  `challenge_heap_valid_*_initialized`,
  `challenge_heap_valid_set_decrypt_count`,
  `challenge_heap_valid_set_table_encrypt`,
  `challenge_heap_valid_set_table_eval1`,
  `challenge_heap_valid_set_table_eval2`,
  and the real/sim package preservation facts except decrypt.

- The decrypt oracle has been factored into:
  `ind_cpad_decrypt_prefix_code`,
  `ind_cpad_real_decrypt_cont`,
  and `ind_cpad_sim_decrypt_cont`.

- The concrete one-call decrypt replacement is proved in short form:

  ```coq
  ind_cpad_decrypt_code_pyth_short
  ind_cpad_decrypt_resolve_pyth_short
  ind_cpad_decrypt_resolve_additive_error_short
  ```

  The current Pythagorean loss shape is `[0; eps]`; the leading zero is from
  the shared deterministic decrypt prefix.

- The specialized compile bridge under `challenge_heap_valid` exists:

  ```coq
  ind_cpad_compiled_decrypt_replacement_from_compile_challenge_heap_valid
  ```

  It still has a separation side condition that is impossible for the original
  open challenger shape, motivating the open-guess factoring route.

- The open-guess factoring support now exists:
  `ind_cpad_moved_adversary`,
  `ind_cpad_open_guess_code`,
  `ind_cpad_moved_adversary_separate`,
  and `ind_cpad_open_guess_code_valid`.

- Generic SSProve nominal helpers were moved into:

  ```coq
  theories/LibExtras/SSProveExtras/NominalExtras.v
  ```

  The important helpers are:
  `moved_package_valid`,
  `moved_resolve_bind_valid`,
  and `moved_resolve_ret_valid`.

## Gaussian/Chart State

- The shifted tuple Gaussian development is in place, including
  `n_dg_shifted`, mass-one facts, and product Pythagorean bounds.

- The successful decrypt branch is connected to raw oracle code:
  `noise_flooding_successful_decrypt_code_pyth` and
  `noise_flooding_successful_decrypt_code_pyth1`.

- The exact-center chart case is axiom-free:

  ```coq
  noise_flooding_message_gaussian_kl_refl
  noise_flooding_message_gaussian_pythDist_refl
  ```

- The metric-to-vector-distance side of local chart reasoning is proved:

  ```coq
  local_chart_metric_to_ivec_dist
  local_chart_center_metric_to_ivec_dist
  noise_flooding_vector_pythDist_from_metric_chart
  ```

- The remaining explicit axiom is:

  ```coq
  noise_flooding_message_gaussian_kl
  ```

  It bundles the chart-change/data-processing claim for nearby distinct charts.
  The likely replacement is deterministic KL data processing for `dmargin`,
  plus domain-specific global chart translation assumptions.

## Library Helpers Added

- `ListExtras.v`:

  ```coq
  nth_valid_irrel
  ```

- `Hoare.v`:

  ```coq
  Pr_code_bind_assertD
  ```

- Whole-game AE/TV composition infrastructure exists for later endpoint
  composition:
  `total_variation_triangle`,
  `additiveErrorOptSameOutputTvdEqRule`,
  `additiveErrorOptSameOutputTvBound`,
  and `additiveErrorOptSameOutputTriangleRule`.

## Cleanup Notes

- The encrypt/eval oracles still assert:

  ```coq
  length updated_table <= max_queries
  ```

  This appears conceptually extraneous for the current reduction, because the
  security accounting is driven by the decrypt counter.  Do not remove only the
  source assertions in `Indcpad.v`: the simulator mirror in
  `IndcpadSimulator.v`, explicit raw-code copies in `NoiseFloodingSecurity.v`,
  bridge lemmas, and preservation proofs must be updated together.

## Next Work

1. Finish the open-guess factoring route.

   The goal is to initialize the challenge heap first, prove
   `challenge_heap_valid`, then apply `compileRule` only to the moved
   adversary's `guess` body.  In that shape, the invariant may depend on
   `IndCpadGame.oracle_mem_spec`, while the open code locations are those of
   `ind_cpad_moved_adversary A`, separated by
   `ind_cpad_moved_adversary_separate`.

2. Generalize or adapt the compile bridge if needed.

   The current invariant-parametric bridge requires the invariant locations to
   be separate from the open code.  The original challenger violates this; the
   factored open-guess program is the intended workaround.

3. Prove the endpoint game-identification chain.

   The named programs already exist:
   `ind_cpad_game_code`,
   `ind_cpad_linked_real_game_code`,
   `ind_cpad_compiled_real_game_code`,
   `ind_cpad_compiled_sim_decrypt_game_code`,
   `ind_cpad_compiled_sim_decrypt_self_link_game_code`,
   `ind_cpad_linked_sim_decrypt_game_code`,
   `ind_cpad_sim_decrypt_game_code`,
   `ind_cpa_reduction_open_game_code`,
   `ind_cpa_reduction_linked_game_code`,
   and `ind_cpa_reduction_game_code`.

   The remaining exact/zero-error equivalences are mainly:
   - replace the real-oracle link in the compiled sim-decrypt game by the
     sim-decrypt self-link;
   - identify the closed sim-decrypt IND-CPAD game with the existing IND-CPA
     reduction presentation;
   - compose those exact steps with the nonzero compile-rule step.

4. Replace `noise_flooding_message_gaussian_kl`.

   Prove or assume smaller, reusable geometric/probabilistic ingredients:
   origin-centered charts, global chart translation, and KL data processing for
   deterministic `dmargin`.

5. Later cleanup: remove the table-length asserts coherently if desired.
