# Noise-Flooding Security Status

This is a living summary of the current proof state.  The detailed timestamped
work log has been collapsed into the milestones and TODOs below.

## Current State

The target proof is still not complete, but the query-counting part is no
longer the main obstacle.  The development now has a concrete
`compileRule`-shaped loss:

```coq
security_loss max_queries =
  2 * sqrt ((max_queries * (dim / (2 * gaussian_width_multiplier^2))) / 2)
```

Equivalently, the compile step uses
`compile_security_error max_queries = security_loss max_queries / 2`.

The focused build currently succeeds:

```sh
make -f Makefile.coq theories/Security/NoiseFloodingSecurity.vo
```

## What Is Proved

- The real and simulated IND-CPAD oracles now both enforce a decryption-query
  counter, so `max_queries` bounds actual decryption calls, not only table size.

- The main security reduction has been refactored so the remaining core
  obligation is an `AE_opt` judgment at the exact loss produced by
  `compileRule`.

- The downstream conversion from an `AE_opt` judgment on completed game outputs
  to a total-variation bound on the winning bit is proved.

- Several older probability/vector admits were removed, including vector
  conversion facts and conditional distribution factorization lemmas.

- The simulator's SSProve Gaussian vector sample is now connected to the
  MathComp tuple Gaussian:
  `dmargin_toIntVec_discrete_gaussians_zero`.

- Shifted tuple Gaussians are available via `n_dg_shifted`, with mass-one and
  shift-by-addition lemmas.

- The per-coordinate Gaussian KL budget is proved, and the coordinate budgets
  sum to the per-query loss
  `noise_flooding_per_query_epsilon dim gaussian_width_multiplier`.

- The product-level Pythagorean fact for shifted tuple Gaussians is proved:
  `noise_flooding_vector_pythDist`.

- The real successful decrypt distribution and the simulator successful decrypt
  distribution have both been packaged as shifted-Gaussian marginals.

- Assuming the explicit chart-change principle
  `noise_flooding_message_gaussian_kl`, the one-sample successful decrypt rule
  is proved:
  `noise_flooding_successful_decrypt_sample_pyth`.

- A closed first hybrid oracle has been added:
  `IndCpadSimDecryptOracle`.
  It keeps real encrypt/eval code and replaces only `oracle_decrypt` by the
  simulator's plaintext/noise response.

- The structural side conditions for the first compile step are proved:
  validity of the real and closed decrypt-hybrid oracle packages, membership of
  the selected decrypt signature in the adversary import interface, and validity
  of the open challenger/adversary main code for any valid adversary.

- There is now an invariant-parametric compile bridge:
  `ind_cpad_compiled_decrypt_replacement_from_compile_with_invariant`.
  This is the important `compileRule` harness: once we have the right one-call
  decrypt package judgment under a suitable heap invariant, query counting gives
  the expected `sqrt(q * eps / 2)` additive error.

- A support-level correctness interface now exists:
  `ApproxCorrectnessPerfect`.  It keeps the original probabilistic
  `ApproxCorrectness` interface separate and instead assumes keygen/encrypt/eval
  bad-event probabilities are exactly zero.  It also provides support lemmas:
  `keygen_support_good`, `encrypt_support_underlying`,
  `eval1_support_underlying`, and `eval2_support_underlying`.

- The library now has basic whole-game composition infrastructure for the
  item-5 hybrid chain:
  `total_variation_triangle`,
  `additiveErrorOptSameOutputTvdEqRule`,
  `additiveErrorOptSameOutputTvBound`, and
  `additiveErrorOptSameOutputTriangleRule`.

- The current `NoiseFloodingSecure` functor is now parameterized by
  `ApproxCorrectnessPerfect`, so the formal theorem-in-progress is explicitly
  the support-level correctness version.

- A first concrete heap/table invariant shape is now formalized:
  `challenge_heap_valid`.  It reads the challenge bit, keys, and table from the
  heap, requires `good_keys` once all keys are present, rejects partial key
  states, and requires every table row to be valid for the selected branch
  plaintext.  The branch-selected form is important because eval gates can map
  distinct labels to equal labels later.  Supporting lemmas are proved for
  encrypt/eval table appends and for extracting the decrypt-time validity fact
  from a table lookup.

## Remaining Formal Gaps

There is one remaining `Admitted` in
`theories/Security/NoiseFloodingSecurity.v`:

```coq
ind_cpa_reduction_additive_error_from_compile
```

There is also one explicit axiom:

```coq
noise_flooding_message_gaussian_kl
```

The axiom records a geometric chart-change/data-processing principle that the
current metric interface does not provide: flooding in two nearby message
charts should give KL-close message-space distributions after applying the two
corresponding `inverse_isometry` maps.

## TODO

1. Prove the concrete one-call decrypt package judgment.

   This should sequence through:
   - decryption counter read/check/increment,
   - table lookup,
   - failure/out-of-range cases,
   - `m0 != m1`, where both oracles return `None`,
   - `m0 == m1` with a valid ciphertext, where the successful-decrypt sampling
     lemma supplies the Gaussian/Pythagorean cost.

2. Design the heap invariant needed for the one-call decrypt judgment.

   The current candidate is `challenge_heap_valid`.  Rather than only recording
   validity when `m0 == m1`, it records validity for the selected branch
   plaintext `if b then m1 else m0` for every table row.  This is necessary
   because an eval gate may turn distinct labels into equal labels, and a later
   decrypt query should still be justified.  The invariant now permits either
   the fully initialized key state or the fully uninitialized key state; mixed
   partial key states are rejected.  This matters because `oracle_encrypt`
   only checks that `pk` is present, so allowing `pk` without `evk/sk` would not
   be support-preserved by real encryption.

   Under `ApproxCorrectnessPerfect`, support lemmas now prove that encrypt/eval
   preserve this table invariant:
   `table_valid_for_branch_rcons_encrypt`,
   `table_valid_for_branch_rcons_eval1`, and
   `table_valid_for_branch_rcons_eval2`.  The decrypt case can use
   `table_valid_for_branch_decrypt_row`.

   New wrinkle: the current invariant-parametric `compileRule` bridge requires
   the invariant to depend only on locations `K` that are separate from the open
   main code locations.  But the open IND-CPAD challenger location set includes
   `oracle_mem_spec`, including the bit/key/table locations that
   `challenge_heap_valid` must inspect.  So the invariant itself is now much
   clearer, but we likely need either a slightly more general compile bridge
   that accepts direct preservation of the root initialization code, or a
   refactoring that factors initialization away from the compiled-call region.

   First support for the factoring route is now in code:
   `challenge_initialized_heap`, `challenge_heap_valid_initialized`,
   `challenge_heap_valid_depends_only_on_oracle_mem_spec`,
   `ind_cpad_moved_adversary`, `ind_cpad_open_guess_code`, and
   `ind_cpad_moved_adversary_separate`.

   Heap-level preservation atoms are also now proved:
   `challenge_heap_valid_good_keys`,
   `challenge_heap_valid_table_for_branch`,
   `challenge_heap_valid_decrypt_row`,
   `challenge_heap_valid_set_decrypt_count`,
   `challenge_heap_valid_set_table_encrypt`,
   `challenge_heap_valid_set_table_eval1`, and
   `challenge_heap_valid_set_table_eval2`.  These are the reusable pieces for
   proving that the real encrypt/eval oracle calls preserve
   `challenge_heap_valid` and that a decrypt lookup has the needed certified
   ciphertext validity.

   The Hoare library now has basic sequencing rules:
   `hoareRetRule`, `hoareBindRule`, `hoareGetRule`, `hoarePutRule`, and
   `hoareSampleRule`.  These should make the concrete package-preservation
   proofs less dependent on manual `Pr_code` unrolling.

   A first concrete oracle-body preservation proof is checked:
   `ind_cpad_real_encrypt_code` is an explicit raw-code copy of the real
   encryption oracle body, and
   `ind_cpad_real_encrypt_code_preserves_challenge_heap_valid` proves that it
   preserves `challenge_heap_valid`.

   Remaining item-2 engineering: connect the explicit raw-code body to the
   package `resolve` form, and repeat the same style for eval1/eval2.  A first
   eval1 attempt exposed annoying dependent-assert plumbing around
   `#assert (r < length table) as r_in_range`; do not spend time on broad
   automation there.  A better path is either a small lemma for support through
   dependent asserts, or an explicit body lemma stated in terms of the already
   proved heap atom `challenge_heap_valid_set_table_eval1`.

   The intended shape is to initialize the challenge heap first, prove
   `challenge_heap_valid` from keygen support, and then apply `compileRule` only
   to the moved adversary's `guess` body.  In that factored body, the invariant
   can depend on `IndCpadGame.oracle_mem_spec`, while the open code locations
   are those of `ind_cpad_moved_adversary A`, separated by
   `ind_cpad_moved_adversary_separate`.

   Caution: a first attempt at proving `ind_cpad_open_guess_code_valid` by
   direct SSProve validity/typeclass search made the focused build appear to
   hang.  The lemma was not kept.  Reintroduce it with a more explicit proof,
   not with broad `typeclasses eauto`.

3. Keep correctness accounting separated.

   Important caveat: literally setting `p_gate_error = 0` in the current
   `ApproxCorrectness` interface is not the right move, because the axioms use
   strict inequalities such as `Pr[bad] < p_gate_error`.  With
   `p_gate_error = 0`, this would require a nonnegative probability to be
   strictly negative.

   The chosen near-term strategy is now represented in code by the separate
   interface `ApproxCorrectnessPerfect`, whose keygen/encrypt/eval correctness
   axioms say the bad-event probability is exactly `0`.  The current
   `NoiseFloodingSecure` functor imports this interface directly.  This is a
   stronger, support-level correctness assumption, not a weakening of
   approximate correctness.

   Under `ApproxCorrectnessPerfect`, item 2 becomes much simpler: the new
   support lemmas say every sampled key/ciphertext/evaluation result is valid.
   The table invariant can then assert directly that every stored ciphertext
   decrypts within its recorded error bound.

   The immediate proof should proceed under `ApproxCorrectnessPerfect`.  The
   later extension back to the original probabilistic `ApproxCorrectness` would
   still require a separate real-to-perfect correctness-error hybrid and an
   added error term.

4. Split and prove/justify `noise_flooding_message_gaussian_kl`.

   Near-term plan: strengthen the metric/isometry interface with the global
   chart laws that are intended for the `Z_q^n`/polynomial quotient setting.
   The useful assumptions are:

   - origin-centered charts:
     `isometry_center0 : forall c, isometry c c = zero_vec`;
   - global chart translation:
     `inverse_isometry b x =
      inverse_isometry a (ivec_add (isometry a b) x)`.

   With origin-centered charts, `iso_correct` gives
   `metric a b = ivec_dist zero_vec (isometry a b)` whenever `b` is in the
   radius of the chart centered at `a`.  So the existing hypothesis
   `metric centerL centerR <= error_bound` gives the coordinate-distance bound
   needed by the already-proved shifted tuple Gaussian KL theorem.

   With global chart translation, the right-chart flooding distribution can be
   rewritten as the pushforward through `inverse_isometry centerL` of a shifted
   tuple Gaussian.  The remaining abstract probability lemma should then be KL
   data processing for deterministic `dmargin`; wrapping modulo `q` is fine
   because pushforward can only decrease KL.  This should replace the current
   bundled axiom by smaller, reusable assumptions/lemmas.

   Caveat for later: if we ever want genuinely local charts rather than global
   quotient charts, the unbounded Gaussian support becomes visible and we will
   need either truncation plus a tail term or a different bundled
   domain-specific assumption.

5. Identify the compiled decrypt-hybrid game with the existing IND-CPA
   reduction game.

   Construction status: the first pass at the missing `progM` chain now exists
   as named Coq constructions.  The remaining gap is no longer simply
   "define the programs"; it is to prove the adjacent exact/zero-error
   equivalences, especially the package-reshaping step that connects the
   simulated-decrypt IND-CPAD game to the existing IND-CPA reduction structure.

   The currently named programs are:
   - `ind_cpad_game_code`: the original real IND-CPAD game,
   - `ind_cpad_linked_real_game_code`: the same game split into open
     challenger/adversary code linked with the real IND-CPAD oracle,
   - `ind_cpad_compiled_real_game_code`: the compiled-call presentation of the
     real game,
   - `ind_cpad_compiled_sim_decrypt_game_code`: the first closed
     decrypt-hybrid produced for `compileRule`,
   - `ind_cpad_compiled_sim_decrypt_self_link_game_code`: the same compiled
     sim-decrypt code linked against the replacement oracle itself,
   - `ind_cpad_linked_sim_decrypt_game_code`: the uncompiled sim-decrypt game,
     still presented as open challenger/adversary code linked with the
     sim-decrypt oracle,
   - `ind_cpad_sim_decrypt_game_code`: the packaged closed sim-decrypt
     IND-CPAD game,
   - `ind_cpa_reduction_open_game_code`: the outer IND-CPA challenger linked
     with the reduction adversary, before closing with the IND-CPA encryption
     oracle,
   - `ind_cpa_reduction_linked_game_code`: the previous program linked with the
     real IND-CPA encryption oracle,
   - `ind_cpa_reduction_game_code`: the existing IND-CPA reduction game.

   The easy presentation equalities are already proved:
   `ind_cpad_game_code_linked`,
   `ind_cpad_compiled_real_linked_correct`,
   `ind_cpad_compiled_sim_decrypt_self_link_correct`,
   `ind_cpad_sim_decrypt_game_code_linked`, and
   `ind_cpa_reduction_game_code_linked`.

   The remaining adjacent equivalences are more substantial:
   - replace the real-oracle link in
     `ind_cpad_compiled_sim_decrypt_game_code` by the sim-decrypt self-link,
     using the fact that the two packages agree on encrypt/eval, and that any
     decrypt call left after compiling `max_queries` calls should be invalid on
     both sides because the decryption counter has already reached the bound;
   - identify `ind_cpad_sim_decrypt_game_code` with the reduction-shaped
     presentation, accounting for the ready flag, simulator key locations,
     freshening/renaming, and the fact that direct real encryption is replaced
     by calls to the enclosing IND-CPA encryption oracle;
   - compose these exact steps with the nonzero compile-rule step and then
     apply the IND-CPA security theorem to the right endpoint.

   The reusable same-output composition lemma now exists for the main case we
   expect to need:

   ```coq
   additiveErrorOptSameOutputTriangleRule
   ```

   It composes two `AE_opt` judgments with the same completed-output equality
   postcondition and adds their errors, assuming the precondition identifies the
   middle input and heap on both sides.  For final game identification, equality
   of final heaps may still be too strong because the games use different
   bookkeeping locations; equality of the sampled output bit, or equality after
   a heap projection/canonicalization, is probably the right postcondition.

6. Revisit the final bound after correctness accounting is settled.

   The current flooding/compile contribution is clear, but the final theorem may
   need an additional approximate-correctness error term unless support-level
   correctness is assumed.

## Conceptual Assessment

We are not stuck on query counting.  `compileRule` suffices for that part once
the decrypt call is isolated, and the formal harness for this is now in place.

The remaining work is partly proof engineering and partly proof design.  The
engineering pieces are the SSProve sequencing, invariant preservation, and
package equivalences.  The conceptual pieces are the chart-change principle and
the treatment of approximate-correctness failure.
