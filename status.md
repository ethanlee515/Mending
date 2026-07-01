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

   The invariant must connect table entries `(m0, m1, c)` to the statement that
   the ciphertext decrypts within its stored error bound, at least in the
   `m0 == m1` case.  The subtlety is that `ApproxCorrectness` currently gives
   encryption/evaluation correctness with high probability, not as a
   support-preserving Hoare invariant.

3. Decide how to account for approximate-correctness failure.

   Likely options:
   - add a separate correctness-failure hybrid/error term, or
   - strengthen/refactor the table invariant or scheme interface so table
     entries carry certified correctness.

   This is the main proof-design decision still open.

4. Prove or justify `noise_flooding_message_gaussian_kl`.

   This may require strengthening `ApproxFheMetric` with a chart-change theorem,
   or adding a domain-specific assumption about the metric/isometry structure.

5. Identify the compiled decrypt-hybrid game with the existing IND-CPA
   reduction game.

   The first compile step now gives a real-vs-closed-decrypt-hybrid relation.
   We still need the semantic factoring/equivalence that connects this hybrid
   to `IndCpaDSim.IndCpaReduction` and then to the IND-CPA security theorem.

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
