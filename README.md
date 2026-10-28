# Mending: Verifying Noise-Flooding Security

This repository is the formal artifact for **Verified Pythagorean Composition
for Adaptive Cryptographic Games: Noise Flooding in Homomorphic Encryption**,
accepted at **CSF 2027**. We are preparing the camera-ready artifact and paper.
The manuscript lives in the [Pythagorean-RHL](Pythagorean-RHL/) Git submodule;
see its [README](Pythagorean-RHL/README.md) for conference and arXiv builds.
Both formats include named authors, affiliations, artifact links, and funding.
There is no anonymous/camera-ready switch.

Mending is a Rocq/SSProve formalization of the noise-flooding countermeasure
for approximate homomorphic encryption.  The formalization is motivated by the
LM attack on approximate FHE and the LMSS noise-flooding defense:

* ["Gaussian Sampling over the Integers: Efficient, Generic, Constant-Time"](https://ia.cr/2017/259)
* ["Securing Approximate Homomorphic Encryption Using Differential Privacy"](https://ia.cr/2022/816)

The current development proves the main noise-flooding reduction theorem for
an abstract approximate FHE scheme with an origin-centered local
integer-vector metric interface.  The theorem `is_secure` lives in
`theories/Security/NoiseFloodingSecurity/Final.v`, in the functor
`NoiseFloodingSecure`.  It bounds the IND-CPAD adversary's probability
of guessing the hidden challenge bit by the supplied IND-CPA security bound
for a concrete reduction plus the verified noise-flooding loss.  The only
nonzero hybrid loss is the compiler/Micciancio-Walter replacement of the
first `q` decrypt calls, with completed-output additive error
`sqrt(q * epsilon_nf / 2)`; the final winning-probability bound uses this
compile distance directly.

## Verified Result

The checked result is a conditional reduction, parameterized by:

* an abstract approximate-FHE scheme with deterministic base decryption;
* support-level correctness (bad key, encryption, and evaluation outputs have
  probability zero);
* an origin-centered local integer-vector chart for the plaintext metric;
* a supplied IND-CPA security theorem and a positive flooding multiplier.

Over this interface, Rocq checks the adaptive game transformation, the
single-call discrete-Gaussian KL argument, the trace-compiled replacement of
the first <code>q</code> decrypt calls, all exact package bridges, and the
final IND-CPAD-to-IND-CPA inequality.

## Specification Audit Size

The formal-interface selection in [Appendix E](Pythagorean-RHL/appendix-formal-interface-excerpts.tex)
contains **732 physical Rocq source lines**, including **259 lines of miscellaneous
helpers**. The first table matches the slide summary; the second breaks down
its helper row with exact source ranges. Blank and comment lines count;
typeset wrapping does not. The second table’s total is already included in
the first.

This selection includes local specification dependencies and the main theorem
statement. It stops at Rocq, MathComp, and SSProve primitives on the trust side,
and excludes checked proof bodies and proof-only intermediate games. Running-time
analysis inspects the counted reduction and its primitives separately.

Regenerate the tables below from the appendix's disjoint listing ranges with:

```bash
make -C Pythagorean-RHL refresh-formal-excerpts
python3 Pythagorean-RHL/scripts/count-interface-excerpts.py --detailed
```

<!-- BEGIN GENERATED SPECIFICATION AUDIT -->
| Specification | Source lines |
|---|---:|
| Scheme / charts / correctness | 91 |
| Gaussian / sampler bridge | 56 |
| Security games | 175 |
| Flooded construction | 45 |
| Concrete reduction | 95 |
| Loss / reduction validity | 11 |
| Misc. helpers | 259 |
| **Total** | **732** |

39 non-overlapping excerpts across 16 source files.

Miscellaneous helpers (source ranges are inclusive, relative to `theories/`):

| Helper group | Source | Ranges | Source lines |
|---|---|---|---:|
| Scheme labels and package wrapper | [ApproxFHE.v](theories/Schemes/ApproxFHE.v) | 20–24, 53–99 | 52 |
| Vector norm, zero, subtraction, and distance | [IntVec.v](theories/Schemes/Utils/IntVec.v) | 10–14, 48–49, 88–89 | 9 |
| Safe table indexing (`nth_valid`) | [ListExtras.v](theories/LibExtras/MathcompExtras/ListExtras.v) | 7–13 | 7 |
| SSProve vector type (`chVec`) | [ChoiceVector.v](theories/LibExtras/SSProveExtras/ChoiceVector.v) | 16–20 | 5 |
| IND-CPA labels, locations, and interfaces | [Indcpa.v](theories/Schemes/Indcpa.v) | 17–52 | 36 |
| IND-CPAD labels, locations, and interfaces | [Indcpad.v](theories/Schemes/Indcpad.v) | 19–65, 135–137 | 50 |
| Simulator interfaces, vector conversions, and location wrapper | [IndcpadSimulator.v](theories/Security/IndcpadSimulator.v) | 36–99, 321–322 | 66 |
| KL divergence definition | [Core.v](theories/Probability/KL/Core.v) | 20–21 | 2 |
| Theorem parameters, reduction/bound wrappers, and main theorem | [Final.v](theories/Security/NoiseFloodingSecurity/Final.v) | 42–48, 523–534, 1954–1957 | 23 |
| Game and simulator module aliases | [GaussianBasics.v](theories/Security/NoiseFloodingSecurity/GaussianBasics.v) | 256–257 | 2 |
| Noise-flooding security result interface | [Prelude.v](theories/Security/NoiseFloodingSecurity/Prelude.v) | 47–53 | 7 |
| **Total misc. helpers** | | | **259** |
<!-- END GENERATED SPECIFICATION AUDIT -->

## Setup

This repository uses Rocq 9.0.1, MathComp 2.6.0, MathComp Analysis and
experimental reals 1.18.0, and SSProve's `main` branch. The repository-local
[`mending.opam`](mending.opam) records the direct dependency versions and the
SSProve branch pin. MathComp 2.6 supplies the ring tactic; the separate
`coq-mathcomp-algebra-tactics` package is no longer needed.
The sources explicitly retain SSReflect's previous rewrite subgoal order
with `Set SsrOldRewriteGoalsOrder.` while using the new library APIs.

From a fresh opam switch, install the dependencies and check the complete
artifact with:

```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update
opam pin add . --no-action
opam install mending --jobs=4
```

For example, a completely fresh switch can be created first with
`opam switch create mending 5.4.1`, followed by
`eval "$(opam env --switch=mending)"`. Four parallel jobs limit memory use.
The development package is named `rocq-ssprove`.

Use the `rocq-released` and `default` package repositories. If the switch also
selects `rocq-extra-dev`, run `opam repository remove rocq-extra-dev` in that
switch before upgrading, so other dependencies resolve to released packages.

To upgrade an existing switch that still pins the old SSProve commit, repin
it explicitly before installing the updated artifact:

```bash
opam update
opam pin add rocq-ssprove git+https://github.com/SSProve/ssprove.git#main --no-action
opam pin add . --no-action
opam install mending --jobs=4
```

## Upstream Dependencies

[SSProve PR #124](https://github.com/SSProve/ssprove/pull/124) was merged on
October 20, 2026, enabling the released MathComp 2.6 / Analysis 1.18.0 stack.
The compatible released dependencies include Extructures 0.6.0 and word 3.5.
Analysis 1.18.0 includes our summation proofs from
[math-comp/analysis#2007](https://github.com/math-comp/analysis/pull/2007),
including `interchange_psum`; SSProve's semantics now uses that proved theorem.
The artifact also uses the proved upstream `psumB`. Local summation proofs
and duplicate distribution/monad compatibility wrappers have been removed in
favor of upstream results.

SSProve tracks `main`, so its branch pin can advance when refreshed with
`opam update`. For reproducibility, the revision used for this upgrade is
`9a37fe0ab79d041f8d835e6cf18e37614b16a791`. To select that snapshot after
pinning this repository, run:

```bash
opam pin add rocq-ssprove git+https://github.com/SSProve/ssprove.git#9a37fe0ab79d041f8d835e6cf18e37614b16a791 --no-action
opam install mending --jobs=4
```

After advancing dependencies, rebuild the complete artifact and rerun
`Print Assumptions is_secure` before updating the paper's trusted-base claims.
Keep dependency and trusted-base descriptions synchronized with the manuscript
submodule, preserving its public, named-author configuration.

## Usage

Generate the Rocq makefile and build the development:

```bash
rocq makefile -f _RocqProject -o Makefile.rocq
make -f Makefile.rocq -j4
```

After changing dependencies, run `make -f Makefile.rocq clean` before the
build to discard compiled files from the previous stack.

To inspect the theorem assumptions in their definition context, open
[`theories/Security/NoiseFloodingSecurity/Final.v`](theories/Security/NoiseFloodingSecurity/Final.v)
and temporarily add the following command immediately before the final
`End NoiseFloodingSecure.`:

```coq
Print Assumptions is_secure.
```

Then process the file in a Rocq editor or rebuild it to display the audit.
Keeping the command inside the functor avoids introducing a setup-dependent
probe module merely to give the instantiated theorem a name.

## Repository Map

Core scheme and game definitions:

* `theories/Schemes/ApproxFHE.v` defines the abstract approximate-FHE scheme
  interface, the message metric/chart interface, and the correctness
  assumptions used by the theorem.
* `theories/Constructions/NoiseFlooding.v` defines the noise-flooded
  construction.
* `theories/Schemes/Indcpa.v` and `theories/Schemes/Indcpad.v` define the
  IND-CPA and IND-CPAD games.
* `theories/Security/IndcpadSimulator.v` defines the simulated-decryption
  reduction components used in the endpoint game.
* `theories/Security/NoiseFloodingSecurity/` contains the security proof:
  `Prelude.v` for global loss helpers and glue,
  `GaussianBasics.v` for vector-Gaussian and one-call decrypt facts,
  `OracleSetup.v` for oracle packages and invariants,
  `OperationBridges.v` for encrypt/eval/decrypt endpoint bridges,
  `DecryptCompiler.v` for bounded decrypt replacement and compiler lifting,
  `GameReduction.v` for game factoring and reduction state relations, and
  `Final.v` for final composition and `is_secure`.

Program logics and compiler:

* `theories/ProgramLogics/Hoare.v` contains ordinary Hoare-style rules for
  deterministic and probabilistic package code.
* `theories/ProgramLogics/Ae.v` contains the additive-error relational logic
  over completed output distributions.
* `theories/ProgramLogics/Pyth.v` contains the Pythagorean/KL relational
  judgment and the bridge to additive error.
* `theories/ProgramLogics/PythCompile.v` contains the trace compiler and the
  oracle-replacement theorems used to lift one-call decrypt replacement to the
  first `q` selected oracle calls.

Probability and analysis:

* `theories/Probability/KL/` contains the KL, Pinsker, and Pythagorean
  probability facts.
* `theories/Probability/DiscreteGaussians/` contains the discrete-Gaussian
  analysis.
* `theories/Security/NoiseFloodingSecurity/GaussianBasics.v` packages the
  vector-Gaussian facts used by noise flooding.
* `theories/Probability/OutputHeap.v` and `theories/Probability/PythSeq.v`
  contain the completed-output and trace-sequencing infrastructure.
* `theories/LibExtras/` contains local MathComp and SSProve helper lemmas.

## Assumption Audit

The complete artifact was rebuilt and audited on October 28, 2026 with the
SSProve revision recorded above. Running `Print Assumptions is_secure` inside
`NoiseFloodingSecure` reports:

* MathComp's propositional extensionality, dependent functional extensionality,
  and constructive indefinite description;
* SSProve's abstract real type `R`;
* abstract scheme and correctness assumptions, including
  `deterministic_dec_correct`;
* the assumed IND-CPA security theorem for the underlying scheme;
* the abstract metric/chart assumptions from `ApproxFheMetric`;
* positivity of the Gaussian width multiplier.

The upgraded dependency stack proves `realsum.interchange_psum`; the former
`realsum.__admitted__interchange_psum` is only a deprecated parsing alias.
The rebuilt top-level audit contains no `__admitted__` entries. The upstream
summation theorem can also be inspected directly:

```coq
From mathcomp Require Import realsum.
Print Assumptions interchange_psum.
```

## Metric and Correctness Interface

The theorem-facing chart interface is the origin-centered one:

```text
I_a(a) = 0
metric a b = ivec_dist 0 (I_a(b))
J_a(0) = a
metric a (J_a(v)) <= max_norm v
J_b(v) = J_a(v + I_a(b))
```

This is the abstract version of the modular-representative story used for
lattice plaintext spaces. Here `J_a` is `inverse_isometry a`. The laws imply
`J_a(I_a(b)) = b`, proved by `inverse_isometry_isometry`; the reverse round
trip is not required, since integer vectors can wrap in a finite message
space. The zero-displacement and displacement-bound laws specify flooding's
meaning; the security comparison uses centering, distance, and translation.

`NoiseFlooding.decrypt` samples independent centered discrete Gaussians and
pushes the resulting vector through `J_a`, where `a` is base decryption's
output. `GaussianBasics.v` proves this exact output law in
`noise_flooding_decrypt_some_centered`, and expresses the simulator's output
as a shifted Gaussian in the same chart in `simulator_decrypt_noise_one_chart`.
These equalities feed the one-call Pythagorean comparison and the adaptive
compiler hop (the paper's `H2 -> H3`). `Tail.v` supplies auxiliary scalar
Gaussian tail bounds that may support future concrete correctness analyses;
the security hop uses KL bounds on the full distributions and does not depend
on those tail bounds.

The abstract scheme keeps decryption distribution-valued:

```coq
decrypt : sk_t -> ciphertext -> distr R message
```

Correctness and metric reasoning use a pure center:

```coq
deterministic_dec : sk_t -> ciphertext -> message
```

The assumption `deterministic_dec_correct` states that `decrypt sk c` is the
point mass at `deterministic_dec sk c`.  A concrete deterministic scheme can
discharge it by defining `decrypt sk c := dunit (deterministic_dec sk c)`.
