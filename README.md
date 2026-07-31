# Mending: Verifying Noise-Flooding Security

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

## Setup

This repository is intended for users who already have some Rocq/opam
experience.  The submission snapshot has been checked with Rocq 9.0.1,
MathComp Analysis 1.16.0, MathComp algebra tactics 1.2.7, and the SSProve
development version at commit
`c6d7d4bc3a0a671c92899aa49dfcfb065d1bdbbd`.

The repository-local [`mending.opam`](mending.opam) records those versions and
pins the exact SSProve commit.  From a fresh opam switch, install the
dependencies and check the complete artifact with:

```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update
opam pin add . --no-action
opam install mending
```

For example, a completely fresh switch can be created first with
`opam switch create mending 5.4.1`, followed by
`eval "$(opam env --switch=mending)"`.  On memory-constrained machines,
`opam install mending --jobs=4` avoids opam using every visible CPU.
The released SSProve package still uses the transitional name `coq-ssprove`;
the pinned development package used here is named `rocq-ssprove`.

## Usage

Generate the Rocq makefile and build the development:

```bash
rocq makefile -f _RocqProject -o Makefile.rocq
make -f Makefile.rocq -j4
```

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

In a fresh switch on the authors' machine, a clean build of the complete
artifact took about six minutes using four parallel jobs.  This is a
reproduction aid, not a performance claim.

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

Running `Print Assumptions is_secure` inside `NoiseFloodingSecure` is expected
to mention:

* foundational real-number and classical axioms from the underlying libraries;
* the current SSProve/MathComp real-summation residue
  `realsum.__admitted__interchange_psum`;
* abstract scheme and correctness assumptions, including
  `deterministic_dec_correct`;
* the assumed IND-CPA security theorem for the underlying scheme;
* the abstract metric/chart assumptions from `ApproxFheMetric`.

The `interchange_psum` entry is inherited through the installed
SSProve/MathComp program semantics.  This repository also proves that statement
as `interchange_psum_proved` in
`theories/LibExtras/MathcompExtras/RealSumExtras.v`.

Reviewers can check the local replacement directly with:

```coq
From Mending.LibExtras.MathcompExtras Require Import RealSumExtras.
Print Assumptions interchange_psum_proved.
```

## Metric and Correctness Interface

The theorem-facing chart interface is the origin-centered one:

```text
I_a(a) = 0
metric a b = ivec_dist 0 (I_a(b))
I_b^{-1}(x) = I_a^{-1}(x + I_a(b))
```

This is the abstract version of the modular-representative story used for
lattice plaintext spaces.

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
