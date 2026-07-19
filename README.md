# Mending: Verifying Noise-Flooding Security

Mending is a Rocq/SSProve formalization of the noise-flooding countermeasure
for approximate homomorphic encryption.  The formalization is motivated by the
LM attack on approximate FHE and the Li-Micciancio-style noise-flooding
defense:

* ["Gaussian Sampling over the Integers: Efficient, Generic, Constant-Time"](https://ia.cr/2017/259)
* ["Securing Approximate Homomorphic Encryption Using Differential Privacy"](https://ia.cr/2022/816)

The current development proves the main noise-flooding reduction theorem for
an abstract approximate FHE scheme with an origin-centered local
integer-vector metric interface.  After applying the security functor, the
main theorem is conventionally referred to as:

```coq
Secure.is_secure
```

The theorem lives in `theories/Security/NoiseFloodingSecurity/Final.v`, in the
functor `NoiseFloodingSecure`.  It bounds the IND-CPAD adversary's probability
of guessing the hidden challenge bit by the supplied IND-CPA security bound
for a concrete reduction plus the verified noise-flooding loss.  The only
nonzero hybrid loss is the compiler/Micciancio-Walter replacement of the
first `q` decrypt calls, with completed-output additive error
`sqrt(q * epsilon_nf / 2)`; the final winning-probability bound uses this
compile distance directly.

## Setup

This repository is intended for users who already have some Rocq/opam
experience.  The development needs SSProve and MathComp, plus the MathComp
algebra tactics package used by the Gaussian arithmetic proofs.
We expect a reasonably recent Rocq installation; the current development has
been checked with Rocq 9.

If you already have a Rocq switch with the following packages, no special
repository-local setup is intended:

```text
rocq-ssprove
coq-mathcomp-algebra-tactics
```

One typical opam setup is:

```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update
opam install rocq-prover rocq-ssprove coq-mathcomp-algebra-tactics
```

Depending on the opam repositories enabled in your switch, some package names
may still use the transitional `coq-` prefix.

## Usage

Generate the Rocq makefile and build the development:

```bash
rocq makefile -f _RocqProject -o Makefile.rocq
make -f Makefile.rocq
```

To check only the main security theorem:

```bash
make -f Makefile.rocq theories/Security/NoiseFloodingSecurity/Final.vo
```

To inspect theorem assumptions, instantiate `NoiseFloodingSecure` with a
scheme, metric interface, correctness proof, IND-CPA security proof, and
noise-flooding parameters, then use Rocq's usual command:

```coq
Print Assumptions Secure.is_secure.
```

The paper draft builds separately:

```bash
make -C Pythagorean-RHL
```

This requires a standard LaTeX setup with XeLaTeX, `latexmk`, and `pygmentize`
for minted code blocks.

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

Paper draft:

* `Pythagorean-RHL/` contains the accompanying paper draft.  Section 4
  describes the program logic, and the noise-flooding section summarizes the
  hybrid proof around the instantiated `Secure.is_secure` theorem.

## Theorem Boundary

At the current milestone, `Print Assumptions` for an instantiated
`Secure.is_secure` is expected to mention:

* foundational real-number and classical axioms from the underlying libraries;
* the current SSProve/MathComp real-summation residue
  `realsum.__admitted__interchange_psum`;
* abstract scheme and correctness assumptions, including
  `deterministic_dec_correct`;
* the assumed IND-CPA security theorem for the underlying scheme;
* the abstract metric/chart assumptions from `ApproxFheMetric`.

It should not mention the old finite-codomain workaround or the removed
optional chart axioms such as `isoK`, `inv_isoK`, `isometry_radius`, and
`iso_correct`.

The remaining `interchange_psum` assumption is inherited through current
SSProve/MathComp program semantics, not through the local KL chain,
maximal-coupling construction, or finite-codomain workaround.

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
