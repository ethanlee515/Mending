# Mending: Verifying Noise-Flooding Security

The ["LM" security vulnerability](https://ia.cr/2020/1533) in homomorphic encryptions is mitigated using the "noise flooding" technique.
Using the [Rocq Prover](https://rocq-prover.org/) and the [SSProve](https://github.com/SSProve/ssprove) framework, we formally verify that this noise-flooding patch is indeed effective.
Specifically, we machine-check the relevant parts of the following papers:
* ["Gaussian Sampling over the Integers: Efficient, Generic, Constant-Time"](https://ia.cr/2017/259)
* ["Securing Approximate Homomorphic Encryption Using Differential Privacy"](https://ia.cr/2022/816)

The current development proves the main noise-flooding reduction theorem for an
abstract approximate FHE scheme with an origin-centered local integer-vector
metric interface.  After instantiating the security functor, the public theorem
is:

```coq
Secure.is_secure
```

in `theories/Security/NoiseFloodingSecurity/Final.v`.

The theorem says that IND-CPAD security of the noise-flooded scheme is bounded
by IND-CPA security of the underlying scheme plus the noise-flooding loss.  The
only nonzero game-hop loss is the compiler/Micciancio-Walter replacement of the
first `q` decrypt calls, with completed-output additive error
`sqrt(q * epsilon_nf / 2)`; the final winning-probability bound uses twice this
compile distance.

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
* `theories/Security/NoiseFloodingSecurity/` contains the security proof split
  into chunks:
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
* `theories/Security/GaussianVector.v` packages the vector Gaussian facts used
  by noise flooding.
* `theories/Probability/OutputHeap.v` and `theories/Probability/PythSeq.v`
  contain the completed-output and trace-sequencing infrastructure.
* `theories/LibExtras/` contains local MathComp and SSProve helper lemmas.

Paper draft:

* `Pythagorean-RHL/` contains the accompanying paper draft.  Section 4
  describes the program logic, and the LMSS/noise-flooding section summarizes
  the game-hop proof around the instantiated `Secure.is_secure` theorem.

## Assumption Shape

`Print Assumptions Secure.is_secure` is expected to mention:

* foundational real-number/classical axioms from the underlying libraries;
* the current SSProve/MathComp real-summation residue
  `realsum.__admitted__interchange_psum`;
* abstract scheme correctness assumptions, including deterministic decryption
  consistency `deterministic_dec_correct`;
* the assumed IND-CPA security bound of the underlying scheme;
* the abstract metric/chart assumptions from `ApproxFheMetric`.

It should not mention the old finite-codomain workaround or the removed optional
chart axioms (`isoK`, `inv_isoK`, `isometry_radius`, `iso_correct`).

The `deterministic_dec_correct` assumption exists because the abstract scheme
interface keeps decryption distribution-valued:

```coq
decrypt : sk_t -> ciphertext -> distr R message
```

while correctness and metric reasoning use a pure deterministic center:

```coq
deterministic_dec : sk_t -> ciphertext -> message
```

`deterministic_dec_correct` states that `decrypt sk c` is the point mass at `deterministic_dec sk c`.  A
concrete deterministic scheme can discharge this assumption by defining
`decrypt sk c := dunit (deterministic_dec sk c)`.

## Setup

Required system packages: `libgmp-dev`, `linux-libc-dev`, `pkg-config`, `git`

Afterwards, run the usual Rocq and SSProve setup:
```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update
opam pin add --no-action rocq-ssprove https://github.com/SSProve/ssprove.git
opam install rocq-prover rocq-ssprove coq-mathcomp-algebra-tactics
```

## Usage

```bash
coq_makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
```

To check only the main security file:

```bash
make -f Makefile.coq theories/Security/NoiseFloodingSecurity/Final.vo
```

To inspect the public theorem in Rocq:

```coq
From Mending.Security.NoiseFloodingSecurity Require Import Final.
From Mending.Schemes Require Import ApproxFHE Indcpa.
From Mending.Constructions Require Import NoiseFlooding.

Module Probe
  (Scheme : ApproxFheScheme)
  (Metric : ApproxFheMetric(Scheme))
  (Correctness : ApproxCorrectnessPerfect(Scheme)(Metric))
  (IndCpaSecurity : IsIndCpa(Scheme))
  (Params : NoiseFloodingParams).
  Module Secure :=
    NoiseFloodingSecure(Scheme)(Metric)(Correctness)(IndCpaSecurity)(Params).
  Print Assumptions Secure.is_secure.
End Probe.
```
