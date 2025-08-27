# Mending: Proof that "Noise Flooding" Fixed the "LM" Bug

The ["LM" security vulnerability](https://ia.cr/2020/1533) in homomorphic encryptions is mitigated using the "noise flooding" technique.
Using the [Rocq Prover](https://rocq-prover.org/) and the [SSProve](https://github.com/SSProve/ssprove) framework, we verify that this noise-flooding patch is indeed effective.
More concretely, we machine-check the relevant parts of the following papers:
* ["Gaussian Sampling over the Integers: Efficient, Generic, Constant-Time"](https://ia.cr/2017/259)
* ["Securing Approximate Homomorphic Encryption Using Differential Privacy"](https://ia.cr/2022/816)

We are still in the early stage of the project;
there is still a lot of proof engineering to be done.

## Usage

```bash
coq_makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
```
