# KL

KL-divergence definitions and probability bounds.

- `Core.v` contains the KL definition, absolute continuity, and basic KL facts.
- `Conditional.v` contains KL facts about conditional distributions, the KL
  chain rule, and the iterated chain-rule bound. Basic conditional-distribution
  infrastructure lives in `LibExtras/MathcompExtras/DistrExtras.v`.
- `Pinsker.v` contains Pinsker and its chi-square/TV support lemmas.
- `Pyth.v` contains the Pythagorean probability-preservation theorem, the
  higher-level Pythagorean distribution judgments, and composition lemmas used
  by the program logic.
