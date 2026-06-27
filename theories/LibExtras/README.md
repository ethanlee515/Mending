# LibExtras

Library-adjacent support code lives here.

- `MathcompExtras/`: extensions and small convenience lemmas for MathComp libraries.
- `SSProveExtras/`: adapters and helpers for expressing project objects inside SSProve.

Files in this directory should avoid depending on schemes, constructions, or security proofs.

## MathComp Analysis upstream notes

The following local lemmas in `MathcompExtras/RealSumExtras.v` are intended as
grafting material for MathComp Analysis:

1. Replace the three admitted lemmas in
   `analysis/experimental_reals/realsum.v` with the local proofs:
   - `__admitted__psumB` from `psumB_proved`
   - `__admitted__interchange_sup` from `interchange_sup_proved`
   - `__admitted__interchange_psum` from `interchange_psum_proved`

2. Once `interchange_psum` is proved upstream, revisit the deprecated
   distribution lemmas in `analysis/experimental_reals/distr.v` whose existing
   proofs currently depend on it:
   - `dlet_dlet`
   - `dlet_dmargin`
   - `dmargin_dlet`
   - `dfst_dswap`
   - `dsnd_dswap`
   - `dsndE`
   - `pr_dlet`

   `pr_dmargin` is not itself deprecated, but its proof uses `pr_dlet`; it
   should become clean as collateral once `pr_dlet` is clean.

Suggested upstream workflow: work from the MathComp Analysis checkout, copy the
proofs from `Mending/theories/LibExtras/MathcompExtras/RealSumExtras.v`, replace
the admitted constants in `experimental_reals/realsum.v`, then remove the
deprecation wrappers/notes for the distribution lemmas above and rebuild the
affected `experimental_reals` files.
