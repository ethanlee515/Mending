# PythCompile Assumption Cleanup Status

Start time: 2026-06-20T14:58:05+08:00
Last update: 2026-06-20T22:32:13+08:00
Approximate uptime: 454 minutes wall-clock since start; active work was interrupted after about 82 minutes and resumed after laptop restart.

## Current focus

- `PythCompile.v` compiles after a direct `q = 0` diagonal-coupling proof.
- `additiveErrorTvdEqRule` is no longer an assumption of `compileRule`.
- Remaining local assumptions are in the KL/Pinsker path:
  - `Pinsker.total_variation_chi2_bound`
  - `Pinsker.kl_lower_bound_chi2`
  - `ChainPointwise.coordinate_finite_kl_absolute_continuous`
  - `ChainPointwise.kl_integrand_chain_decomp_pointwise`
  - `ChainPointwise.sum_coordinate_log_contribution_prefix_weighted`
  - `log_sum_inequality_partition`
  - `kl_dmargin_fpos_le_fiber_fpos`
- Remaining external/classical assumptions include MathComp/SSProve admitted infinite-sum lemmas (`__admitted__psumB`, `__admitted__interchange_psum`), extensionality/choice/proof-irrelevance axioms, and the ambient `R : realType`.

## Log

- 2026-06-20T14:58:05+08:00: Started pass. Read the bottom of `PythCompile.v`; `compileRule` depends on the local `pythCompileCallsRule` stack and the final `MicciancioWalterRule` bridge.
- 2026-06-20T14:59:43+08:00: Forced build is through the KL/PythSeq dependencies and compiling `ProgramLogics/Ae.v`. Early candidate assumptions are additive-error coupling rules plus KL total-variation support lemmas; external MathComp deprecated admitted lemmas are being left for last.
- 2026-06-20T15:06:08+08:00: Added `diagonalCoupling` in `PythCompile.v` and replaced the `q = 0` TV proof with a direct reflexive `AE_opt` coupling. Rebuild succeeds. `Print Assumptions compileRule` still lists `additiveErrorTvdEqRule`, but now because `MicciancioWalterRule` uses `additiveErrorCompletedOutputHeapTvdEqRule`.
- 2026-06-20T15:07:06+08:00: Final verification for this round: `make -f Makefile.coq theories/ProgramLogics/PythCompile.vo` reports the target is up to date after the successful rebuild. Remaining local work is the maximal-coupling/TV bridge in `ProgramLogics/Ae.v` or a direct replacement inside `MicciancioWalterRule`.
- 2026-06-20T15:10:00+08:00: Resumed after the premature report. Checked the KL chain and Pinsker assumptions; they are substantial analytic/chain-rule facts, not small wrappers. No installed maximal-coupling theorem turned up, so the next attempt is a local overlap/residual construction for the TV-to-coupling bridge.
- 2026-06-20T15:14:17+08:00: Added and compiled real-sum scaffolding in `RealSumExtras.v`: `minr_lel`, `minr_ler`, `summable_minl_nonneg`, and `summable_minr_nonneg`. These are needed for the overlap part of a maximal-coupling construction.
- 2026-06-20T15:20:12+08:00: Added and compiled `overlap_mass`, `isdistr_overlap_mass`, `overlap_distr`, and `overlap_distrE` in `Probability/Ae.v`. This packages the diagonal overlap `min P Q` as a subdistribution for the maximal-coupling proof.
- 2026-06-20T15:25:33+08:00: Added and compiled residual scaffolding in `Probability/Ae.v`: `residual_mass`, pointwise lower/upper bounds, `residual_distr`, and rewrite lemmas. The overlap/residual pieces now both compile.
- 2026-06-20T15:28:12+08:00: Added and compiled `diagonal_overlap` plus its left/right margin lemmas and `coupling_with_loss` wrapper. Next target is the residual-mass equality needed to finish a maximal coupling for completed distributions.
- 2026-06-20T15:32:23+08:00: Forced rebuild of `PythCompile.vo` succeeds. `Print Assumptions compileRule` still has one local program-logic assumption, `additiveErrorTvdEqRule`; the new overlap pieces are scaffolding but not yet wired into `MicciancioWalterRule`.
- 2026-06-20T15:35:02+08:00: Added and compiled residual-weight algebra in `Probability/Ae.v`: overlap symmetry, residual weight as `dweight P - dweight overlap`, and equality of residual weights when source weights match.
- 2026-06-20T15:45:46+08:00: Added and compiled a reusable `normalize_distr` helper for positive-mass subdistributions, including `dweight_normalize_distr`. This will support constructing the residual product part of a maximal coupling.
- 2026-06-20T15:48:38+08:00: Added and compiled `residual_product`, `dlet_const_kernelE`, and exact left/right margin lemmas for the residual product. The right margin uses equal residual weights plus positive residual mass.
- 2026-06-20T15:53:30+08:00: Added and compiled `distr_plus` plus weight-accounting lemmas for `diagonal_overlap`, `residual_product`, and overlap-plus-residual mass. Next assembly step is combining overlap and residual product into a full coupling, with a separate zero-residual branch.
- 2026-06-20T15:54:52+08:00: Target rebuild `make -f Makefile.coq theories/ProgramLogics/PythCompile.vo` succeeds after the scaffolding. `Print Assumptions compileRule` remains unchanged at the top level: the remaining local item is still `additiveErrorTvdEqRule`.
- 2026-06-20T15:58:10+08:00: Added and compiled `dmargin_distr_plus` and positive-residual combined-coupling margin lemmas. In the positive residual case, `distr_plus diagonal_overlap residual_product` has exact left/right marginals.
- 2026-06-20T15:59:07+08:00: Added and compiled zero-residual margin lemmas. Diagonal overlap alone has exact marginals when the residual mass is zero. Remaining hard piece is the TV identity/success-probability bound needed to replace `additiveErrorTvdEqRule`.
- 2026-06-20T16:07:19+08:00: Added and compiled the TV/overlap bridge and a probability-side `maximal_coupling_total_variation` lemma. Next interface issue: `MicciancioWalterRule` supplies TV for packed `complete_output_heap`, while `AE_opt` needs original `complete` outputs, so I am adding a decode/marginal bridge in `OutputHeap.v`.
- 2026-06-20T16:20:21+08:00: Full target rebuild of `theories/ProgramLogics/PythCompile.vo` completed. `Print Assumptions compileRule` no longer depends on the q=0 TV bridge, but still lists local `additiveErrorTvdEqRule` through `MicciancioWalterRule`; next attempt is a narrower TV-transfer lemma from packed `complete_output_heap` back to original `complete`.
- 2026-06-20T22:30:19+08:00: After automatic resume, added and compiled `total_variation_complete_output_heap`, then rewrote `additiveErrorCompletedOutputHeapTvdEqRule` to construct its coupling via `maximal_coupling_total_variation` instead of the admitted `additiveErrorTvdEqRule`. `make -f Makefile.coq theories/ProgramLogics/PythCompile.vo` succeeds, and `Print Assumptions compileRule` no longer lists `additiveErrorTvdEqRule`.
- 2026-06-20T22:31:03+08:00: Refreshed the remaining-assumption map. The assumption frontier is now the KL/Pinsker chain and log-sum support facts; unrelated admitted program-logic rules still exist in `ProgramLogics/Ae.v`, but they are not in `Print Assumptions compileRule`.
- 2026-06-20T22:32:13+08:00: Added the same remaining-assumption map as a source comment immediately above `Print Assumptions compileRule` in `PythCompile.v`. Rebuilt `theories/ProgramLogics/PythCompile.vo`; it succeeds and the printed assumption list matches the documented frontier.
