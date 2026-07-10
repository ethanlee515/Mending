# Noise-Flooding Security Status

Compact handoff for the current formalization state.

## Current Result

The main security file builds:

```sh
timeout 600s rocq c -Q theories Mending theories/Security/NoiseFloodingSecurity.v
```

The public theorem is still not `Print Assumptions` clean. The current
remaining `realsum.__admitted__interchange_psum` source is no longer our KL
chain, maximal-coupling construction, or local use of SSProve's
`coupling`/`lmg`/`rmg`.

After migrating the local AE/security coupling layer to pointwise marginals,
focused probes show:

```coq
Print Assumptions clean_coupling.          (* clean, modulo foundations *)
Print Assumptions coupling_bind_kernel.    (* clean, modulo foundations *)
Print Assumptions complete.
Print Assumptions complete_dweight.
Print Assumptions complete_bind.
```

But these are still dirty:

```coq
Print Assumptions raw_code.
Print Assumptions Pr_code.
Print Assumptions raw_package.
Print Assumptions additiveErrorJudgmentOpt.
Print Assumptions additiveErrorOptSeqRule.
Print Assumptions Secure.is_secure.
```

Latest `Print Assumptions Secure.is_secure` grouping:

- External/foundational residue:
  `Axioms.R`, proof irrelevance, propositional extensionality, functional
  extensionality, constructive indefinite description, and
  `realsum.__admitted__interchange_psum`.
- Expected scheme/correctness assumptions:
  the abstract scheme types and algorithms, `keygen_lossless`,
  `dec'_correct`, `keygen_perfect_correct`, `encrypt_perfect_correct`,
  `eval1_perfect_correct`, and `eval2_perfect_correct`.
- Expected reduction assumptions:
  `IndCpaSecurity.security_bound` and `IndCpaSecurity.is_secure`.
- Expected noise-flooding/metric assumptions:
  `Params.gaussian_width_multiplier`, `Params.gt0_gaussian_width_multiplier`,
  `Metric.dim`, `Metric.metric`, `Metric.isometry`,
  `Metric.inverse_isometry`, `Metric.isometry_center0`,
  `Metric.metric_chartE`, and `Metric.inverse_isometry_shift`.

Notably absent from the current public endpoint assumptions:
`finite_encoding_cert`, `chart_center_dist_le_metric_cert`,
`finite_common_inverse_isometry_encoding`, `inv_isoK`, `isoK`, and
`iso_correct`.

The new frontier is therefore SSProve's program/package semantics themselves.
`raw_code`, `Pr_code`, and `raw_package` expose the admitted interchange axiom,
so any theorem whose proof depends on those constants can inherit it even if
all local probability lemmas are clean.

SSProve dirty slice:

- Inherited through MathComp `experimental_reals/distr.v`:
  `__deprecated__dlet_dlet` depends on
  `realsum.__admitted__interchange_psum`. SSProve uses it in
  `Crypt/rhl_semantics/only_prob/SubDistr.v` (`SDistr_assoc`, the main route
  to dirty `P_OP`/`raw_code`), plus `Couplings.v`, `Theta_dens.v`,
  `Crypt/nominal/Pr.v` (`dlet_dlet_ext`), `pkg_rhl.v`,
  `TotalProbability.v`, and some rules proofs.
- Direct SSProve uses of the admitted interchange are currently
  `Crypt/rules/RulesStateProb.v:SD_commutativity` and
  `Crypt/nominal/Pr.v:Lossless_sample`.

If the MathComp Analysis PR on `experimental-reals-fixes` lands and SSProve is
rebuilt against it, most inherited uses should become clean without changing
Mending. Direct SSProve references may still require a small upstream SSProve
source refresh/name update, so avoid carrying a local SSProve fork unless this
becomes publication-blocking.

Minimal upstream boundary found so far:

```coq
From SSProve.Crypt.rhl_semantics Require Import FreeProbProg.
From SSProve.Crypt Require Import SubDistr.
From SSProve Require Import pkg_core_definition.

Print Assumptions SDistr.       (* dirty *)
Print Assumptions SDistr_bind.  (* clean, modulo foundations *)
Print Assumptions SDistr_unit.  (* clean, modulo foundations *)
Print Assumptions P_OP.         (* dirty *)
Print Assumptions P_AR.         (* dirty *)
Print Assumptions Op.           (* dirty *)
Print Assumptions Arit.         (* dirty *)
Print Assumptions opsig.        (* clean *)
Print Assumptions Location.     (* clean *)
Print Assumptions Interface.    (* clean *)
```

`pkg_core_definition.v` imports `RulesStateProb`; its `raw_code` sampler
constructor mentions `op : Op`, where `Op := FreeProbProg.P_OP` and
`P_OP := { X : choice_type & SDistr X }`. The packaged `SDistr` relative
monad is already dirty, even though the raw bind/unit functions are clean.
The deepest confirmed root is in SSProve's `SubDistr.v`: `SDistr_assoc` uses
mathcomp's deprecated `__deprecated__dlet_dlet`, and that theorem proves
general bind associativity by calling `__admitted__interchange_psum`.

Concrete upstream dirty uses:

```text
~/.opam/Mending/.opam-switch/sources/rocq-ssprove/theories/Crypt/rhl_semantics/only_prob/SubDistr.v
```

`SDistr_assoc` currently finishes with:

```coq
apply __deprecated__dlet_dlet.
```

and mathcomp's `__deprecated__dlet_dlet` calls:

```coq
rewrite __admitted__interchange_psum.
```

```text
~/.opam/Mending/.opam-switch/sources/rocq-ssprove/theories/Crypt/rules/RulesStateProb.v
```

`SD_commutativity` currently finishes with:

```coq
apply __admitted__interchange_psum.
```

There is also a downstream dirty use in:

```text
~/.opam/Mending/.opam-switch/sources/rocq-ssprove/theories/Crypt/nominal/Pr.v
```

In `Lossless_sample`, SSProve proves losslessness of sampled code by rewriting:

```coq
rewrite __admitted__interchange_psum.
```

The nominal file also defines `HasAction` instances for `raw_code` and
`raw_package`, but the smaller root is already visible before importing the
nominal semantics.

## Cleaned In Recent Passes

The following focused probes now list only the usual foundational axioms, not
`realsum.__admitted__interchange_psum`:

```coq
Print Assumptions conditional_coordinate_zero_prefix.
Print Assumptions coordinate_finite_kl_absolute_continuous.
Print Assumptions coordinate_bounded_kl_finite_kl.
Print Assumptions pythDist_final_total_variation.
Print Assumptions maximal_coupling_total_variation.
Print Assumptions dmargin_comp.
Print Assumptions clean_coupling.
Print Assumptions coupling_bind_kernel.
```

Main changes:

- Restored `RealSumExtras.interchange_psum_proved` from commit `ca0e8e75`,
  along with its helper `summable_pair_from_rows_psum`. A direct probe shows it
  does not depend on `realsum.__admitted__interchange_psum`; it only reports
  the usual MathComp classical/funext foundations. This gives us a clean local
  replacement when a proof really needs the full countable `psum`
  interchange.
- Compared the upstream/community-service branch
  `ethanlee515/analysis:experimental-reals-fixes` at
  `e5c6b8f0790fb07540d2b1cf6badc21c409a6e1a`. Besides
  `interchange_psum`, that branch proves `psumB` and `interchange_sup`, and
  updates `experimental_reals/distr.v` so `dlet_dlet`, `dlet_dmargin`,
  `dmargin_dlet`, `dfst_dswap`, `dsnd_dswap`, `dsndE`, and `pr_dlet` use the
  proved names while keeping deprecated aliases. Current grep finds no local
  Mending references to `__admitted__psumB` or `__admitted__interchange_sup`,
  so those two proofs are not current blockers. If future assumption probes
  expose them, restore the local `psumB_proved`/`interchange_sup_proved`
  mirrors from `ca0e8e75` or port the upstream proof shape.
- Added clean generic marginal lemmas in `DistrExtras.v`, including
  `pr_dmargin_pred1_clean` and `dlet_dmargin_partition`.
- Added clean independent-product lemmas in `DistrExtras.v`:

```coq
dlet_pairE :
  (\dlet_(x <- P) \dlet_(y <- Q) dunit (x, y)) xy = P xy.1 * Q xy.2

dlet_pair_revE :
  (\dlet_(y <- Q) \dlet_(x <- P) dunit (x, y)) xy = P xy.1 * Q xy.2

dlet_pairC :
  (\dlet_(x <- P) \dlet_(y <- Q) dunit (x, y)) =1
  (\dlet_(y <- Q) \dlet_(x <- P) dunit (x, y))

dlet_pair_bindE :
  (\dlet_(xy <- \dlet_(x <- P) \dlet_(y <- Q) dunit (x, y)) F xy) =1
  (\dlet_(x <- P) \dlet_(y <- Q) F (x, y))

dlet_pair_bind_revE :
  (\dlet_(xy <- \dlet_(y <- Q) \dlet_(x <- P) dunit (x, y)) F xy) =1
  (\dlet_(y <- Q) \dlet_(x <- P) F (x, y))

dlet_commut_indep_clean :
  (\dlet_(x <- P) \dlet_(y <- Q) F x y) =1
  (\dlet_(y <- Q) \dlet_(x <- P) F x y)
```

  `Print Assumptions dlet_pairC` is clean modulo foundational axioms. This is
  a proof-shaped replacement for the special independent-sampling
  commutativity that SSProve currently proves via general
  `__admitted__interchange_psum`. `dlet_commut_indep_clean` lifts that
  special pair commutation through clean bind associativity, giving a clean
  replacement for SSProve's `Pr.v:dlet_commut`/`RulesStateProb.SD_commutativity'`
  route.
- Added clean losslessness and SSProve-carrier bridge lemmas:

```coq
dlet_dlet_clean :
  (\dlet_(x <- \dlet_(y <- mu) f1 y) f2 x) =1
  (\dlet_(y <- mu) \dlet_(x <- f1 y) f2 x)

dweight_dlet_lossless :
  dweight D = 1 ->
  (forall x, dweight (K x) = 1) ->
  dweight (\dlet_(x <- D) K x) = 1

SDistr_assoc_clean :
  SDistr_bind A C (SDistr_bind B C f ∙ g) =
  SDistr_bind B C f ∙ SDistr_bind A B g

SDistr_clean :
  ord_relativeMonad choice_incl

SDistr_bind_pairC :
  SDistr_bind X (X * Y)%type
    (fun x => SDistr_bind Y (X * Y)%type
      (fun y => SDistr_unit (X * Y)%type (x, y)) q) p =
  SDistr_bind Y (X * Y)%type
    (fun y => SDistr_bind X (X * Y)%type
      (fun x => SDistr_unit (X * Y)%type (x, y)) p) q

SDistr_bind_commut_clean :
  SDistr_bind X Z (fun x =>
    SDistr_bind Y Z (fun y => g x y) q) p =
  SDistr_bind Y Z (fun y =>
    SDistr_bind X Z (fun x => g x y) p) q

SDistr_bind_lossless :
  dweight p = 1 ->
  (forall x, dweight (k x) = 1) ->
  dweight (SDistr_bind X Y k p) = 1

P_OP_clean :
  Type

P_AR_clean :
  P_OP_clean -> choiceType

rFreePr_clean :
  ord_relativeMonad choice_incl

rFreeProb_squ_clean :
  ord_relativeMonad _
```

  `Print Assumptions dlet_dlet_clean` is clean modulo foundational axioms.
  `SDistr_assoc_clean`, `SDistr_clean`, `SDistr_bind_pairC`,
  `SDistr_bind_commut_clean`, and `SDistr_bind_lossless` live in
  `LibExtras/SSProveExtras/SubDistrExtras.v`. They use the clean raw
  `SDistr_carrier`/`SDistr_bind`/`SDistr_unit` interface. `SDistr_clean`
  packages the same carrier/bind/unit into an assumption-clean relative monad
  by using `SDistr_assoc_clean` instead of SSProve's dirty `SDistr_assoc`.
  These are exact patch candidates for SSProve's `SubDistr.SDistr_assoc`,
  `RulesStateProb.SD_commutativity`, and `Pr.v:Lossless_sample` proof shapes.
- Added `LibExtras/SSProveExtras/FreeProbProgExtras.v`. It rebuilds the
  probabilistic sampler signature and free probabilistic monad using
  `SDistr_clean`:

```coq
P_OP_clean :=
  { X : choice_type & ord_relmonObj SDistr_clean X }

P_AR_clean op :=
  projT1 op
```

  `Print Assumptions P_OP_clean`, `P_AR_clean`, `rFreePr_clean`,
  `rFreeProb_squ_clean`, `P_OP_cleanE`, `rFreePr_cleanE`, and
  `rFreeProb_squ_cleanE` are clean modulo foundational axioms. The equalities
  are reflexive, so the clean sampler/free-monad data is definitionally the
  same as SSProve's aliases once the clean `SDistr` carrier is projected
  explicitly. No old-name bridge for `P_AR` is kept: mentioning SSProve's old
  dependent `P_AR` name in a theorem statement re-exposes the dirty `SDistr`
  packaging.
- Reproved conditional-coordinate and KL/Pyth bridge lemmas without dirty
  marginal rewrites.
- Reproved maximal-coupling margin/probability lemmas without deprecated
  `pr_dlet`/marginal rewrites where needed.
- Added local `clean_coupling`:

```coq
Definition clean_coupling d P Q :=
  dmargin fst d =1 P /\ dmargin snd d =1 Q.
```

- Migrated `ProgramLogics/Ae.v` to `clean_coupling`.
- Migrated `PythCompile.diagonalCoupling` to `clean_coupling`.
- Migrated the local coupling helpers in `NoiseFloodingSecurity.v` to
  `clean_coupling`.
- `rg -n "\bcoupling\b|\blmg\b|\brmg\b"` over the migrated AE/security files
  now finds no real proof dependency on SSProve `coupling`; only a comment
  remains in `PythCompile.v`.
- Removed the duplicate `completed_output_heap` wrapper from
  `Probability/PythSeq.v`. Pythagorean trace sequencing now uses the canonical
  `Probability/OutputHeap.v:complete_output_heap` wrapper directly, i.e.
  "pack output/heap, then apply `complete`." A grep for the exact identifier
  `completed_output_heap` under `theories/` now returns no matches.

## Metric Interface Ground Truth

Current chart assumptions are intentionally the one-chart/origin-centered
version:

```coq
isometry_center0 :
  forall center, isometry center center = ivec_zero

metric_chartE :
  forall center m,
    metric center m = ivec_dist ivec_zero (isometry center m)

inverse_isometry_shift :
  forall centerL centerR v,
    inverse_isometry centerR v =
    inverse_isometry centerL (ivec_add v (isometry centerL centerR))
```

This replaced the false common-inverse-isometry direction. The intended chart
compatibility remains:

```text
I_b^{-1}(x) = I_a^{-1}(x + I_a(b))
metric a b = ivec_dist 0 (I_a(b))
I_a(a) = 0
```

`inv_isoK`, `isoK`, `isometry_radius`, and `iso_correct` remain restored in
`ApproxFHE.v` for the user's original metric interface record. They are not
the current proof route.

The old `finite_encoding_cert`/`chart_center_dist_le_metric_cert` route still
exists as legacy scaffolding for older lemmas, but it is explicitly marked
obsolete in `NoiseFloodingSecurity.v` and is not used by the public endpoint.
In particular, `finite_common_inverse_isometry_encoding` should not guide new
work; it conflicts with the intended origin-centered chart story. The current
endpoint uses the one-chart vector comparison plus `metric_chartE` instead.
The practical finite-codomain workaround is therefore resolved for the public
security theorem: `ApproxFHE.v` has no finite isometry-codomain assumption, and
`Print Assumptions Secure.is_secure` no longer lists `finite_encoding_cert`,
`chart_center_dist_le_metric_cert`, or `finite_message_encoding_cert`. Some
finite-encoding lemmas remain in `NoiseFloodingSecurity.v` as legacy or
short/scalar variants; the theorem-facing path uses the ready-vector-bound
compiler route, proving the KL/Pythagorean cost on integer-vector Gaussians and
then applying the deterministic message continuation operationally.

## Current Frontier

The next hard question is how to avoid or clean the SSProve semantic constants
that themselves expose `realsum.__admitted__interchange_psum`.

Current policy after discussion: do not contort the local noise-flooding proof
only to avoid an external mathcomp/SSProve admit. Since
`interchange_psum_proved` has been restored, use it where it is a direct
replacement; otherwise treat any remaining upstream admitted interchange as
acceptable scaffolding for now and keep it explicitly documented in
`Print Assumptions` probes.

Known dirty probes:

```coq
From SSProve.Crypt.nominal Require Import Pr.
From SSProve Require Import pkg_core_definition pkg_advantage.

Print Assumptions raw_code.
Print Assumptions Pr_code.
Print Assumptions raw_package.
```

Possible strategies:

- Patch or locally shadow SSProve's `SubDistr.SD_assoc`/`SDistr` packaging to
  use `dlet_dlet_clean`/`SDistr_assoc_clean`. The local `SDistr_clean` proves
  this patch is feasible.
- `FreeProbProgExtras.v` shows that the sampler/free-monad data can be rebuilt
  cleanly and remains definitionally equal to the old aliases. This suggests
  the upstream patch can be surgical: rebuild `FreeProbProg.P_OP/P_AR` and
  `rFreePr` from the cleaned `SDistr` package, or replace the upstream `SDistr`
  proof and recompile SSProve.
- Then recheck whether `P_OP/P_AR`, `Op/Arit`, and `raw_code` become clean
  under the patched compiled names. If not, continue tracing other dirty
  obligations inside the program semantics.
- Patch or shadow `RulesStateProb.SD_commutativity` to use
  `SDistr_bind_pairC` instead of the general admitted `interchange_psum`.
- Patch or shadow `RulesStateProb.SD_commutativity'` and `Pr.v:dlet_commut`
  with `SDistr_bind_commut_clean`/`dlet_commut_indep_clean`.
- Separately inspect `Pr.v:Lossless_sample`; it may also be replaceable by
  `SDistr_bind_lossless`/`dweight_dlet_lossless` rather than general
  interchange.
- If the compiled SSProve constants cannot be repaired locally, decide whether
  to vendor/patch SSProve or introduce a local wrapper layer for the needed
  program/package interface.

Lower-priority cleanup still visible by grep:

```sh
rg -n "__deprecated__dlet_dmargin|__deprecated__dmargin_dlet" \
  theories/ProgramLogics theories/Security theories/Probability -g'*.v'
```

Those remaining deprecated rewrites are not currently the known public-theorem
`interchange_psum` source, but they are worth cleaning eventually.

## Paper Notes

`Pythagorean-RHL/pyth-rhl.tex` has been updated to match the current
program-logic surface:

- Added a rule-inventory figure covering Hoare, additive-error,
  Pythagorean, and compiler/oracle-replacement rules, now grouped by proof
  role: semantic base rules, derived rules, and compiler theorems.
- Clarified that legacy admitted non-option AE convenience lemmas are not the
  paper-facing route; the proof uses completed-output/total variants.
- Documented the scalar versus tuple compiler/oracle-replacement rules, with a
  `\Codex{...}` note that the compiler-family soundness proof is the hardest
  program-logic proof to explain later.
- Replaced the concrete author list in `main.tex` with an author-list
  placeholder.
- Removed the scratch KL summability section from the compiled paper. The
  useful point from that scratch section, namely that value-level KL and
  summability use the same prefix-grouping argument, was folded into
  `discrete-gaussian-analysis.tex`.
- Updated Section 5.1.2 (`lmss.tex`) to remove the obsolete "Limitation of our
  program logic" example. The query-bound adversary story now says that
  data-dependent oracle calls are handled by the verified trace compiler, while
  the raw fixed-tuple Pythagorean judgment remains a lower-level design choice.

Paper build command currently succeeds:

```sh
make -C Pythagorean-RHL
```

The build still reports existing overfull/underfull boxes from long inference
rules/equations and dense rule-table wrapping, but no fatal LaTeX errors.

## Verification Commands

Known passing commands after the clean-coupling migration:

```sh
timeout 600s make -f Makefile.coq theories/Security/NoiseFloodingSecurity.vo
timeout 600s rocq c -Q theories Mending theories/LibExtras/MathcompExtras/RealSumExtras.v
timeout 600s rocq c -Q theories Mending theories/LibExtras/MathcompExtras/DistrExtras.v
timeout 600s rocq c -Q theories Mending theories/LibExtras/SSProveExtras/SubDistrExtras.v
timeout 600s rocq c -Q theories Mending theories/LibExtras/SSProveExtras/FreeProbProgExtras.v
timeout 600s rocq c -Q theories Mending theories/Probability/Ae.v
timeout 600s rocq c -Q theories Mending theories/Probability/OutputHeap.v
timeout 600s rocq c -Q theories Mending theories/Probability/PythSeq.v
timeout 600s rocq c -Q theories Mending theories/Probability/KL/Core.v
timeout 600s rocq c -Q theories Mending theories/ProgramLogics/Ae.v
timeout 600s rocq c -Q theories Mending theories/ProgramLogics/Pyth.v
timeout 600s rocq c -Q theories Mending theories/ProgramLogics/PythCompile.v
timeout 600s rocq c -Q theories Mending theories/Security/NoiseFloodingSecurity.v
```

Public theorem probe:

```coq
From Mending.Security Require Import NoiseFloodingSecurity.
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

Current expected result: still includes `realsum.__admitted__interchange_psum`,
now traced to SSProve semantic constants rather than local coupling.

## Estimate

The lower-level KL/Pyth/maximal-coupling work is no longer the bottleneck.
The remaining uncertainty is semantic infrastructure:

- If `interchange_psum` is confined to a small SSProve semantic lemma that can
  be locally reproved or bypassed: several focused days.
- If `raw_code`/`Pr_code`/`raw_package` intrinsically depend on the admitted
  interchange theorem throughout SSProve: likely one or more weeks, and perhaps
  an upstream-cleanup task rather than a local refactor.
