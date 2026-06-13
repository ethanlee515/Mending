# Program Logics

Program logics for SSProve `raw_code` programs live at this level.

`Pyth.v` is the existing total-correctness-style Pythagorean judgment.
`CompletedPyth.v` is the partial-program variant that completes output
subdistributions with an explicit `None` divergence/failure point.

Probability-level distribution facts used by the logics live in `Probability/`.
Generic MathComp helpers used by the logics live in `LibExtras/MathcompExtras/`.
