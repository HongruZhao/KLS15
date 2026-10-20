<a name="detailed-changes-from-paper-v2" id="detailed-changes-from-paper-v2"></a>
# Changes in version 3.0.0

[Main README](README.md) · [Preserved v2 comparison with the paper](lean_15/DETAILED_CHANGES.md)

The new release proves the universal upper bound **13.810833 < 14**, improving the preserved v2 endpoint **14.9963 < 15**. Both statements cover the original isotropic log-concave probability laws in every positive finite dimension and locally Lipschitz L² tests. The proof builds on the deterministic compatible-field, curvature and approximation framework of [Balasubramanian and Kasiviswanathan](https://arxiv.org/abs/2610.07728v2). The quantitative refinements below extend that framework.

## Sharper cubic control and coupled observations

The [original-law cubic theorem](lean_14/KLSConstantImprovement/OriginalCubic4013023465.lean) gives the raw cubic cap **401.3023465** with its analytic obligations discharged. The next step retains a [cubic/quartic support estimate](lean_14/KLSConstantImprovement/QuarticM48Support20261020.lean) for the **same measure and test function**. This shared-source structure matters: the proof uses a joint budget, rather than combining independently maximized observations.

The [quartic endpoint barrier](lean_14/KLSConstantImprovement/RawCubicQuarticEndpointBarrier.lean) supplies the analytic support used in the all-rank induction. The final theorem has no extra cubic or quartic estimate as an assumption.

## An all-rank budget and a positive mixture

For one fixed test, the proof controls a weighted sum of its Appell energies over every finite degree range. The [weighted generator](lean_14/KLSConstantImprovement/RawCubicQuarticWeightedBudget.lean) keeps the degree-dependent allocations and the coupled low-degree support.

The final [mixed budget](lean_14/KLSConstantImprovement/AcceptedMix96Weighted.lean) is an exact positive combination of two proved original-law budgets, after rescaling to a common parameter. The combination uses actual energies of the same test. Truncating its positive remainder produces the final retained profile and a constant infinite tail. It adds no restriction to the admissible laws.

## Exact-cap Bellman certificates and the infinite tail

The scalar argument retains the quadratic transition cap instead of replacing it by a chord. Its [two-variable square identities](lean_14/KLSConstantImprovement/ExactQuadraticCapBellmanCertificates.lean) and rational coefficient inequalities are checked in Lean.

There are **95 finite Bellman stages**, covering ranks 2 through 96. These are finite algebraic payment inequalities, followed by a [proved infinite-tail payment](lean_14/KLSConstantImprovement/WeightedOrbitBellmanTail.lean). They do not truncate the all-rank theorem or leave a limiting estimate as a hypothesis. The [final data](lean_14/KLSConstantImprovement/QuarticM96MixTrueCapBellman20261020TightData.lean) uses exact rational constants, with no numerical optimizer supplied as a theorem premise.

## From the budget to the original Poincaré statement

The [operator endgame](lean_14/KLSConstantImprovement/QuarticM96MixTrueCapBellman20261020TightOperator.lean) bounds the squared norm of the actual centered inverse-gradient operator by **12.810833**. The original-law transfer then yields

```math
C_P(\mu)\le 1+\|J\|^2
\le \frac{13810833}{1000000}=13.810833<14.
```

The [endpoint module](lean_14/KLSConstantImprovement/QuarticM96MixTrueCapBellman20261020TightEndpoint.lean) includes the universal and OpenAI formulations. Regularization transfers the regular-law argument to the original law class. The exponential benchmark remains 4.

These are upper bounds, with no claim that the universal constant or the full proof method is optimal. A sharp scalar calculation for one fixed weighted profile does not establish optimality over all profiles or produce an extremizing probability law.

## Preserved history and link compatibility

The complete earlier project, including its pinned configuration and v2 proof receipts, is retained in [lean_15](lean_15/README.md). Its [original paper comparison](lean_15/DETAILED_CHANGES.md) remains available. Compatibility Markdown pages retain the earlier documentation paths and redirect their file links to the preserved project. Fixed-commit external links keep their original targets. The release migration manifest records any Markdown-only retargeting; Lean sources and historical verification receipts are preserved.

See the [current verification guide](lean_14/verification/README.md) for the exact source and axiom-check scope.
