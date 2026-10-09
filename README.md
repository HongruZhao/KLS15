# KLS15

This project continues [KLS500](https://github.com/HongruZhao/KLS500), which recorded the earlier upper bound 500.

Lean 4 formalization of a dimension-free Poincaré bound for every isotropic log-concave probability measure $\mu$ on $\mathbb{R}^n$, $n\ge1$:

```math
\mathrm{Var}_{\mu}(f)\le15\int\lVert\nabla f\rVert^2\,d\mu.
```

The inequality covers locally Lipschitz $L^2(\mu)$ functions. The constant 15 is a sufficient upper bound; optimality is not asserted.

| Statement | Lean declaration |
|---|---|
| Poincaré bound | `KLS15.poincare15` |
| Universal upper bound | `KLS15.universalPoincareUpper15` |
| OpenAI formulation with witness 15 | `KLS15.openaiPoincare15` |
| Exact upstream OpenAI KLS statement | `KLS15.openaiKLS` |

The final theorem has exactly the unchanged [OpenAI `KLSStatement`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/KLS/Model.lean#L47-L58) as its type, with universal witness 15. See [KLS15.lean](KLS15.lean) and the separately compiled [Challenge.lean](Challenge.lean).

The proof builds on the improved deterministic method of [Krishnakumar Balasubramanian and Shiva Kasiviswanathan, *A Dimension-Free Bound on the Poincaré Constant of Isotropic Log-Concave Measures*, v2](https://arxiv.org/abs/2610.07728v2). Their Theorem 1.1 states the upper bound 25, twenty times smaller than the earlier 500 in KLS500. Hongru Zhao's further quantitative refinements, developed with GPT-6.1 Sol (Ultra) assistance and verified in Lean 4, give the integer bound **15**, a further **40% reduction** from 25. Model attribution is an author-provided acknowledgement; the verification evidence concerns the Lean statements and proofs.

The following changes lead to 15. Write $b_d(\mu,f)=\lVert B_d^\mu(f)\rVert/d!$ for the normalized Appell response of the **same** test function, and $E_d=\lVert B_d^\mu(f)\rVert^2$.

| Part of paper v2 | Refinement used in this Lean release |
|---|---|
| Rank-two generator estimate, (3.14): loss $24/(1-\alpha)-18$ | Full cubic symmetry reduces the loss to $64/[3(1-\alpha)]-18$, for $1/3\le\alpha<1$. See [the actual generator proof](ActualSymmetricQuadraticNoise.lean). |
| Joint maximum and terminal terms, §3.4 and Proposition 3.1 | Variance centering replaces the terminal cost $2x(1+uq)$ by $x(1+uq)$ in the criterion's notation. See [the centered heat inequality](ActualCenteredAdjacentHeat.lean) and [terminal cancellation](ActualCenteredAdjacentTerminal.lean). |
| Theorem 4.1 proof, “The Cubic Coefficient”, (4.2)–(4.3): $c_3^2\le121/4=30.25$ | A centered joint barrier gives $b_3(\mu,f)^2\le(49/2)\lVert f\rVert_2^2$, with $49/2=24.5$. See [the seed](ActualSymmetricCenteredCubicSeed245.lean) and [its cap](ActualSymmetricCubicSeed245Cap.lean). |
| Individual geometric bounds, Theorem 4.1 and (4.1): $c_d^2\le(121/4)(223/10)^{d-3}$ for $d\ge3$ | Exact triangular contraction bounds and degree-dependent Young allocations give a coupled energy induction, with scale $K=67/5=13.4$ and summed budget $C=6/125=0.048$, as displayed below. See [the all-degree proof](ActualWeightedAppellInductionSub15.lean). |
| Spectral endgame, Proposition 7.3: $\lVert J\rVert^2\le24$ | Retaining separate quadratic and cubic observation caps gives $\lVert J\rVert^2\le139963/10000=13.9963$. See [the operator endgame](TwoHeadObservationOperatorEndgame.lean) and [exact parameters](CoupledSub15Numerics.lean). |

The coupled estimate is, for every finite $N$,

```math
\sum_{d=2}^{N}\frac{b_d(\mu,f)^2}{(67/5)^d}
\le\frac{6}{125}\lVert f\rVert_2^2.
```

This is a joint bound for one test function, rather than a sum of separately maximized coefficient norms. Its $K,C$ are not a direct substitution into the paper's individual geometric bound. With $p=2089/2000$, the final [unconditional endpoint](ActualKLS149963Endpoints.lean) is

```math
C_P(\mu)\le1+Kp=\frac{149963}{10000}=14.9963<15.
```

The compatible-field curvature and approximation framework is retained. These refinements and smaller constants are additions to the paper, and no sharp or optimal universal constant is claimed.

The complete source closure contains 1,654 Lean modules. A fresh source rebuild passed for all 1,654 project modules, with only `propext`, `Classical.choice`, and `Quot.sound` in the final theorem axiom closures. See [verification](verification/README.md) for its exact scope and evidence. Comparator and Nanoda have not been run.

With Elan and the pinned dependencies:

```sh
lake exe cache get
lake build
```

Project contributions use [Apache 2.0](LICENSE); retained third-party licenses and [notices](NOTICE) apply. The repository layout follows [OpenAI/PrimeGaps186](https://github.com/openai/PrimeGaps186).
