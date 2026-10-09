# KLS15

This project continues [KLS500](https://github.com/HongruZhao/KLS500), which recorded the earlier upper bound 500.

Lean 4 formalization of the Poincaré formulation of the **Kannan–Lovász–Simonovits (KLS) conjecture**, with the explicit dimension-free constant **15**. For every isotropic log-concave probability measure $\mu$ on $\mathbb{R}^n$, $n\ge1$:

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

The following changes lead to 15. The coefficient comparison uses the paper's [normalized operator norms (§1.3, page 3)](https://arxiv.org/pdf/2610.07728v2#page=3): $c_d(\mu)=\frac{1}{d!}\sup_{\lVert f\rVert_{L^2(\mu)}=1}\lVert B_d^\mu(f)\rVert$ and $c_d=\sup_{\mu\in\mathcal C_n}c_d(\mu)$, where $\mathcal C_n$ is the class of isotropic log-concave laws in the fixed dimension $n$.

For the first row, [equation (3.14), page 11](https://arxiv.org/pdf/2610.07728v2#page=11) is specialized to $j=2$, with $E_d=\lVert B_d^\mu(f)\rVert^2$ at the isotropic base point. Both columns compare the loss $L_\beta$ in the same inequality:

```math
\mathcal D E_2\ge\beta E_3-L_\beta E_2-2\langle B_2,R_2\rangle.
```

Here $\mathcal D$ acts on the covariance-normalized tilt energies at the isotropic base point, and $R_2$ is the full lower-cumulant drift tensor. Keeping the paper's parameter $\beta$, its coefficient is

```math
A_\beta=\frac{4}{1-\beta}-2,\qquad
4A_\beta+2(A_\beta-3)=6A_\beta-6=\frac{24}{1-\beta}-18.
```

| Estimate and paper v2 location | Paper v2 | This Lean release |
|---|---|---|
| Rank-two loss $L_\beta$: (3.14) specialized to $j=2$, on $1/3\le\beta<1$ | $24/(1-\beta)-18$ | $64/[3(1-\beta)]-18$, using full cubic symmetry. [Proof](ActualSymmetricQuadraticNoise.lean). |
| Adjacent terminal cost at the quotient maximum: [Proposition 3.1 proof, §3.6, page 14](https://arxiv.org/pdf/2610.07728v2#page=14) | $2x(1+uq)$ | $x(1+uq)$, using variance centering. [Heat inequality](ActualCenteredAdjacentHeat.lean) and [cancellation](ActualCenteredAdjacentTerminal.lean). |
| Cubic operator norm: [Theorem 4.1, (4.1), page 14](https://arxiv.org/pdf/2610.07728v2#page=14) | $c_3^2\le121/4=30.25$ | $c_3^2\le49/2=24.5$, using a centered joint barrier. [Seed](ActualSymmetricCenteredCubicSeed245.lean) and [cap](ActualSymmetricCubicSeed245Cap.lean). |
| Abstract operator norm: [Proposition 7.3, page 28](https://arxiv.org/pdf/2610.07728v2#page=28) | $\lVert R\rVert^2\le24$ | $\lVert R\rVert^2\le139963/10000=13.9963$, retaining separate quadratic and cubic observation caps. [Endgame](TwoHeadObservationOperatorEndgame.lean) and [parameters](CoupledSub15Numerics.lean). |
| Poincaré constant, Theorem 1.1 | $C_P(\mu)\le25$ | $C_P(\mu)\le149963/10000<15$. [Endpoint](ActualKLS149963Endpoints.lean). |

The paper also states $c_3^2\le B$ explicitly at the end of “The Cubic Coefficient” on [page 15](https://arxiv.org/pdf/2610.07728v2#page=15), after (4.3), with $B=121/4$ from (4.1). The Lean cap gives $\lVert B_3^\mu(f)\rVert^2\le36(49/2)\lVert f\rVert_2^2$ for every law and test; dividing by $(3!)^2=36$ and taking the same suprema gives the displayed $c_3^2\le49/2$.

The terminal-cost row refers to the **unnumbered display** immediately after “We obtain” and before “Divide by $x>0$” in the [proof on page 14](https://arxiv.org/pdf/2610.07728v2#page=14). Its signed term is $-2x(1+uq)$; the table records the positive cost $2x(1+uq)$. The centered Lean inequality has $-x(1+uq)$. In the cubic specialization, $x=E_3$, $u=E_2/8$ and $q=-\phi'(u)/\phi(u)$ for the adjacent barrier $\phi$.

The operator row uses the paper's abstract $R$ in both columns, under the respective observation hypotheses of Proposition 7.3 and the Lean joint-budget endgame. The paper explicitly sets $R=J$ in [§8, proof of Theorem 1.1, page 30](https://arxiv.org/pdf/2610.07728v2#page=30), using (6.15)–(6.16), and obtains $\lVert J\rVert^2\le24$ and $C_P(\mu)\le1+\lVert J\rVert^2\le25$. The Lean [actual operator assembly](ActualRegularEndpointSub15.lean) likewise sets $R=J$, the centered graded integration operator. The applications to $J$ use regular laws; approximation extends the Poincaré bound to all isotropic log-concave laws.

The all-degree estimates have different forms and are therefore stated separately. The paper's Theorem 4.1 and (4.1) give the individual operator bounds $c_d^2\le(121/4)(223/10)^{d-3}$ for $d\ge3$. For the joint estimate, write $b_d(\mu,f)=\lVert B_d^\mu(f)\rVert/d!$ for one fixed measure and test function. Exact triangular contractions and degree-dependent Young allocations give the following [joint bound](ActualWeightedAppellInductionSub15.lean), with $\lVert f\rVert_2=1$ and the **same** $f$ in every summand, for every finite $N$:

```math
\sum_{d=2}^{N}\frac{b_d(\mu,f)^2}{(67/5)^d}
\le\frac{6}{125}.
```

Here $K=67/5=13.4$ and $C=6/125=0.048$ are parameters of the joint estimate, not replacements in the paper's individual geometric bound. The sum contains $b_d(\mu,f)^2$, not separately maximized $c_d^2$. For general $f$, homogeneity adds the factor $\lVert f\rVert_2^2$ on the right. With $p=2089/2000$, the final [unconditional endpoint](ActualKLS149963Endpoints.lean) is

```math
C_P(\mu)\le1+Kp=\frac{149963}{10000}=14.9963<15.
```

The compatible-field curvature and approximation framework is retained. These refinements and smaller constants are additions to the paper, and no sharp or optimal universal constant is claimed.

The complete source closure contains 1,654 Lean modules. A fresh source rebuild passed for all 1,654 project modules, with only `propext`, `Classical.choice`, and `Quot.sound` in the final theorem axiom closures. See [verification](verification/README.md) for its exact scope and evidence.

With Elan and the pinned dependencies:

```sh
lake exe cache get
lake build
```

Project contributions use [Apache 2.0](LICENSE); retained third-party licenses and [notices](NOTICE) apply. The repository layout follows [OpenAI/PrimeGaps186](https://github.com/openai/PrimeGaps186).
