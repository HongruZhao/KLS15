# KLS15

This project continues [KLS500](https://github.com/HongruZhao/KLS500), which recorded the earlier upper bound 500.

Zenodo archive: [version 2.0](https://doi.org/10.5281/zenodo.23272815).

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

The proof builds on [Krishnakumar Balasubramanian and Shiva Kasiviswanathan, *A Dimension-Free Bound on the Poincaré Constant of Isotropic Log-Concave Measures*, v2](https://arxiv.org/abs/2610.07728v2).

See [Detailed changes](DETAILED_CHANGES.md) for the comparison with the paper and links to the Lean refinements.

The complete source closure contains 1,654 Lean modules. A fresh source rebuild passed for all 1,654 project modules, with only `propext`, `Classical.choice`, and `Quot.sound` in the final theorem axiom closures. See [verification](verification/README.md) for its exact scope and evidence.

With Elan and the pinned dependencies:

```sh
lake exe cache get
lake build
```

Project contributions use [Apache 2.0](LICENSE); retained third-party licenses and [notices](NOTICE) apply. The repository layout follows [OpenAI/PrimeGaps186](https://github.com/openai/PrimeGaps186).
