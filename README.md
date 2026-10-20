<a name="kls14" id="kls14"></a>
# KLS15

The repository keeps its original **KLS15** name and address. The current proof is in `lean_14`; the previous proof is preserved in `lean_15`.

Lean 4 proofs of the dimension-free Poincaré bound **13.810833 < 14** for isotropic log-concave probability measures. For every such measure $\mu$ on $\mathbb R^n$, $n\ge1$, and every locally Lipschitz $L^2(\mu)$ function:

```math
\mathrm{Var}_{\mu}(f)
\le \frac{13810833}{1000000}\int\|\nabla f\|^2\,d\mu.
```

Version **3.0.0** continues the earlier KLS15 release. The proof retains the same law and test-function classes and verifies the original OpenAI formulation. The constant is a sufficient upper bound; no optimality is claimed.

Start with the public [KLS14 interface](lean_14/KLS14.lean) and its separately compiled [statement checks](lean_14/Challenge.lean). The [exact endpoint](lean_14/KLSConstantImprovement/QuarticM96MixTrueCapBellman20261020TightEndpoint.lean) records the stronger rational constant. See [detailed changes](DETAILED_CHANGES.md) for the mathematical route and [verification](lean_14/verification/README.md) for reproduction and proof receipts.

The improvement combines sharper cubic estimates and a coupled cubic/quartic estimate for the same law and test, an all-rank weighted budget, and exact quadratic-cap Bellman certificates with a proved infinite tail. The operator transfer then gives the bound for the original admissible laws.

This work builds on [Krishnakumar Balasubramanian and Shiva Kasiviswanathan's deterministic framework](https://arxiv.org/abs/2610.07728v2) and continues [KLS500](https://github.com/HongruZhao/KLS500). The earlier proof and its verification evidence are preserved in [lean_15](lean_15/README.md).

To build the current project with its pinned dependencies:

```sh
cd lean_14
lake exe cache get
lake build KLS14
lake env lean AxiomAudit.lean
```

The two projects build independently. See the [release verification guide](verification/RELEASE_V3.md) for external storage, exact checks, and the preserved legacy build.

Zenodo archive: [version 3.0.0](https://doi.org/10.5281/zenodo.23516248) · [all versions](https://doi.org/10.5281/zenodo.23229033). Historical archive: [version 2.0](https://doi.org/10.5281/zenodo.23272815).

Project contributions use [Apache 2.0](LICENSE); retained third-party licenses and [notices](NOTICE) apply. The repository layout follows [OpenAI/PrimeGaps186](https://github.com/openai/PrimeGaps186).
