# KLS14 Lean project

This project proves the dimension-free Poincare inequality with constant **14**
for every isotropic log-concave probability law in positive finite dimension.
The stronger verified upper bound is **13.810833 = 13810833/1000000**. The public
original-law theorem covers locally Lipschitz, square-integrable real tests;
the unchanged OpenAI model uses smooth compactly supported real tests.

Start with [`KLS14.lean`](KLS14.lean), [`Challenge.lean`](Challenge.lean), and
[`AxiomAudit.lean`](AxiomAudit.lean). `KLS14.openaiKLS` supplies the explicit witness
14 for the unchanged `OAI.LeanBlast.KLS.KLSStatement`.
`OpenAIModel.openaiKLSStatement` is only a transparent compatibility abbreviation.

The separate number **13.068 is a lower obstruction for the displayed proof
family**, not a universal KLS upper or lower bound. No global optimum for the
technical method is claimed. The exponential benchmark with Poincare constant 4
is preserved in the inherited source development.

## Build

Lean and Mathlib are pinned in `lean-toolchain` and `lake-manifest.json`.
After installing Elan, run these commands from this directory:

```sh
lake exe cache get
lake build KLS14
lake env lean AxiomAudit.lean
```

`FullAudit.lean` imports the complete accepted 921-module publication, including
the general scalar infinite-value results and their scope checks. The bundled
source/import manifests are in `verification/`. The export contains no build
caches or compiled objects. The source-export provenance is inherited build
evidence; a fresh release build is recorded separately when performed.

For external build storage and the completed release checks, see the
[verification guide](verification/README.md). The optional launcher requires
an explicitly selected mounted disk before creating compilation files.
