# Verification

The public theorem proves constant **14** for every original admissible law and
locally Lipschitz square-integrable real test in positive finite dimension. Its
stronger exact upper bound is **13810833/1000000 = 13.810833**. The upstream OpenAI
model is unchanged; `KLS14.openaiKLS` supplies its explicit witness 14.

The separate number **13.068 is a proof-family obstruction**, not a universal
KLS upper or lower bound. No global optimum for this method is asserted.

The shipped closure has **2,955 library sources**: 2,951 inherited files and four
release entry points. All sources are registered as Lake roots. The inherited
921-module publication and the older dependency receipts are preserved as
fingerprints in this directory. They are inherited evidence, not a new clean
rebuild of this release.

## Source integrity

From the repository root:

```sh
python3 verification/verify_release.py sources --project all
```

This checks hashes, the complete local import graph, registered Lake roots,
the pinned Lean/Mathlib environment and internal artifact exclusions. It does
not load Lean objects or prove theorems. The preserved legacy project has 1,654
library sources; its historical auxiliary `EndpointAudit.lean` is counted
separately. Its retained prebuild manifest status is not a current build result.

## Build

With Elan and the pinned dependencies, an ordinary complete Lake build is:

```sh
cd lean_14
lake exe cache get
lake build KLS14
lake env lean AxiomAudit.lean
```

The explicit roots include the complete bundled source set. `FullAudit.lean`
imports the inherited aggregate; `AxiomAudit.lean` queries the public endpoints.
Expected theorem closures contain only `propext`, `Classical.choice` and
`Quot.sound`. Success of a target alone does not say which dependencies were
freshly compiled or reused.

The optional repository build launcher can keep each project's `.lake`, caches,
objects, temporary files and logs on an explicitly selected mounted disk. See
[`../../verification/RELEASE_V3.md`](../../verification/RELEASE_V3.md). It refuses
a missing required mount and never creates a substitute mount folder.

## Release evidence

The final release report records separately:

- Source-only integrity and unchanged original model.
- Source-matched inherited project-object reuse, including `.olean.private`
  and `.olean.server` companions when present.
- Fresh compilation of the strongest actual endpoint, public entry points and
  aggregate audit, plus independent normal-environment replay.
- Actual compiler/dependency pins, source/object/log hashes and axiom queries.

**Release report:** [version 3.0.0 verification](../../verification/RELEASE_V3.md) and [machine-readable result](../../verification/v3/RELEASE_VERIFICATION.json). The fresh relocated checks passed on 20 October 2026, including all 3,388 aggregate axiom queries.
The immediate cache-backed release audit must not be described as a fresh
2,955-source rebuild. A clean whole-project result requires a separately
recorded run that freshly compiles every local source without project-cache reuse.
