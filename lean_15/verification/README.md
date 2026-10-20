# Verification

The shipped KLS15 project consists of the complete 1,652-module transitive source closure of `ActualKLS15VerifiedEndpoints`, plus the public `KLS15.lean` interface and its proof-bearing `Challenge.lean` statement checks: 1,654 modules in total. Older unused KLS500 branches and experimental conditional improvements are not part of this project.

All imported project sources are included. The public theorem preserves the original admissible isotropic log-concave probability-law class and locally Lipschitz L² tests. Its OpenAI endpoint uses the unchanged pinned `OAI.LeanBlast.KLS.KLSStatement` and witness 15.

The new clean source rebuild **passed for all 1,654 shipped modules**. Its [final receipt](clean-build-r1/receipt.json) and [independent final binding](CLEAN_BUILD_FINAL_CORRESPONDENCE.md) record completion. It starts with an empty project object directory and replaces `LEAN_PATH` with that directory, the pinned external dependency caches, and the pinned Lean standard library. No historical project objects are reused. Lean runs at kernel trust level zero. Mathlib and the Lean standard library are pinned external dependencies; their sources are not rebuilt in this run.

The build checks every shipped source hash, dependency revision, compilation result, and final theorem's transitive axioms. Its [source manifest](source-manifest.json), clean-build preflight, per-module logs, progress and final receipt record the evidence. All five final declarations were checked; each has only `propext`, `Classical.choice`, and `Quot.sound` in its transitive axiom closure. Historical linter and deprecation warnings are retained in the logs; the build passed without errors.

Portable reproduction, after installing the pinned Lean toolchain and dependency cache:

```sh
lake exe cache get
python3 verification/rebuild.py --output verification/clean-build-reproduction
```

The expected endpoint axiom closure is exactly `propext`, `Classical.choice`, and `Quot.sound`, with no custom mathematical axioms or theorem placeholders. `Challenge.lean` was written after the proof and imports it; it is a separately compiled statement check, not an independent prior specification. Comparator, lean4export and Nanoda have not been run. The correspondence assessment is an AI-assisted source review, not independent human peer review.

The separately reproducible [scalar audit](SCALAR_CERTIFICATE_AUDIT.md) passed 399 exact arithmetic and source-provenance checks, including a detached-copy replay.

Preflight, staging manifests and earlier reviews retain their original pre-build status as immutable historical evidence; the final receipt and release summary record completion.

The launcher bytes used at `verification/rebuild.py` during the complete proof run are archived as the [executed-script snapshot](clean-build-r1/executed-rebuild.py). The current reproduction launcher adds project-local Elan resolution and exact version/commit checks without a mandatory platform-specific binary hash; its compilation scheduler and endpoint audit are unchanged. [The script binding](execution-script-binding.json) distinguishes these versions. The updated launcher passed input preflight and rejection tests; it was not used for a second complete build and has not been tested on Linux or Windows.
