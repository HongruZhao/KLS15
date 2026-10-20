# Final KLS15 release documentation review

Status: **PASS — no material documentation or correspondence issue found.** This is a new final review; earlier staging and pre-build reviews remain unchanged.

The final `README.md`, `formalization.yaml`, and `verification/README.md` agree with the completed build and the public endpoint types. `KLS15.poincare15` retains positive dimension, the original admissible isotropic log-concave probability law, and locally Lipschitz L² test assumptions. The OpenAI endpoint has the exact pinned, byte-identical upstream `KLSStatement`, with witness 15. No physical joint gate, regularity hypothesis, maximizing-law premise, or numerical candidate remains in the public declarations. Constant 15 is presented as sufficient; no optimality, sharpness, method-specific floor, or bound-4 claim appears.

## Paper and quantitative comparison

The README correctly credits Balasubramanian–Kasiviswanathan v2, Theorem 1.1, for 25 and connects this project to KLS500's earlier 500. The factors 500/25=20 and (25−15)/25=40% are exact. The GPT-6.1 Sol (Ultra) acknowledgement is expressly author-provided and separate from proof verification.

The five comparison rows agree with the cached v2 text and the shipped strict-sub15 chain:

- Equation (3.14), rank-two **generator** loss: `24/(1−α)−18` becomes `64/[3(1−α)]−18` for `1/3≤α<1`. This compares generator losses, not the noise-only losses whose constants are −20.
- Section 3.4 and Proposition 3.1: actual variance centering changes the terminal cost `2x(1+uq)` to `x(1+uq)`; the links point to the centered adjacent heat and terminal sources.
- Theorem 4.1 proof, “The Cubic Coefficient,” (4.2)–(4.3): the paper's `c₃²≤121/4` is compared with the actual same-test normalized cap `b₃²≤(49/2)‖f‖²`.
- Theorem 4.1/(4.1): the paper's individual geometric bounds use `B=121/4`, `K=223/10`. The release instead proves the same-test finite sum `Σ₂ᴺ b_d²/(67/5)^d ≤(6/125)‖f‖²`. The README explicitly distinguishes this joint budget from separately maximized coefficient bounds and from the paper's differently defined C.
- Proposition 7.3: the paper's operator bound 24 is compared with the new two-head bound 13.9963. The release endgame retains separate quadratic/cubic caps; it does not claim to use the later nonlinear correlated graded Schur refinement.

The normalizations `b_d=‖B_d(f)‖/d!`, `E_d=‖B_d(f)‖²`, `K=67/5`, `C=6/125`, `B=49/2`, and `p=2089/2000` are consistent. The exact endpoint is `1+Kp=149963/10000=14.9963<15`. All relative links in the two READMEs and scalar-audit documentation resolve.

## Completed verification and launcher scope

The final receipt records **1,654/1,654 shipped project modules rebuilt from source**, from an empty project-object directory with replaced `LEAN_PATH`, and no historical project objects reused. This is the 1,652-module endpoint dependency closure plus the public interface and Challenge; it is not a rebuild of unused old or experimental branches. Pinned external Mathlib/dependency caches and the pinned Lean standard library were reused explicitly and were not rebuilt.

All five final type/axiom queries passed. Each nonempty axiom block is exactly `propext`, `Classical.choice`, and `Quot.sound`, with no custom endpoint axiom or `sorryAx`. The independent clean-build binder rehashed every source, object, and log before the launcher changed; this final review additionally rechecked all 1,654 current manifest source hashes and the final five axiom blocks. There are 960 `warning:` text occurrences, representing 910 classified diagnostic headers; these are retained linter/deprecation diagnostics, not a warning-free build.

The exact executed launcher is archived at `clean-build-r1/executed-rebuild.py`; it ran from `verification/rebuild.py` during the completed build. The archived snapshot is evidence of the executed bytes, not a claim that its archived location is the default runnable project layout. The current launcher adds project-local Elan resolution, exact Lean version/commit validation, optional platform-specific compiler hashing, and an explicit preflight-only mode. Independent text comparison confirms the dependency scheduler, compiler command/flags, final endpoint audit, and final source checks are unchanged; final receipt metadata has additional compiler/launcher fields. Its preflight and rejection tests passed, but it has not performed a second full build and has not been tested on Linux or Windows.

The unchanged source manifest retains pre-build status metadata as historical evidence; final receipt and release summary explicitly carry completion. The scalar audit remains a separate 399-check exact arithmetic/source-provenance audit with detached-copy replay. Challenge is accurately described as a post-solution proof-bearing statement check. Comparator, lean4export and Nanoda were not run; AI-assisted review is not represented as independent human peer review.

The pinned OpenAI model and retained license hashes match. The five previously missing retained license files are present and match their provenance manifest. This is a file-provenance check, not a legal opinion. No Lean, manifest, launcher, README, historical review, or proof evidence was edited in this final review.

## Exact binding

- `README.md`: `1b211c1e007c5f938b11f79034c6956167fdbaed5d24d289b409ce348f88ee8c`
- `formalization.yaml`: `c0eec182c2338bc0a0df98f765a0043ac92041e54c3efdc1a799ccea015fcd24`
- `verification/README.md`: `d4c572d54bd330773b277659b20cbd643a4adf3ef6461a9963f691bafe784821`
- `verification/source-manifest.json`: `b1ca777bd1c45f9b98f863e0fbd26631002e9e9b0a165c6f213520f796930c17`
- `verification/clean-build-r1/receipt.json`: `efa3f0278c315ee132b2df845d9253aaa2156d6bfdce7c0bb93dfa75637856ba`
- `verification/clean-build-r1/executed-rebuild.py`: `016f676311bb954594bb49834efe6bf164778232d9c37bfac1f5c7f3e5361a24`
- `verification/rebuild.py`: `2d8309b9ffed45d4220444034a9356191b7ac8a3f19883955bf375e7ad00d6d5`
- `verification/execution-script-binding.json`: `858bc0e86854eec029b560dda45e122229fe1e347919da1904522210f04825b6`
- `verification/clean-build-final-correspondence.json`: `814c2c2fa621ef53c917db4aed2df3f74d6f8c157f4ca14a44a7b40e798aebc2`

The companion `FINAL_RELEASE_DOCUMENTATION_REVIEW.json` binds all reviewed artifacts, the cached primary text, and local-link checks.
