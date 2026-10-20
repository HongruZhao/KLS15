> Archived v2 documentation. [Preserved project copy](../lean_15/verification/notation-correction-audit.md). Current release: [KLS14](../README.md).

# README notation correction audit

Status: **PASS — documentation correction; proof sources and verification evidence unchanged.** Checked 2026-10-09T21:57:02.932994+00:00.

The corrected README is bound to SHA-256 `d3d923ac367ff2479ce79bfedd962f35b21f2b4b40c36de2f308d729988f6013`. Its predecessor at commit `be824cc1c304b46b605b0c40779d50f755e51032` is `1b211c1e007c5f938b11f79034c6956167fdbaed5d24d289b409ce348f88ee8c`. Before adding this audit, `README.md` was the sole tracked change from that commit.

The table now fixes one admissible law in a fixed dimension and the same unit L² test function. Both cubic cells use `b₃²`: the paper's supremum bound implies `b₃²≤121/4`, while the shipped cap `E₃≤36·(49/2)‖f‖²` and `E₃=(3!)²b₃²` imply `b₃²≤49/2` for a unit test. The separately maximized `c_d` and same-test `b_d` are explicitly distinguished. The geometric bounds and coupled sum are stated separately; the latter retains the same test in every summand and gives `Σ₂ᴺ b_d²/K^d≤C`. Homogeneity supplies `‖f‖²` for general tests.

The terminal row explicitly applies at the quotient maximum and defines the cubic adjacent variables `x=E₃`, `u=E₂/8`, and `q=−φ′(u)/φ(u)`. The integration operator `J` has the same meaning in both columns. The generator row uses the common range `1/3≤α<1`; the new Poincaré row compares the same `C_P(μ)`. Exact arithmetic confirms `Kp=139963/10000` and `1+Kp=149963/10000<15`, with `K=67/5`, `C=6/125`, and `p=2089/2000`.

These checks used the shipped definitions and the cached v2 primary text (SHA-256 `f2cb9d2788a30d2e2b1a54458f2183233b0877c7e612687c448b14e2643847f4`); no new live fetch was performed. Every local README link resolves. The requested Comparator/Nanoda sentence was removed only from the top-level README. No additional Lean compilation or external checker run was performed or is implied by that deletion.

## Unchanged proof and historical evidence

All **1,654** current Lean source hashes match both the source manifest and completed clean-build receipt, with zero mismatches. The manifest, receipt, final endpoint audit, public interfaces, upstream OpenAI model, launchers, and launcher binding are byte-identical to the baseline commit. No Lean source, manifest, build receipt, or historical audit file was edited.

Both earlier review pairs remain immutable records of the README versions they reviewed. In particular, the final review still binds the predecessor README hash. This audit supplements its notation assessment for the corrected README rather than rewriting that historical binding.

| Preserved historical review | SHA-256 |
|---|---|
| `release-documentation-review.json` | `ebd08c0c36d862ea0e9fa8c42af10c117d39317e54de8fafdc98eabc7493a66b` |
| `RELEASE_DOCUMENTATION_REVIEW.md` | `295326f6170ea22228d3826b7c056c871892fe146da36af9c68c488747c20793` |
| `FINAL_RELEASE_DOCUMENTATION_REVIEW.json` | `193f27d5c5ea45978121646826891ed2b6d854f2df244e849e7c5956593b7ff1` |
| `FINAL_RELEASE_DOCUMENTATION_REVIEW.md` | `e915b2f8be9ba07734ca5738aad17ea1ce5cdae599296a1eed23e59f6f07b47e` |

The companion `notation-correction-audit.json` records the before/after README hashes, evidence hashes, normalization checks and unchanged completed-build scope. The only additions made by this audit are this report and that JSON file.
