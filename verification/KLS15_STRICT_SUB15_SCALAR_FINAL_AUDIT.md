> Archived v2 documentation. [Preserved project copy](../lean_15/verification/KLS15_STRICT_SUB15_SCALAR_FINAL_AUDIT.md). Current release: [KLS14](../README.md).

# Constant-15 release: independent strict-sub15 scalar audit

October 9, 2026. **PASS: 399 exact arithmetic and frozen receipt checks.**
This is an independent reconstruction from frozen Lean source. No producer
script or producer JSON was executed or imported. It supplements the
parent's whole-project clean build; it is not itself a clean Lean rebuild.
No frozen mathematical source was changed.

The release wrapper `ActualKLS15VerifiedEndpoints` imports
`ActualKLS149963Endpoints`. This uses the older, independently frozen
strict-sub15 chain with K=67/5, C=6/125 and p=2089/2000. Its exact conclusion
is 1+Kp=149963/10000=14.9963<15. The new conditional physical creation caps
12.05, 12.1 or 12.2, and later numerical profiles are not inputs to this
chain.

## Exact scalar reconstruction

The independent checker reads the literal Lean definitions, rather than a
sampling grid. It reconstructs seedV, its two derivatives, and the seven
seed245 polynomials. Each denominator-cleared polynomial agrees exactly
with the delivered unnormalized Bernstein expansion on the entire closed
interval [0,18/25], and every delivered coefficient is strictly positive.
The endpoint inverse range, zero-parameter margin, radical majorant, and
alpha>=1/3 gate also pass. Here B=49/2 and the actual cubic energy cap is
36B=882; later improvements of that seed are not substituted.

For the all-degree energy certificate, all finite coefficients for degrees
4 through 25 are at least c=149/10. For real d>=26 the coefficient is exactly

    (6767/14850)d^2-(2848/165)d+1068301/5000.

Its value at 26 exceeds c and its derivative is positive there and beyond.
Thus no finite truncation replaces the tail. The literal Young prefix was
checked against its finite sum, and all alpha ranges were checked. The
rank-two head is 447391331/16980429; the degree-three coefficient is
-2355275515819/74323050000. All four degree-22 head representations agree
coefficient by coefficient and cover the closed seed interval, with all
Bernstein coefficients positive.

The two-head observation arithmetic uses firstCap=2/K^2 and
secondCap=B/K^3. The positive denominators, cap sum, monotone lower anchors
and strict residual ratio all pass exactly. The conversion factors are
4=(2!)^2 and 36=(3!)^2. No missing degree-zero observation is being added.

## Correspondence and final quantifiers

Read-only source inspection confirms the all-N induction quantifies over
all original admissible laws and all actual L2 tests at the fixed dimension.
The previous N-1 bound is applied to the internally constructed genuine
maximizing law and every test needed for the proper contractions. The
maximum, stationarity, heat inequality and finite energy crossing are
discharged internally; the exported all-N theorem has none of these as
extra premises. The return to the original raw MemLp test uses the actual
AE/norm identities. The correlated head keeps the same test in E2 and E3.

The regular endpoint consumes that all-N estimate and the actual cubic
cap. The full endpoint removes its temporary smooth strong-convexity
premises using the existing regular-to-original-class transfer. Its final
test class is the unchanged `LocallyLipschitzTests`, and its final law
hypothesis is the original `admissibleMeasure`. The OpenAI endpoint keeps
the original log-concave density and isotropy interface. The constant-15
wrapper is only monotonicity from the frozen 14.9963 result.

Ten frozen mathematical source/log/object receipts were bound to the exact
files read by this audit. All report successful compilation and their
hashes match. This receipt correspondence is distinct from the parent
fresh build, which must independently establish closure and axiom reports
for the complete release tree.

Reproducible checker:
`coupled20-exploration/independent_kls15_scalar_source_audit.py`.
Exact result: `upper11/kls15-independent-scalar-source-audit.json`.
