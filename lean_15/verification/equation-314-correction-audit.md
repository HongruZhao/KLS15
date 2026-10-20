# Equation (3.14) README correction audit

Status: **PASS — documentation-only clarification; all proof and historical evidence bytes preserved.** Checked 2026-10-09T22:03:35.223225+00:00.

The README at baseline commit `8cc86cbc3bad49e5c380671de5a0f980f0e0f6e3` has SHA-256 `d3d923ac367ff2479ce79bfedd962f35b21f2b4b40c36de2f308d729988f6013`. The corrected README has SHA-256 `2aece5b4157d13fbca11843c988b0c3728b42f3d28ce7a5d72d2a11960397421`. It was the sole tracked change before this audit was added.

Equation (3.14) in the cached paper v2 gives the coefficient `Aβ·j²+(Aβ−3)·j`, with `Aβ=4/(1−β)−2`. At `j=2` this is `4Aβ+2(Aβ−3)=6Aβ−6=24/(1−β)−18`. The README now displays the common full inequality `𝒟E₂≥βE₃−LβE₂−2〈B₂,R₂〉`, uses the paper's parameter β, and compares only `Lβ` on the shared range `1/3≤β<1`. The symmetric Lean theorem changes that loss to `64/[3(1−β)]−18` while retaining the same next-energy and drift terms. These are generator losses, not the noise-only coefficients with constant −20.

The shipped `actualAppellLowerDriftTensor` is exactly the paper's full `R_j` in (3.8): it includes every subset of size at least two, including the terminal full subset. At rank two the proper remainder is empty, but `R₂=κ₃(·,·,B₁)` generally remains. The README correctly retains its inner-product term and states that `𝒟` acts on the covariance-normalized tilt energy at the isotropic base point. Direct definitions and the exact compiled general/symmetric generator statements confirm the signs and raw ordered-tensor normalization.

All **1,654** current Lean source hashes again match the source manifest, completed-build source records, and previous notation audit's aggregate source-hash digest. All earlier review files, both notation-correction audit files, the source manifest, build receipt, endpoint audit, public interfaces, upstream OpenAI model and launcher evidence remain byte-identical to the baseline commit. Historical reviews retain their original README bindings; this new audit supplements them without rewriting them.

This audit used the cached primary paper text, SHA-256 `f2cb9d2788a30d2e2b1a54458f2183233b0877c7e612687c448b14e2643847f4`. The coordinating agent also viewed the live arXiv PDF. No new Lean compilation, external checker run or full rebuild was performed. All local README links resolve. The only files created by this audit are this report and `equation-314-correction-audit.json`.
