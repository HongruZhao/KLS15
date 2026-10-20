# Version 3.0.0 verification

`lean_15/` preserves the earlier project. `lean_14/` proves constant 14 and the
stronger exact universal upper **13.810833**. The two projects use separate
source roots and separate object directories. Both retain Lean
`leanprover/lean4:v4.35.0-rc3` and Mathlib
`4beb549110aa44b87d699166cece6e3642bddf34`.

**13.068 is a lower obstruction for the covered scalar proof family. It is not
a universal KLS upper or lower bound.** The epsilon-limit theorem keeps its
explicit family-of-upper-bounds premise. No global technical-method minimum is
claimed.

## Source-only check

```sh
python3 verification/verify_release.py sources --project all
```

This uses only Python's standard library and reads no compiled theorem objects.
It verifies the original manifests, source hashes, local imports, Lake roots and
pins. The legacy library has 1,654 sources, including `KLS15` and `Challenge`;
its retained auxiliary `verification/clean-build-r1/EndpointAudit.lean` is not
an additional library module. The new library has 2,955 sources. A source check
must not be described as Lean verification.

## Ordinary Lake build

```sh
(cd lean_15 && lake exe cache get && lake build KLS15)
(cd lean_14 && lake exe cache get && lake build KLS14)
```

Every library source is explicitly registered. These commands use Lake's normal
freshness decisions. State whether each run rebuilt or reused project objects
from its actual evidence, rather than inferring that from target success.

## External build storage

The optional portable launcher accepts an explicit build root and its required
mount. Each project receives its own external `.lake` directory; temporary files,
logs and custom objects also stay under that root. Supply your own paths:

```sh
python3 verification/build_release.py --project lean_14 \
  --build-root "$KLS_BUILD_ROOT" --required-mount "$KLS_BUILD_MOUNT" \
  --packages-root "$KLS_PACKAGES_ROOT" --cache-ledger "$KLS_CACHE_LEDGER" \
  --cache-objects "$KLS_PROJECT_CACHE" --lean "$KLS_LEAN" \
  --mode entries --execute
```

Use a fresh checkout or extracted archive and an empty external output directory.
`KLS_LEAN` identifies the existing pinned compiler. `KLS_PROJECT_CACHE` and its
ledger identify a previously verified source-matched cache; caches are not
bundled in the source release.

Without `--execute`, the launcher validates sources/storage and prints the plan
without compiling. Existing source `.lake` directories are preserved; the
launcher will not replace an internal directory or redirect a different link.
An absent required mount is an error before any directory creation or compiler
run. The source author's local default disk profile is optional and must also
pass the real mount check. Public readers should supply their own paths.

In `entries` mode, the cache ledger must bind every reused module's shipped
source hash to its actual main-object hash and include every present
`.olean.private`/`.olean.server` companion. No `.olean`-only completeness claim is
made. New or selected sources are compiled again against the isolated, checked
ledger. `all` mode uses an empty project-object directory and compiles every
registered local module, recording each exit status and hash; pinned external
dependency objects may still be reused.

## Metadata edits and wrapper repairs

After documentation or report edits:

```sh
python3 verification/verify_release.py refresh-metadata --project lean_14
```

This refresh refuses all Lean-source or pin changes. The only exception is an
explicit root-receipt-gated amendment of the four new release wrappers:

```sh
python3 verification/verify_release.py refresh-metadata --project lean_14 \
  --wrapper-receipt "$KLS_PASSED_RELEASE_RECEIPT"
```

That option requires a completed PASS replay of all four new wrappers, the
strongest actual endpoint and the public nine-query axiom audit. It records old
and new source hashes. It never permits changes to the 2,951 inherited scientific
sources. Legacy source files and the original legacy manifest remain unchanged;
legacy metadata refresh writes a separate overlay manifest.

## Actual release results

On **20 October 2026**, both relocated projects passed their fresh named checks
and their independent normal Lake-environment statement audits. All generated
compilation files were kept on the mounted external SSD. Lean and Mathlib pins
match those above; external dependencies and source-matched project objects were
reused.

| Project | Library sources | Source-matched cache seeds | Fresh named checks | Normal Lake replay |
|---|---:|---:|---|---|
| `lean_15` | 1,654 | 1,651 | `ActualKLS15VerifiedEndpoints`, `KLS15`, `Challenge` | `lake env lean Challenge.lean`: PASS |
| `lean_14` | 2,955 | 2,951 | strongest actual endpoint, `KLS14`, `Challenge`, `AxiomAudit`, aggregate audit, `FullAudit` | `lake env lean AxiomAudit.lean`: PASS |

The fresh named runs produced **3,422 axiom-query outputs**, including the
aggregate audit's 3,388 queries. Every reported axiom set was contained in
`propext`, `Classical.choice`, and `Quot.sound`. The public constant-14 and exact
13.810833 statements retain the original law and test classes. The unchanged
upstream OpenAI statement is checked with explicit witness 14.

[Machine-readable result](v3/RELEASE_VERIFICATION.json),
[full source/cache/compilation ledger](v3/SUMMARY.json), and
[normal Lake replay](v3/NORMAL_LAKE_ENV.json), and
[independent source and build audit](v3/INDEPENDENT_BUILD_AUDIT.json) record the exact scope and hashes.
Primary cached `.olean` hashes match accepted receipts; the run separately
records the currently observed companion-object hashes. Two cache seeds in the
new project were then replaced by fresh endpoint/audit compilations. The legacy
clean-build receipts remain historical evidence.

This is a fresh relocated endpoint, API and audit verification **with inherited
dependency reuse**, not a new clean rebuild of every local source or of Mathlib
and the Lean standard library. The source archive contains no compiled objects
or build caches. Each project can also be rebuilt from its pinned sources using
the ordinary Lake commands above.
