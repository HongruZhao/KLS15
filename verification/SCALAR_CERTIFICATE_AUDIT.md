> Archived v2 documentation. [Preserved project copy](../lean_15/verification/SCALAR_CERTIFICATE_AUDIT.md). Current release: [KLS14](../README.md).

# Portable independent scalar audit

`check_scalar_certificates.py` reconstructs the strict-sub15 arithmetic
directly from the shipped Lean source. It executes or imports no producer
script and requires only Python 3's standard library. No separate
mathematical certificate JSON is needed.

From the repository root, use a fresh result path:

```sh
python3 verification/check_scalar_certificates.py --output verification/scalar-audit-reproduction.json
```

The checker preserves existing evidence and refuses to replace an existing
output. Its default source root is the repository containing the checker;
`--root` can select another staged copy. It contains no private absolute
workspace paths.

The [staged result](../lean_15/verification/scalar-audit.json) passes **399 checks**: 369 exact
arithmetic checks and 30 source-provenance checks. The arithmetic includes
the seven seed245 polynomial identities and their whole closed-interval
Bernstein certificates, the four head intervals, every finite degree
4–25, the real tail from 26 onward, parameter ranges, Young prefixes, and
the two-observation endpoint (149963/10000<15).

The source-provenance checks bind ten shipped modules to both the release
source manifest and the source hashes of the original frozen independent
audit. They do not recheck historical compilation logs or objects. The
original 399-check result also included 30 historical source/log/object
receipt checks; that original checker and result have been preserved.

The [portability receipt](../lean_15/verification/scalar-audit-portability-receipt.json) records a
second run in a detached temporary tree containing only the checker, the
source manifest and these ten Lean files. It used no project objects or
external Python packages and produced a byte-identical exact result.

This arithmetic audit is separate from the whole Lean clean build. Its
PASS does not report completion of that build, recompile external
dependencies, or constitute independent human mathematical peer review.
