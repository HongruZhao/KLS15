# Source provenance

The export preserves 2,951 inherited Lean files byte-for-byte: all 921 named
modules in the accepted publication of 20 October 2026, plus 2,030 local imports.
Of those imports, 1,957 match the earlier complete 1,971-source fresh-build
manifest; the remaining 73 match individual historical verification receipts.
The four new release sources are `KLS14.lean`, `Challenge.lean`, `AxiomAudit.lean`
and `FullAudit.lean`. Their release verification is reported separately.

The portable fingerprints and import graph are in `verification/`. They preserve
the distinction between a current named receipt, an inherited direct receipt,
and an inherited complete-project build. No source-export operation constitutes
a new Lean proof check. Conditional and scalar-only theorems keep their original
hypotheses and scientific scope.

`OAI/Analysis/KLS/Model.lean`, its original namespace and its proposition are
unchanged. Source headers, the project license, and third-party legal records
are retained. `MERGED_PROJECT_NOTICE.txt` is the verbatim historical notice.
