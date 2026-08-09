# Seed-novelty audit — scenario `pdd-failure-classification` (design §4.1.1 step 6)

| Field | Value |
|---|---|
| Upstream repo / pinned commit | `github.com/promptdriven/pdd` @ `4056cfecab558cf6a8e29072e4f3796ddda6fa7b` |
| Upstream target file | `pdd/failure_classification.py` (sha256 `0675857d23f52e447f15ace22ec37c2f003a61d3c810254c8547129c29d697ff`) |
| Seeded core target | `core/src/pdd/failure_classification.py` (sha256 `f8494a8773c3e1428c93a7f58d99808e521771e1d7a92523443eb2e5c5c75d62`) |
| Oracle-fixed target | sha256 `77779994eea60b185e6f4c5e39e0d4eff46b1e4983ac4bddc9d736bb35c02f61` |
| Oracle patch (old→new) | sha256 `e935ac5ba150deeae26acdea2a78a7025f78bc4a9f08f77e788064c903be7a2f` |
| Reviewer | scenario author (recorded in the sub-PR that introduced this directory) |
| **Classification** | **`upstream_recall_caveat`** |

## Byte-novelty check (mechanical)

The **oracle-fixed** target file is **not** byte-identical to the pinned
upstream file (regex constants renamed `_RE_TIMEOUT`/`_RE_SYNTAX_IMPORT` →
`_TIMEOUT_PATTERN`/`_SYNTAX_IMPORT_PATTERN`, `lower` → `lowered`,
`fm`/`em` → `file_match`/`exception_match`; the upstream ordering comments
— "Match before generic errors…" and the docstring's "Order: …" line — were
removed as part of normalization so the seed is not self-announcing). The
exact fixed hunk does **not** occur verbatim in upstream (different
identifier names). The byte-for-byte-restoration rejection criterion does
**not** fire.

## Semantic-restoration review (judgment)

The oracle patch swaps the two cascade checks back to timeout-first — a
minimal undo of the seeded hunk restoring upstream *behavior* with no new
logic. Per §4.1.1 this is a **semantic restoration of upstream behavior**,
so the scenario is recorded in the **upstream-recall stratum**: a model that
has memorized upstream `pdd` could recall the correct precedence rather
than derive it from the brief. Mitigations: the sliced surface form differs
from upstream (verbatim recall does not produce a valid patch), and results
stratify under the recorded caveat (design §7.4).

## Slicing artifacts (part of the invariant core, never distractors)

- `core/src/pdd/__init__.py` is a minimal stub replacing the upstream
  package `__init__` (outside the dependency closure of the visible tests).
- The visible suite is the upstream test file minus its mixed-marker
  precedence case (`test_classify_timeout_before_syntax_keyword`); that
  contract moved (strengthened) into the hidden verifier, per the §4.1.1
  requirement that the target site be under-covered by visible tests.
