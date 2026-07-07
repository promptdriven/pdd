# Seed-novelty audit — scenario `pdd-language-extensions` (design §4.1.1 step 6)

| Field | Value |
|---|---|
| Upstream repo / pinned commit | `github.com/promptdriven/pdd` @ `4056cfecab558cf6a8e29072e4f3796ddda6fa7b` |
| Upstream target file | `pdd/language_extensions.py` (sha256 `cb2636f737feac2033e8746d810ee98afd447446e05e33760c37fc2faf1a0792`) |
| Seeded core target | `core/src/pdd/language_extensions.py` (sha256 `d85621006d801d8a7bc635dda7d32affdacc5c06f188f3d4c4a45019230ea21b`) |
| Oracle-fixed target | sha256 `60976fd36b10b35eefe182e12c49e5cb26bd5b1c98f19d3ab6bbf9f12cff24f7` |
| Oracle patch (old→new) | sha256 `6242050b67f999f7110fc82b16558e588d7fdb927b93d99cacaa8ec4b43fcf3e` |
| Reviewer | scenario author (recorded in the sub-PR that introduced this directory) |
| **Classification** | **`upstream_recall_caveat`** (strongest of the three scenarios — see below) |

## Byte-novelty check (mechanical)

The **oracle-fixed** target file is **not** byte-identical to the pinned
upstream file (the upstream first-match-wins comments, the issue #551
references, and the duplicate-YAML docstring paragraph were removed during
normalization so the seed is not self-announcing). The file-level
byte-for-byte-restoration rejection criterion does **not** fire.

**However**, the fixed *line* (`if language and language not in mapping:`)
**does occur verbatim in the upstream file** (upstream carries it with a
trailing comment). This is recorded explicitly: at the line level the
oracle fix is upstream text.

## Semantic-restoration review (judgment)

The oracle patch restores the upstream first-match-wins guard — a semantic
restoration whose surface form is also (at line level) upstream text. This
scenario therefore carries the **strongest upstream-recall caveat of the
pilot set** and its results must be stratified accordingly (design §7.4).
It is retained (rather than replaced) deliberately: the three scenarios
then span a recall-risk gradient — `pdd-find-section` (fix not verbatim
anywhere upstream) → `pdd-failure-classification` (fix is a reordering of
renamed upstream lines) → `pdd-language-extensions` (fix line verbatim in
upstream) — which lets the analysis check whether recall risk, not just
distractor dose, predicts success (a useful internal control the §7.4
methodology note can exploit).

## Slicing artifacts (part of the invariant core, never distractors)

- `core/src/pdd/__init__.py` is a minimal stub replacing the upstream
  package `__init__` (outside the dependency closure of the visible tests).
- `core/src/pdd/data/language_format.csv` is **verbatim upstream package
  data** — part of the dependency closure, never a distractor.
- The visible suite is the upstream test file minus (a) the duplicate-row
  test (`test_yaml_first_match_is_yml` — moved, strengthened, into the
  hidden verifier) and (b) the CSV-unreadable fallback test, which imports
  sync/generation modules outside this slice's closure.
