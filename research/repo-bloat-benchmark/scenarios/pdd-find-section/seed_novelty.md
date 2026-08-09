# Seed-novelty audit — scenario `pdd-find-section` (design §4.1.1 step 6)

| Field | Value |
|---|---|
| Upstream repo / pinned commit | `github.com/promptdriven/pdd` @ `4056cfecab558cf6a8e29072e4f3796ddda6fa7b` |
| Upstream target file | `pdd/find_section.py` (sha256 `973fc53d8e0a0c24401a52f5a565598aeb5436fec4e0ab0314afb2983580fc47`) |
| Seeded core target | `core/src/pdd/find_section.py` (sha256 `84587b0367037e22eeb27d4c3db7af76894287c182a59accf9c35a3070c0b756`) |
| Oracle-fixed target | sha256 `4635f15a530b6979235a6dbb4a21606e413ebd47805f296d3f1fd12169a50127` |
| Oracle patch (old→new) | sha256 `13cd5f33e289e3f9e867bb2601993e621be70bf678b6b0c035138c1a329740af` |
| Reviewer | scenario author (recorded in the sub-PR that introduced this directory) |
| **Classification** | **`upstream_recall_caveat`** |

## Byte-novelty check (mechanical)

The **oracle-fixed** target file is **not** byte-identical to the pinned
upstream file (identifiers, structure, and docstrings were normalized during
slicing — the full transform is recorded in `seed.patch`). The exact fixed
line, `found.append((language, start, len(lines) - 1))`, does **not** occur
verbatim in the upstream file (upstream spells the same behavior as
`sections.append((lang, start, len(lines) - 1))` with different
identifiers). The byte-for-byte-restoration rejection criterion therefore
does **not** fire.

## Semantic-restoration review (judgment)

The oracle patch is a minimal undo of the seeded hunk: it restores the
upstream *behavior* (unclosed blocks end at `len(lines) - 1`) with no new
logic. Per §4.1.1 this is a **semantic restoration of upstream behavior**,
so the scenario is recorded in the **upstream-recall stratum** rather than
claimed as `novel`: a model that has memorized upstream `pdd` could, in
principle, recall the correct unclosed-block semantics rather than derive
them. Mitigations that remain in force: the sliced file's surface form
differs from upstream (recall of exact upstream text does not produce a
valid patch for this tree), and the report stratifies this scenario's
results under the recorded caveat (design §7.4).

## Slicing artifacts (part of the invariant core, never distractors)

- `core/src/pdd/__init__.py` is a minimal stub replacing the upstream
  package `__init__` (which re-exports the CLI surface and sits outside the
  dependency closure of the visible tests).
- The visible suite is the upstream test file minus its unclosed-block
  cases; those cases moved (strengthened) into the hidden verifier, per the
  §4.1.1 requirement that the target site be under-covered by visible tests.
