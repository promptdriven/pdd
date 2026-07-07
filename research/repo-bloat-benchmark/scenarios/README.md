# Pilot scenarios — status

Design §4.1.0: the pilot uses **3 frozen bug-fix scenarios**, dependency-
sliced from the PDD repository @ a pinned commit, ≥2 from distinct PDD
subsystems (the third may come from a second OSS repo as an external-validity
check if time allows).

| # | Scenario | Subsystem | Status |
|---|----------|-----------|--------|
| — | `example-pagination` | (synthetic demo) | committed — pipeline validation only, **not** a pilot scenario |
| 1 | `pdd-find-section` | template/markdown postprocessing | **committed** — seeded bug, hidden verifier, seed-novelty audit (`upstream_recall_caveat`), ladder manifests 1x–50x committed + locked, §4.1.2 preflight PASS at every step |
| 2 | *TODO* `pdd-failure-classification` (candidate) | fix-loop failure triage (`pdd/failure_classification.py`) | not authored — stdlib-only leaf, offline upstream tests (`tests/test_failure_classification.py`); candidate seed: reorder the timeout/syntax regex cascade so mixed logs misclassify |
| 3 | *TODO* `pdd-language-extensions` (candidate) | CSV-driven language→extension resolution (`pdd/language_extensions.py`) | not authored — stdlib-only, offline upstream tests; candidate seed: drop the first-match-wins guard (flips `.yml`/`.yaml` resolution) |

Authoring checklist for scenarios 2–3 (mirror `pdd-find-section`):
`scenario.json` + `task.md` + sliced `core/` + `core_files.txt` +
`seed.patch` + `hidden/` verifier + `seed_novelty.md` + `leak_denylist.txt`,
then generate + commit ladder manifests (`harness.distractors.cli`) and gate
with `harness.runner.preflight` — all zero-billing.
