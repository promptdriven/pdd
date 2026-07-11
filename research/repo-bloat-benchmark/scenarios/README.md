# Pilot scenarios — status

Design §4.1.0: the pilot uses **3 frozen bug-fix scenarios**, dependency-
sliced from the PDD repository @ a pinned commit
(`4056cfecab558cf6a8e29072e4f3796ddda6fa7b`), from distinct PDD subsystems.
**All three are committed and gated** — the scenario-authoring blocker is
closed.

| # | Scenario | Subsystem | Seeded defect | Recall stratum | Status |
|---|----------|-----------|---------------|----------------|--------|
| — | `example-pagination` | (synthetic demo) | off-by-one | n/a | pipeline validation only, **not** a pilot scenario |
| 1 | `pdd-find-section` | template/markdown postprocessing | unclosed-fence end index off-by-one | `upstream_recall_caveat` (fix not verbatim upstream) | **committed**, manifests 1x–50x locked, preflight PASS |
| 2 | `pdd-failure-classification` | fix-loop failure triage | timeout/syntax precedence inversion | `upstream_recall_caveat` (fix = reordering of renamed upstream lines) | **committed**, manifests 1x–50x locked, preflight PASS |
| 3 | `pdd-language-extensions` | sync/path-resolution data layer | duplicate-CSV-row last-write-wins | `upstream_recall_caveat` (**strongest** — fix line verbatim upstream) | **committed**, manifests 1x–50x locked (10% tolerance, documented), preflight PASS |

The three seed-novelty classifications intentionally span a recall-risk
gradient (weakest → strongest); the §7.4 methodology note can use it as an
internal control: if recall risk rather than distractor dose predicted
success, scenario 3 would stand apart from scenarios 1–2 at equal sizes.

Each scenario directory contains: `scenario.json`, `task.md`, sliced
`core/`, `core_files.txt`, `seed.patch`, `hidden/` verifier,
`seed_novelty.md`, `leak_denylist.txt`, `preflight.json`, `README.md`.
Committed ladder manifests live under `../distractors/<scenario_id>/`.
Gate everything with `python3 -m harness.runner.preflight --config
scenarios/<scenario_id>/preflight.json` — zero model tokens.
