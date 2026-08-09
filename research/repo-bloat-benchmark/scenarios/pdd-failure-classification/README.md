# Scenario `pdd-failure-classification` — real PDD pilot scenario 2/3

A frozen bug-fix scenario per design §4.1.0/§4.1.1: a dependency-sliced core
of the **PDD repository itself** (pinned commit in `scenario.json`), one
seeded behavior defect, a withheld hidden verifier, and real out-of-core PDD
files as the distractor pool. Subsystem: fix-loop failure triage (distinct
from scenario 1's markdown postprocessing).

- **Target**: `src/pdd/failure_classification.py` (sliced from upstream
  `pdd/failure_classification.py`; transform recorded in `seed.patch`).
- **Seeded defect** (precedence inversion): syntax/import markers are
  checked before timeout markers, so a log containing both (a run timing
  out during import/collection) misclassifies as `SYNTAX_IMPORT`. Visible
  tests (upstream subset) exercise only single-marker logs; the hidden
  verifier pins the precedence contract.
- **Pool** (`pool/src/pdd/`): verbatim upstream leaf modules
  (`find_section.py`, `comment_line.py`, `get_lint_commands.py`).
- **Audit**: `seed_novelty.md` (classification: `upstream_recall_caveat`).
- **Committed manifests**: `../../distractors/pdd-failure-classification/`
  (ladder 1x–50x + `manifests.lock`, tolerance 2%, all budgets met).

Regenerate / gate (no model tokens):

```bash
cd research/repo-bloat-benchmark
python3 -m harness.distractors.cli \
    --scenario-id pdd-failure-classification \
    --core scenarios/pdd-failure-classification/core \
    --pool scenarios/pdd-failure-classification/pool \
    --target-file src/pdd/failure_classification.py \
    --sizes 1 2 5 10 20 50 --seed 1209 \
    --leak-denylist-file scenarios/pdd-failure-classification/leak_denylist.txt \
    --out distractors/pdd-failure-classification
python3 -m harness.runner.preflight --config scenarios/pdd-failure-classification/preflight.json
```
