# Scenario `pdd-find-section` — real PDD pilot scenario 1/3

A frozen bug-fix scenario per design §4.1.0/§4.1.1: a dependency-sliced core
of the **PDD repository itself** (pinned commit in `scenario.json`), one
seeded behavior defect, a withheld hidden verifier, and real out-of-core PDD
files as the distractor pool.

- **Target**: `src/pdd/find_section.py` (sliced from upstream
  `pdd/find_section.py`; transform recorded in `seed.patch`).
- **Seeded defect**: unclosed fenced blocks report end index `len(lines)` —
  one past the final line. Visible tests (upstream subset) exercise only
  closed-block behavior; the hidden verifier pins the unclosed contract.
- **Pool** (`pool/src/pdd/`): verbatim upstream leaf modules
  (`comment_line.py`, `failure_classification.py`, `get_lint_commands.py`) —
  stdlib-only, dependency-closed, never imported by the visible tests. The
  generator's `mutate`/`template` modes extend past the pool for high ladder
  steps.
- **Audit**: `seed_novelty.md` (classification: `upstream_recall_caveat`).
- **Committed manifests**: `../../distractors/pdd-find-section/` (ladder
  1x–50x + `manifests.lock`), regenerable with:

```bash
cd research/repo-bloat-benchmark
python3 -m harness.distractors.cli \
    --scenario-id pdd-find-section \
    --core scenarios/pdd-find-section/core \
    --pool scenarios/pdd-find-section/pool \
    --target-file src/pdd/find_section.py \
    --sizes 1 2 5 10 20 50 --seed 1209 \
    --leak-denylist-file scenarios/pdd-find-section/leak_denylist.txt \
    --out distractors/pdd-find-section
```

Gate it (no model tokens) with:

```bash
python3 -m harness.runner.preflight --config scenarios/pdd-find-section/preflight.json
```
