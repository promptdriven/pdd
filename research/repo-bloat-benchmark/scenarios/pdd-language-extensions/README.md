# Scenario `pdd-language-extensions` — real PDD pilot scenario 3/3

A frozen bug-fix scenario per design §4.1.0/§4.1.1: a dependency-sliced core
of the **PDD repository itself** (pinned commit in `scenario.json`), one
seeded behavior defect, a withheld hidden verifier, and real out-of-core PDD
files as the distractor pool. Subsystem: sync/path-resolution data layer
(distinct from scenarios 1 and 2). The core includes verbatim upstream
package data (`data/language_format.csv`) — the only pilot scenario whose
closure carries a data file.

- **Target**: `src/pdd/language_extensions.py` (sliced from upstream;
  transform recorded in `seed.patch`).
- **Seeded defect** (last-write-wins): the first-match-wins guard on
  duplicate CSV rows is missing, so `bundled_extension("YAML")` returns
  `"yaml"` instead of the canonical `"yml"`. Visible tests exercise only
  singleton languages; the hidden verifier pins the duplicate-row contract.
- **Audit**: `seed_novelty.md` — classification `upstream_recall_caveat`,
  the **strongest** of the pilot set (the fixed line occurs verbatim
  upstream); retained deliberately so the three scenarios span a
  recall-risk gradient (see the audit for the rationale).
- **Committed manifests**: `../../distractors/pdd-language-extensions/`
  (ladder 1x–50x + `manifests.lock`). **Tolerance is 10%** for this scenario
  (recorded per-manifest in `size_token_tolerance_pct`): the 2x step's
  residual (~90 tokens) is below the template generator's minimum viable
  module, so the 2% default cannot converge — a documented §9
  infeasibility accommodation. Analysis is unaffected: fits and thresholds
  use the exact measured `distractor_tokens_on_disk`, not the target.

Regenerate / gate (no model tokens):

```bash
cd research/repo-bloat-benchmark
python3 -m harness.distractors.cli \
    --scenario-id pdd-language-extensions \
    --core scenarios/pdd-language-extensions/core \
    --pool scenarios/pdd-language-extensions/pool \
    --target-file src/pdd/language_extensions.py \
    --sizes 1 2 5 10 20 50 --seed 1209 --tolerance-pct 10 \
    --leak-denylist-file scenarios/pdd-language-extensions/leak_denylist.txt \
    --out distractors/pdd-language-extensions
python3 -m harness.runner.preflight --config scenarios/pdd-language-extensions/preflight.json
```
