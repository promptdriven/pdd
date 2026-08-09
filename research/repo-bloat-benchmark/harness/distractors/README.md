# Distractor definition + generator

Implements design.md **§5** (v2): the formal distractor-file contract and the
deterministic generator that fills per-(scenario, size) token budgets on the
ladder `1x/2x/5x/10x/20x/50x` — and beyond, for the H3 breakdown probe.

## Pieces

| File | Role |
|------|------|
| `DEFINITION.md` | the five-condition distractor contract, mapped to its machine checks |
| `definition.py` | `DefinitionChecker` — the single implementation of those checks; every admitted file passes it, whatever its source mode |
| `vocabulary.py` | deterministic identifier/word harvest from the core (feeds mutate/template plausibility) |
| `generator.py` | `generate_manifest(config, size)` — budget filling via the fixed mode cascade **regrow → mutate → template**, dependency-closed regrow groups, tier assignment from layout, rejection log |
| `manifest.py` | manifest persistence (+ generated-file contents), `manifests.lock` freeze enforcement |
| `cli.py` | `python3 -m harness.distractors.cli` — generate a whole ladder + lockfile |

## Generate a ladder

```bash
cd research/repo-bloat-benchmark
python3 -m harness.distractors.cli \
  --scenario-id off-by-one-pagination \
  --core scenarios/off-by-one-pagination/core \
  --pool snapshots/pdd@<commit>/pool \
  --target-file src/pkg/pagination.py \
  --sizes 1 2 5 10 20 50 \
  --seed 1209 \
  --out distractors/
```

Each manifest records: token budget vs. realized dose, per-file
`mode`/`tier`/`sha256`/`import_group`, `mode_counts`, a `budget_met` flag, and
the full **rejection log** (which candidates the definition checks refused and
why) — so the freeze-before-runs commit is auditable.

## Properties the tests pin down

- **Determinism**: same inputs + seed ⇒ byte-identical manifest; different
  seed ⇒ different selection.
- **Budget convergence**: 50x is met within ±2 % even from a tiny pool — the
  cascade falls through to `mutate` then `template`, and `template` is
  size-tunable so any budget converges (this is what makes the breakdown
  probe past 50x possible).
- **Contract enforcement**: core/target collisions, core-importable names,
  `conftest.py`-style ambient files, dynamic-import red flags, unparseable
  code, off-vocabulary generated code, hidden-assertion leakage, and
  tell markers are all rejected (each has a dedicated test).
- **1x control** is exactly the empty manifest.
- **Freeze**: `manifests.lock` verification fails on any post-commit edit.

No external dependencies (stdlib + pytest only).
