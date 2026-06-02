# Context snapshot & replay demo (issue #826)

Self-contained mini-project for human QA of snapshot/replay reproducibility
([promptdriven/pdd#826](https://github.com/promptdriven/pdd/issues/826),
PR [#1345](https://github.com/promptdriven/pdd/pull/1345)).

## Quick verify (from repository root)

```bash
pytest -vv tests/test_issue_826_snapshot_touchpoint.py
./examples/context_snapshot_demo/run_demo.sh
```

## Branch

Maintained on `demo/issue-826-snapshot-verification` (child of `change/issue-33`) so
other feature branches are not disturbed.

## Manual walkthrough

```bash
cd examples/context_snapshot_demo
export PYTHONPATH="$(cd ../.. && pwd)"

# 1) Snapshot preprocess (shell + web mocked in automated test; live shell runs here)
pdd --quiet preprocess prompts/dynamic_python.prompt --snapshot

# 2) Policy should fail before any snapshot exists for a fresh tree
pdd checkup snapshot prompts/dynamic_python.prompt --project-root . && echo UNEXPECTED_PASS || echo "expected fail"

# 3) Replay the snapshot manifest written under .pdd/evidence/
RUN=$(ls -1t .pdd/evidence/runs/*.json | head -1)
pdd replay "$RUN" --verify-only --json

# 4) Policy passes after snapshot
pdd checkup snapshot prompts/dynamic_python.prompt --project-root .

# 5) Optional: generate with snapshot context (requires configured LLM)
# pdd generate prompts/static_python.prompt --snapshot-context --evidence --output pdd/static.py
```

## Fixtures

| File | Purpose |
|------|---------|
| `prompts/dynamic_python.prompt` | Active `<shell>` + `<web>` tags |
| `prompts/static_python.prompt` | Deterministic include only |
| `context/note.prompt` | Included by static prompt |
