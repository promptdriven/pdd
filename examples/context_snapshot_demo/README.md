# Context snapshot & replay demo (issue #826)

Self-contained mini-project for human QA of snapshot/replay reproducibility
([promptdriven/pdd#826](https://github.com/promptdriven/pdd/issues/826)).

Work on branch `change/issue-33` only; this tree is isolated from other feature branches.

## Automated test plan (from repository root)

```bash
pytest -q tests/test_context_snapshot_replay.py \
         tests/test_context_snapshot_policy.py \
         tests/test_evidence_manifest.py \
         tests/test_issue_826_snapshot_touchpoint.py

./examples/context_snapshot_demo/run_demo.sh
./examples/context_snapshot_demo/run_test_plan_manual.sh
```

`run_test_plan_manual.sh` runs the full manual test plan end-to-end (step 5 uses a
stubbed generate test when no LLM API keys are configured).

## Manual touchpoint (human-verifiable)

```bash
cd examples/context_snapshot_demo
export PYTHONPATH="$(cd ../.. && pwd)"

# Snapshot preprocess (records shell/web/include outputs under .pdd/evidence/runs/)
pdd preprocess prompts/foo_python.prompt --snapshot

# Policy gate: fails on a fresh tree with no snapshot for this prompt
pdd checkup snapshot prompts/with_shell_python.prompt --project-root .
# expect exit code 1

# Replay the manifest written by preprocess
RUN=$(ls -1t .pdd/evidence/runs/*.json | head -1)
pdd replay "$RUN" --verify-only --json

# After preprocess on foo_python, checkup passes for that prompt
pdd checkup snapshot prompts/foo_python.prompt --project-root .
```

### Optional: generate + evidence + replay (needs LLM credentials)

```bash
pdd generate prompts/foo_python.prompt \
  --output pdd/foo.py \
  --snapshot-context \
  --evidence \
  --force

pdd replay "$(ls -1t .pdd/evidence/runs/*.json | head -1)" --verify-only
```

The touchpoint test `tests/test_issue_826_snapshot_touchpoint.py` stubs `code_generator_main`
so CI can exercise `--snapshot-context --evidence` without API keys.

## Fixtures

| File | Purpose |
|------|---------|
| `prompts/foo_python.prompt` | Test-plan preprocess + generate (`<shell>`, `<web>`, include) |
| `prompts/with_shell_python.prompt` | Test-plan checkup snapshot fail-before-snapshot |
| `prompts/dynamic_python.prompt` | Same dynamic tags as `foo_python` (legacy name) |
| `prompts/static_python.prompt` | Deterministic include only (policy passes without snapshot) |
| `context/note.prompt` | Included static context |
