# pdd prompt lint — feature demo

This directory demonstrates every acceptance criterion of the `pdd prompt lint` command.

This is the canonical example for the built-in PDD prompt-lint workflow.

For a **before/after** walkthrough (lint warnings, coverage linkage, prompt diff),
see [`../prompt_lint_e2e_demo/`](../prompt_lint_e2e_demo/).

## Quick start

```bash
# From repo root, with the local dev install active
pip install -e .                                 # ensure local version is installed
export PDD_SKIP_UPDATE_CHECK=1                   # prevent auto-upgrade overwriting the dev install
bash examples/prompt_lint_demo/demo.sh
```

## Files

| File | Purpose |
|------|---------|
| `prompts/payment_api_vague_python.prompt` | Payment API with 10 undefined vague terms — triggers warnings |
| `prompts/payment_api_clean_python.prompt` | Same prompt with complete `<vocabulary>` — zero warnings |
| `stories/story__charge_flow.md` | User story with vague Acceptance Criteria |
| `stories/story__charge_flow_defined.md` | Same story with `## Covers` vocabulary — zero warnings |

## Feature cheat-sheet

All commands run **from the repo root**. Set `PDD_SKIP_UPDATE_CHECK=1` to avoid
the auto-upgrade prompt overwriting your dev install.

```bash
export PDD_SKIP_UPDATE_CHECK=1
VAGUE=examples/prompt_lint_demo/prompts/payment_api_vague_python.prompt
CLEAN=examples/prompt_lint_demo/prompts/payment_api_clean_python.prompt
STORIES=examples/prompt_lint_demo/stories

# ① Non-LLM default mode (no API key needed)
pdd --quiet prompt lint $VAGUE

# ② Defined terms suppress warnings
pdd --quiet prompt lint $CLEAN                                  # exits 0

# ③ Works on stories
pdd --quiet prompt lint --stories $STORIES $VAGUE
pdd --quiet prompt lint --stories $STORIES

# ④ Suggests <vocabulary> additions  (human output and JSON include suggestions)
pdd --quiet prompt lint $VAGUE

# ⑤ Emits JSON
pdd --quiet prompt lint --json $VAGUE
pdd --quiet prompt lint --json --stories $STORIES $VAGUE

# ⑥ Read-only by default (no --apply → file never changes)
cp $VAGUE /tmp/demo.prompt
pdd --quiet prompt lint /tmp/demo.prompt
diff $VAGUE /tmp/demo.prompt   # empty — file unchanged

# ⑦ --apply writes vocabulary suggestions into the file
cp $VAGUE /tmp/demo.prompt
pdd --quiet prompt lint --ambiguity --apply /tmp/demo.prompt
cat /tmp/demo.prompt   # <vocabulary> block written with LLM-sourced definitions

# ⑧ Optional LLM review (auto coach + clarify when ambiguities found)
pdd --quiet prompt lint --ambiguity $VAGUE
pdd --quiet prompt lint --ambiguity --json $VAGUE

# ⑪ --strict mode (CI gate — exit 2 on any warning)
pdd --quiet prompt lint --strict $VAGUE
echo $?   # 2
```

## Acceptance criteria checklist

| Criterion | Command / behaviour |
|-----------|---------------------|
| Non-LLM default mode | `pdd prompt lint <file>` — no API key needed |
| Optional LLM review | `--ambiguity` — skipped if omitted, never breaks CI |
| Auto coaching + clarification | runs when `--ambiguity` finds LLM-detected ambiguities |
| Works on prompts and stories | `--stories <dir>` scans `story__*.md` files; combine it with a prompt path to scan both |
| Suggests `<vocabulary>` additions | every issue includes a `Suggestion:` line |
| Emits JSON | `--json` flag produces a parseable array |
| Read-only by default | file is unchanged without `--apply` |
| Tests for vague terms, defined terms, story AC, JSON | `tests/test_prompt_lint.py` + `tests/commands/test_prompt.py` |
