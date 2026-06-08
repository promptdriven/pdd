# Lean Prompt Mode Research Harness

Tracks issue [#1473](https://github.com/promptdriven/pdd/issues/1473).

A publishable research harness for measuring and reducing PDD prompt token overhead at the **prompt structure** level without dropping source-truth semantics. This is distinct from dependency-level `--context-compression`, which operates on `<include>` graph content.

---

## Design

### Problem

PDD prompts accumulate workflow framing, repeated narrative, and explanatory boilerplate that does not improve generated output quality but does add token cost on every generation call. In multi-shot and routing scenarios this overhead compounds with `k` — every unnecessary token is paid once per candidate.

### Approach: Deterministic Section-Level Pruning

Lean mode applies a versioned, hardcoded policy rule table that classifies each prompt section as `required` or `removable`. This is intentionally non-LLM-based so the policy artifact is fully auditable without model calls.

**Five required field groups** are always preserved:

| Group | Examples |
|---|---|
| Source-truth content | `<contract_rules>`, `<vocabulary>`, `<responsibility>`, `<non_responsibilities>` |
| Output files | `<output_files>`, allowed-path declarations |
| Verifier command | `<verifier>`, test runner specification |
| Output delimiters | Machine-parseable begin/end tags and schema |
| Safety constraints | `MUST NOT` capability rules, `<capabilities>` block |

**Removable** (pruned in lean mode): workflow narrative (`% Steps`, `% Instructions` when purely procedural), repeated role framing, explanatory preamble boilerplate, and non-contract prose sections.

**Contamination check**: Before pruning any candidate section the harness scans its content for required-field markers. If found, the section is preserved rather than removed, and the policy artifact records it as `preserved_contaminated`.

### Section Parser

PDD prompts use two section-boundary conventions:

1. **`%`-prefixed sections**: `% Role`, `% Requirements`, `% Steps`, `% Instructions`, `% Deliverables`
2. **XML-tag blocks**: `<contract_rules>`, `<capabilities>`, `<vocabulary>`, `<pdd-reason>`, `<output_files>`, `<verifier>`, etc.

The parser handles both styles and assigns each section a stable `section_id` used in the policy artifact.

### Token Counting

Token counting uses a three-tier fallback hierarchy (recorded in `prompt_token_audit.json`):

1. **`pdd.server.token_counter`** — litellm-based counting (used when `pdd/server/token_counter.py` is importable from the repo root).
2. **tiktoken `cl100k_base`** — used when the PDD package is unavailable but tiktoken is installed.
3. **Char approximation** — `1 token ≈ 4 chars`; used when neither of the above is available.

The `approximation` flag in the audit artifact is always `true` in v1 of this harness regardless of which tier is used.

### Structural Floor

The structural floor is the minimum token count achievable while keeping all five required field groups. It is always computed and reported in `aggregate.structural_floor_tokens` and `aggregate.structural_floor_ratio`. If lean mode cannot beat this floor without removing required content, the audit reports the floor rather than silently producing an under-specified prompt.

---

## Usage

```bash
# Lean mode: prune and emit audit artifacts
python research/lean-prompt-mode/lean_prompt.py --mode lean prompts/your_module.prompt

# Current mode (default): pass-through, no pruning
python research/lean-prompt-mode/lean_prompt.py --mode current prompts/your_module.prompt

# Specify output directory for artifacts
python research/lean-prompt-mode/lean_prompt.py --mode lean --out-dir /tmp/audit prompts/your_module.prompt

# Specify model for token counting
python research/lean-prompt-mode/lean_prompt.py --mode lean --model claude-sonnet-4-20250514 prompts/your_module.prompt
```

**Output** (written to `--out-dir`, defaulting to the current directory):

- `<stem>_lean.txt` — the pruned prompt (lean mode) or original (current mode)
- `prompt_policy.json` — pruning decisions and source hashes
- `prompt_token_audit.json` — per-task and aggregate token counts

In `current` mode the lean prompt output is identical to the input; the policy artifact records `mode: "current"` and `removed_sections: []`.

---

## Artifact Schemas

### `prompt_policy.json`

```json
{
  "schema_version": "1.0",
  "mode": "lean",
  "compression_method": "deterministic_section_pruning",
  "policy_version": "1.0",
  "removed_sections": [
    {
      "section_id": "pct_instructions",
      "reason": "workflow_narrative",
      "token_delta": 42
    }
  ],
  "preserved_contract_fields": [
    "contract_rules",
    "vocabulary",
    "responsibility",
    "capabilities",
    "output_files",
    "verifier"
  ],
  "source_inputs": [
    {
      "path": "prompts/your_module.prompt",
      "sha256": "abc123..."
    }
  ]
}
```

Full schema: `schemas/prompt_policy.schema.json`

### `prompt_token_audit.json`

```json
{
  "schema_version": "1.0",
  "tokenizer": "litellm/cl100k_base",
  "approximation": true,
  "model": "claude-sonnet-4-20250514",
  "tasks": [
    {
      "task_id": "your_module",
      "current_tokens": 850,
      "lean_tokens": 530,
      "ratio": 0.624
    }
  ],
  "aggregate": {
    "total_current_tokens": 850,
    "total_lean_tokens": 530,
    "aggregate_ratio": 0.624,
    "structural_floor_tokens": 410,
    "structural_floor_ratio": 0.482
  }
}
```

Full schema: `schemas/prompt_token_audit.schema.json`

---

## Fixtures

Frozen golden fixtures under `fixtures/` enable deterministic CI tests without live model calls:

| File | Description |
|---|---|
| `fixtures/current_prompt.txt` | Synthetic publishable PDD prompt (unmodified) |
| `fixtures/lean_prompt.txt` | Expected lean-pruner output on the golden fixture |
| `fixtures/prompt_policy.json` | Expected `prompt_policy.json` for the golden fixture |
| `fixtures/prompt_token_audit.json` | Expected `prompt_token_audit.json` for the golden fixture |

Fixtures use a synthetic prompt with no private corpus rows. To regenerate them after policy changes:

```bash
cd research/lean-prompt-mode
python lean_prompt.py --mode lean --out-dir fixtures fixtures/current_prompt.txt
# Then rename the output and commit the updated fixtures.
```

---

## Tests

```bash
# Run all harness tests (no API key required)
pytest research/lean-prompt-mode/tests/ -v

# Or from repo root
pytest research/lean-prompt-mode/tests/test_lean_prompt.py -v
```

Tests cover:
- Pruning rule classification (required vs. removable per section type)
- Invariant preservation (all five required groups present in lean output)
- JSON schema validation for both artifact types
- Default-mode regression (current mode leaves prompt unchanged)
- Anomaly flag when lean token count ≥ current token count
- Structural floor is always ≤ lean token count

---

## Relationship to `--context-compression`

| Mechanism | Operates on | Controls |
|---|---|---|
| Lean prompt mode | Prompt structure | Workflow framing, narrative sections |
| `--context-compression` | `<include>` graph | Dependency file content |

Both are orthogonal and can be combined:

```bash
pdd --context-compression examples sync my_module
# Then separately audit prompt structure with the lean harness
python research/lean-prompt-mode/lean_prompt.py --mode lean prompts/my_module_python.prompt
```

---

## CI Integration

The fixture tests require no API key and no network access:

```yaml
# .github/workflows/ci.yml (excerpt)
- name: Lean prompt mode fixture tests
  run: pytest research/lean-prompt-mode/tests/ -v
```

To add the aggregate ratio to CI reporting, pipe the audit artifact:

```bash
python -c "
import json, sys
audit = json.load(open('prompt_token_audit.json'))
ratio = audit['aggregate']['aggregate_ratio']
print(f'Lean/current ratio: {ratio:.3f}')
sys.exit(0 if ratio < 1.0 else 1)
"
```
