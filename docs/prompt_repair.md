# Non-Interactive Prompt Repair Loop

When automatic prompt checkup fails, PDD can run a **bounded, non-interactive repair pass**, re-run checkup, then continue or report remaining issues.

Keeps PDD in prompt space: improve the prompt before code-level debugging.

## Workflow

```text
PDD creates/modifies prompt
     ↓
deterministic prompt checkup
     ↓
pass → continue to code generation/change
fail → non-interactive prompt repair
     ↓
prompt checkup again
     ↓
pass/warn → continue | else report remaining issues (strict may block)
```

## Usage

```bash
# Disable repair (default)
pdd checkup ... --prompt-repair off

# Best-effort repair (continues even if issues remain after repair)
pdd checkup ... --prompt-repair best-effort
```

## What the Repair Loop Fixes (v1)

Schema-aware, bounded edits only:

- Add missing `<vocabulary>` definitions for flagged vague terms
- Normalize contract rule IDs (e.g., `R1`, `R2`, ...)
- Add missing `<coverage>` lines for existing rules
- Add TODO-style story/test action recommendations in `<coverage>`
- Add waiver placeholders when policy allows
- Clarify vague terms with structured patches (not a full rewrite)
- Add `<contract_rules>` skeleton when requirements exist but no contracts

The repair loop does **not** perform full-file rewrites or edit generated code.

## Configuration

```yaml
# .pddrc or pyproject.toml [tool.pdd]
checkup:
  prompt_repair: best-effort   # off | best-effort | strict
  max_prompt_repair_rounds: 1
  max_prompt_token_growth: 1000
  max_prompt_repair_seconds: 120
```

| Key | Default | Description |
|-----|---------|-------------|
| `prompt_repair` | `off` | Repair mode: `off` disables; `best-effort` repairs and continues on failure; `strict` blocks on unresolved issues after repair |
| `max_prompt_repair_rounds` | `1` | Maximum repair-and-recheck iterations |
| `max_prompt_token_growth` | `1000` | Maximum token increase allowed during repair |
| `max_prompt_repair_seconds` | `120` | Wall-clock timeout for the entire repair loop |

## CLI Flags

The following flags can be passed to `pdd checkup` (and related commands that invoke checkup) to override `.pddrc` defaults:

| Flag | Default | Description |
|------|---------|-------------|
| `--prompt-repair MODE` | `off` | Non-interactive repair mode: `off`, `best-effort`, or `strict` |
| `--max-prompt-repair-rounds INT` | `1` | Maximum repair-and-recheck iterations |
| `--max-prompt-token-growth INT` | `1000` | Maximum token increase allowed during repair |
| `--max-prompt-repair-seconds FLOAT` | `120.0` | Wall-clock timeout for the entire repair loop |

## Token Delta Reporting

After repair, PDD reports the token impact:

```
Prompt token delta: +312 tokens
Note: 240 tokens are reusable contract preamble.
```

A warning is emitted if growth exceeds `max_prompt_token_growth`.

## Safety

- Deterministic checkup remains the authority — repair proposals are validated before write
- No arbitrary full-file rewrites in v1
- No generated code edits
- Audit note written under `.pdd/evidence/prompt_repair/<slug>-<timestamp>.json`

## Evidence

Each repair run writes a record to the run's evidence manifest:

```json
{
  "run_id": "...",
  "prompt_path": "prompts/my_module_python.prompt",
  "tokens_before": 412,
  "tokens_after": 724,
  "token_delta": 312,
  "rounds_used": 1,
  "issues_before": 3,
  "issues_after": 0,
  "status": "repaired"
}
```

## Non-goals

- No separate `pdd checkup coach` command
- No interactive questions (deferred to a later issue in the stack)
- No CI interactive mode
- No unbounded agentic repo search
