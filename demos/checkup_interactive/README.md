# Interactive Checkup Demo — issue #1423

Proves that `pdd checkup <prompt>` routes through the same call abstraction
layer as the six direct checkup subcommands.

**Branch:** `demo/interactive-checkup-1423`  
**Integration branch:** `change/issue-1423`

---

## What this demo validates

Issue #1423 unified the following six commands into a single interactive flow:

| Direct subcommand | What it checks |
|---|---|
| `pdd checkup lint <target>` | Vague terms in requirements / contract sections |
| `pdd checkup contract check <target>` | Structural defects in `<contract_rules>` |
| `pdd checkup coverage <target>` | Contract rules without story or test evidence |
| `pdd checkup gate <target>` | Evidence manifests and waiver policy |
| `pdd checkup snapshot <target>` | Nondeterministic context (requires snapshot) |
| `pdd checkup drift <devunit>` | Regeneration stability against evidence |

The unified command `pdd checkup <prompt>` calls `build_prompt_source_set_report`,
which invokes the same underlying engines as each direct subcommand.
The demo shows both paths produce consistent results for identical inputs.

**Merged sub-issues that affect this demo:**
- `#1436` — CLI flags (`--interactive`, `--apply`, `--preview`) and interaction policy
- `#1437` — Deterministic patch apply for interactive checkup
- `#1434` — Pi spike evidence (drift/gate plumbing)
- `#1435` — Session dataclasses moved to `checkup_interactive_session.py`
- `#1438` — `requires_clarification` findings excluded from auto-repair; routed to interactive path

---

## Prerequisites

```bash
pip install -e .          # from the repo root
```

Confirm the CLI is available:

```bash
python -m pdd --version
```

---

## Quick start (CI-safe, no TTY needed)

```bash
bash demos/checkup_interactive/run_demo.sh --all
```

Expected: `=== Results: 21 passed, 0 failed ===`

---

## Interactive menu

From a real terminal:

```bash
bash demos/checkup_interactive/run_demo.sh
```

You will see a menu:

```
  1) Overview    — all checks visible in unified --explain --json
  2) Lint        — vague-term detection (02_vague_requirements)
  3) Contract    — contract rule validation (03_contract_coverage)
  4) Coverage    — contract coverage matrix (03_contract_coverage)
  5) Gate        — waiver/evidence gate (01_clean_task, shows skip)
  6) Snapshot    — nondeterministic context (05_snapshot_candidate)
  7) Drift       — direct subcommand only (evidence required)
  8) Adversarial — error paths and edge cases
  a) All         — run all automated checks
  q) Quit
```

---

## Per-mode demo commands

### Overview — see all 6 checks at once

```bash
pdd checkup demos/checkup_interactive/prompts/01_clean_task.prompt --explain --json \
  | python -m json.tool
```

Look at `reports[0].checks` — all six check names appear: `lint`, `contract`,
`waivers`, `coverage`, `gate`, `snapshot`.  
Drift surfaces as a finding (not a check name) when a `.pdd/evidence/` manifest exists.

### Lint — vague-term detection

```bash
# Unified
pdd checkup demos/checkup_interactive/prompts/02_vague_requirements.prompt --explain

# Direct equivalent
pdd checkup lint demos/checkup_interactive/prompts/02_vague_requirements.prompt
```

Expected: both report vague terms (`valid`, `invalid`, `graceful`, etc.) in the
`<requirements>` block. All findings have `requires_clarification: true` — they
are routed to the interactive path, **not** the auto-repair loop (#1438).

### Contract check — structural validation

```bash
# Unified
pdd checkup demos/checkup_interactive/prompts/03_contract_coverage.prompt --explain

# Direct equivalent
pdd checkup contract check demos/checkup_interactive/prompts/03_contract_coverage.prompt
```

Expected: both report a vague term (`duplicate`) inside `<contract_rules>`.

### Coverage — rule coverage matrix

```bash
# Unified (shows coverage: warn in checks array)
pdd checkup demos/checkup_interactive/prompts/03_contract_coverage.prompt --explain --json \
  | python -m json.tool | grep -A3 '"name": "coverage"'

# Direct equivalent (shows the coverage table)
pdd checkup coverage demos/checkup_interactive/prompts/03_contract_coverage.prompt
```

Expected: rules R901, R902, R903 are `unchecked` (no linked stories or tests).

### Gate — evidence/waiver gate

```bash
# Unified
pdd checkup demos/checkup_interactive/prompts/01_clean_task.prompt --explain

# Direct equivalent
pdd checkup gate demos/checkup_interactive/prompts/01_clean_task.prompt
```

Expected: gate is **skipped** because no `.pdd/evidence/` manifest exists for
`format_list`. This is the correct, expected outcome for a new devunit.

### Snapshot — nondeterministic context

```bash
# Unified
pdd checkup demos/checkup_interactive/prompts/05_snapshot_candidate.prompt --explain

# Direct equivalent
pdd checkup snapshot demos/checkup_interactive/prompts/05_snapshot_candidate.prompt
```

Expected: both fail with "nondeterministic context (query_include) … no replayable
snapshot found". The prompt uses `<include query=...>` which triggers the policy.

### Drift — direct subcommand

Drift requires a `.pdd/evidence/<devunit>.latest.json` manifest. None exists for
the demo prompts, so the direct command needs a real devunit name. The demo shows
the help text to confirm the subcommand is wired.

```bash
pdd checkup drift --help
```

In the unified command, when evidence exists, drift appears as an `info` finding:
```
[drift] drift_readiness — consider 'pdd checkup drift <devunit>' before shipping
```

---

## Adversarial scenarios

### A1: `--apply` without `--interactive` is rejected

```bash
pdd checkup demos/checkup_interactive/prompts/01_clean_task.prompt --apply
```

Expected: exit 2, `Error: --apply requires --interactive.`

### A2: `--interactive` without a TTY fires the guard

```bash
pdd checkup demos/checkup_interactive/prompts/01_clean_task.prompt --interactive < /dev/null
```

Expected: exit 2, `Error: --interactive requires a TTY`

### A3: `--explain --json` on a failing prompt produces valid JSON

```bash
pdd checkup demos/checkup_interactive/prompts/05_snapshot_candidate.prompt --explain --json 2>/dev/null \
  | python -m json.tool
```

Expected: well-formed JSON with `deterministic_exit_code: 2` and a finding for `snapshot_policy`.

### A4: Formatting edge case does not crash

```bash
pdd checkup demos/checkup_interactive/prompts/04_formatting_edge_case.prompt --explain
```

Expected: exit 0, `Status: PASS`, `No findings.`  
The prompt contains `%`, `{}`, code fences, and nested structures — none crash the tool.

### A5 / A6: `requires_clarification` field present and correctly set

```bash
pdd checkup demos/checkup_interactive/prompts/02_vague_requirements.prompt --explain --json 2>/dev/null \
  | python -m json.tool | grep requires_clarification
```

Expected: every finding includes `"requires_clarification": true`.  
These findings must **not** be processed by the auto-repair loop — they need human
clarification via the interactive path (enforced by `_actionable_findings()` in
`prompt_repair.py`, fixed in commit `2fdf39c`).

---

## Prompt fixtures

| File | Trigger | Expected check result |
|---|---|---|
| `01_clean_task.prompt` | Clean baseline | All checks pass or skip |
| `02_vague_requirements.prompt` | Vague terms in `<requirements>` | `lint: warn`, 10 findings with `requires_clarification=true` |
| `03_contract_coverage.prompt` | Contract rules R901–R903 with no evidence | `contract: warn`, `coverage: warn` (3 unchecked rules) |
| `04_formatting_edge_case.prompt` | `%`, `{}`, code fences, nested bullets | No crash, `lint: pass` |
| `05_snapshot_candidate.prompt` | `<include query=...>` tag | `snapshot: fail` (no snapshot evidence) |

---

## How unified maps to direct

The unified command calls `build_prompt_source_set_report`, which internally calls:

| Unified check name | Internal function | Same as direct subcommand |
|---|---|---|
| `lint` | `scan_prompt()` | `pdd checkup lint` |
| `contract` | `check_prompt()` | `pdd checkup contract check` |
| `coverage` | `build_coverage()` | `pdd checkup coverage` |
| `gate` | `run_gate_policy()` | `pdd checkup gate` |
| `snapshot` | `check_snapshot_policy()` | `pdd checkup snapshot` |
| drift (finding) | surfaced as info finding | `pdd checkup drift` (direct only) |

The `source_check` field on every finding in `--explain --json` output identifies
which engine emitted it, making the routing observable.

---

## Run individual modes

```bash
bash demos/checkup_interactive/run_demo.sh --mode overview
bash demos/checkup_interactive/run_demo.sh --mode lint
bash demos/checkup_interactive/run_demo.sh --mode contract
bash demos/checkup_interactive/run_demo.sh --mode coverage
bash demos/checkup_interactive/run_demo.sh --mode gate
bash demos/checkup_interactive/run_demo.sh --mode snapshot
bash demos/checkup_interactive/run_demo.sh --mode drift
bash demos/checkup_interactive/run_demo.sh --mode adversarial
```

---

## Cleanup

The demo is read-only by default. If you ran `--apply` or `--preview` during manual
interactive testing, any file written to a `demo/` or `demos/` prompt path can be
reset with:

```bash
git checkout -- demos/checkup_interactive/prompts/
```

Debug snapshots written to `.pdd/core_dumps/` are auto-generated by the CLI and
can be removed with:

```bash
rm -f .pdd/core_dumps/pdd-core-*.json
```

---

## Troubleshooting

**"python -m pdd: No module named pdd"** — run `pip install -e .` from the repo root.

**"--interactive requires a TTY"** — this is expected in CI. The interactive menu
requires a real terminal (not a pipe). Use `--all` for CI.

**Coverage shows unexpected test matches** — the coverage engine does cross-project
test scanning. If you add tests named `test_R901_...`, they will be picked up.
The demo fixtures use R901–R903 specifically to avoid collisions with existing tests.

**Drift demo shows help text only** — correct. Drift needs a `.pdd/evidence/` manifest
that does not exist for demo prompts. See the Gate section for the evidence workflow.
