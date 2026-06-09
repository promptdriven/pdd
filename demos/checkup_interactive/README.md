# Agentic Checkup Demo — issue #1423

Proves, with **real `python -m pdd …` commands**, that `pdd checkup <prompt>`
is now an **LLM-agentic, interactive** workflow that plans, runs, and repairs
across the same six check engines exposed by the direct subcommands.

**Branch:** `demo/interactive-checkup-1423`
**Implementation branch:** `change/issue-1423`

---

## What this demo proves

A human reviewer running this demo from a fresh checkout can verify that:

1. the agentic architecture exists and is wired into the CLI;
2. `pdd checkup <prompt> --interactive` drives an agentic session;
3. deterministic planning works **offline** (no LLM, CI-safe);
4. the LLM planning path is exposed and **falls back gracefully** when no
   credential or network is available;
5. `--auto` applies the best repair for every finding without prompts;
6. typing `a` during an interactive session switches the rest of the session
   to auto mode;
7. the unified agentic flow reaches **all six tools** —
   `lint · contract · coverage · gate · snapshot · drift`;
8. the **direct subcommands** still work on their own;
9. it is human-verifiable end-to-end, not just a unit test.

---

## Architecture (added on `change/issue-1423`)

| Component | File | Responsibility |
|---|---|---|
| `CheckupTool` + `ALL_TOOLS` | `pdd/checkup_tools.py` | Six wrappers (lint, contract, coverage, gate, snapshot, drift) that extract each engine's result from one unified report. |
| `DeterministicPlanner` | `pdd/checkup_planner.py` | Always plans all tools in fixed order. No LLM. CI-safe. |
| `LLMPlanner` | `pdd/checkup_planner.py` | Asks an LLM which tools matter most for the prompt; **falls back to `DeterministicPlanner`** on any failure (no key, no network, parse error). |
| `CheckupAgent` | `pdd/checkup_agent.py` | Orchestrates plan → confirm → run report → per-tool interactive repair. Supports interactive and auto modes. |
| `TerminalCheckupSession` / `RecordingCheckupSession` | `pdd/checkup_agent.py` | Terminal I/O session, and an offline test-double session. |

The unified command calls `build_prompt_source_set_report`, which invokes the
**same underlying engines** as each direct subcommand — so the agentic flow and
the direct subcommands cannot diverge.

---

## CLI surface

```bash
pdd checkup <prompt> --interactive [--planner deterministic|llm] [--auto]
```

| Flag | Meaning |
|---|---|
| `--interactive` | Enter the agentic per-finding session (requires a TTY unless `--auto`). |
| `--planner deterministic` | Plan all tools in fixed order, offline (default when `--auto` is used). |
| `--planner llm` | Let an LLM prioritise tools; falls back to deterministic on failure. |
| `--auto` | Apply the best repair option for every finding with **no prompts**. Safe without a TTY (CI / scripted replay). |

Interactive per-finding menu:

```
[1] primary repair      [2] alternative repair
[3] write my own        [4] skip
[a] switch to auto mode for all remaining findings
```

Direct subcommands (unchanged):

```bash
pdd checkup lint <target>
pdd checkup contract check <target>
pdd checkup coverage <target>
pdd checkup gate <target>
pdd checkup snapshot <target>
pdd checkup drift <devunit>
```

---

## Prerequisites — install the editable source

```bash
source .venv/bin/activate
pip install -e .
```

> **Why the demo uses `python -m pdd` (not bare `pdd`)**
> A stale `.venv/bin/pdd` shim can point at an older installed build and fail
> with `ImportError: cannot import name 'get_version' from 'pdd'`.
> `python -m pdd` always runs the editable source in the current interpreter.
> If you still see that error, your editable install is stale — re-run
> `source .venv/bin/activate && pip install -e .`.

---

## How to run

### Interactive menu (run in a real terminal)

```bash
bash demos/checkup_interactive/run_demo.sh
```

```
1) Run unified agentic interactive demo (live, needs a terminal)
2) Run deterministic planner demo (offline, all six tools)
3) Run auto mode demo
4) Run LLM planner fallback demo
5) Run direct subcommand comparison
6) Run all non-interactive checks
7) Cleanup generated demo artifacts
q) Quit
```

### Non-interactive replay (CI-safe, no TTY required)

```bash
bash demos/checkup_interactive/run_demo.sh --all            # 2+3+4+5
bash demos/checkup_interactive/run_demo.sh --deterministic  # offline planner, all six tools
bash demos/checkup_interactive/run_demo.sh --auto           # auto-apply every finding
bash demos/checkup_interactive/run_demo.sh --llm-fallback   # LLM path + graceful fallback
bash demos/checkup_interactive/run_demo.sh --direct         # six direct subcommands
bash demos/checkup_interactive/run_demo.sh --cleanup        # remove generated artifacts
```

### Drive the interactive session by hand

```bash
python -m pdd checkup \
  demos/checkup_interactive/prompts/02_vague_clarification.prompt \
  --interactive --planner deterministic
```

Choose `[4]` (skip) for the first vague-term finding, then type `a` on the
second finding to watch the session finish the rest in auto mode.

The non-interactive equivalents (no TTY needed):

```bash
python -m pdd checkup demos/checkup_interactive/prompts/02_vague_clarification.prompt \
  --interactive --planner deterministic --auto

python -m pdd checkup demos/checkup_interactive/prompts/03_formatting_edge_case.prompt \
  --interactive --planner llm --auto
```

---

## Prompt fixtures

| Fixture | Demonstrates |
|---|---|
| `01_clean_task.prompt` | Clean baseline — checks pass or skip. |
| `02_vague_clarification.prompt` | Vague requirement terms → lint warns; findings flagged `requires_clarification` and routed to the interactive/agentic repair path. |
| `03_formatting_edge_case.prompt` | `%`, `{}`, code fences, nested bullets — formatting-sensitive paths do not crash. |
| `04_contract_sensitive.prompt` | `<contract_rules>` (R901–R903) for `contract check`; coverage reports 3 unchecked rules. |
| `05_coverage_sensitive.prompt` | Rules R301–R304 + user stories; coverage reports 4 unchecked rules. |
| `06_snapshot_candidate.prompt` | Declares nondeterministic `<include query=…>` context; `snapshot` fails until a replayable snapshot exists. |
| `07_drift_candidate.prompt` | Documents the drift dev unit (runnable copy lives in `drift_workspace/`). |

### Extra fixtures

- `context/github_issues_example.py` — stand-in context source for the snapshot prompt.
- `drift_workspace/` — a minimal PDD project (`prompts/drift_candidate_python.prompt`
  + baseline `src/drift_candidate.py`) so the **direct** `pdd checkup drift` command
  can resolve a dev unit. `drift` resolves a dev unit from a project root, not from
  a bare prompt file, so the demo runs it as:

  ```bash
  ( cd demos/checkup_interactive/drift_workspace \
    && PYTHONPATH="$REPO_ROOT:$PYTHONPATH" \
       python -m pdd checkup drift drift_candidate --dry-run )
  ```

  `--dry-run` compares the committed baseline for stability and performs **no
  regeneration**, so it makes no LLM/network call. (The `PYTHONPATH` prefix keeps
  the real `pdd` package importable while the working directory is the dev unit.)

---

## What success looks like

- `--deterministic` / `--auto` / `--all` end with `Summary: PASS: N  FAIL: 0`.
- The deterministic run prints `Checking: lint … contract … coverage … gate …
  snapshot … drift` — proof the agentic flow reaches all six tools.
- The auto run prints `[auto] …` lines and a summary with `… auto-applied`.
- The direct run shows each subcommand's own output and the drift report
  (`Status: stable`).

### Expected, intentional warnings/failures

These are **demonstrations, not bugs**:

- `02_vague_clarification` → `lint: warn` (10 vague terms).
- `04_contract_sensitive` → `contract: warn` (1 vague term) and `coverage` shows
  unchecked rules.
- `05_coverage_sensitive` → `coverage: warn` (4 unchecked rules).
- `06_snapshot_candidate` → `snapshot: FAIL` (no replayable snapshot exists).

---

## Troubleshooting

| Symptom | Fix |
|---|---|
| `ImportError: cannot import name 'get_version' from 'pdd'` | Stale editable install: `source .venv/bin/activate && pip install -e .`. |
| `--interactive requires a TTY` | Add `--auto` for a non-interactive agentic session, or run in a real terminal. |
| LLM planner prints model/auth errors then “falling back to deterministic” | Expected with no API key / no network — the session still completes. Set a credential to exercise real LLM planning. |
| `command not found: pdd` | Use `python -m pdd …` (the demo already does). |
| Leftover `.pdd/` or `pdd-core-*.json` under the demo dir | `bash run_demo.sh --cleanup`. |

---

## How this verifies the unified flow reaches all six tools

`run_demo.sh --deterministic` runs `pdd checkup <prompt> --interactive
--planner deterministic --auto` and asserts the session output contains a
`Checking: <tool>` line for each of lint, contract, coverage, gate, snapshot,
and drift. `tests/commands/test_checkup_interactive_demo.py` additionally drives
`CheckupAgent` directly (offline, no TTY, no LLM) and asserts six `tool_start`
events — one per engine.
