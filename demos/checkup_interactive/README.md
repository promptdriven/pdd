# Agentic Checkup Demo — issue #1423

Proves, with **real `python -m pdd …` commands**, that `pdd checkup <prompt>`
is a **simple, fast, safe, human-friendly** agentic workflow that plans, runs,
groups findings, recommends safe fixes, writes useful artifacts, and prints a
short, truthful summary — across the same six check engines exposed by the
direct subcommands.

**Branch:** `demo/interactive-checkup-1423`
**Implementation branch:** `change/issue-1423`

---

## What this demo proves

A human reviewer running this demo from a fresh checkout can verify that:

1. the **simple default command** — `pdd checkup <prompt>`
   — runs all checks, groups findings, and prints a concise summary **without a
   single prompt** (review mode);
2. repeated findings are **grouped** (10 vague terms → one summary, not ten menus);
3. tool **skips show a reason** (`coverage: skip — no <contract_rules> to cover`);
4. fixes are **risk-gated**: low-risk = auto/queue, medium = saved for review,
   high = manual — the tool **never fabricates** a risky change;
5. **artifacts** (a report + a patch preview) are written automatically only when
   there are findings, and their paths are printed in the summary;
6. the **final summary** distinguishes fixed-manually / fixed-automatically /
   skipped / remaining and applied / queued / saved-for-review;
7. `--interactive` asks **one grouped question** with an `[a]` switch to auto;
   `--apply` is what actually edits files, after which checks are **re-verified**;
8. the LLM planning path is exposed and **falls back gracefully** offline;
9. the unified flow reaches **all six tools** and the **direct subcommands**
   still work on their own.

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
# Simple default — the bare command IS the agentic review:
# checks, grouped findings, summary, decision, artifacts. No prompts, no flags.
pdd checkup <prompt>

# A whole directory: every prompt is checked; one aggregate pass/warn/block
# summary; exit 2 if any prompt blocks (one gate for the set).
pdd checkup <directory>/

# Interactive: one grouped question per finding group, with an [a] auto switch.
pdd checkup <prompt> --interactive

# Auto: resolve all findings without prompts (low-risk queued, rest saved).
pdd checkup <prompt> --auto

# Actually edit files (then re-verify): add --apply (with --interactive or --auto).
pdd checkup <prompt> --interactive --apply

# Machine output stays on the structured path:
pdd checkup <prompt> --json
pdd checkup <prompt> --explain
```

| Flag | Meaning |
|---|---|
| *(no flags)* | **Agentic review** (default): run checks, group findings, write artifacts, print a summary + decision. Never prompts, never edits. CI-safe, no LLM. |
| `--interactive` | One grouped question per group: `[Y]` queue · `[n]` skip · `[edit]` write your own · `[auto]` finish the rest automatically. Requires a TTY. |
| `--planner deterministic` | Default planner — all tools in fixed order, offline. (Implied by the bare command.) |
| `--planner llm` | Let an LLM prioritise tools; falls back to deterministic on failure. |
| `--auto` | Apply **low-risk** fixes automatically; medium → saved for review; high → manual. Never makes a risky change. No prompts. |
| `--apply` | Actually write the low-risk fixes to the prompt, then re-run the affected checks to verify. Requires `--interactive`. |
| `--json` / `--explain` | Machine-readable / read-only structured output (stays on the non-agent path). |

**Safety model (repair risk).** Every finding is classified:

| Risk | Examples | Default behaviour |
|---|---|---|
| low | mechanical lint fix | auto-applied (with `--apply`) / queued |
| medium | undefined vague term, coverage/gate/snapshot gaps | **saved for review** (never fabricated) |
| high | contract/evidence errors | left as a **manual TODO** |

By default **nothing is written** — fixes are queued / saved and a patch preview
is produced. `--apply` is the only thing that edits files.

**Decision (gate before code generation).** Every run ends with a `Decision:`
line and an exit code so it can gate the next PDD step:

| Outcome | Decision | Exit code |
|---|---|---|
| clean prompt | `pass → continue` | 0 |
| non-blocking findings | `warn → continue with review note` | 0 |
| `--strict` with findings | `strict failure → block` | 2 |
| hard error (e.g. snapshot policy) | `blocking findings → block` | 2 |

```bash
if python -m pdd checkup "$PROMPT" --strict; then
  python -m pdd generate "$PROMPT"     # prompt is ready → generate code
else
  echo "blocked — see .pdd/checkup/*.report.md"
fi
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
1) Run fast prompt checkup demo (the simple default command)
2) Run LLM / interactive repair demo
3) Run strict gate / blocking demo (pass · warn · block)
4) Run full workflow demo (one command over the whole directory)
5) Run all checkup demos
6) Cleanup generated artifacts
d) Direct subcommand comparison (lint/contract/.../drift)
i) Live interactive session (grouped, needs a terminal)
q) Quit
```

### Non-interactive replay (CI-safe, no TTY required)

```bash
bash demos/checkup_interactive/run_demo.sh --all          # every demo below
bash demos/checkup_interactive/run_demo.sh --fast         # the simple default command
bash demos/checkup_interactive/run_demo.sh --repair       # LLM/interactive repair
bash demos/checkup_interactive/run_demo.sh --strict-gate  # pass / warn / strict block
bash demos/checkup_interactive/run_demo.sh --workflow     # one command over the whole directory
bash demos/checkup_interactive/run_demo.sh --auto         # apply low-risk only
bash demos/checkup_interactive/run_demo.sh --llm-fallback # LLM path + graceful fallback
bash demos/checkup_interactive/run_demo.sh --direct       # six direct subcommands
bash demos/checkup_interactive/run_demo.sh --cleanup      # remove generated artifacts
```

**Full lifecycle walkthrough:** see
[`FULL_WORKFLOW.md`](FULL_WORKFLOW.md) — PRD/issue → prompt → checkup → repair →
decision → code, with the exact commands to run.

### Drive the simple command by hand

The fast path — the bare command, agentic review by default (checks, grouped
findings, summary, decision, artifacts, **no prompts, no flags**):

```bash
python -m pdd checkup \
  demos/checkup_interactive/prompts/02_vague_clarification.prompt
```

A whole directory in one command — every prompt is checked, with one aggregate
pass/warn/block summary and exit 2 if any prompt blocks:

```bash
python -m pdd checkup demos/checkup_interactive/prompts/
```

The live interactive session — **one grouped question** for all 10 vague terms,
with an `[a]` switch to auto and `[q]` to quit:

```bash
python -m pdd checkup \
  demos/checkup_interactive/prompts/02_vague_clarification.prompt \
  --interactive
```

Answer `n` to skip the group, `auto` to switch the rest to auto mode, or `q` to
quit (remaining findings left untouched).

Auto mode (no prompts; low-risk applied with `--apply`, the rest saved):

```bash
python -m pdd checkup demos/checkup_interactive/prompts/02_vague_clarification.prompt \
  --auto
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

- `--review` / `--auto` / `--all` end with `Summary: PASS: N  FAIL: 0`.
- The review run prints a compact `Plan:`, a per-tool `Checks:` block with skip
  **reasons**, a single **grouped** vague-term summary, an `Artifacts:` block,
  and a `Findings:` / `Patches:` accounting summary.
- The auto run shows `Saved for review` and `Fixed automatically: 0` — vague
  terms are medium-risk and are **not** fabricated.
- The direct run shows each subcommand's own output and the drift report
  (`Status: stable`).

Example review-mode summary:

```
Checkup complete: warn

Findings:
  Total: 10
  Fixed manually: 0
  Fixed automatically: 0
  Skipped by user: 0
  Remaining: 10

Patches:
  Applied: 0
  Queued: 0
  Saved for review: 10

Artifacts:
  Patch preview: .pdd/checkup/02_vague_clarification.patch
  Report: .pdd/checkup/02_vague_clarification.report.md
```

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
| `--interactive requires a TTY` | Drop `--interactive` for non-interactive **review mode**, or run in a real terminal. |
| LLM planner prints model/auth errors then “falling back to deterministic” | Expected with no API key / no network — the session still completes. Set a credential to exercise real LLM planning. |
| `command not found: pdd` | Use `python -m pdd …` (the demo already does). |
| Leftover `.pdd/checkup/`, `.pdd/`, or `pdd-core-*.json` artifacts | `bash run_demo.sh --cleanup`. |
| Nothing got written to my prompt | By design — only `--apply` (with `--interactive`) edits files; everything else queues / saves for review. |

---

## How this verifies the unified flow reaches all six tools

`run_demo.sh --review` runs `pdd checkup <prompt>` and
asserts the per-tool `Checks:` block names lint, contract, coverage, gate,
snapshot, and drift (with skip reasons). `tests/commands/test_checkup_interactive_demo.py`
additionally drives `CheckupAgent` directly (offline, no TTY, no LLM) and asserts
six `tool_start` events — one per engine — plus the grouped summary, skip
reasons, accounting, and artifact generation.
