# `pdd checkup` in the PDD lifecycle

This walks through where `pdd checkup <prompt>` fits in prompt-driven
development, with the exact commands a reviewer can run. It is understandable
without reading the source.

```
PRD / issue / user request
    ↓
generate or update prompt(s)
    ↓
automatic prompt checkup          ← pdd checkup <prompt>
    ↓
LLM-assisted / interactive repair ← --interactive  (or --auto)
    ↓
pass / warn → continue   OR   strict failure → block
    ↓
generate or modify code           ← pdd generate <prompt>
```

Run the whole thing non-interactively:

```bash
bash demos/checkup_interactive/run_demo.sh --workflow
```

The `--workflow` demo runs the **one simple command in auto mode over every
prompt** in `demos/checkup_interactive/prompts/`:

```bash
for f in demos/checkup_interactive/prompts/*.prompt; do
  python -m pdd checkup "$f" --planner deterministic --auto
done
```

Auto mode handles everything — it groups findings, applies low-risk fixes,
saves medium-risk fixes for review (never fabricated), writes artifacts, and
prints a `Decision:` for each prompt. The demo tallies the outcomes, e.g.:

```
Prompts checked: 7    pass: 3    warn: 3    block: 1
```

`pass`/`warn` continue the lifecycle; `block` (here `06_snapshot_candidate`, a
hard snapshot-policy error) stops it until the prompt is fixed. The steps below
explain one prompt end to end.

---

## Step 1 — PRD / issue / user request

A real request, slightly vague:

> "Add an auth-check module that validates user sessions and rejects
> unauthorized or duplicate tokens."

## Step 2 — generate or update the prompt

The request becomes a PDD prompt. For this demo it is
`demos/checkup_interactive/prompts/02_vague_clarification.prompt`, whose
`<requirements>` use undefined words like *valid*, *active*, *unauthorized*,
*duplicate*, …

## Step 3 — automatic prompt checkup (the gate)

```bash
python -m pdd checkup demos/checkup_interactive/prompts/02_vague_clarification.prompt \
  --planner deterministic
```

This is the **simple default command** — no extra flags. It:

- runs all six checks (lint, contract, coverage, gate, snapshot, drift);
- **groups** the 10 undefined terms into one summary (not ten prompts);
- shows **why** tools were skipped (`coverage: skip — no <contract_rules> to cover`);
- writes artifacts under `.pdd/checkup/` (a report + a patch preview);
- prints a truthful **accounting** summary and a **Decision**.

```
Found 10 undefined vague terms in requirements:
  active, valid, invalid, unauthorized, graceful,
  successful, duplicate, untrusted, authorized, trusted

Recommended fix:
  Add a <vocabulary> block with observable definitions.
...
Decision:
  warn → continue with review note
```

## Step 4 — LLM-assisted / interactive repair

By default nothing is written — the recommended fix (a `<vocabulary>` block) is
**saved for review** as a patch preview:

```
.pdd/checkup/02_vague_clarification.patch
```

Drive it interactively (one grouped question, with an `[a]` switch to auto):

```bash
python -m pdd checkup demos/checkup_interactive/prompts/02_vague_clarification.prompt \
  --interactive --planner deterministic
```

Apply for real (then checkup **re-verifies** the fix):

```bash
python -m pdd checkup demos/checkup_interactive/prompts/02_vague_clarification.prompt \
  --interactive --planner deterministic --apply
```

Repair risk decides what auto mode may do:

| Risk | Examples | Behaviour |
|---|---|---|
| low | mechanical lint fix | auto-applied (`--apply`) / queued |
| medium | undefined vague term, coverage/gate gaps | **saved for review** (never fabricated) |
| high | contract / evidence errors | **manual TODO** |

## Step 5 — decision: continue or block

`checkup` is a **gate**. Its exit code lets CI or the next PDD step decide:

| Outcome | Decision | Exit code |
|---|---|---|
| clean prompt | `pass → continue` | 0 |
| non-blocking findings | `warn → continue with review note` | 0 |
| `--strict` with findings | `strict failure → block` | 2 |
| hard error (e.g. snapshot policy) | `blocking findings → block` | 2 |

Try all three:

```bash
python -m pdd checkup demos/checkup_interactive/prompts/01_clean_task.prompt --planner deterministic            # pass  → continue (exit 0)
python -m pdd checkup demos/checkup_interactive/prompts/02_vague_clarification.prompt --planner deterministic   # warn  → continue (exit 0)
python -m pdd checkup demos/checkup_interactive/prompts/02_vague_clarification.prompt --planner deterministic --strict  # block (exit 2)
```

## Step 6 — generate or modify code

Because the decision is **continue**, the next PDD step runs:

```bash
python -m pdd generate demos/checkup_interactive/prompts/02_vague_clarification.prompt
# → produces pdd/auth_check.py
```

If the decision had been **block**, this step would be skipped until the prompt
is repaired and re-checked. (Code generation needs an LLM and is not executed by
the demo — but this is the exact next command in the lifecycle.)

---

## One-liner gate in a script

```bash
if python -m pdd checkup "$PROMPT" --planner deterministic --strict; then
  python -m pdd generate "$PROMPT"     # prompt is ready
else
  echo "Prompt not ready — see .pdd/checkup/*.report.md"; exit 1
fi
```
