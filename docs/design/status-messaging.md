# PDD CLI status & progress messaging

EPIC #1540, workstream 2. This is the design note for `pdd/cli_status.py`, the
single source of truth for *what a command is doing right now*. It builds on the
color system (`pdd/cli_theme.py`, workstream 1) and does not introduce any new
colors.

## Why

Across PDD commands, status output was ad-hoc: some commands printed a green
"done", others said nothing during a multi-second LLM call, and failures often
gave a bare exception string with no next step. Users couldn't reliably tell
what was happening, whether the tool was stuck, or what to do when it failed.

This workstream defines one small, consistent vocabulary so that — in every
command — the user can always answer four questions:

1. **What is happening now?**  → `start` / `step`
2. **What comes next?**        → `next_step=` on `start` / `success`
3. **Is it waiting on me / IO / the model?** → `waiting(...)`
4. **What succeeded or failed, and what do I do about it?** → `success` / `failure`

## The five primitives

There are exactly five message types (`Status` enum). Keeping the set small is
the point — the same kind of event looks identical in every command.

| Primitive  | Glyph | Theme role        | Meaning |
|------------|:-----:|-------------------|---------|
| `START`    | `▶`   | `command.strong`  | A command/operation is beginning. |
| `STEP`     | `→`   | `info`            | The current human-readable step. |
| `WAITING`  | `…`   | `muted`           | Blocked on IO / network / LLM — show progress, not silence. |
| `SUCCESS`  | `✓`   | `success.strong`  | Finished, with an optional next action. |
| `FAILURE`  | `✗`   | `error`           | Failed, with root cause + what to try next. |

Glyphs come from `GLYPHS`, colors from `ROLES` (semantic roles resolved by the
central theme). Nothing here hard-codes a hex value.

## Message rules

- **Short and skimmable.** One line per event; structured extras (`Why:`,
  `Try:`, `Next:`) are indented follow-on lines.
- **Action-oriented.** Say what is being done ("analyzing 3 prompts"), not just
  that something is happening.
- **Non-duplicative.** An identical rendered line emitted twice in a row is
  collapsed, so retry loops and re-entrant steps don't spam the terminal.
- **Consistent.** Every command uses the same five primitives and wording shape.

## Errors must be actionable

`failure(step, *, reason=None, suggestions=())` is structured to meet the UX
criteria: it names **what** failed (the step), **why** (root cause if known), and
**what to try next** (1–2 concrete suggestions). Example render:

```
✗ reading the change file
  Why: change.txt not found
  Try: check the path to the change file
  Try: run `pdd detect --help` for the expected arguments
```

## Long-running work shows progress

`with reporter.waiting("asking the model …", on="LLM"):` records a `WAITING`
event and, on an interactive terminal, shows a spinner for the duration so a
multi-second model/network/disk call never looks frozen. `on=` names what is
being awaited (`"LLM"`, `"network"`, `"disk"`). The spinner is automatically
inert when output is suppressed, redirected, or non-TTY — so it adds no timing
dependence and tests stay deterministic.

## Machine-readable output is preserved

Some commands emit JSON on stdout for dashboards/automation. Status messaging
never breaks that contract:

- **`quiet` mode** (`--quiet`, and machine-JSON invocations that set
  `PDD_QUIET`): nothing is printed.
- **`json_mode`**: the reporter's default console is `get_console(stderr=True)`,
  so human status goes to **stderr** and stdout stays payload-only.

Either way the reporter still *records* every message (`reporter.messages`),
which is also how tests assert behavior by shape — no wall-clock, no ANSI
scraping.

## Using it from a command

```python
from .cli_status import from_context

def my_main(ctx, ...):
    status = from_context(ctx, command="pdd detect")
    status.start("analyzing 3 prompt(s) against the change description")
    try:
        with status.waiting("asking the model which prompts need changes", on="LLM"):
            result = detect_change(...)
    except Exception as e:
        status.failure(
            "detecting changes",
            reason=str(e),
            suggestions=["verify the prompt and change files exist",
                         "re-run with --verbose for details"],
        )
        raise
    status.success(
        f"{len(result)} prompt(s) need changes",
        next_step="review the results, then run `pdd change`",
    )
```

`from_context` inherits the global `--quiet` flag from `ctx.obj`, so commands
don't re-plumb it.

## Adoption

`detect_change_main` and `conflicts_main` are migrated as the first adopters in
this PR. Remaining commands move onto the reporter incrementally in follow-on
work under this EPIC, the same way the color system rolled out.
