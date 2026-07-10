# EPIC #1540 — Design refresh, Phase 1 (color system, status messaging, context token viz)

Tracking issue: [promptdriven/pdd#1540](https://github.com/promptdriven/pdd/issues/1540)

This EPIC is the **Phase 1** integration branch for the PDD design refresh,
covering the three foundational workstreams: more intentional color, clearer
status/progress messaging, and better `pdd context` token visualization.

> **Split into two phases.** The remaining workstreams — adaptive theming, a
> `pdd connect` redesign, an AI-review refresh, and sync/checkup motion — moved
> to **Phase 2 → [#1560](https://github.com/promptdriven/pdd/issues/1560)**
> (`epic/1560-design-refresh-phase-2`, [PR #1561](https://github.com/promptdriven/pdd/pull/1561)).

Each workstream lands as its **own PR targeting this EPIC branch**
(`epic/1540-design-refresh`), not `main`. The EPIC is merged to `main` only once
the Phase 1 workstreams are complete.

## Design source of truth

All visual decisions derive from the **PromptDriven.ai Brand Guidelines
(v1.4, May 2026)** — see `docs/design/color-system.md` for the CLI color
mapping distilled from §3 (Color Palette) and §7 (ASCII & Terminal Assets).

## Demos

Terminal captures of the merged workstreams (PRs 1–3) live in
[`docs/design/demos/`](./demos/README.md), regenerable from this branch via
`docs/design/demos/generate_demos.py`.

## Workstream status

| # | Workstream | PR | Status |
|---|------------|----|--------|
| 1 | Command color system — one consistent palette for commands, tags, labels, and states | sohni-tagirisa/pdd#1 | ✅ Merged into EPIC |
| 2 | Better status & progress communication — START/STEP/WAITING/SUCCESS/FAILURE primitives (`pdd/cli_status.py`); see `docs/design/status-messaging.md` | sohni-tagirisa/pdd#2 | ✅ Merged into EPIC |
| 3 | `pdd context` token visualization — color usage-box/table by token category (`status`) from the central palette; `--color/--no-color` auto-detect (NO_COLOR / non-TTY); JSON unchanged. See `docs/design/context-token-colors.md` | sohni-tagirisa/pdd#3 | ✅ Merged into EPIC |

Legend: ✅ merged · 🟡 in progress · ⬜ not started

## Enhanced experience is the default (no flags required)

Phase 1 landed the *infrastructure* — the brand palette (`pdd/cli_theme.py`),
the status primitives (`pdd/cli_status.py`), and the revamped `pdd context`
usage box — but several surfaces still defaulted to the pre-refresh look. This
follow-up makes the enhanced experience the **default**, so users get it without
opting in via any flag:

- **Color system, on by default.** The shared CLI console (`pdd/core/errors.py`,
  re-exported as `pdd.console` and used by the command-execution summary,
  `pdd update`, `pdd templates`, and other base commands) now renders every
  semantic role from the central brand palette in `pdd/cli_theme.py` instead of
  an ad-hoc per-module theme. `[command]`/`[success]`/`[error]` markup that was
  already in place across the CLI now resolves to the brand colors automatically.
- **Consistent status vocabulary, on by default.** The per-step *Command
  Execution Summary* (`pdd/core/cli.py`) now prefixes each step with the shared
  `cli_status` glyphs — `✓` for success, `✗` for failure — in their semantic
  roles, so chained commands end with the same SUCCESS/FAILURE shorthand the
  rest of the refresh uses.
- **`pdd context` revamped view, on by default.** The Claude-Code-style usage
  box is the no-flag default (`--table`/`--json` remain opt-in); color
  auto-enables on a TTY and respects `NO_COLOR` / `--no-color`. Locked by
  `tests/commands/test_context.py::test_default_output_is_context_usage_box`.

### Limiting color: a global `--color` / `--no-color`

Color is the default, and a single global flag on the root `pdd` command lets a
user force or disable it across **every** command (not just `pdd context`):

- `pdd --no-color …` disables color everywhere; `pdd --color …` forces it on
  even through a pipe (`pdd --color sync | less -R`).
- Default is auto: color on a TTY, off when piped or when `NO_COLOR` is set.
- Precedence for `pdd context` (which keeps its own `--color/--no-color`): the
  command's own flag wins, else the global flag, else auto-detect.
- Implementation (`pdd.core.errors.apply_color_preference`): sets
  `NO_COLOR` / `FORCE_COLOR` so every console built during the run inherits the
  choice (including `get_console`/`StatusReporter` and per-command consoles),
  and updates the already-constructed shared console(s) in place. No per-command
  plumbing was required.

Remaining ad-hoc `Console()` instances in individual command modules are left
for incremental adoption of `pdd.cli_theme.get_console()` and
`pdd.cli_status.StatusReporter` (as already done in `detect_change`/`conflicts`);
because they read `NO_COLOR`/`FORCE_COLOR` at construction, they already honor
the global flag.

## Phase 2 (split out to #1560)

The remaining workstreams moved to **[#1560](https://github.com/promptdriven/pdd/issues/1560)**
/ [PR #1561](https://github.com/promptdriven/pdd/pull/1561)
(`epic/1560-design-refresh-phase-2`):

| # | Workstream |
|---|------------|
| 4 | Adaptive theming (detect IDE/editor light/dark theme) |
| 5 | `pdd connect` redesign |
| 6 | AI review refresh |
| 7 | Sync & checkup animation improvements |

## Conventions for child PRs

- Branch off `epic/1540-design-refresh`; target it in the PR base.
- Reference this EPIC and the workstream number in the PR description.
- Build on the central color system (`pdd/cli_theme.py`) rather than
  re-introducing ad-hoc color choices, so the CLI stays consistent.
- Update the status table above when a workstream PR is merged.
