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
