# EPIC #1540 — Design refresh for PDD command UX, theming, and motion

Tracking issue: [promptdriven/pdd#1540](https://github.com/promptdriven/pdd/issues/1540)

This EPIC is the integration branch for a broader design refresh across PDD
commands: more intentional color, clearer status/progress messaging, better
`pdd context` token visualization, adaptive theming, a `pdd connect` redesign,
an AI-review refresh, and improved sync/checkup motion.

Each workstream lands as its **own PR targeting this EPIC branch**
(`epic/1540-design-refresh`), not `main`. The EPIC is merged to `main` only once
the workstreams that are in scope for it are complete.

## Design source of truth

All visual decisions derive from the **PromptDriven.ai Brand Guidelines
(v1.4, May 2026)** — see `docs/design/color-system.md` for the CLI color
mapping distilled from §3 (Color Palette) and §7 (ASCII & Terminal Assets).

## Workstream status

| # | Workstream | PR | Status |
|---|------------|----|--------|
| 1 | Command color system — one consistent palette for commands, tags, labels, and states | sohni-tagirisa/pdd#1 | ✅ Merged into EPIC |
| 2 | Better status & progress communication — START/STEP/WAITING/SUCCESS/FAILURE primitives (`pdd/cli_status.py`); see `docs/design/status-messaging.md` | sohni-tagirisa/pdd#2 | ✅ Merged into EPIC |
| 3 | `pdd context` token visualization (multi-color tokens) | — | ⬜ Not started |
| 4 | Adaptive theming (detect IDE/editor light/dark theme) | — | ⬜ Not started |
| 5 | `pdd connect` redesign | — | ⬜ Not started |
| 6 | AI review refresh | — | ⬜ Not started |
| 7 | Sync & checkup animation improvements | — | ⬜ Not started |

Legend: ✅ merged · 🟡 in progress · ⬜ not started

## Conventions for child PRs

- Branch off `epic/1540-design-refresh`; target it in the PR base.
- Reference this EPIC and the workstream number in the PR description.
- Build on the central color system (`pdd/cli_theme.py`) rather than
  re-introducing ad-hoc color choices, so the CLI stays consistent.
- Update the status table above when a workstream PR is merged.
