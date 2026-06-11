# EPIC #1560 — Design refresh, Phase 2 (theming, connect, AI review, motion)

Tracking issue: [promptdriven/pdd#1560](https://github.com/promptdriven/pdd/issues/1560)
Parent EPIC: [promptdriven/pdd#1540](https://github.com/promptdriven/pdd/issues/1540) (Phase 1)

This is the **Phase 2** integration branch for the PDD design refresh. The work
was split out of #1540 so it ships in two trackable halves:

- **Phase 1 — #1540 / PR #1557** delivered the foundational visual workstreams
  ① command color system, ② status & progress messaging, and ③ `pdd context`
  token visualization (all merged into the Phase 1 epic branch).
- **Phase 2 — this branch** covers the remaining workstreams ④–⑦: adaptive
  theming and the larger per-surface redesigns.

Each workstream lands as its **own PR targeting this branch**
(`epic/1560-design-refresh-phase-2`), not `main`. The EPIC merges to `main` once
the in-scope workstreams are done.

## Design source of truth

All visual decisions derive from the **PromptDriven.ai Brand Guidelines
(v1.4, May 2026)**, and build on the Phase 1 foundation — the central color
system (`pdd/cli_theme.py`) and the status/progress vocabulary
(`pdd/cli_status.py`) — rather than re-introducing ad-hoc visuals.

## Workstream status

| # | Workstream | PR | Status |
|---|------------|----|--------|
| 4 | Adaptive theming — detect the user's IDE/editor light/dark theme and apply a matching/complementary CLI theme; fall back gracefully when detection is unavailable | — | ⬜ Not started |
| 5 | `pdd connect` redesign — clearer visual hierarchy and communication of connection state, actions, and outcomes | — | ⬜ Not started |
| 6 | AI review refresh — more polished, legible presentation of feedback, reasoning, and review state | — | ⬜ Not started |
| 7 | Sync & checkup animation improvements — smoother, more modern, more informative motion that supports usability | — | ⬜ Not started |

Legend: ✅ merged · 🟡 in progress · ⬜ not started

## Conventions for child PRs

- Branch off `epic/1560-design-refresh-phase-2`; target it in the PR base.
- Reference this EPIC (#1560) and the workstream number in the PR description.
- Build on `pdd/cli_theme.py` and `pdd/cli_status.py` from Phase 1 rather than
  re-introducing ad-hoc color or messaging choices, so the CLI stays consistent.
- Update the status table above when a workstream PR is merged.
