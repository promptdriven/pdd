# EPIC #1560 — Design refresh follow-up

Tracking issue: [promptdriven/pdd#1560](https://github.com/promptdriven/pdd/issues/1560)
Parent EPIC: [promptdriven/pdd#1540](https://github.com/promptdriven/pdd/issues/1540) (Phase 1)

This branch is the design-refresh follow-up that is merging the concrete work
that actually landed after Phase 1:

- **Phase 1 — #1540 / PR #1557** delivered the foundational visual workstreams
  ① command color system, ② status & progress messaging, and ③ `pdd context`
  token visualization (all merged into the Phase 1 epic branch).
- **This follow-up — #1560 / PR #1561** makes the enhanced CLI experience the
  default, adds a global `pdd --color/--no-color` preference, and redesigns the
  `pdd sync` animation around the real execution pipeline.

Earlier planning notes also mentioned adaptive theming, a `pdd connect`
redesign, and an AI-review refresh. Those are not implemented here and are not
part of this PR's merge scope.

## Design source of truth

All visual decisions derive from the **PromptDriven.ai Brand Guidelines
(v1.4, May 2026)**, and build on the Phase 1 foundation — the central color
system (`pdd/cli_theme.py`) and the status/progress vocabulary
(`pdd/cli_status.py`) — rather than re-introducing ad-hoc visuals.

## Delivered scope

| # | Workstream | PR | Status |
|---|------------|----|--------|
| 1 | Enhanced CLI default — shared brand palette for console output and shared success/failure glyphs in the execution summary | #1629 | ✅ Merged into follow-up |
| 2 | Global color preference — root-level `pdd --color/--no-color`, inherited by `pdd context` unless overridden locally | #1629 | ✅ Merged into follow-up |
| 3 | Sync animation pipeline model — Entry → Inspect → Plan → Execute → Output, with execute-step strip and fixed-height rendering | #1621, #1630, #1631 | ✅ Merged into follow-up |
| 4 | Generated regression coverage for enhanced CLI defaults, color precedence, and sync animation contracts | #1637 | ✅ Merged into follow-up |

Legend: ✅ merged · 🟡 in progress · ⬜ not started

## Out of scope

- Adaptive theming based on IDE/editor light/dark theme.
- `pdd connect` redesign.
- AI-review presentation refresh.
