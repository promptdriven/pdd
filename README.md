# PDD Autopilot Conversion Stats

This orphan branch holds daily PDD Autopilot scorecards, stage conversion metrics, and verified root-cause issues filed from conversion drops (https://github.com/promptdriven/pdd/issues/3361). It contains metrics and issue ledgers only, with zero repository source code.

## How to Read Each Day Folder

Each `YYYY-MM-DD/` folder records a 24-hour Pacific window (`09:00` to `09:00` PT):

- `WEEKLY-METRICS-AND-BOTTLENECKS.html` — Visual report of daily volume, stage conversion rates, skill readiness (`small-change`, `pdd-bug`, `pdd-feature`), and worker slot utilization.
- `scorecard.json` — Machine-readable daily and weekly counts (`Issues`, `M/WM`, `Conv%`, `PRs`, `End`, `Ask`, `Rel`, `Run`), per-skill breakdowns, and pipeline funnel stages.
- `created-issues.json` — Verified PDD and Runtime issues filed or tracked from that window's conversion drops and slot bottlenecks (https://github.com/promptdriven/pdd/issues/3262).

## Daily Snapshots

| Date | Window (PT) | Weekly M/WM (`Conv%`) | Latest Day M/WM (`Conv%`) | Files | Tracked Drop & Reliability Issues |
|---|---|---:|---:|---|---|
| `2026-11-13` | Mon Nov 9 – Fri Nov 13 (`09:00` PT) | `78 / 121` (`64.5%`) | `30 / 37` (`81.1%`) | [HTML](2026-11-13/WEEKLY-METRICS-AND-BOTTLENECKS.html) · [scorecard.json](2026-11-13/scorecard.json) · [created-issues.json](2026-11-13/created-issues.json) | [#3360](https://github.com/promptdriven/pdd/issues/3360), [#3361](https://github.com/promptdriven/pdd/issues/3361), [#3362](https://github.com/promptdriven/pdd/issues/3362), [#3252](https://github.com/promptdriven/pdd/issues/3252), [#3230](https://github.com/promptdriven/pdd/issues/3230), [#3228](https://github.com/promptdriven/pdd/issues/3228), [#2710](https://github.com/promptdriven/pdd/issues/2710), [#3262](https://github.com/promptdriven/pdd/issues/3262) |
