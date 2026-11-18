# Autopilot metrics report

As an Autopilot operator running repositories on one machine, I want a clear local report of open issues, issues taken, pull requests created, merge conversion, gate pass rates, and skill mix with an on/off switch, so that I can see how Autopilot performs without manual bookkeeping.

## Acceptance criteria

1. Running `pdd metrics` at "2026-11-17T18:00:00Z" in "America/Los_Angeles" prints unified "Last 24h" and "Week (Mon-Sun)" rows with live "Open" issues, plain "Taken" and "PR Created" counts, and "M/WM (Conv%)" ("3 (75.0%)" when 3 of 4 taken issues merged or reached would-merge), and `pdd metrics --repos` breaks each window down by repository with a "Total" row.
2. Running `pdd metrics stages` prints "Taken", "PR", "Runtime", "Vectors", "Formal", "Suite", "Review", "CI", "M/WM", and "Reopen", showing each check gate as "passed/applicable" (or "-" when 0 runs used that gate) and one "Non-merged" summary line naming where unfinished or ended runs stopped.
3. Running `pdd metrics skills` prints "small-change", "bug", "feature", and "Total" rows with "Taken", "PR Created", "M/WM (Conv%)", and "Median Time" in minutes across merged or would-merge runs ("n/a" when none merged).
4. Running `pdd metrics --date 2026-11-16` in "America/Los_Angeles" reports only runs active on "2026-11-16", and when GitHub open issue counts are unavailable "Open" prints "?" and exits with code 0.
5. Recording defaults to "on", running `pdd metrics off` (globally or with `--repo OWNER/REPO`) pauses recording new Autopilot runs while keeping earlier history in the report, and `pdd metrics on` resumes recording.

```pdd-boundary
prompts/cli/metrics-model.prompt.md
```
