# Autopilot Metrics v2 Scorecard

As an Autopilot operator, I want the metrics scorecard to show live open issues, accumulated window pools, reconciled merges, stage gates, regressions, and monthly targets across enabled repositories so I can measure conversion and quality honestly.

```pdd-boundary
prompts/cli/metrics-model.prompt.md
```

## Acceptance criteria

1. A unified report names enabled repositories explicitly in the header, excludes turned-off repositories from unified counts and scope labels, and shows the live open issue count.
2. Each window computes its accumulated pool as the union of currently open issues, issues closed in the window, and issues taken in the window, so Pool is at least Taken, Taken is at least PRs, and PRs is at least Merged, with distinct pools for Last 24h and Week (Mon-Sun).
3. Pull requests merged on GitHub after observe or stopped runs count as Merged, while unmerged pull requests stay under Unmerged PRs alongside the Before PR breakdown so Taken equals Before PR plus PRs and PRs equals Merged plus Unmerged PRs.
4. Funnel and Gates separates PR Gates over all pull requests (including E2E when recorded) from Prompt Checks over prompt-changing pull requests, and reports auto-detected regressions both in the overview table and in the regressions breakdown.
5. The overview includes a monthly Target row below Week (Mon-Sun) defaulting to >=90% conversion and 0.0% regressions, honors custom configured targets, and shows question marks for open and pool counts when live GitHub counts are unavailable.
6. Filtering explicitly by a turned-off repository still renders that repository's scorecard while keeping pre-pause runs and excluding runs recorded after it was paused.
