# Shared measurements

As a repository maintainer reviewing PDD runs, I want to follow a fixed group or Monday-to-Sunday week of issues and see what happened, so that missing evidence, weekly pace and later deliveries stay visible.

## Acceptance criteria

1. A group containing issues 1 and 2 still contains two issues when issue 1 has two attempts and two pull requests.
2. An attempted launch without a confirmed start does not count as a start.
3. A checker pass for an old candidate does not validate a changed candidate.
4. A later delivered fix remains attributed to the original group, and an administrative reopen is separate from a human report that the fix is still broken.
5. Importing the same event twice does not add a second issue or event, and an absent machine is shown as a coverage gap.
6. A weekly report anchored on Wednesday 2026-11-11 covers Monday 2026-11-09 through Wednesday 2026-11-11 (3 elapsed days, refreshing Monday), counts an issue worked on both Tuesday and Wednesday once in weekly totals, and resets to 1 elapsed day on Monday 2026-11-16.

## Rules to check

- A fixed group keeps its recorded issue membership through the observation cutoff. Count each canonical repository and issue pair once, regardless of attempts, pull requests, machines, or later delivery. Never drop an issue because it did not start.
- A claim, attempted launch, failed launch, or uncertain delivery is not a confirmed workflow start. Missing start evidence is unknown; do not invent a start from a later event.
- A checker result validates a candidate only when its head matches that candidate and the existing evidence acceptance rules accept its identified reviewer and evidence. An old head, missing evidence, or conflict cannot establish a fresh pass. CI, prompt Runtime checks, and internal review remain separate evidence.
- A code delivery needs an explicit issue relationship and relevant evidence; a prompt PR alone or an incidental mention does not establish delivery. A later delivery remains in the original fixed group.
- Count a failed fix only for a linked explicit human report about the delivered fix. Administrative reopen, new scope, revert, and an unclassified report are distinct. A missing report does not establish lasting success; show 7-day and 30-day follow-up maturity.
- Identical source-event identities with identical facts count once. Conflicting observations are visible uncertainty; an absent machine or incomplete capture is a coverage gap, not evidence of zero events. A zero denominator has no applicable percentage.
- A weekly report spans the Monday-to-Sunday calendar week of its anchor date in the declared timezone through that anchor date (1 elapsed day on Monday through 7 elapsed days on Sunday, refreshing every Monday), and counts each active issue once in weekly totals even when it has activity on multiple days.
