# Shared measurements

I can follow a fixed group of issues and see what happened, including missing evidence and later deliveries.

## Acceptance criteria

1. A group containing issues 1 and 2 still contains two issues when issue 1 has two attempts and two pull requests.
2. An attempted launch without a confirmed start does not count as a start.
3. A checker pass for an old candidate does not validate a changed candidate.
4. A later delivered fix remains attributed to the original group, and an administrative reopen is separate from a human report that the fix is still broken.
5. Importing the same event twice does not add a second issue or event, and an absent machine is shown as a coverage gap.

## Rules to check

- A fixed group keeps its recorded issue membership through the observation cutoff. Count each canonical repository and issue pair once, regardless of attempts, pull requests, machines, or later delivery. Never drop an issue because it did not start.
- A claim, attempted launch, failed launch, or uncertain delivery is not a confirmed workflow start. Missing start evidence is unknown; do not invent a start from a later event.
- A checker result validates a candidate only when its head matches that candidate and the existing evidence acceptance rules accept its identified reviewer and evidence. An old head, missing evidence, or conflict cannot establish a fresh pass. CI, prompt Runtime checks, and internal review remain separate evidence.
- A code delivery needs an explicit issue relationship and relevant evidence; a prompt PR alone or an incidental mention does not establish delivery. A later delivery remains in the original fixed group.
- Count a failed fix only for a linked explicit human report about the delivered fix. Administrative reopen, new scope, revert, and an unclassified report are distinct. A missing report does not establish lasting success; show 7-day and 30-day follow-up maturity.
- Identical source-event identities with identical facts count once. Conflicting observations are visible uncertainty; an absent machine or incomplete capture is a coverage gap, not evidence of zero events. A zero denominator has no applicable percentage.
