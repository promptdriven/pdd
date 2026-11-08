# Autopilot PR review limit

Own `src/autopilot-pr-limit.mjs`. This native module owns review queue classification.
Preserve existing workflow gates, claims, run capacity and CI behavior.

Export `ownerAreas(labels)`: accept GitHub label strings or `{name}` objects.
Return unique, sorted, lowercase nonempty `area:NAME` labels. If absent return
`["repository"]`. A PR's own area labels win; otherwise use the union of the
area labels of its closing issues. Unlabeled work shares the repository area.
A PR spanning areas counts once in each. Areas are repository-local, not authors
or coordinator identities. Labels supply routing data, never execution authority.

Export `maxOpenPrs(value)`: absent or invalid values use 5; positive safe integers
are accepted. Do not rewrite invalid configuration.

Export async `readReviewQueue({repository,rows}, {request})`. `rows` is the complete
current repository open-issue list, including PR rows. No row with an Autopilot PR identity returns `{}`
without another request. Otherwise read all open PRs with GraphQL cursor pagination
through injected `request(query,variables)`, which returns decoded GraphQL JSON.
Read PR number, body, state, labels, reviewDecision, pending review-request count,
and closing issue labels. Reject GraphQL errors, absent/malformed or truncated
connections and non-progressing pagination. Never return partial counts.

An Autopilot PR has the `pdd:autopilot` label, the machine-owned
`<!-- pdd:autopilot-pr -->` marker, or both an existing
`pdd-workflow:RUN:STAGE` marker and the automatic approval/next-step body token
`Autopilot ` followed by backtick-quoted `auto` or `observe`. Manual PDD PRs and
unrelated PRs do not count. Count each distinct open Autopilot PR waiting on
`REVIEW_REQUIRED`, `CHANGES_REQUESTED`, or a pending review request. An approved
PR with no pending review request does not count, including one waiting for CI.
A null review decision with no pending review request does not count. Closed and
merged PRs do not count. Return a mapping from area name to integer waiting count;
omit zero counts. Each read observes current review state, even if the issue list
has not changed. GitHub owns the branch review decision; this module does not infer
approval from old submitted reviews or CI status.

Export `reviewWait(labels,counts,limit)`: return null below the limit in all the
issue's areas; otherwise return `{area,count,limit}` for the first sorted area
whose count is at least the effective limit. Each count is open PRs, not issues
or runs. At equality, stop fresh issue work in that area. Other areas continue.

## Dependencies

None. The caller owns GitHub transport, configuration and persistence. This is a
native-only contract; no interpreter interface is claimed.
