# Autopilot merge admission and results

Own `src/autopilot-merge.mjs`. Preserve the current Autopilot authority,
trust, strict approvals, human review, red-pair and exact-head rules. This module
adds deterministic admission and GitHub queue support; it never grants authority
or approves a prompt. Native only: no interpreter interface or model call.

Export `DEFAULT_MERGE_RULES`, a frozen machine-readable object, and
`evaluateMergeRules({config, evidence, pull, ci, trusted, equivalent})`.
The optional `config.autopilot.merge` overlays these defaults:
`fresh_review: true`, `full_suite: true`, `required_ci: true`, `max_repairs: 2`,
`autonomy: "merge"`, `areas: {}`, `post_merge_audit: true`. The Boolean guards
are mandatory; false or malformed settings refuse `policy`. `max_repairs` may
be tightened to 0 or 1 but not raised. `autonomy` and each named `areas` value
are `manual`, `observe` or `merge`; missing area overrides inherit autonomy.
Unknown policy keys refuse rather than silently disable a guard.

Return exactly `{allowed, rule, message, action}`. `allowed` is Boolean, `rule`
is the first failing identifier (null on success), `message` is a short diagnostic
that includes that identifier, and `action` is `merge`, `observe` or null.
Evaluate these ordered rules; missing or malformed proof fails closed:

| Rule | Required proof |
|---|---|
| policy | Valid settings as above |
| exact_head | Nonblank evidence head and base equal the live PR head and base |
| authorization | Nonblank attributed authorization and `gatesSatisfied: true`; never infer from mode or checker words |
| autonomy | Repository mode auto/observe; trusted issue author; named area; effective level permits merge or observe; off/manual refuses |
| fresh_review | Nonempty reviews with fresh true, verdict PASS, mustFix 0, unique nonblank sessions; every head is current or has locally computed equal nonempty patch IDs; risk integer 1..5. splitVerdict and sensitive must both be explicit Booleans. Two reviews when risk >=4, splitVerdict true or sensitive true |
| full_suite | `fullSuite` has exact head, passed true and noNewSkips true |
| required_ci | CI complete true on exact head, at least one well-formed check (nonblank name, passed true), every reported check passed, and all required names nonblank and present; an empty required list does not exempt other checks. Missing, pending, failed or unknown checks refuse. Live merge state CLEAN, HAS_HOOKS or BEHIND; UNSTABLE/BLOCKED/UNKNOWN refuse |
| human_review | Live reviewDecision APPROVED or null (no required review), and pendingReviews exactly 0; explicit pending/changes-requested or unknown counts refuse |
| repairs | repairs is an integer from zero through max_repairs |
| question | questionOpen is false |
| post_merge_audit | audit.planned is true |

`pull` supplies `id`, `head`, `base`, `baseOid`, `state`, `draft`,
`reviewDecision`, `pendingReviews` (live reviewRequests.totalCount), `mergeStateStatus`, `mergeCommit`, `queue` (Boolean or null for
unknown), `entry` (null or `{id,state}`). Draft/non-open PRs refuse `pull_state`
before admission. `ci` is `{head,complete,checks:[{name,passed}],required:[name]}`.
`equivalent` maps an old review head to true only after native git patch-id equality.
`config` combines current default-branch Autopilot controls with only
`autopilot.merge` from the immutable PR base. `trusted` comes from the issue
author's live repository permission or current default-branch explicit trust,
not a payload Boolean. Review and suite evidence remain attributed
operator records, not independently authenticated test execution.

Export `runAutopilotMerge({pr,cwd,stdin,observe}, ports={})`. `pr` is a positive
PR number; stdin is JSON evidence as above plus `issue` (positive number), `area`
and `comment` (nonblank authorization/evidence comment). Bad arguments return exit
2, outcome refused, rule input. Every result has exactly `exitCode`, `outcome`,
`rule`, `message`, `head`, `mergeCommit`. Unavailable facts return exit 1 and a
named rule. Outcomes are refused, would_merge, queued, merged_pending_audit,
audited, queue_failed or unknown. Pending/unknown results exit 3, queue failures
and refusals exit 1, would_merge/audited exit 0.

Use injected `github` methods `pull(pr)`, `config(pull)`, `authority()`, `trusted(issue,config)`,
`ci(pr,head)`, `comment(pr,body)`, `enqueue(id,head)` and `merge(pr,head)`;
`patchEquivalent(oldHead,head)` is another port. Native defaults use gh, git and
the call ledger; no shell interpolation. `config(pull)` reads merge policy from
the immutable live base commit, never the proposing branch. `authority()` reads
current repository mode and explicit trust from pdd.json on the default branch
returned by resolveWorkflowRepository, through GitHub contents with that branch
as ref, as the existing Autopilot settings commands do. Base settings cannot
override those controls; default-branch merge policy cannot override base policy.
Unavailable or malformed authority refuses autonomy. Missing default-branch
pdd.json means mode off, not auto.
Native CI retains nonzero gh pr checks exits 1 (failure) and 8 (pending) as
complete false, even when their JSON can be read. Both all-check and required-check
observations must succeed. No required checks reported permits an empty required
list but never waives the all-check observation or the requirement that every
reported check pass.
Unknown queue discovery refuses `merge_queue`; never fall back to direct merge.

An `observe` request only reconciles GitHub results, without comments or writes.
A merged PR with known mergeCommit returns merged_pending_audit until payload
`audit.head` equals that commit, `audit.passed` is true, `audit.independent` is
true and `audit.evidence` is nonblank; failed/missing audit never reports audited.
For an open PR an existing entry returns queued, except UNMERGEABLE returns
queue_failed. An observe request with no entry returns queue_failed; do not
resubmit removed entries automatically. Closed unmerged returns queue_failed.
No issue closing/label cleanup is permitted before audit completion by callers.

For a new request gather live facts, evaluate rules once, then post the supplied
comment. A failed comment stops with rule comment. Observe mode posts the comment
and returns would_merge without a merge write. Before a merge write read the PR
again; changed head, base or baseOid refuses exact_head. Re-read CI, current
default-branch authority and issue-author trust, and evaluate the same function
again before submission. A switch to off or revoked trust refuses autonomy;
a switch to observe returns would_merge with no second comment or merge write.
When the base has a queue, enqueue with expectedHeadOid;
otherwise preserve `gh pr merge PR --merge --match-head-commit HEAD`, never
--auto or --admin. Read GitHub back once. Enqueue success alone is not a merge;
only MERGED plus mergeCommit starts audit. Entry disappearance is queue_failed.
A lost write reply reads back once, never retries or switches routes. If no
definite result exists return unknown. No polling loop or real audit subprocess.

## Dependencies

- [GitHub calls](github-calls.prompt.md): native call accounting.
- [Workflow GitHub](workflow-github.prompt.md): resolve the current GitHub origin.
- [Merge handoff](../../skills/pdd-autopilot/steps/handoff.md#merge-conditions):
  consumer context for red-pair ordering and review requirements.
