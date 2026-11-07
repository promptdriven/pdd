# Publish workflow PRs as drafts

I can request draft PRs when I start a workflow, or at its current unpublished
approval gate, so my prompt PR and later code PR follow that saved policy.

## Acceptance criteria

1. `pdd workflow run bug 2544 --draft` saves draft publication before starting its chat; after reload, both the prompt PR and separately approved code PR are created as drafts. A small-change run follows the same policy.
2. At an existing run's current ready unpublished approval gate, `pdd workflow approve 2544 --draft --said WORDS` applies the normal approval checks and saves draft publication before publishing. A retry of that same gate retains its original decision and evidence; omitting the flag later never turns draft publication off.
3. Without a draft request, new runs and older runs without a saved policy keep ready publication. Explicit false at a direct module boundary has the same default, and a nonboolean request or saved policy is refused before publication effects.
4. Requested draft publication succeeds only when GitHub confirms that the exact matching PR is a draft. A ready PR, missing draft observation or malformed draft observation yields recovery required; an existing ready PR stays unchanged, with no duplicate or conversion.
5. A missing or changed current review, incomplete steps, strict-policy refusal, invalid saved configuration, cancellation, replacement or failed policy save prevents policy adoption and publication. A retained decision for another gate cannot substitute for the current gate's review and approval; a reopened gate can be shown and approved normally. The existing nonblank-word approval route does not grade repeated words.
6. Requesting draft mode cannot change an already published stage or silently replace an active nondraft run. Starting again refuses that policy change with guidance to use approval at a legitimate unpublished gate. Approving PR 1 alone still stops before code, which needs its own approval.
7. Draft mode preserves the saved PR identity, exact prepared intent, source and marker checks, body limits, uncertainty recovery and absence checks. A matching draft PR is reused without writes under ordinary reconciliation; explicit absence-only recovery still refuses every existing PR.

## Rules to check

The saved draft policy is a Boolean and can strengthen from false to true only
through an eligible start or legitimate current-gate approval. False or omission
cannot downgrade true. Draft is supplied separately to publication, never added
to the prepared intent's eight keys. No successful draft result may be inferred
from a create command or its printed URL. A refused approval must not adopt the
policy, weaken a review, reuse another gate's consent or start code.

## What must not change

Keep the default ready behavior, existing strict/terminal/chat approval routes,
current review binding and same-gate retry evidence. Preserve run custody, PR
identity, branch/base/SHA, exact marker checks, body-size protection, no-force
publication and read-only uncertain-effect recovery. Draft PR mode is separate
from draft prompt approval. The existing runner durable-prepared-intent gap is
outside this Story; this change does not establish a new global duplicate guarantee.

## Verification boundary

The [native case plan](../test/cases/workflow-draft-publication.native.md) is a
reviewable inventory, not executable proof. The runner has no Runtime entries for
start/approval, and the GitHub helper's existing entry binds preparation only.
CLI dispatch can fake its existing start callback, but that cannot prove durable
policy, GitHub publication or approval. No new test-only operation or guessed
Runtime binding is introduced. Native execution and Runtime checks are not run
at this prompt/Story step; native implementation must later verify these cases.
