# Native coordinator dependency intake

Own `src/issue-dependencies-intake.mjs`. Export module functions
`prepareDependencyIntake({cwd,repository,issue},ports)`,
`completeDependencyIntake({cwd,request,analysis},ports)`,
`reconcileDependencyIntake({cwd,repository,trigger,mode},ports)` and
`runDependencyIntake({command,cwd,issue,stdin},ports)` and
`checkDependencyStart({cwd,repository,issue,coordinator},ports)`.
The selected native coordinator supplies semantic analysis from actual source,
plans and trusted issue requirements. Code builds the packet, validates fresh
results and persists them. These functions select no model, start no agent,
call no AI service, allocate no worktree and start no workflow.
This new boundary does not change existing trust, mode, owner or room policy.

## Prepare and complete through one supported route

`pdd dependencies prepare [--issue N]` returns UTF-8 JSON with a request and queued
subjects. The default repository is the current checkout. This agent route has
no graph-only `--repo` selector. `pdd dependencies complete --input -` reads one
strict UTF-8 JSON object `{request,analysis}` from stdin, calls completion, and
prints its JSON result. Native `runDependencyIntake` returns `{exitCode,message}`;
message is exactly the serialized result plus one newline on success. Invalid
JSON, unknown fields, wrong repository/issue identity or invalid analysis returns
exit 2 before writes. Do not interpolate JSON into shell code. The agent uses
these supported commands, never an ad hoc import, shell-eval JavaScript or raw
GitHub write. Prepare is read-only. Complete is the explicit save/effect route.
For a repository where Autopilot runs on this machine, both commands get the
[floor guard](issue-dependencies-github.prompt.md#saved-dependency-snapshot)
(`commandGithubFloor`): below the floor their non-safety reads stop, and a
stopped completion is [kept](#kept-completion).

Prepare rereads GitHub, repository-bound trust and current ownership, then
projects with the model. Queue only root-repository subjects the owner can receive;
external prerequisites remain context. `owners.read({repository,issues})` returns
JSON `{localOwner,claims:[{issue,owner,active,coordinatorId,machine,commentId,labelEventId}],runs:[],runsKnown}`.
A claim may also carry `lastSeen`, `expired`, `stuckSince`, `claimedAt`, `takeovers`, `previousOwner` and `longRunningAlertedAt` from the
[claim expiry rules](issue-dependencies-github.prompt.md#claims-heartbeat-and-expiry); the native reply may also give `localMachine`.
An expired claim is not active, so it is neither owned elsewhere nor an own claim.
The runs list reuses current local active-run/allocation observations, with issue,
runId and state; deduplicate the same observed slot by its existing identity.
Use the existing occupied-slot classification in this repository/commonDir.
Starting, unknown and unconfirmed slots count. Waiting/paused/stuck/question work yields
a slot only with confirmed no occupied worker; labels or age alone never free it.
runsKnown is true only for a complete current local count.
The extra identity fields and runs are optional on legacy observations; missing
identity cannot establish that a claim belongs to this coordinator. `owner` is a
coordinator identity, not a machine name. Preserve the existing shared claim winner
policy and local run/allocation observations. Another or unknown owner yields a
skip. Unclaimed reviews use the existing repository coordinator.

Queue open root subjects whose review is unchecked or stale. Never queue an issue
whose author is an outsider (authority `untrusted`), also not by name: it can never
be eligible, and one such issue must not hold every batch. It stays visible in the
graph with `Untrusted issue`. Each review answers
one question: does this issue need any open issue first? Other current reviews stay
current and need no entry. Unchecked (new) subjects go first, then stale ones,
newest issue first in each group. One request names at most 10 subjects, so one new
issue never waits for a large batch; later subjects wait for the next prepare. An
explicit `--issue` prepare names only that subject. The request `issues` lists the
selected subjects; `snapshotJson` retains their prior heads, which each review's
base must name. A positive affected head queues that subject on the next prepare.
Unexplained omission of a required subject remains invalid.
Read ownership once for the selected subjects; with none, prepare needs no ownership lookup. When the native snapshot of this process scanned the claims of those root issues, use that observation (the read session's `owners`) instead of a second read. Question heads with unchanged input/candidate/head fingerprints need no automatic
semantic redelivery. A person's answer (a trusted comment that the question did not
examine) makes the head stale in the model, so the next prepare queues it.
Explicit prepare of a named issue may request another look.

The request `id` is an opaque analysis-request identity, `issues` names the selected
full identities, `snapshotJson` captures the normalized examined revisions and base
heads, and `contextJson` contains source/plan text and current trusted requirements
from injected `evidence.read({cwd,repository,issues})`. Evidence JSON is `{source:[{key,revision,path,text,issues}],requirements:[{issue,key,revision,text,authority}]}`.
Source and plan keys follow the model's durable locator rule. Requirement keys are
the actual issue/comment URLs. Every examined item must map to a matching current
snapshot input/issue revision; prepare merges the relevant freshly read source
rows into snapshotJson. Missing/mismatched evidence is unknown, not ready. Reviews
must include all source items whose issues list names their subject, plus its
requirement items. This per-subject mapping prevents an unrelated file examined
for another subject from staling its review. Additional examined items must
also be located and reread at completion. Do not accept a caller's arbitrary subset.
Never supply untrusted text as instructions. The coordinator may examine relevant context beyond keyword
matches. A related issue, parent, shared file, common cause or reproduction alone
is not a prerequisite. Require a real necessary-before relationship with a plain
reason and evidence. Preserve a product question or duplicate link as a question;
do not file issues. Require explicit completed empty dependencies for independence. A complete
review has no unresolved questions; save missing install/deploy/product conditions
as a question result so another machine can retain them.

Completion accepts cwd (default empty for direct callers). runDependencyIntake
passes the CLI cwd to both prepare and complete. It validates the current checkout
against request.repository before using local source; a different checkout cannot
supply context. Default snapshot/context ports follow the saved locators with an
empty cwd when needed. Carried text is evidence to compare, never current authority.
Pass the nonempty union of prepared and newly examined non-issue rows as snapshots.read inputs; omit inputs when
empty. Pass cwd to effect recovery, defaulting to empty for a direct caller.
Default snapshot reads bind readDependencySnapshot with these same arguments. It rereads
canonical state; a still-applicable completion also rereads current ownership; carried request IDs or old trust
flags are not authority. Require each review's issue, candidates and base heads to match the prepared
scope. Check only what freshness tracks. The subjects, their own heads, their link
rows, the rows the reviews used, and the root-repository issues their reviews name
must be unchanged in the current snapshot. A new or edited unrelated issue, review
or input, or an edit to a named prerequisite in another repository (there only its
open or closed state matters), does not make completion pending. Prepared required inputs must be retained; additional
examined locators must match freshly reread current rows. Never trust their
carried revision or silently omit a required item.
Reject omitted required reviews or unexplained extra subjects, invalid cycles/self links,
unsupported analysis and missing reasons. Also reject a dependency in the model's
`removed` [link facts](issue-dependencies.prompt.md#link-facts) for its subject: a
person removed that link, so a coordinator that still believes it is needed records
a question. Outcome `pending` needs at least one named link: reject a pending
review with no dependencies. A coordinator that cannot decide records a question.
A rejected answer saves nothing, so its subject gets a
[repeated delivery](#repeated-delivery). Code owns each subject's link row:
completion drops a carried copy from the analysis inputs and saves each review
with the row from the current links plus
the request's validated additions, which count as PDD links of the request's
intents. A stale or unknown observation returns
pending and queues fresh review without edge writes (see [pending reasons](#pending-reasons)). Questions append a question
record. Additions append pending intent BEFORE effects and delegate recovery to
the GitHub owner. Checked-empty results append complete effects-none records.
Do not erase existing edges or resolve conflicts by record arrival order.
The record base must name all heads it resolves. Never record draft prompt approval
or invent a person's approval words as part of semantic completion.

<a id="pending-reasons"></a>
<details><summary>Pending reasons, rows and the completion note</summary>

Every pending result names a `reason`, so the coordinator can act on it:

| Reason | When |
|---|---|
| `observations-incomplete` | The reread of a subject's relevant observations or owners is incomplete or fails, for example on a GitHub 5xx or rate limit. |
| `input-changed` | A subject, its trust, its own heads or links, a root prerequisite that a review names, or a row that a review used changed after prepare or cannot be read. |
| `answer-row-mismatch` | A review did not copy its base heads, candidates or required rows exactly from the request. |
| `owner-changed` | Another or unknown owner holds a subject. |
| `write-unconfirmed` | An impact, review or link write is not confirmed; `pendingStage` names it. |
| `github-limit` | The reread is incomplete because the [floor guard](github-calls.prompt.md#floor-guard) stopped its reads: fewer calls than the floor are left until the reset. |

`rows` (at most 20, omitted when empty) names the rows behind the reason. For a
mismatch it gives the row the request expects: key `ISSUE#base` carries the
expected base heads as a sorted JSON list, and an unexpected candidate has revision
`""`. For a change it gives the current row, with revision `""` when it cannot be
read. A used row whose revision differs from its prepared revision is a mismatch;
a prepared or extra examined row that differs now is a change. A failed reread is
a pending result, not an error.

With a checkout (nonempty cwd), completion keeps the request ID, reason and rows of
its last pending result as a local note through `results.save({repository,json})`.
The native default writes one private file in the repository's Git common
directory, so the coordinator and the launcher on that checkout share it. A failed
note write does not change the result. The note only names a reason for a later
[repeated delivery](#repeated-delivery); it never decides one. Direct callers with
an empty cwd keep no note.

</details>

Impact analysis is optional. A nonempty parsed `analysis.impactJson` names the
examined new/changed revisions, affected existing issues and the exact prior review
heads considered. An impact is stored on a selected issue in `request.repository`;
only an impact hosted in a graph head's root repository can establish that head's
freshness. Other repositories' impact comments remain visible but cannot override
that graph's impact decision.

Validate the full current request, every review and every proposed dependency
before writing. If an impact is supplied, save it before per-subject
reviews and dependency effects. This preserves valid impact evidence when an
unrelated subject save later fails. Before saving, reuse an identical complete,
trusted, intact impact already hosted on the selected root issue. If impact saving
is uncertain, stop before any review or dependency write and return `pendingStage`
`impact-save` with its `pendingIssue`. After that, save reviews and apply their
pending dependencies in order. When the GitHub owner refuses a write (a person
removed that link, or it closes a cycle), it saves one question; completion adds
that review ID and question, and continues with the next subject. A later failure returns `pendingStage` as
`review-save` or `edge-confirmation` with the affected `pendingIssue`; earlier
confirmed records remain saved. Do not retry an uncertain effect or continue to a
later subject in that call. Saved reviews of other issues stay current without AI
on any machine. Incomplete or affected coverage cannot make unchecked or stale
work current. Relevant source changes queue
only subjects with changed recorded requirement inputs. Persist impact through
`reviews.saveImpact`, whose default is the GitHub adapter's append-only impact save.

<a id="kept-completion"></a>
### Finished work is kept

A completion can stop partway: a read fails, the GitHub limit runs out, or a write
is not confirmed after some reviews are saved. The saved reviews stay on GitHub,
and the analysis of the other subjects is finished work too. So:

- A completion skips each review of its request that is already saved: a trusted,
  intact review on the subject, not in the prepared snapshot, with the same
  analysis, base, continuation, candidates, inputs (without the link row),
  outcome, dependencies, questions and effects. The checks of this section then
  cover only the other subjects; the result lists the saved ID for each skipped
  review in request order. A repeated or resumed completion of the same request so
  saves no duplicate intent and needs no new analysis. A saved pending link intent
  is unfinished: resume its effects through the GitHub owner before reporting
  completion. Confirm already present edges without adding them twice. A confirmed
  continuation ends that intent; an existing question continuation returns its
  questions. An unconfirmed effect returns `write-unconfirmed` at
  `edge-confirmation` and keeps the completion for another retry.
- A pending result with reason `observations-incomplete`, `write-unconfirmed` or
  `github-limit` keeps `{request, analysis, reason, attempts}` through the
  `completions` port (`read`, `save`, `clear`), default the kept completion file
  of the [saved snapshot](issue-dependencies-github.prompt.md#saved-dependency-snapshot)
  for an Autopilot repository; `attempts` counts the kept results of the same
  request. Any other result of the same request clears it. A failed keep only
  means a new analysis later.
- After a complete or question result that saved a review, and with a saved
  snapshot, completion reads the snapshot once more, so the saved snapshot holds
  the new reviews. A failure there does not change the result.

## One reconciliation path

Startup, restart, fallback tick, event hint, completion and explicit refresh are
caller-owned triggers for `reconcileDependencyIntake`; completion does not itself
run reconciliation. `completeDependencyIntake` owns the validation and durable
review, impact and effect operations specified above. Each reconciliation initially reads GitHub and existing
pending state once. A `completion` trigger (after `pdd dependencies complete`,
after the idle wake of a busy coordinator, or after a worker yield) whose saved
snapshot list was read less than 10 minutes ago reads no issue list: it asks the
snapshot for the saved list and delivers the next request from it. Other triggers
read what changed. Then a non-off reconciliation finishes a [kept
completion](#kept-completion) of this repository: it runs the same completion
with the kept request and analysis, after `admitEffect`, and reads the snapshot
again when that saved or ended something. A kept value of another repository,
or that completion rejects is removed. Transient outages and repeated floor
waits keep the analysis without a retry cap; they do not make finished work
invalid. Non-off
reconciliation also reads current ownership once for
its selected root subjects before recovery, delivery or eligibility handoff; the
claims of the native snapshot's own claim scan are that read, so the open issues
are not read again. If that native scan fails, return pending with no queued or
eligible subjects; do not replace it with a live all-issue scan.
It reprojects saved decisions and
coalesces pending subjects. Native close/reopen/merge/relation changes normally
need only reprojection; substantive changes require the selected coordinator.
Off permits reads and retains saved data but queues no automatic analysis/start.
A non-off reconciliation also returns `claims`, the claims of that ownership read,
so the launcher can refresh its own claims and offer expired ones without another read.
Observe and auto both analyze and return execution-eligible subjects to the
existing scheduler; observe leaves merging to a person. No reconciliation operation launches work.

In each non-off reconciliation, route a current accepted pending-effects head to
`reviews.apply({cwd,repository,issue,reviewId})` before semantic delivery, then
reread and reproject. An observed confirmed continuation needs no new analysis.
Unsafe, stale or conflicting intent stays pending and queues only needed review.
Off performs neither recovery effects nor semantic delivery.

The durable semantic fingerprint is canonical JSON of repository, sorted subject
identities, their substantive input/candidate key/revision rows (with their link
rows) and sorted current head IDs. It excludes capture time, unrelated paths and bookkeeping. Existing
pending JSON stores requested and confirmed delivered fingerprints; busy/dialog
never advances delivered. A saved unchanged question is itself durable evidence
that its analysis finished: reconstruct its fingerprint from the saved head and
inputs on an empty-cache/new-machine restart, and wait for changed requirements
or explicit refresh/named prepare. Ordinary ticks do not resend that question.

Call `pending.deliver({repository,requestJson})` only for new/coalesced semantic
work or a [repeated delivery](#repeated-delivery) in a non-off mode. Its reply is delivered, busy or dialog. Save pending via
`pending.save({repository,json})`; advance the delivered fingerprint only on a
confirmed delivered reply. Busy/dialog remains pending across restart. Default
30-minute polling remains owned by the launcher and active without event delivery.
Before the existing scheduler starts any candidate it must establish its current
claim winner, reread ownership and this model, then apply its own trust, activation,
PR, mode, room and allocation rules. An owner elsewhere is skipped. This handoff
provides no strict simultaneous cross-machine exclusivity guarantee.

<a id="repeated-delivery"></a>
### Repeated delivery

Autopilot never waits silently. A delivered request can end without saved reviews:
its completion is pending, or no completion comes (the coordinator stopped). Then
its subjects stay unchecked or stale, and the fingerprint may never change in a
quiet repository. For the last confirmed delivery, pending JSON also keeps its
request ID, its time from `clock.now({})`, its sorted subject set and the count of
repeated deliveries for that set. A confirmed delivery of another set starts the
count again at 0.

When the fresh fingerprint equals the delivered one and at least 30 minutes have
passed since that delivery, deliver the fresh request (same subjects, new ID) again
through `pending.deliver`, at most 3 times for the set. Before the send, save
`redelivery` `{attempt,cap,reason,rows}` in pending JSON, so the deliverer can name
it; remove it after the reply. Take the reason and rows from the completion note
when its request ID is the delivered one; otherwise the reason is `not-completed`.
Use only known reasons and GitHub locators from the note. Only a confirmed
delivered reply counts and starts the next wait; a busy reply tries again at a later
reconciliation. A saved delivery without a time or subject set starts its wait now.

When the count is at the cap and the next wait has passed, save one question review
on each subject through `reviews.save`, after `admitEffect`, and then clear the set,
time and count. The question has the subject's current heads as base; its inputs are
the issue row, its required source and requirement rows and its link row; its
candidates are the root issues; effects are none. It names the number of deliveries
and the last reason, and asks a person which open issues the subject must wait for.
The question is visible on the issue and in `pdd graph`, and the issue is not
eligible. Nothing is delivered again until a person's answer makes the question
stale. A question save that is not confirmed is tried again at a later
reconciliation; a saved question is observed, so it is never repeated.

## Current automatic start check

`checkDependencyStart` is the narrow production read before a new automatic start.
`coordinator` is `{repository,coordinatorId,machine,activation,runs?,claim}`; runs
is the existing optional positive safe-integer concurrent-run cap, not a lifetime
run total. Claim is
`{commentId,labelEventId}` for the existing winning shared GitHub claim. The
launcher supplies stable opaque coordinatorId per independent coordinator lifetime;
restart retains it. Two coordinators on one machine have different identities.
The claim comment carries this identity with the machine using the existing
single-comment policy. Missing/legacy identity is unknown, not this coordinator.

The subject is read live: before the snapshot, the read session marks it, so its
issue, claim, labels and links come from GitHub, not from the saved snapshot.
Read current mode via `settings.read({cwd,repository})`, bound to the existing
Autopilot settings owner for mode and existing repository launcher state for the
original activation and optional configured runs cap, plus fresh snapshot and
owners. Never derive current mode or
activation from the carried packet. Off returns allowed false
with reason `off` for a new automatic start. Another/unknown winner returns
`owner`; match the current local owner to the coordinatorId, and match repository,
coordinatorId and actual winning comment/label event identities, not just machine or carried packet. Changed activation or a mismatch in the optional carried/current cap is stale.
The current local cap is authoritative; omitting it from a packet cannot bypass it.
When configured, an unknown local count returns runs, without another start. With
a known count, count existing occupied run/allocation slots. Add one
only when the selected issue has no existing slot; actual reuse consumes none.
If that would exceed the configured cap, return runs. This cap result does not
permit replacing a live run or relaxing any ownership/dependency rule.
Read mode, snapshot and ownership once per check, even when Off; no early mode
result may treat a carried packet as current ownership. Compare the selected issue,
claim, occupied-run and projected-node identities using the pure model’s canonical
GitHub issue identity. Repository owner/name spelling is case-insensitive; preserve
the full repository and positive issue number. Invalid or foreign identities cannot
match the selected issue. Then project the shared model. Optional snapshot `executionClaim` carries the observed coordinatorId,
commentId and labelEventId; `runIds` retains observed run identities as provenance,
which alone does not establish a currently occupied worker. For this check only,
discount the matching claim's running/claim holds when executionClaim exactly matches
the winning claim and the fresh ownership read has a complete current run observation
with no occupied slot for the selected issue. Apply the existing occupied-slot
classification; unknown occupancy or an incomplete read cannot qualify. Preserve
runIds, and never discount another run, PR, stuck state, unverified authority or
any other hold. Return `{allowed,reason}` (`ok`, `off`,
`owner`, `stale`, `runs`, `dependency`, `unknown`). A current own winner with otherwise
eligible work returns ok. Failed observations remain unknown/denied. No claim
write, allocation or chat occurs here; existing account/room/native custody rules
still apply after ok. This read is not atomic exclusion across machines.

Retain body-free snapshot warnings in the request packet. For a partial snapshot,
use the shared model's explicit coverage for selected subjects and their complete
blocker closure; preserve global partial status. Completion revalidates coverage,
the subjects' own heads and named issues, impact observations, required input revisions, and current
owner and cap before effects. Legacy partial packets without coverage stay pending.

## Dependencies

- [Pure model](issue-dependencies.prompt.md): required authoring, generation,
  runtime and verification context; sole freshness, precedence and eligibility owner.
- [GitHub adapter](issue-dependencies-github.prompt.md): required for all uses;
  default snapshot/review/impact/effect ports bind its named public exports.
- [Autopilot settings](autopilot.prompt.md): required generation/verification
  context for the read-only settings port; preserve its mode and activation owner.
- [Allocation owner](workflow-worktree.prompt.md): generation/verification context
  for reading existing local assignment only; no allocation during review.

<details><summary>Runtime interface</summary>

```json
{"status":"approved","prose_sha256":"a050534b553dc4db8821db1d6f69161269e7a0527dc7afd3bc156e826d036924","entries":[{"operation":"prepareDependencyIntake","input_schema":{"type":"object","properties":{"cwd":{"type":"string"},"repository":{"type":"string"},"issue":{"type":"string"}},"required":["cwd","repository"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"request":{"type":"object","properties":{"id":{"type":"string"},"repository":{"type":"string"},"issues":{"type":"array","items":{"type":"string"}},"snapshotJson":{"type":"string"},"contextJson":{"type":"string"}},"required":["id","repository","issues","snapshotJson","contextJson"],"additionalProperties":false},"queued":{"type":"array","items":{"type":"string"}},"skipped":{"type":"array","items":{"type":"string"}}},"required":["request","queued","skipped"],"additionalProperties":false},"errors":["invalid-input"]},{"operation":"completeDependencyIntake","input_schema":{"type":"object","properties":{"request":{"type":"object","properties":{"id":{"type":"string"},"repository":{"type":"string"},"issues":{"type":"array","items":{"type":"string"}},"snapshotJson":{"type":"string"},"contextJson":{"type":"string"}},"required":["id","repository","issues","snapshotJson","contextJson"],"additionalProperties":false},"analysis":{"type":"object","properties":{"reviews":{"type":"array","items":{"type":"object","properties":{"analysis":{"type":"string"},"base":{"type":"array","items":{"type":"string"}},"continuation":{"type":"string"},"issue":{"type":"string"},"inputs":{"type":"array","items":{"type":"object","properties":{"key":{"type":"string"},"revision":{"type":"string"}},"required":["key","revision"],"additionalProperties":false}},"candidates":{"type":"array","items":{"type":"object","properties":{"key":{"type":"string"},"revision":{"type":"string"}},"required":["key","revision"],"additionalProperties":false}},"outcome":{"type":"string","enum":["complete","question","pending"]},"dependencies":{"type":"array","items":{"type":"object","properties":{"key":{"type":"string"},"reason":{"type":"string"},"evidence":{"type":"array","items":{"type":"string"}}},"required":["key","reason","evidence"],"additionalProperties":false}},"questions":{"type":"array","items":{"type":"string"}},"effects":{"type":"string","enum":["none","pending","confirmed"]}},"required":["analysis","base","continuation","issue","inputs","candidates","outcome","dependencies","questions","effects"],"additionalProperties":false}},"impactJson":{"type":"string"}},"required":["reviews","impactJson"],"additionalProperties":false},"cwd":{"type":"string"}},"required":["request","analysis"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"state":{"type":"string","enum":["complete","pending","question"]},"reason":{"type":"string","enum":["observations-incomplete","input-changed","answer-row-mismatch","owner-changed","write-unconfirmed"]},"rows":{"type":"array","items":{"type":"object","properties":{"key":{"type":"string"},"revision":{"type":"string"}},"required":["key","revision"],"additionalProperties":false}},"reviewIds":{"type":"array","items":{"type":"string"}},"eligible":{"type":"array","items":{"type":"string"}},"questions":{"type":"array","items":{"type":"string"}},"pendingStage":{"type":"string","enum":["impact-save","review-save","edge-confirmation"]},"pendingIssue":{"type":"string"}},"required":["state","reviewIds","eligible","questions"],"additionalProperties":false},"errors":["invalid-analysis"]},{"operation":"reconcileDependencyIntake","input_schema":{"type":"object","properties":{"cwd":{"type":"string"},"repository":{"type":"string"},"trigger":{"type":"string","enum":["startup","tick","event","completion","refresh"]},"mode":{"type":"string","enum":["off","observe","auto"]}},"required":["cwd","repository","trigger","mode"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"queued":{"type":"array","items":{"type":"string"}},"eligible":{"type":"array","items":{"type":"string"}},"skipped":{"type":"array","items":{"type":"string"}},"pending":{"type":"boolean"}},"required":["queued","eligible","skipped","pending"],"additionalProperties":false},"errors":["invalid-input"]},{"operation":"runDependencyIntake","input_schema":{"type":"object","properties":{"command":{"type":"string","enum":["prepare","complete"]},"cwd":{"type":"string"},"issue":{"type":"string"},"stdin":{"type":"string"}},"required":["command","cwd"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"exitCode":{"type":"integer"},"message":{"type":"string"}},"required":["exitCode","message"],"additionalProperties":false},"errors":[]},{"operation":"checkDependencyStart","input_schema":{"type":"object","properties":{"cwd":{"type":"string"},"repository":{"type":"string"},"issue":{"type":"string"},"coordinator":{"type":"object","properties":{"repository":{"type":"string"},"coordinatorId":{"type":"string"},"machine":{"type":"string"},"activation":{"type":"string"},"claim":{"type":"object","properties":{"commentId":{"type":"string"},"labelEventId":{"type":"string"}},"required":["commentId","labelEventId"],"additionalProperties":false},"runs":{"type":"integer","minimum":1,"maximum":9007199254740991}},"required":["repository","coordinatorId","machine","activation","claim"],"additionalProperties":false}},"required":["cwd","repository","issue","coordinator"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"allowed":{"type":"boolean"},"reason":{"type":"string","enum":["ok","off","owner","stale","runs","dependency","unknown"]}},"required":["allowed","reason"],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[{"name":"snapshots","kind":"port","access":"read","operations":[{"name":"read","access":"read","arguments_schema":{"type":"object","properties":{"cwd":{"type":"string"},"repository":{"type":"string"},"inputs":{"type":"array","items":{"type":"object","properties":{"key":{"type":"string"},"revision":{"type":"string"}},"required":["key","revision"],"additionalProperties":false}}},"required":["repository"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"snapshot":{"type":"object","properties":{"repository":{"type":"string"},"capturedAt":{"type":"string"},"complete":{"type":"boolean"},"issues":{"type":"array","items":{"type":"object","properties":{"key":{"type":"string"},"nodeId":{"type":"string"},"title":{"type":"string"},"revision":{"type":"string"},"state":{"type":"string","enum":["open","completed","not_planned","unknown"]},"authority":{"type":"string","enum":["trusted","untrusted","unknown"]},"conditions":{"type":"array","items":{"type":"string"}},"execution":{"type":"string","enum":["idle","running","unknown"]},"holds":{"type":"array","items":{"type":"string"}},"conditionSources":{"type":"array","items":{"type":"object","properties":{"text":{"type":"string"},"source":{"type":"string"},"inputs":{"type":"array","items":{"type":"object","properties":{"key":{"type":"string"},"revision":{"type":"string"}},"required":["key","revision"],"additionalProperties":false}}},"required":["text","source","inputs"],"additionalProperties":false}},"executionClaim":{"type":"object","properties":{"coordinatorId":{"type":"string"},"commentId":{"type":"string"},"labelEventId":{"type":"string"}},"required":["coordinatorId","commentId","labelEventId"],"additionalProperties":false},"runIds":{"type":"array","items":{"type":"string"}},"assignees":{"type":"array","items":{"type":"string"}}},"required":["key","nodeId","title","revision","state","authority","conditions","execution","holds"],"additionalProperties":false}},"edges":{"type":"array","items":{"type":"object","properties":{"dependent":{"type":"string"},"blocker":{"type":"string"}},"required":["dependent","blocker"],"additionalProperties":false}},"reviews":{"type":"array","items":{"type":"object","properties":{"id":{"type":"string"},"analysis":{"type":"string"},"base":{"type":"array","items":{"type":"string"}},"continuation":{"type":"string"},"issue":{"type":"string"},"inputs":{"type":"array","items":{"type":"object","properties":{"key":{"type":"string"},"revision":{"type":"string"}},"required":["key","revision"],"additionalProperties":false}},"candidates":{"type":"array","items":{"type":"object","properties":{"key":{"type":"string"},"revision":{"type":"string"}},"required":["key","revision"],"additionalProperties":false}},"outcome":{"type":"string","enum":["complete","question","pending"]},"dependencies":{"type":"array","items":{"type":"object","properties":{"key":{"type":"string"},"reason":{"type":"string"},"evidence":{"type":"array","items":{"type":"string"}}},"required":["key","reason","evidence"],"additionalProperties":false}},"questions":{"type":"array","items":{"type":"string"}},"intact":{"type":"boolean"},"effects":{"type":"string","enum":["none","pending","confirmed"]},"authority":{"type":"string","enum":["trusted","outsider","unverified"]}},"required":["id","analysis","base","continuation","issue","inputs","candidates","outcome","dependencies","questions","intact","effects","authority"],"additionalProperties":false}},"impacts":{"type":"array","items":{"type":"object","properties":{"id":{"type":"string"},"inputs":{"type":"array","items":{"type":"object","properties":{"key":{"type":"string"},"revision":{"type":"string"}},"required":["key","revision"],"additionalProperties":false}},"reviews":{"type":"array","items":{"type":"string"}},"affected":{"type":"array","items":{"type":"string"}},"complete":{"type":"boolean"},"trusted":{"type":"boolean"},"intact":{"type":"boolean"},"authority":{"type":"string","enum":["trusted","outsider","unverified"]}},"required":["id","inputs","reviews","affected","complete","trusted","intact"],"additionalProperties":false}},"inputs":{"type":"array","items":{"type":"object","properties":{"key":{"type":"string"},"revision":{"type":"string"}},"required":["key","revision"],"additionalProperties":false}},"coverage":{"type":"object","properties":{"scope":{"type":"boolean"},"issues":{"type":"array","items":{"type":"object","properties":{"key":{"type":"string"},"issue":{"type":"boolean"},"authority":{"type":"boolean"},"comments":{"type":"boolean"},"blockedBy":{"type":"boolean"},"blocking":{"type":"boolean"},"timeline":{"type":"boolean"},"reviewImpact":{"type":"boolean"},"missing":{"type":"array","items":{"type":"string"}},"context":{"type":"boolean"},"execution":{"type":"boolean"}},"required":["key","issue","authority","comments","blockedBy","blocking","timeline","reviewImpact","missing","context","execution"],"additionalProperties":false}}},"required":["scope","issues"],"additionalProperties":false},"warnings":{"type":"array","items":{"type":"string"}}},"required":["repository","capturedAt","complete","issues","edges","reviews","impacts","inputs"],"additionalProperties":false}},"required":["snapshot"],"additionalProperties":false}}]},{"name":"owners","kind":"port","access":"read","operations":[{"name":"read","access":"read","arguments_schema":{"type":"object","properties":{"repository":{"type":"string"},"issues":{"type":"array","items":{"type":"string"}}},"required":["repository","issues"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"json":{"type":"string"}},"required":["json"],"additionalProperties":false}}]},{"name":"evidence","kind":"port","access":"read","operations":[{"name":"read","access":"read","arguments_schema":{"type":"object","properties":{"cwd":{"type":"string"},"repository":{"type":"string"},"issues":{"type":"array","items":{"type":"string"}}},"required":["cwd","repository","issues"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"json":{"type":"string"}},"required":["json"],"additionalProperties":false}}]},{"name":"reviews","kind":"port","access":"write","operations":[{"name":"save","access":"write","arguments_schema":{"type":"object","properties":{"repository":{"type":"string"},"issue":{"type":"string"},"review":{"type":"object","properties":{"analysis":{"type":"string"},"base":{"type":"array","items":{"type":"string"}},"continuation":{"type":"string"},"issue":{"type":"string"},"inputs":{"type":"array","items":{"type":"object","properties":{"key":{"type":"string"},"revision":{"type":"string"}},"required":["key","revision"],"additionalProperties":false}},"candidates":{"type":"array","items":{"type":"object","properties":{"key":{"type":"string"},"revision":{"type":"string"}},"required":["key","revision"],"additionalProperties":false}},"outcome":{"type":"string","enum":["complete","question","pending"]},"dependencies":{"type":"array","items":{"type":"object","properties":{"key":{"type":"string"},"reason":{"type":"string"},"evidence":{"type":"array","items":{"type":"string"}}},"required":["key","reason","evidence"],"additionalProperties":false}},"questions":{"type":"array","items":{"type":"string"}},"effects":{"type":"string","enum":["none","pending","confirmed"]}},"required":["analysis","base","continuation","issue","inputs","candidates","outcome","dependencies","questions","effects"],"additionalProperties":false}},"required":["repository","issue","review"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"id":{"type":"string"},"state":{"type":"string"},"warnings":{"type":"array","items":{"type":"string"}}},"required":["id","state","warnings"],"additionalProperties":false}},{"name":"apply","access":"write","arguments_schema":{"type":"object","properties":{"repository":{"type":"string"},"issue":{"type":"string"},"reviewId":{"type":"string"},"cwd":{"type":"string"}},"required":["repository","issue","reviewId"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"state":{"type":"string"},"added":{"type":"array","items":{"type":"string"}},"warnings":{"type":"array","items":{"type":"string"}},"questions":{"type":"array","items":{"type":"string"}},"reviewId":{"type":"string"}},"required":["state","added","warnings"],"additionalProperties":false}},{"name":"saveImpact","access":"write","arguments_schema":{"type":"object","properties":{"repository":{"type":"string"},"issue":{"type":"string"},"impact":{"type":"object","properties":{"inputs":{"type":"array","items":{"type":"object","properties":{"key":{"type":"string"},"revision":{"type":"string"}},"required":["key","revision"],"additionalProperties":false}},"reviews":{"type":"array","items":{"type":"string"}},"affected":{"type":"array","items":{"type":"string"}},"complete":{"type":"boolean"}},"required":["inputs","reviews","affected","complete"],"additionalProperties":false}},"required":["repository","issue","impact"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"id":{"type":"string"},"state":{"type":"string"},"warnings":{"type":"array","items":{"type":"string"}}},"required":["id","state","warnings"],"additionalProperties":false}}]},{"name":"pending","kind":"port","access":"write","operations":[{"name":"read","access":"read","arguments_schema":{"type":"object","properties":{"repository":{"type":"string"}},"required":["repository"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"json":{"type":"string"}},"required":["json"],"additionalProperties":false}},{"name":"save","access":"write","arguments_schema":{"type":"object","properties":{"repository":{"type":"string"},"json":{"type":"string"}},"required":["repository","json"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"ok":{"type":"boolean"}},"required":["ok"],"additionalProperties":false}},{"name":"deliver","access":"write","arguments_schema":{"type":"object","properties":{"repository":{"type":"string"},"requestJson":{"type":"string"}},"required":["repository","requestJson"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"state":{"type":"string","enum":["delivered","busy","dialog"]}},"required":["state"],"additionalProperties":false}}]},{"name":"settings","kind":"port","access":"read","operations":[{"name":"read","access":"read","arguments_schema":{"type":"object","properties":{"cwd":{"type":"string"},"repository":{"type":"string"}},"required":["cwd","repository"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"mode":{"type":"string","enum":["off","observe","auto"]},"activation":{"type":"string"},"runs":{"type":"integer","minimum":1,"maximum":9007199254740991}},"required":["mode","activation"],"additionalProperties":false}}]},{"name":"clock","kind":"port","access":"read","operations":[{"name":"now","access":"read","arguments_schema":{"type":"object","properties":{},"required":[],"additionalProperties":false},"result_schema":{"type":"object","properties":{"iso":{"type":"string"}},"required":["iso"],"additionalProperties":false}}]},{"name":"results","kind":"port","access":"write","operations":[{"name":"read","access":"read","arguments_schema":{"type":"object","properties":{"repository":{"type":"string"}},"required":["repository"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"json":{"type":"string"}},"required":["json"],"additionalProperties":false}},{"name":"save","access":"write","arguments_schema":{"type":"object","properties":{"repository":{"type":"string"},"json":{"type":"string"}},"required":["repository","json"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"ok":{"type":"boolean"}},"required":["ok"],"additionalProperties":false}}]}],"limits":{"max_steps":30,"max_model_calls":12},"conventions":[]}
```
</details>
