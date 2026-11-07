# Workflow draft publication: native case plan

Unexecuted requirement-derived cases for [the Story](../../user_stories/workflow-draft-publication.md).
Every row is one bounded public action unless its reload/continuation is explicitly
split. These are synthetic local fixtures, never actual approval or publication.
All expected observations are fixed here before implementation.

## Fixtures and boundaries

Use real exported parser, CLI, runner and GitHub-helper functions, isolated Git
repositories/run folders and existing native fixture helpers. Bind process,
GitHub and chat effects through existing injectable ports or deterministic fixture
executables; fail unexpected network, model or Herdr requests. Preserve real local
ordinary-update and review-selection checks. Tests use a scoped dummy Codex folder;
any later actual native journey must use the required work4 profile explicitly.
Never alter global environment, auth or Pocket state. Prepare a normal current
gate with completed steps, genuine saved snapshot and later explicit synthetic
approval input. Do not raw-edit approval fields to make a positive pass.

Use the helper's exact prepared keys: repository, runId, stageId, headBranch,
baseBranch, headSha, marker, title. Supply draft as a separate argument. Exact
matching synthetic PRs have canonical identity, original marker, head/base/SHA and
all ordinary verification facts. Assert the intended state/effects as well as exit
code; a generic successful message is insufficient.

## Normal cases

| ID / AC | One action or split sequence | Required observation |
|---|---|---|
| N1 / 1,3 | Parse run/approve with --draft, omitted flag, and quiet workflow start. | Flags accepted as Boolean; omission unchanged; alias parity. Help and completion expose both flags; required CLI docs forms stay synchronized when implemented. |
| N2 / 1 | Start fresh bug run with --draft. | Saved draft=true visible before first chat launch; no PR at startup. |
| N3 / 1,2,6 | Reload N2; legitimately approve prompt publication; reload; separately approve code entry; complete code publication (separate actions). | PR1 and PR2 each create once with --draft; policy remains true; no code branch/chat before its own gate approval. PR2 retains ordinary stacking/base rules. |
| N4 / 1 | Complete small-change publication in a fresh saved draft run. | Single create includes --draft; ordinary completion unchanged. |
| N5 / 2 | At valid existing unpublished gate, approve with --draft and later person words. | Approval validation/save succeeds; identity-checked policy save precedes publication; readback true confirms draft. |
| N6 / 2 | Retry N5 after failed publication at the same durable gate; then reload. | Same decision/evidence/time reused, no duplicate approval; saved true retained. No automatically repeated uncertain effects. |
| N7 / 2,3 | Later approve with omitted/false draft on saved true; use fresh false/legacy-absent controls separately. | True never downgraded; false/legacy default creates ready PR without --draft and retains old acceptance of readback lacking isDraft. |
| N8 / 4,7 | Publish or reconcile with exact existing draft PR and draft=true. | Actual isDraft=true required; original verified PR returned, zero push/create/edit/convert. |

## Limits and refusals

| ID / AC | Setup and action | Required observation |
|---|---|---|
| L1 / 3 | Direct start/approve/publish/reconcile draft values null, 0, 1, empty string, "true", object; separate omission/false controls. | Each incoming nonboolean refuses before effects; no run/policy/approval mutation. Independently seed malformed saved policies and require refusal before publication, with no truthiness coercion. |
| L2 / 1,3 | Duplicate --draft, unknown --draft-only, stray flag value/extra operands; approve --said missing/blank. | Existing local parser refusal before dispatch/effects; ordinary option errors unchanged. |
| L3 / 4 | Exact readback isDraft false, absent, null, string "true" or number 1; exact true control. | Only true permits requested-draft success; others recovery_required with pr:null. |
| L4 / 4,7 | Exact matching ready PR before publication or reconciliation. | Recovery required; PR unchanged; no push/create/edit/convert/duplicate. |
| L5 / 5 | Independently missing/stale snapshot, changed prompt/path selection, missing steps, strict said refusal, invalid saved config. | Normal refusal; policy unchanged; no decision/publication/chat/branch effect. No approve-anyway for draft strengthening. |
| L6 / 5 | Saved old decision/evidence for a distinct current gate with missing review. | Normal missing-review refusal; the old decision/id/time cannot substitute for current review and approval. In a separate action, show the current review and obtain a legitimate fresh normal approval; repeated nonblank wording is not graded. Synthetic legacy shape only; no Pocket edits. |
| L7 / 5 | Cancellation/replacement/gate change while validation waits; fail policy persistence after valid approval. | Refuse before publication/branch/chat effects; retain newest owned state and saved legitimate approval evidence. Failed save never claims policy adoption. |
| L8 / 6 | Start --draft with active nondraft run; separately approve --draft for already published selected stage or uncertain eligibility. | Refuse policy change, preserve run/PR, no replacement/convert/duplicate; start reply points to legitimate approval route. |
| L9 / 7 | Add draft inside prepared intent; alter one identity/source/marker/body precondition independently. | Exact eight-key schema and all ordinary refusals retained; no pre-effect writes. Preserve existing 65,536 code-point boundary. |
| L10 / 7 | Explicit unpublishedOnly with any existing PR or present/unknown remote head. | Existing stronger absence refusal wins even for exact draft PR; zero push/create. |

## Error and uncertainty cases

| ID / AC | Setup and action | Required observation |
|---|---|---|
| E1 / 4,7 | Nonzero/lost create reply with exact unique true readback; false/absent/unavailable variants separately. | Only verified exact draft may succeed; uncertain outcomes stay recovery_required, no automatic create retry. Preserve explicit known GraphQL rejection behavior when PR is proven absent. |
| E2 / 7 | Ambiguous/saturated candidates, changed head/base/SHA/marker, foreign repository, unavailable lookup. | Existing recovery-required/failed semantics win; no adoption of a similar PR, merge or duplicate. |
| E3 / 3,7 | Mutate caller draft or intent while a port awaits. | Captured original inputs govern the attempt; no post-await mode/identity change. |
| E4 / 5,7 | Failed approval/journal/ordinary update, source/body changes during absence checks, failed/uncertain push. | Existing fail-closed behavior; no create after uncertain push and no fabricated successful progression. |

## Required proof after implementation

Run focused native parser/CLI/runner/helper cases and the unchanged helper baseline;
keep before/after failures and raw output outside source. Verify exact saved fields,
intent keys and effect counts, not prose matches alone. The original baseline has
four intended failures and two passing controls, plus 32/32 existing helper passes.
This plan is not a green test result. Runtime: NOT RUN; no invented outside-world
binding, report URL or Prompt tests line. Hosted equivalence, actual publication,
combined candidate suite and original-flow acceptance remain separate later proof.
