# Saved workspace evidence: native case draft

This is the native setup/check plan for every step in
`test/cases/import-authorized-workspace-evidence.scenario`. The normal native
vector test executes those cases; results must come from its actual run.
`recordEvidence` is intentionally unbound in Runtime, and the empty simulation
is not an outside-world adapter. These vectors stay outside Runtime JSON test
discovery so they cannot be uploaded as an allegedly executable AI check. Each
case gets an isolated fixture, except the repeat case. Paths are synthetic
fixture paths, not host permissions.

## Fixture and public boundary

Create `/fixture/owned-worktree` as a local Git repository and register a synthetic run for `example/project#17` using existing native fixture helpers. Copy the Harbor selected test, Story, prompt and complete required source. Keep a waiting gate, completed-step sentinel, decisions, question and PR sentinel. Capture selected source with the **real** preflight `captureSource`, never an invented hash reply. Generate each original saved JSON once with the real `renderJson`; use synthetic structured rows, actual producer root, request/report identity, step/check identities and authored expected values. These fixtures are not paid results.

Call the real exported `recordEvidence({ref:'17',summaryFile,cwd:'/fixture/owned-worktree'}, ports)` and actual CLI `workflow evidence 17 --summary FILE`. Bind production native ports where supported; use real local Git/filesystem for uninjectable capture/read boundaries. Do not add a test-only product API. Throw on network/Herdr/model calls. Keep receipts and native outputs outside tracked source.

For associated cases, call the eventual real `associateEvidenceWorkspace({ref:'17',workspace,stage,tests,cwd:'/fixture/owned-worktree'})` registration and its actual `workflow evidence-associate` CLI route under existing fixture run ownership. Supply no approval words or terminal confirmation and assert that registration does not change protected approval fields or add a gate. Validate run ownership independently of receipt fields. Use exactly the named producer, stage and test selection. Until that operation exists, positives remain unexecuted draft requirements. For PR 1 derive the anchor from the fixture run's recorded PR 1 identity; pass no source ref. Registration may bind the original owned root after code entry without treating its later code bytes as PR 1 source. Capture exact status/evidence bytes and workflow/Git snapshots before each call.

## Cases

| Scenario step | Native setup before the one import | Required result |
|---|---|---|
| same-worktree | Producer is the registered root; ordinary current source, no alternate association. | Accept; existing behavior. |
| authorized-clone | Clean clone at exact authored head; registered root/run/owner/current-selection association. | Accept unchanged original clone JSON. |
| authorized-nested | Separate Git repository at `owned-worktree/.pdd-runtime/project`; registered exact-root association and complete same authored-relative selected closure. | Accept unchanged original nested JSON. |
| unassociated-clone | Identical selected bytes, commit and remote; no association. | Refuse despite equality. |
| unassociated-nested | Matching nested repository; no association. | Refuse despite containment. |
| wrong-run | Matching bytes and root, but association has another run identity. | Refuse. |
| wrong-owner | Matching bytes/root/run, but association names another repository owner. | Refuse. |
| wrong-root | Registration names clean clone, receipt names a second same-content clone. | Refuse. |
| changed-story | Authorized clone; change one selected Story byte after registration, leaving test unchanged. | Refuse stale complete source. |
| changed-dependency | Authorized nested root; change one required prompt dependency byte, leaving test unchanged. | Refuse stale complete source. |
| changed-authored-source | Producer retains original matching receipt bytes, but current authored run Story changes after registration. | Refuse stale current-stage anchor. |
| extra-selection | Receipt adds another valid test outside registered selection. | Refuse; association scope cannot grow. |
| missing-source | Authorized producer lacks one required captured source file. | Refuse; no partial source acceptance. |
| pr1-after-code | Record an owned PR 1 head and register its frozen selection; enter code through normal fixture lifecycle and change current prompt, Story and test. Producer retains exact frozen PR 1 bytes. | Accept for PR 1 only, despite current-code drift. |
| same-root-pr1-after-code | Original receipt repo names registered root before code entry; enter code and change current code-area source, then explicitly register that original root against the retained recorded PR 1 source. | Accept for PR 1 only without comparing the root's later code bytes. |
| missing-anchor | Same PR 1 setup, but frozen source is unavailable. | Refuse; no current-source fallback. |
| changed-anchor | Producer remains exact, but retained frozen source bytes change. | Refuse; original source identity must still match. |
| wrong-anchor | Corrupt the saved association to name an unrelated or non-recorded PR 1 head with equal selected files; the public registration route never accepts a caller-supplied head. | Refuse; equality cannot establish ownership. |
| repeat-original | Repeat successful authorized-clone import with the exact same original file. | Accept without execution or approval; retain append/order semantics. |

## Assertions beyond the exit code

For **every** case, compare original receipt bytes before/after and every original repository, request/report, row/test/step, expected-value and source identity in saved evidence. On success, only evidence/import-time and separate association metadata may change. On refusal, exact evidence/status bytes must remain unchanged. Preserve workflow steps, gate, question, decisions, approvals, chats, Git HEAD/files and PR state. Assert zero model/network/Herdr/PR calls. Repeat retains the same receipt and report provenance and does not claim fresh execution.

Repeat registration for the same run/producer/selection/source key and verify replacement affects only that key. If its stage changes, retain previously imported evidence metadata: status and re-import must not relabel original PR 1 JSON as current code. Revalidate its saved stage separately.

Read status after current-source imports and after PR 1 import with code drift. Check stage-specific Story eligibility and unknown warnings after association/anchor loss. Compare later **prepared** PR 1 evidence with its original report and frozen selection; current-code status must not count it as a code pass. Status performs no write or PR update. Verify the existing authorized publication path selects only the matching stage; do not publish in these cases. These native checks are separate from any Interpreter result and must not be reported as run until executed.
