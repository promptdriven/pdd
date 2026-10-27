# Local issue workflows and recipe conversations

## Run an issue through stages

The local workflow runner uses a current Git checkout, GitHub CLI and the installed native Codex or Claude executable. Run it from the actual Git checkout root, using this package's absolute entrypoint if it is elsewhere:

```sh
node /actual/package/bin/pdd.mjs workflow run feature 123 --agent codex
```

Replace `/actual/package` and `123` with the actual package path and an issue in that project. Keep using this absolute entrypoint inside native stages and when resuming or attaching; retain the supplied Node executable path if absolute. The native shell can resolve bare `pdd` differently from the outer terminal, so its PATH is not evidence that the same package will run. The syntax is `pdd workflow run NAME ISSUE [--agent codex|claude]`. Bundled names are `feature`, `bug` and `small-change`; validated project definitions can add safe names or override a complete bundled definition. Codex is the default. ISSUE is a positive number, `owner/repo#number` or `https://github.com/owner/repo/issues/number`. Git/GitHub resolution requires the same current repository and an actual issue, not a PR.

Starting a run permits agent work and the workflow's real Git/PR effects under the user's existing access. The runner resolves the repository and assigns this issue a separate Git worktree and branch. Each agent stage invokes a fresh native session in that immutable assigned worktree with the full canonical [Prompting guide](prompting-guide.md) loaded first, skill/references, selected workflow and actual issue/current-step/prior-artifact context. The agent must summarize the relevant guide method before Story drafting. Each stage must supply its required evidence; process exit zero alone does not establish that evidence.

## Background stages and attachment

The PDD `run` or `resume` process is the foreground controller. Native agent stages run in an owned named Herdr session, without a visible TUI requirement. Each active agent still needs a real backing pane/PTY. This is not a pane-free engine or a PDD daemon.

For every agent stage, the runner records its exact identity and prompt intent before one submission to a fresh ready agent. It observes that same agent working and then ready. That is a candidate, not a pass: the runner must also validate the exact closed handoff, input revision, file hashes, approved tests and currentness. Only durable acceptance permits cleanup of that owned settled workspace and a fresh next stage. Do not fabricate a child exit, native turn ID, handoff or success status.

Use the actual printed UUIDv4 run ID:

```sh
node /actual/package/bin/pdd.mjs workflow attach RUN_ID
```

Run attach from another terminal in the same repository, including its original or a linked checkout. This attaches the saved active conversation. Normal Herdr detach leaves that native process running; it is different from exiting or closing the agent. Normal detach reports workflow waiting (exit 2), not completed. Use the actual run/stage message. Watching does not pause acceptance or cleanup. Sending a prompt requires fresh settlement/currentness validation after the agent finishes, including a quiet idle window of 10 seconds by default. When PDD accepts the step, it closes that stage pane and both terminals report acceptance; later messages cannot change the run. The runner preserves the original identity; it does not start another conversation to satisfy attach.

Accepted completed stage panes can be closed after evidence is retained. Their archived identities are not live attach targets. Later native history resume is not promised by this command. The adapter allows one active stage workspace per owned run server, plus at most one recorded seed workspace; occupied or unknown inventory refuses instead of killing work. Each running stage is a full Codex or Claude session on your computer. There is no fixed repository stage limit; PDD keeps one run per issue and one active stage per run. A run server may retain its seed workspace: automatic cleanup of historical servers is not promised. Concurrent-session throughput is not guaranteed.

Keep the PDD controller alive for automatic handoff. If it exits, Herdr native work may continue, but PDD does not keep advancing. Explicitly resume the saved run to inspect/reconcile. Blocked, unknown, stalled, timed-out or ambiguously delivered work remains the original attempt; do not resend a prompt, restart an agent or close uncertain work as a retry.

### Environment and prerequisites

Herdr 0.9.1 is the capability baseline; compatibility with other versions is not guaranteed. The owned target's client/server/API compatibility must be checked; unsupported targets fail without automatic upgrade, restart or shared-session takeover.

The backing native shell inherits the owned server environment and its normal shell startup. It does not automatically inherit each later CLI invoker's environment. Native executable lookup/login/provider settings follow that backing shell. PDD must pass the assigned absolute issue-worktree cwd and check the actual ready cwd before prompt submission. A missing tool/login/configuration mismatch is surfaced in the original session; it is not repaired by copying environment tokens/credentials, changing HOME or restarting a shared server.

## Stages and decisions

| Workflow | Total listed steps | Agent stages | Human, PR and merge stages |
|---|---:|---|---|
| [Feature](../.pdd/workflows/feature/WORKFLOW.md) | 12 | understand, visual (optional), prompt-story, check, try (optional), build, verify | approve, prompt-pr (optional), prompt-merge (conditional), code-pr, code-merge |
| [Bug](../.pdd/workflows/bug/WORKFLOW.md) | 11 | reproduce, prompt-story, check, try (optional), build, verify | approve, prompt-pr (optional), prompt-merge (conditional), code-pr, code-merge |
| [Small change](../.pdd/workflows/small-change/WORKFLOW.md) | 5 | scope, change, verify | open-pr, wait-merge |

For the bundled definitions, these are 7 possible native sessions for feature (5 required), 6 for bug (5 required), and 3 for small-change. The total step counts include optional/human work. Optional preview uses the project's actual available preview tools, not a PDD-hosted preview service. A recorded skip remains a skip after interruption; the skipped stage must not run on resume. A skipped prompt PR skips its merge wait. Human approval applies to the current revision, not a prior draft.

## Saved identity and resume

The runner retains the canonical repository/issue, saved workflow snapshot, native agent and assigned worktree/branch/base. Complete source context is saved before allocation under the common Git directory's `pdd/workflow-inputs/RUN_ID`; the assigned worktree's actual Git directory contains its `pdd/workflows/RUN_ID` journal and artifacts. Each issue has its own actual Git worktree and journal; stage cwd never falls back to the original checkout. Allocation preserves existing user work, including a dirty original checkout. A shared canonical common-repository index lets original and linked checkouts locate the same assignment/run.

Issue ownership, serialized shared-index updates and one active controller per run apply across linked checkouts sharing that common Git directory. Separate clones do not share those locks. Attachment uses a separate stage guard so it can coexist with a controller waiting for native work without racing acceptance or cleanup. Do not delete journals/claims, reuse another issue's checkout or remove uncertain worktrees to force progress. The runner does not automatically clean up ambiguous user work.

Use the saved run:

```sh
node /actual/package/bin/pdd.mjs workflow resume RUN_ID
node /actual/package/bin/pdd.mjs workflow resume RUN_ID --decision approve
node /actual/package/bin/pdd.mjs workflow resume RUN_ID --decision skip
```

Replace RUN_ID with the actual returned UUIDv4 identity. Resume retains the saved workflow, agent, issue and repository. Without a decision, it only inspects/reconciles saved evidence or reads merge state; it cannot launch the next agent, push or create a PR. `approve` explicitly advances eligible work, accepts the current human decision or selects optional work. `skip` bypasses optional work only. A merge wait reads the saved PR number/URL and actual head state; it advances only after GitHub reports that same original PR head MERGED and never invokes a merge operation. Do not invent a new status or recovery command.

Exit 0 means completed; 2 means waiting; 1 means failed or recovery_required. Use the actual message and current stage. Uncertain native work requires inspection of the saved original identity and durable attempt. An earlier readiness candidate does not authorize progress after changed inputs, attachment or new activity. The runner must freshly validate the original current evidence; it cannot blindly launch another attempt. Uncertain PR effects are reconciled without blind resend. Saved-input HEAD, branch/worktree contents and accepted file hashes are checked before progress. Manual source changes after that input are refused, except for the explicit merged-prompt transition below. No decision flag supplies missing artifacts or accepts arbitrary source changes.

### After a separate prompt PR merges

Before implementation continues, the immutable assigned issue branch must contain the exact recorded prompt merge commit. Prepare that transition through your normal Git workflow in that worktree, with a clean working tree and the approved contract files unchanged. Keep the assigned branch identity; do not move the run to another checkout or branch. Then resume the saved run with `--decision approve`. The runner validates that transition; it does not check out a branch, reset work or rewrite the base for you. Without a decision, merge observation does not launch code work. A different revision or modified approved contract does not inherit the prior approval.

## Evidence between fresh sessions

Each agent receives the canonical issue, current step, exact input revision, accepted prior file pointers and a required handoff location under the run's `artifacts` directory. It must write a JSON handoff with `version`, `runId`, `stageId`, `issueUrl`, `inputRevision`, `summary` and `files`; each file records its project-relative `path`, actual `sha256` and `role`. The exact schema is supplied in the stage request. Any named project files must be real regular files within the project. The understand, visual, check, try and reproduce stages may instead supply a substantive report-only handoff; that report does not establish executable evidence. Work stages require actual files.

The runner checks the identities, input revision, containment and actual file hashes. Missing or stale evidence cannot be repaired by declaring the native session successful. The prompt-story stage supplies prompt, Story and independent-case files plus concrete `testCommands` argument arrays. The small-change scope supplies expectations/cases and its test plan. Review those actual files and commands before approving their use. Approval pins the current revision, contract files and test plan; it is not permission to change the expectations to match code.

At verify, the runner executes the approved commands as argv without a shell and records their real results. After those checks it rereads the exact closed handoff, rechecks pinned and output file hashes and starting-commit ancestry, and requires the execution HEAD and Git-visible worktree fingerprint to be unchanged. Ordinary ignored generated files are outside that fingerprint. Test exit zero cannot certify a changed execution input or handoff. An agent's report or process exit zero does not substitute for test execution. A failed or interrupted native stage needs inspection; resume cannot blindly relaunch it. Do not fabricate or edit journal evidence to force completion.

## Real PR effects

At a PR stage the runner needs clean committed work on a non-base branch, with commits beyond the local default-branch tracking ref. A verified publication also requires actual successful approved checks for that exact current HEAD, worktree fingerprint and accepted argv plan. Later edits, including files changed by a report stage, cannot reuse an older pass. Proposal PRs retain their separate accepted-proposal semantics. The project must have a GitHub `origin` and an existing `refs/remotes/origin/<default-branch>` commit ref. The helper does not fetch that ref for you. It saves intent before push/create and uses explicit repository, base, head and a body file with a stable run/stage marker. It verifies the returned PR number/URL, repository, branch, base, head commit and run/stage marker. Once saved, that exact PR identity must remain the one observed; another matching-intent PR is not a substitute. After uncertainty it reconciles that same identity before any further create; unknown delivery never authorizes a blind resend. Do not fabricate a URL or equate local PR preparation with a real posted PR.

Workflow run is separate from ordinary `session` and the named-recipe shortcuts below. Starting either kind of native work can consume the existing provider allowance; no account eligibility or private service setup is imposed by this kit.

## Use a recipe in one conversation

`pdd workflow feature|bug|small-change [--agent codex|claude] [request text]` remains a companion shortcut for a single native conversation. It loads the complete guide, skill/references, overview and selected WORKFLOW with sibling/subdirectory Markdown. It does not itself create separate stage sessions, drive the local run journal or post PRs. You can also follow the same recipe manually in an existing conversation after loading the full guide.

`pdd session` loads all bundled recipes for open-ended native work. Native login and conversation resume remain with the installed tool. Sessions and workflow stages start agents in full-access mode without approval prompts, with invocation-only Codex trust for the exact cwd and no global configuration writes.

## Discover executable workflows

From the target project, invoke the actual package entrypoint:

```sh
node /actual/package/bin/pdd.mjs workflow list --json
```

The JSON shape is `{ "workflows": [{ "name": "feature", "source": "bundled" }], "default": null }` with actual validated names and `project` or `bundled` sources. Listing performs no agent or PR work. Completion uses that same local catalog as data.

## Edit workflows

Executable definitions live in `.pdd/workflows/NAME/workflow.json`, with their Markdown under that same folder. To customize, copy a complete bundled workflow folder into your project's `.pdd/workflows`, keep its name or rename both the folder and JSON `name`, then edit its stages and instructions. Use a safe lowercase name beginning with a letter, digits and single separating hyphens, at most 64 characters. Run your custom definition with `pdd workflow run NAME ISSUE`; no CLI source change is required.

A present project folder is a complete override. A malformed JSON file, missing referenced Markdown or invalid graph refuses; it does not silently mix in bundled files. Without a project override, the bundled definition is used. Listing validates selected definitions as well.

The closed version-1 definition has `version`, `name`, `overview` and `stages`. `overview` and each stage's `file` are contained Markdown paths. Every stage has a unique `id`, `kind` and `file`; `kind` is `agent`, `human`, `pr` or `merge`. Only agent/PR stages can be optional. Agent stages declare `protocol`: `report`, `proposal`, `work` or `verify`. A proposal declares required artifact roles and approval through `human` or `next-advance`; `next-advance` still pauses until an explicit current approve before further effects. Work requires prior proposal acceptance. A verified PR requires mandatory verification after the latest work stage; later work invalidates an earlier verification. PR stages declare publication `proposal` or `verified`; merge stages reference their prior PR with `prStage`. Invalid references, unknown fields and unsafe file paths refuse. Use a complete bundled JSON as the editable schema example rather than inventing unsupported fields.

The runner captures the definition and complete referenced Markdown with their digests before worktree allocation. Each fresh conversation receives the full canonical guide first plus the saved selected workflow context. Make workflow edits before starting a new run. During an existing run, changed definition/Markdown, canonical guide/skill/reference context or saved snapshot bytes refuse progress; the runner does not silently reload the edited source. The original source selection must still match the saved snapshot on resume. Accepted test commands come from the proposal handoff and person's current decision, not arbitrary executable fields in workflow JSON.
