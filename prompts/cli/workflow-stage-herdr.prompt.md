# Background native workflow stage transport

Own `src/workflow-stage-herdr.mjs`. Export runHerdrStage({runId,stageId,attemptId,agent,cwd,repository,sourceRoot,commonDir,issueNumber,workflowName,context,instructions,backend?,checkpoint},ports), inspectHerdrStage({backend,cwd},ports), attachHerdrStage({backend},ports), closeHerdrStage({backend,acceptance},ports), closeHerdrRun({backend},ports). Native interactive pdd session and its launcher remain unchanged. Use only documented Herdr0.9.1 commands as the capability baseline. No upgrade, shared restart, credentials/config copy, shell interpolation, shared-session takeover or native flags beyond the full-access launch options specified below.

The runner is the foreground controller; Herdr hosts background native agents. The adapter does not keep PDD advancing after its invoking controller exits. It returns state settled|blocked|recovery_required, backend, evidence, optional reason. Settled means transport candidate only: the runner still checks exact closed handoff, original stage/input, revision/file hashes and actual tests before durable acceptance. Never equate idle with success or invent a native turn ID.

## Identity and effect boundary

Run/attempt IDs are UUIDv4; stage is a safe bounded name; agent codex|claude; cwd is the actual immutable assigned worktree. Herdr PTYs inherit the owned long-running server environment plus shell startup, not later CLI invoker environment. Preserve those ordinary user settings; never serialize/forward the whole environment or tokens. Explicit workspace cwd and actual ready-agent cwd must match the assigned worktree. Surface missing native/settings without repair or shared-server restart. New runs select the shared named `pdd` server explicitly, never default or the focused session. Provision it only when absent after durable intent, under the cross-process layout lock. Reuse a compatible existing pdd server across runs; recorded attempts still pin their actual server fingerprint. Refuse incompatible protocol or changed saved server identity. Do not stop/restart servers to repair compatibility.

Await checkpoint(serializableBackend) BEFORE server/workspace/start/prompt effects and after each returned identity, BEFORE any prompt delivery. Failed durability halts that path. A fresh native stage has a new no-focus tab and backing pane inside its run worktree workspace, allocated by the layout module, with recorded actual workspace/tab/pane/terminal/name/kind/native-session identity when actually present. Names identify local correlation only. Native session absence remains null; never derive a native ID from pane/name/attempt. Preserve startup blocked/failed original pane; do not autoanswer or start again.

Record exact full context+stage instruction digest and durable prompt intent before exactly ONE prompt. Include guide-first actual supplied bytes, never merely links. Confirm fresh ready identity immediately before submit. Prompt reply loss, timeout/stall or unknown identity preserves original intent and becomes recovery_required with no resend, replacement agent or fresh attempt. The explicit backend input is reconciliation only, except a durably closed previous stage backend may donate its same-run owned server reference for a new stage.

## Observation and acceptance

Use actual Herdr agent status/interactive_ready/state_change_seq and agent_session. Pin workspace/tab/pane/terminal/name/agent and any reported native identity; reject replacement/move/identity change rather than selecting another target. Observe this fresh owned ready agent working after the one prompt and later ready idle/done with later lifecycle sequence. A successful prompt --wait carries its documented observed-activity gate but must be paired with fresh identity/readiness reassertion; it is not a native turn receipt. Return transport settled only with observed working->ready evidence. blocked returns blocked; unknown, lost identity, stalled/timeout or incomplete evidence returns recovery_required. Inspect is read-only, never a prompt/start/wait mutation. Do not recover missing evidence from terminal prose or fabricate a report.

closeHerdrStage requires the runner's actual durable acceptance record bound to run/stage/attempt/prompt digest/terminal plus validated evidence digest. Recheck exact owned identity and ready status/sequence before closing only that stage's tab. Acceptance is not person consent. Do not close working/blocked/unknown/replaced/unrelated stages. Checkpoint cleanup intent before effect. Lost cleanup reply becomes uncertain and does not repeat prompt or pretend cleanup succeeded. Preserve actual IDs/native identity before closure; completed closed stages are archived evidence, not live attachable conversations. Keep the run worktree workspace and its initial shell tab between stages; stage tabs are archived and closed after acceptance. closeHerdrRun requires a closed accepted backend and closes only the run workspace at terminal completion; it never removes a Git worktree.

attachHerdrStage checks exact saved active identity and invokes documented agent attach with inherited terminal/cwd/environment, no takeover. It does not create a new native conversation, resume closed history, move unrelated panes or change lifecycle success. Return native attach exit; missing/closed identity refuses finitely.

## Attach-as-watch semantics

`pdd workflow attach` is a watch, not a takeover. It must not hold the stage guard or run lock while the viewer is open. A person prompt is detected when the owned agent becomes working with a lifecycle sequence newer than the saved PDD prompt/settled evidence; record `agent.person.stepped_in`, keep observing, and accept only after the configurable quiet window (default 10 seconds) of idle state. Herdr pane send-text documents a successful empty stdout acknowledgement: accept exit0 with empty stdout only for this notification command, not for identity, prompt, allocation or close commands. Cleanup sends `This step is done. Messages here no longer change the run.` to the old pane and closes its tab before advancing.

## Dependencies

Read entire [Prompting guide](../../docs/prompting-guide.md) before authoring. Load [Herdr layout](workflow-herdr-layout.prompt.md) for allocation and cleanup during generation and verification. Follow [public boundary](public-boundary.prompt.md). Existing runner owns journal/currentness/acceptance/worktree assignment and supplies awaited checkpoint; this adapter owns transport identity and one-delivery observations only. Existing native launcher owns ordinary foreground pdd session. Herdr's public0.9.1 schema/skill commands establish concrete transport behavior; no private service dependency. Tests use capturing Herdr command/process stand-ins and temporary paths, never live servers/agents/models/accounts.

Repository workspace reuse, collision labels, run allocation and cross-process serialization belong to [Herdr layout](workflow-herdr-layout.prompt.md). Concurrent runs may share a compatible pdd server but never a stage tab or native conversation. Common-repository issue ownership and controller locks remain with the runner.

Require ports.withStageGuard(backend,async action) for stage operation; absent guard refuses, never silently falls back to unprotected prompt/attach/cleanup. Main owns the common-repository/run filesystem lock, AsyncLocalStorage same-call reentrance and fsynced attachment epoch. Wrap current identity/ready reassertion + prompt intent/delivery, each observation and cleanup including its fresh inspection. Main holds the same guard across full handoff/currentness/tests/durable acceptance/close. Attach remains nonblocking as specified above; fresh lifecycle and quiet-window validation fence acceptance. Native code must not write a parallel journal/epoch or hold the guard across the whole waiting loop (which would prevent authorized attachment).

A previously captured candidate must not be refreshed by silently substituting a later lifecycle sequence: changed candidate sequence is recovery_required. A cleanup-intent backend stays cleanup-uncertain during inspection and cannot be relabeled as a fresh candidate. Explicit main reconciliation may inspect the original resources, but no unknown prompt or close effect is replayed by this adapter.

Cleanup confirmation is strict: tab close returns id cli:tab:close and result.type ok; then require a valid cli:tab:list/result.type tab_list with the saved tab absent. Keep close_intent on uncertainty and never repeat close or prompt. Historical per-run backends retain workspace-close acknowledgement and inventory checks.

## Headless bootstrap and pre-native recovery

Bootstrap an owned named headless Herdr server with ordinary inherited environment and process cwd. Do not overlay HERDR_STARTUP_CWD, persist environment values, send them through workspace/native/public ports or read/copy auth/config files. Require a usable workspace-list response before stage allocation; an empty inventory is valid. No shared-server restart or settings repair.

Preserve structured Herdr subprocess error code, bounded structured message and command group instead of erasing numeric process exit into generic uncertainty; never include the Node command-failure message or raw prompt/stdout/stderr/environment. Invalid JSON has its own finite transport code.

A direct runHerdrStage invocation may recover the SAME original run/stage/attempt/prompt digest ONLY when saved phase is exactly server_intent, nativeSession null, evidence empty, and no workspace/tab/pane/terminal/seed/sequence/submission/cleanup fields exist. This proves this adapter never reached a workspace mutation or prompt intent. Reuse the actual recorded server fingerprint and owned name; if that exact owned target is stopped, normal bootstrap under the shared stage guard is allowed after another awaited checkpoint, with the SAME IDs/cwd/context/attempt, not a fresh operation. Running target must match the saved server fingerprint; never touch a different/shared session. Recovered bootstrap reads the actual workspace inventory then continues once. Other phases remain original-only inspection: workspace/start/prompt intents, pending/uncertain delivery, candidate and cleanup can never trigger bootstrap restart or prompt retry. inspectHerdrStage remains strictly read-only even for server_intent. Main must explicitly select this proven pre-native recovery through normal resume; no product operation is authorized merely by source delivery.


## Saved-name compatibility

New runs use pdd. Recognize historical pdd-20hex and pdd-FULLUUID backends for original-only inspection and cleanup. Proven pre-native recovery may migrate to pdd only after a normal read proves the historical target stopped, then checkpoint the new name before effects. Never stop or restart historical servers. Refuse an accepted historical predecessor when starting its next stage with legacy_layout_requires_inspection, before any layout effect; never pass a legacy session to the shared registry. Submitted and later phases never migrate or resend.

## Ordinary Codex launch compatibility and honest liveness

For new Codex stages pass --no-daemon via Herdr agent start's supported -- native-argument boundary, together with the full-access options below. This selects the non-daemon interactive process. Do not change profile/env/auth/home/model/effort/settings or ordinary pdd session. Claude uses the full-access argument below. Do not retry an unknown submitted prompt or relaunch a saved later-phase stage.

Agent start readiness and immediate pre-submit identity/readiness remain required; agent disappearance, missing known kind, launch_pending or noninteractive replies cannot qualify. If exact saved pane/terminal identity returns no native agent, report native_agent_unavailable, not replacement identity or account absence; preserve original phase/backend/evidence and no replay. Structured errors for safe native start/get lifecycle commands may retain bounded actual message+operation, but native prompt errors must never retain message/raw text that could contain the stage prompt. Native session IDs remain optional, never fabricated. Launch refusal/vanishing before intent means ZERO stage prompts; after intent/delivery remains unknown model consumption and original-only recovery.

Owning controls verify exact Codex/Claude argv; stand-ins reject daemon-only startup unless no-daemon is supplied, with no real agent/model call. Add liveness cases for native disappearing before/after submit and preservation of noresend/actual phase; daemon startup failure is not classified as successful completion or safe retry.

## Existing native startup blocked before first PDD prompt

On start refusal, perform read-only exact agent lookup: if the saved owned agent is blocked or launch_pending, return blocked/native_start_person_action_required with actionable normal `pdd workflow attach RUN_ID` guidance, preserving phase. Do not scrape terminal text, answer update choices, restart native, or add update/config flags.

A direct runHerdrStage call with SAME run/stage/attempt/input digest may continue the FIRST prompt on an existing exact saved start_intent or ready agent after normal person startup action. Require no working/settled evidence or acceptance/cleanup/submission fields. Reassert server and full actual agent identity/cwd; if not ready return blocked/recovery without starting/replacing anything. Checkpoint actual ready native identity and sequence, then perform the existing one durable prompt_intent and one prompt under shared guard. NEVER server/workspace/native start effects on this path. NativeIDs remain optional, no fake ID. Any saved prompt_intent/submitted/later phase stays inspection-only. Main must explicitly route normal resume to this pre-prompt continuation; inspect stays read-only.

## Pin launch acknowledgement before live reassertion

A validated start acknowledgement is actual identity/evidence, not disposable. Record its native session (when supplied) and sequence, then await the same direct-backend checkpoint in start_intent before any live lookup/first prompt. Live lookup must match that native session and cannot reverse sequence. For agent_not_ready startup-error exact-agent lookup, record/checkpoint that supplied native ID and sequence BEFORE returning blocked or propagating the refusal. Missing native IDs stay null. Any durability failure fences further lookup/prompt; no account/settings/launch flags change. Controls must reject startA->liveB, backwards seq, retain blocked ID/seq and prove post-ack checkpoint failure sends zero prompts.


## Temporary stage contention

Observation maps only WORKFLOW_STAGE_BUSY to active/stage_temporarily_guarded and re-polls the original within the overall deadline. Do not count these unobservable intervals against first activity. Attach itself holds no guard while watching. Acceptance and cleanup still require the guard and fresh exact identity, readiness and quiet-window evidence.

## Full-access native launch

Start every new workflow stage in full-access mode without approval prompts. Codex native arguments after Herdr's -- boundary are --no-daemon --dangerously-bypass-approvals-and-sandbox followed by -c and one invocation-only projects={"<actual assigned absolute cwd>"={trust_level="trusted"}} override; use the simple root override key projects because Codex 0.159.1 splits override keys on literal dots. Encode the path as a quoted TOML inline-table VALUE key so dots, spaces, quotes, backslashes and equals signs remain one exact worktree key; native config selects an exact cwd entry before a parent repo-root entry; Claude uses --dangerously-skip-permissions. Preserve canonical installed agent, cwd/environment/auth/provider/model/effort and actual stage identity/first-prompt/noresend checks. No permission/config/sandbox fallback or global writes. Existing startup/consent/root failure remains actionable/finite, no autoanswer or mode retry. Never persist trust/config/auth/environment changes, automate update choices or alter an existing live agent. Existing live runs/agents must not be relaunched or modified when launch options change. Preserve the four exports and controller semantics.

## Finite area-chat transport

`runHerdrStage` additionally accepts `startOnly:true` and `areaChat:{id,label}`.
This opens one area main native, uses the shared layout module, renames its tab
to the area label and checkpoints prompt delivery before returning `active`.
It must not poll for completion in this mode. Startup/uncertain prompt recovery
retains the same original identity and never resends a possibly delivered prompt.
Area agent environments carry `PDD_AGENT_SESSION=<run>/<area>`; set it inside
the owned pane before native startup, since a preexisting shared server cannot
inherit a newly set parent environment. Normal stage behavior is preserved.

`inspectHerdrChat({backend,cwd},ports)` checks the saved server, pane, terminal,
agent, native-session identity when known, and cwd; it returns `active` with
the live backend even while the agent invokes a report command. It makes no
claim about artifact validity or person intent and never sends a prompt.
The runner owns those checks. Chat attachment remains a view and holds no
mutation guard for its interactive lifetime.

When the named agent is unavailable, chat inspection may return stopped only
if a fresh pane get proves the exact saved workspace/tab/pane/terminal and cwd,
no native agent, no pending launch and no working state. Missing or replaced
panes remain uncertain. This evidence authorizes explicit runner continuation,
not an automatic transport restart.

W1b decision integration: every native stage receives PDD_AGENT_SESSION using
Codex's per-invocation shell_environment_policy.set config or Claude's per-
invocation settings.env. Use run/stage for stage mode and run/area for chat
mode. No global settings are written; this marker routes decisions to evidence
verification and is not a hard security boundary.
