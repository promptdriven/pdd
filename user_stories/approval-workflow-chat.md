# Approve a gate and its prompts in one step

I can approve a ready workflow gate and its draft prompts with one chat decision.

## Acceptance criteria

1. After I approve in chat, `pdd workflow approve 2755 --said -` with my words in a quoted heredoc approves the ready gate and every draft prompt belonging to it, listing each path and current hash.
2. Unrelated unchanged drafts stay draft; a missing gate, malformed selected prompt or invalid policy refuses without advancing or partially approving a different prompt.
3. PR creation and later updates show all recorded gate and matching standalone prompt approvals with actor, time, route and verbatim chat words safely quoted.
4. A person terminal lists the gate paths and hashes and approves the ready gate and all its drafts with one y/N answer. Without --said, an agent, non-terminal or current area pane must ask me and use --said; strict mode permits only the person terminal.
5. Chat approval refuses if the shown gate snapshot is absent or its selected paths or prose hashes changed. Show the gate again before asking me again.
6. Approving PR 1 does not approve the later code-or-stop gate; distinct or reopened gates keep separate approvals even at the same clock time, while retrying publication of the same gate reuses its evidence without duplication.

## Rules to check

The [runner](../prompts/cli/workflow-runner.prompt.md#approval-through-the-persons-words) owns batch selection/validation and effect ordering. It uses the [run record](../prompts/cli/workflow-runs.prompt.md#approval-history) and [publisher](../prompts/cli/workflow-pr-evidence.prompt.md#approval-evidence-in-prs). Test multiple changed drafts, stale approved prose, unchanged unrelated drafts, staged/unstaged/untracked files, a deleted prompt, current approvals, a missing comparison and ask-code PR 1 paths. Native history is recording only: latest questions, changes, genuine approvals and queued messages never authorize a gate. Any nonblank --said words work at every gate; the agent judges intent after showing the gate. Strict mode refuses valid native Herdr evidence too. Injected actor/session and clock facts must survive save/reload and initial/create/update publication. Hostile words include backticks, newlines, @mentions, #references, HTML, bidi and exact pdd-workflow: prefixes; no supplied value may become a mention, issue link or extra ownership marker. Private scratch proof uses stub agents, scratch HOME and a private Herdr session; no live session or provider call.

## Acceptance and review

Acceptance is checked by executable native Node tests, not manual manifests. New review cases still need execution against base and implementation; this source edit claims no native pass. Filesystem, Git, stdin, terminal, Herdr and gh effects use injected native ports or isolated scratch processes. Unexecuted JSON manifests are removed; they are not Runtime checks. Runtime check: NOT RUN — these native effects have no Interpreter binding. Report actual native results separately; no Runtime pass or person approval is claimed.
