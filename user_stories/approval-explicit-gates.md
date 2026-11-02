# Keep every gate waiting for my decision

I can use my own words in any agent chat after seeing the gate, without pdd treating another chat message as approval.

## Acceptance criteria

1. A latest native chat question, change request, "I approve" or queued message alone never passes any gate; an agent approval call without --said refuses, asks the agent to ask me and use --said, and reads no approval evidence.
2. At each story, PR-opening and code-or-stop gate, any nonblank --said words such as "looks good" or "ship it" are accepted without grading their meaning; empty words refuse and strict mode requires a person terminal.
3. A person terminal keeps y/N, with no approval or advance on decline; no chat arrival, step, done or status crosses an approval gate without an explicit approve call.
4. A workflow without an approve boundary before code shows an advisory and remains usable, including a valid custom single-area PR workflow.

## Rules to check

The [runner](../prompts/cli/workflow-runner.prompt.md#approval-through-the-persons-words) owns approval authority. The [workflow areas](../prompts/cli/workflow-areas.prompt.md#approval-gate-advisory) owner detects the advisory; startup and listing display it. The agent obtains my words after showing the gate; native timestamps cannot prove that. Refusal keeps gate, decisions, prompts, commits, publication and next chats unchanged. Preserve public inputs/exports and existing terminal confirmation, draft selection, journal, PR stacking and recovery rules. No yes-word list or semantic grader is permitted.

## Acceptance and review

Acceptance is checked by executable native Node tests, not manual manifests. New review cases still need execution against base and implementation; this source edit claims no native pass. Filesystem, Git, stdin, terminal, Herdr and gh effects use injected native ports or isolated scratch processes. Unexecuted JSON manifests are removed; they are not Runtime checks. Runtime check: NOT RUN — these native effects have no Interpreter binding. Report actual native results separately; no Runtime pass or person approval is claimed.
