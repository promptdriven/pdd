# Ask my agent to merge a checked PR

I can ask my coding agent to merge a checked pdd PR.

## Acceptance criteria

1. The bug, feature and small-change skills let my agent merge a pdd PR only after my explicit chat request and at least one check, with all required checks green, first recording my exact request in a PR comment.
2. The merge uses `gh pr merge` with `--merge --match-head-commit <head>`; absent request, failed or pending checks, a changed head or a failed request comment cannot merge.
3. Help, docs and skills describe one-step approval of a ready gate and all its selected drafts. Any nonblank person words can be relayed from any chat through --said - with a quoted heredoc, without grading them. All UTF-8 stdin, including trailing newlines, is preserved. Without --said, my agent asks me, then relays my words. Person-terminal y/N lists and approves the gate and its drafts in one call. Standalone approval reads my target checkout's pdd.json; workflow approval reads the main checkout's pdd.json, so changing the run worktree cannot turn off strict_approvals. Strict mode permits terminal approval only. Latest chat alone never approves. The agent never changes expected values on its own.

## Rules to check

This is an acceptance contract for code-step skill/doc edits, not permission for this builder to merge. Update skills/pdd-{bug,feature,small-change}/SKILL.md and their applicable gate/finish steps; reviewer and scope briefs carry no merge authority; skills/pdd-prompting/RUNBOOK.md and byte-identical root RUNBOOK.md; README.md, AGENTS.md, docs/cli.md, docs/USAGE.md and docs/workflows.md. Keep skill byte caps, guide copies and before-code stop. Preserve agents running pdd rather than hand-editing approval fields. The comment begins `Merge requested by the person: "…"`, contains the verbatim request safely quoted, and is posted before the merge. Resolve and check the exact merge head; pass that head to --match-head-commit. Do not add a pdd merge command. The [catalog](../prompts/cli/command-catalog.prompt.md) owns route forms/help; the [CLI](../prompts/cli/pdd-cli.prompt.md) forwards said literally. Native acceptance stubs gh to inspect argv/input and never merges a real PR. Source/skill/doc implementation belongs to PR 2.

## Acceptance and review

Acceptance is checked by executable native Node tests, not manual manifests. New review cases still need execution against base and implementation; this source edit claims no native pass. Filesystem, Git, stdin, terminal, Herdr and gh effects use injected native ports or isolated scratch processes. Unexecuted JSON manifests are removed; they are not Runtime checks. Runtime check: NOT RUN — these native effects have no Interpreter binding. Report actual native results separately; no Runtime pass or person approval is claimed.
