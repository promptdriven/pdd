# Ask my agent to merge a checked PR

I can ask my coding agent to merge a checked pdd PR.

## Acceptance criteria

1. The bug, feature and small-change skills let my agent merge a pdd PR only after my explicit chat request and green checks, first recording my exact request in a PR comment.
2. The merge uses `gh pr merge` with `--merge --match-head-commit <head>`; absent request, failed or pending checks, a changed head or a failed request comment cannot merge.
3. Help, docs and skills describe --said, the one-step gate/prompt approval, preserved terminal/native-chat routes and root pdd.json strict_approvals, while the agent never changes expected values on its own.
4. The workflow start command is `pdd workflow run`; other 0.1.12 command names and the rule that pdd itself never merges stay unchanged.

## Rules to check

This is an acceptance contract for code-step skill/doc edits, not permission for this builder to merge. Update skills/pdd-{bug,feature,small-change}/SKILL.md and their applicable gate/review/finish steps; skills/pdd-prompting/RUNBOOK.md and byte-identical root RUNBOOK.md; README.md, AGENTS.md, docs/cli.md, docs/USAGE.md and docs/workflows.md. Keep skill byte caps, guide copies and before-code stop. Preserve agents running pdd rather than hand-editing approval fields. The comment begins `Merged at the person's request: "…"`, contains the verbatim request safely quoted, and is posted before the merge. Resolve and check the exact merge head; pass that head to --match-head-commit. Do not add a pdd merge command. The [catalog](../prompts/cli/command-catalog.prompt.md) owns route forms/help; the [CLI](../prompts/cli/pdd-cli.prompt.md) forwards said literally. Native acceptance stubs gh to inspect argv/input and never merges a real PR. Source/skill/doc implementation belongs to PR 2.

## Acceptance and review

[Native/manual cases](../test/approval-chat/approval-requested-merge.json) are requirement-derived and remain UNRUN until code/proof. Runtime check (approval-requested-merge): NOT RUN — no provider calls authorized; native filesystem, Git, TTY, Herdr and gh effects are not bound as Interpreter behavior. No Runtime pass, person approval or publication is claimed.
