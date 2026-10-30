# Approve a prompt through my agent

I can approve one prompt through my coding agent without leaving the chat.

## Acceptance criteria

1. After I approve in chat, `pdd approve PATH --said "yes, go ahead"` approves that prompt without a terminal and reports its current prose hash.
2. Absent --said keeps terminal y/N; empty, whitespace-only or missing --said values never approve or change a file.
3. Root `pdd.json` with `strict_approvals: true` refuses chat approval and requires a person terminal; missing or false keeps easy mode.
4. Every successful approval durably records the invoking actor, time, route, verbatim words and prompt path/hash; unrelated prompt bytes stay unchanged.

## Rules to check

The [prompt owner](../prompts/cli/prompt-approve.prompt.md) owns validation and editing; [shared policy/journal](../prompts/cli/approval-policy.prompt.md) owns strict configuration and durable provenance. Refuse malformed/unreadable policy and journal before writes. Real terminal decline, schema errors and non-Git-visible/symlink paths never approve. A matching old path with changed prose cannot borrow an earlier approval. No-said agent/piped input still refuses; native Simulator callback remains compatible. An already approved/current standalone prompt remains a no-op. Native concurrent journal writes must retain both successful decisions.

## Acceptance and review

[Native/manual cases](../test/approval-chat/approval-prompt-chat.json) are requirement-derived and remain UNRUN until code/proof. Runtime check (approval-prompt-chat): NOT RUN — no provider calls authorized; native filesystem, Git, TTY, Herdr and gh effects are not bound as Interpreter behavior. No Runtime pass, person approval or publication is claimed.
