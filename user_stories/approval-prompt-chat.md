# Approve a prompt through my agent

I can approve one prompt through my coding agent without leaving the chat.

## Acceptance criteria

1. After I approve in chat, `pdd approve PATH --said -` with my words in a quoted heredoc approves that prompt without a terminal and reports its current prose hash.
2. The stdin form preserves all UTF-8 words, including trailing newlines, backticks, dollar substitutions and quotes, without executing them. A quoted heredoc uses a delimiter absent from my words.
3. Absent --said keeps terminal y/N; empty, whitespace-only or missing --said values never approve or change a file.
4. Root `pdd.json` with `strict_approvals: true` refuses chat approval and requires a person terminal; missing or false keeps easy mode.
5. Every successful approval durably records the invoking actor, time, route, verbatim words and prompt path/hash; unrelated prompt bytes stay unchanged.

## Rules to check

The [prompt owner](../prompts/cli/prompt-approve.prompt.md) owns validation and editing; [shared policy/journal](../prompts/cli/approval-policy.prompt.md) owns strict configuration and durable provenance. Refuse malformed/unreadable policy and journal before writes. Real terminal decline, schema errors and non-Git-visible/symlink paths never approve. A matching old path with changed prose cannot borrow an earlier approval. No-said non-terminal agent/piped input still refuses; easy mode preserves both-TTY y/N even with agent markers, while strict mode refuses marked TTY invocations; native Simulator callback remains compatible. An already approved/current standalone prompt remains a no-op. Native concurrent journal writes must retain both successful decisions. Both routes read policy at the target checkout root. Only a confirmed dead lock owner on this hostname is reclaimed; alive, foreign, malformed or unverifiable ownership remains protected.

## Acceptance and review

Acceptance is checked by executable native Node tests, not manual manifests. New review cases still need execution against base and implementation; this source edit claims no native pass. Filesystem, Git, stdin, terminal, Herdr and gh effects use injected native ports or isolated scratch processes. Unexecuted JSON manifests are removed; they are not Runtime checks. Runtime check: NOT RUN — these native effects have no Interpreter binding. Report actual native results separately; no Runtime pass or person approval is claimed.
