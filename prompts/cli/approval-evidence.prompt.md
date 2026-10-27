# Approval evidence from a native chat

Own `src/approval-evidence.mjs`. A person can tell a stage agent to approve or
request changes. This module checks for a user message in that stage's native
session after the gate question and returns the original text and session ID for
the caller's journal and status record. It reads files only. The caller owns the
current gate, decision semantics, persistence and application of the decision.
This is evidence of a user turn, not proof against an agent modifying local files
or proof that arbitrary user text means approval.

New standalone interface; preserve the worktree/window matching rule from the
existing session-file matcher. A native session ID is optional. When the caller
knows it (pdd started the chat with that ID, or Herdr reported it), only that
session's file can match.

<details>
<summary>Required function, inputs and outcomes</summary>

Export async module function `readApprovalEvidence({stage, gateAskedAt, decision}, ports = {})`.
`decision` is `approve` or `changes`. `stage` has `agent` (`codex` or `claude`),
absolute worktree `root`, finite epoch-millisecond `startedAt` and `endedAt`, and
an optional native `sessionId`. Optional `ignorePrefixes` is a list of text
starts; a user message that starts with one of them (after trimming) is not
evidence. pdd uses it for the change requests it sent itself. A message that
starts with `[Request interrupted` is never evidence.
Those bounds inclusively identify when the native session started, not when its
later approval conversation must end. `gateAskedAt` is finite epoch milliseconds,
at or after stage start, and at or before the observation time. Stage end must be
at or after start and at or before observation time.

Ports optionally supply `fs` (Node promises filesystem), `home`, `env`,
`codexHome`, `claudeConfigDir`, and `now` (a function returning epoch milliseconds).
Defaults are Node's filesystem, OS home, process environment and `Date.now`.
Explicit native roots take precedence over the supplied environment, then the
usual home defaults. Read no other accounts or homes on discovery failure.

Success returns `{ok:true, decision, agent, sessionId, userMessage, userMessageAt}`;
the text is untrimmed and timestamps are epoch milliseconds. Select the latest
eligible user message; ties select the later record in the file. Return no file
contents beyond that message. Failure returns `{ok:false, code, message}` with
one plain, newline-free diagnostic. Codes are `invalid_request`,
`session_not_found`, `session_ambiguous`, `session_unreadable`, and
`user_message_missing`. Never print, throw ordinary filesystem/parse failures,
write files, launch an agent, or grant a decision itself.

</details>

Exactly one native session must match the exact worktree and stage start window. Files with the same session ID (a resumed session) count as one session. A Codex subagent rollout (`thread_source:subagent`, a `parent_thread_id`, or a `source.subagent` object) is never a candidate: step subagents share the worktree cwd but are not the person's chat.
Zero matches refuses; multiple files refuse even if only one has a user reply.
Incomplete discovery must refuse rather than silently discard unreadable files
and manufacture uniqueness. Missing discovery directories mean no matches.
Skip symlink entries and refuse over-depth discovery rather than silently truncate.

<details>
<summary>Native identity and user-message rules</summary>

Codex discovery recursively reads `rollout-*.jsonl` under
`(codexHome | env.CODEX_HOME | home/.codex)/sessions`. Its `session_meta`
record supplies UUID `id`, exact `cwd` and start `timestamp`. Accept user text
from `response_item` payloads with `type:message, role:user` (string content or
`input_text`/`text` blocks), and `event_msg` payloads with `type:user_message`
and string `message`. The outer record's timestamp dates the user turn.

Claude discovery reads only direct `*.jsonl` children under
`(claudeConfigDir | env.CLAUDE_CONFIG_DIR | home/.claude)/projects/<escaped cwd>`.
Escape every non-ASCII-alphanumeric cwd character to `-`, as native Claude does.
Use the first main conversation record carrying UUID `sessionId`, `cwd` and
`timestamp` as identity/start. Native Claude needs no Codex `session_meta` record.
Only `type:user` with `message.role:user`, matching session/cwd, and string or
`text` content counts. Exclude `isMeta`, `isSidechain`, tool-result-only content,
and `subagents` directories. A later conflicting identity invalidates the file.

Text blocks join with newlines; blank-only text cannot serve as evidence.
Timestamps accept finite epoch milliseconds or parseable date strings. The
message must be strictly after the gate and no later than observation time.
Assistant, developer, tool and system records cannot serve as user evidence.
Codex can store generated environment context and AGENTS instructions in user-role
records. Exclude messages consisting only of `<environment_context>` or
`<permissions instructions>` wrappers, and messages beginning with the generated
`# AGENTS.md instructions for ` heading. These are not a person's reply; role
alone does not make these known generated records evidence.
Malformed complete records in a matched file refuse; an unterminated final line
is an in-progress write and never serves as evidence. A matched file's metadata
and messages come from the same read snapshot.

</details>

## Dependencies

- [Prompting guide](../../docs/prompting-guide.md): authoring and generation.
- [Public boundary](public-boundary.prompt.md): authoring and verification; use
  Node built-ins only, with no services or private runtime dependencies.
