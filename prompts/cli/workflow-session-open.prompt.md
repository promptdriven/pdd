# Reopen accepted native history

Own `src/workflow-session-open.mjs`. Export module function
`reopenNativeSession({session:{agent,id},cwd,stderr},ports?)` returning the native
exit code. This opens an existing finished conversation for inspection, never
creates a workflow stage or submits a prompt. Validate the agent, UUID session id
and absolute cwd before spawning. Invalid identity returns 1 without launch.

Use argv with no shell, inherited terminal and native login/environment, saved cwd,
and no global configuration writes. Supply invocation-only Codex folder trust for the exact saved cwd, as for an already-authorized native session; do not ask to persist a new trust choice. Codex resumes the exact id with explicit
read-only sandbox and approval policy never; never use full-access/bypass flags.
Claude resumes the exact id with tools disabled and plan permission mode. These
settings restrict file-changing tools; the CLI warning still tells a person not
to type into an accepted conversation. Pass no prompt or new user message.
Spawn errors produce a finite diagnostic (127 when the CLI is absent, otherwise 1).
Return actual exit status or signal status and forward termination signals while
preserving normal foreground Ctrl-C handling. Clean up signal listeners.

## Dependencies

- [CLI](pdd-cli.prompt.md): navigation only; the caller owns selection, finished-stage
  eligibility and mandatory default-no TTY confirmation. This module owns only
  native read-only invocation and never supplies workflow acceptance.
