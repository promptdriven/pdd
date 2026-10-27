# Workflow run records

Own `src/workflow-run-records.mjs`. Keep the journal authoritative and expose read-only run discovery for the CLI. Append one small derived entry per new run to `~/.pdd/runs/index.jsonl`; malformed or incomplete index lines are ignored. Resolve a repository from the nearest ancestor `.git` (including a linked worktree pointer) and its `commondir`, so a main checkout, any PDD run worktree and any subfolder share one identity. A repository lookup reads its main checkout and linked worktree journals. A machine lookup reads the index and each saved journal. Stage rows retain start/end times, agent and worktree; for every finished agent stage, match the agent's session files by exact cwd and a timestamp inside the stage window. Exactly one match yields `{agent,id,source:'session-file'}` and a native resume command for compatibility; the public CLI replaces it with its guarded issue-based open command; zero or multiple matches stay null with a reason. Readers never start or mutate a run.

Claude discovery reads ordinary top-level project JSONL files under its configured
config directory (otherwise ~/.claude). Escape every nonalphanumeric cwd character
as a hyphen. Its native user/assistant records carry sessionId, cwd and timestamp;
sidechain records do not identify the main stage. Codex retains session_meta.
Status carries the actual waitingDecision decisions when present; a merge wait
has an empty decision list, so readers can suggest resume instead of approve.

A saved backend session id alone does not establish a finished-stage match. Missing or invalid stage windows, zero matches and multiple matches all leave the session unknown, even if backend metadata has an id. Active stages retain their saved backend identity for attachment.
