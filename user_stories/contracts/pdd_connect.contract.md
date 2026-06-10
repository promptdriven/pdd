<!-- pdd-story-contract derived-from-story="../story__pdd_connect.md" story-hash="<auto>" issue-ref="https://github.com/promptdriven/pdd/pull/1501#issuecomment-4662232582" -->

# Contract: pdd connect

> Generated from the human-verified user story + issue. Do not hand-edit:
> it is regenerated to align whenever the Story changes. Humans verify the
> Story (`../story__pdd_connect.md`), not this contract.

## Covers

- R1: Local server startup exposes browser and API endpoints.
- R2: Port selection respects default auto-detection and explicit user choices.
- R3: Remote access requires explicit safety handling.
- R4: Cloud registration is optional and cleaned up on shutdown.

## Context

The `pdd connect` command is implemented by
`prompts/commands/connect_python.prompt`. It does not perform LLM work; it
starts a local server and may register a remote session when authenticated.

## Acceptance Criteria

1. Given the default port is available, when the user runs `pdd connect`, then the command starts the server on the requested host/port, prints the local server URL, API docs URL, frontend URL, and stop instructions.
2. Given the default port is busy and the user did not explicitly choose a port, when the command starts, then it scans the configured fallback range and reports the replacement port.
3. Given an explicitly requested port is unavailable, when the user runs `pdd connect --port <port>`, then the command exits with an error instead of silently picking a different port.
4. Given remote binding is requested without a token, when the user runs `pdd connect --allow-remote`, then the command warns and requires explicit confirmation before exposing the server.
5. Given the user is authenticated and does not request local-only mode, when the server starts, then the command registers a cloud session, starts session maintenance, and confirms registration to the user. The cloud access URL is captured but not printed (its display is deferred until the production `/connect` page is deployed).
6. Given shutdown or interruption, when a remote session was registered, then the command stops listeners/heartbeat and deregisters the session.

## Oracle

These details matter for pass/fail:
- localhost-only default binding
- explicit-port vs default-port conflict behavior
- browser opening is skipped by `--no-browser`
- cloud registration is skipped by `--local-only` or missing authentication
- the cloud access URL is not printed to the user (display deferred until the production `/connect` page ships)
- remote session cleanup is attempted on shutdown
- no cost tracking or LLM invocation is introduced

## Non-Oracle

These details should not matter:
- exact browser implementation used by the platform
- exact cloud URL hostname
- exact color/style of console messages
- exact Uvicorn logging format

## Negative Cases

- An explicit unavailable port must not be replaced automatically.
- Remote binding without token must not proceed silently.
- Local-only mode must not register a cloud session.
- Shutdown must not leave an active registered session when cleanup is possible.

## Non-Goals

- This story does not verify frontend UI behavior after connection.
- This story does not cover cloud authentication setup.
- This story does not assert network behavior outside command startup and cleanup.

## Candidate Prompts

- `prompts/commands/connect_python.prompt` — primary owner of the `pdd connect` CLI.
- `prompts/server/app_python.prompt` — related local server application.
- `prompts/remote_session_python.prompt` — related cloud session manager.

## Notes

This story is part of the command-by-command user-story split requested from
the PR 1501 integration comment.
