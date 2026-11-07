# Keep the Autopilot start context in Codex coordinator commands

I can start Autopilot with a Codex profile that limits shell variables, and the commands of the coordinator chat still get the Autopilot start context.

Issue: https://github.com/promptdriven/pdd/issues/3031

## Acceptance criteria

1. With a Codex profile that keeps only basic shell variables (`inherit = "core"`), the Codex start of the coordinator sets `PDD_AUTOPILOT_CONTEXT` for the commands of the chat to the same start context that the coordinator process gets.
2. The Codex start sets `HERDR_PANE_ID` and `HERDR_SOCKET_PATH` for the commands of the chat only when the launcher knows both exact values, and it never invents them. The launcher does not know the socket path of the coordinator pane, so the start sets neither, even when the pane has both.
3. The Codex start keeps its folder-trust and update-check settings, and Autopilot writes no Codex configuration.
4. When Autopilot starts with an explicit Codex profile folder (`CODEX_HOME`), the Codex start also sets `CODEX_HOME` for the commands of the chat to that same folder, so a `pdd workflow run` from the chat keeps the coordinator's Codex profile.

Why AC2 is limited: the Autopilot context alone makes a `pdd workflow run` from the chat automatic (reproduction control B2), and the launcher has no reliable source for the socket path of the pane.

## Rules to check

- Codex applies `set` after `inherit`, so `inherit = "core"` and `inherit = "none"` keep these values. A profile with `include_only` that omits these names still removes them, because Codex applies `include_only` last. Autopilot names this limit and does not change the profile.
- Claude, Gemini and agy starts do not change. Native test: the existing provider startup tests.
- Without an explicit `CODEX_HOME`, the Codex start sets no `CODEX_HOME` for the commands. Native test.
- Values with quotes, backslashes, spaces or shell syntax reach the command unchanged. Native test.
