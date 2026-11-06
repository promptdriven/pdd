# Keep the Autopilot start context in Codex coordinator commands

I can start Autopilot with a Codex profile that limits shell variables, and the commands of the coordinator chat still get the Autopilot start context.

Issue: https://github.com/promptdriven/pdd/issues/3031

Draft from the reproduce step. The prompt-story step owns the final text.

## Acceptance criteria

1. With a Codex profile that keeps only basic shell variables (`inherit = "core"`), the Codex start of the coordinator sets `PDD_AUTOPILOT_CONTEXT` for the commands of the chat to the same start context that the coordinator process gets.
2. When the coordinator pane has a Herdr pane id and socket path, the Codex start also sets `HERDR_PANE_ID` and `HERDR_SOCKET_PATH` for the commands of the chat to those values.
3. The Codex start keeps its folder-trust and update-check settings, and Autopilot writes no Codex configuration.

## Rules to check

- Codex applies `set` after `inherit`, so `inherit = "core"` and `inherit = "none"` keep these values. A profile with `include_only` that omits these names still removes them, because Codex applies `include_only` last. Autopilot names this limit and does not change the profile.
- Claude, Gemini and agy starts do not change. Native test: the existing provider startup tests.
- Values with quotes, backslashes, spaces or shell syntax reach the command unchanged. Native test.
