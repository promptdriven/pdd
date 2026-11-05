# Start Autopilot without Codex startup questions

I can start Autopilot with my chosen Codex account without an update or folder-trust question holding the launch.

## Acceptance criteria

1. Autopilot starts interactive Codex with trust for the selected repository folder and the startup update check disabled for that invocation.
2. A configured Codex launcher keeps its executable, environment, account profile, model and effort.
3. Folder paths and the first message keep their content when they contain spaces, quotes, backslashes or shell syntax.
4. Startup does not change saved agent settings or saved folder trust.
5. Other agent providers, timers and later message delivery keep their existing behavior.

## Rules to check

The two Codex startup settings apply only to that invocation and the trust setting names the selected repository folder. A changed saved setting, changed account or model, interpreted path/message text, or Codex-only option on another provider is forbidden.
