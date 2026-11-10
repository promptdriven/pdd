# Autopilot alert ports

I can check `prompts/cli/autopilot-alerts.prompt.md` with declared blob, directory, HTTP, repository, token-command, OS, clock, lock and compute ports.

```pdd-boundary
prompts/cli/autopilot-alerts.prompt.md
```

## Acceptance criteria

1. `runAutopilotAlerts` validates and saves a Slack webhook in `autopilot-alerts.json` (`exitCode: 0`), rejects non-HTTPS or unsupported webhook URLs (`exitCode: 2`), and records and sends an `alert` through `http.request` (`exitCode: 0` with `HTTP 404 no_service` recorded in `bf4e28e0718a385f034b.json`).
2. `alertStatusLine` reads the saved alert record and destination for `promptdriven/pdd` to report undelivered open alerts and the last failed delivery, and returns the empty string for an invalid repository name.
