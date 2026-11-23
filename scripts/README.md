# Team maintenance scripts

## Autopilot daily observe runner

`scripts/benchmark/run-autopilot-observe.mjs` runs daily read-only Autopilot `--observe` checks across configured repositories with strictly `GET`-only GitHub reads, local `If-None-Match` ETag caching, zero issue/PR mutations, and zero commit-hash/UUID/secret leaks:

```sh
node scripts/benchmark/run-autopilot-observe.mjs --observe \
  --repo promptdriven/pdd \
  --state-dir ~/.local/state/pdd/observe \
  --out ~/.local/state/pdd/observe/observe-runs.jsonl
```

Or pass an operator config file outside the repository (`--config ~/.local/state/pdd/observe/config.json`) listing repositories and optional local checkouts:

```json
{
  "repos": [
    { "repo": "promptdriven/pdd", "checkout": "/path/to/pdd" }
  ]
}
```

### Daily user-level systemd timer (Linux)

Keep daily read-only observe telemetry accumulating under `~/.local/state/pdd/observe/` with a user `systemd` unit (`~/.config/systemd/user/pdd-autopilot-observe.service` and `.timer`):

```ini
# ~/.config/systemd/user/pdd-autopilot-observe.service
[Unit]
Description=Run daily read-only PDD Autopilot observe scorecard

[Service]
Type=oneshot
ExecStart=/bin/bash %h/.local/state/pdd/observe/run-daily-observe.sh
TimeoutStartSec=10min
```

```ini
# ~/.config/systemd/user/pdd-autopilot-observe.timer
[Unit]
Description=Daily read-only Autopilot observe timer

[Timer]
OnCalendar=*-*-* 08:00:00 UTC
Persistent=true
AccuracySec=1min

[Install]
WantedBy=timers.target
```
