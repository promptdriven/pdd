# Check the repository coordinator status

As a repository maintainer, I can see whether this repo's saved Autopilot coordinator is healthy, so that a running Herdr server does not hide a missing coordinator.

## Acceptance criteria

1. When the saved coordinator matches the repository, status reports whether it is working, starting, idle, blocked or done; idle is healthy.
2. When Herdr is running but the saved coordinator is missing, unreadable or mismatched, status reports the coordinator as unavailable and does not claim it is running.
3. Checking status never wakes, replaces or repairs a coordinator and does not query GitHub.

## Rules to check

- Use the saved pane and workspace identity and the actual repository path and provider reported by Herdr.
- Keep timer/server availability separate from coordinator availability.
- Native Node tests inject Herdr and timer responses, then inspect the public status result and calls.
