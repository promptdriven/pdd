# Autopilot can wait for machine and account capacity

As the person who runs Autopilot all day, I can leave it running when Codex
reaches its usage limit or the machine runs low on disk or memory. It checks
without an AI call. It keeps my work and resumes after capacity returns.

## Acceptance criteria

- AC1: Each tick reads the saved Codex profile's usage and reset time with the
  read-only account call. It never spends, resets a limit, requests credits or
  signs out. A read failure is visible and pauses new admissions.
- AC2: Memory below 10%, or disk below 1 GiB or 5%, pauses new admissions.
  Equality passes. Unknown observations also pause.
- AC3: One machine incident of each kind covers the repository's affected issues.
  Repeated ticks and a restarted launcher do not send duplicate alerts.
- AC4: Claims, progress and heartbeats remain. A working coordinator cannot start
  a new run during a saved health hold.
- AC5: A later positive read sends one recovery per incident and wakes the
  coordinator. Busy delivery keeps recovery pending for another tick. A past
  reset time without a positive account read does not resume work.
- AC6: Status shows the saved health and known reset time without probing again.
- AC7: Cleanup removes only ended, verified, clean, fully pushed worktrees whose
  branch has a closed or merged PR. Active runs and unknown evidence keep files.
- AC8: Health and machine-sized checks share the same machine observation port.

## Rules to check

For valid total memory and disk, admission passes only when available memory is
at least 10%, and disk is at least both thresholds. Check boundary values with
native fakes. Account recovery needs a healthy read, regardless of the clock.

## Verification

Native Node tests use controlled machine, app-server, GitHub, Herdr and clock
ports. They make no model calls. Live account, timer and alert-service operation
are outside this verification. Prompt approval remains with the person.
