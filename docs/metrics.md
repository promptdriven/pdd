# Metrics

`pdd metrics` reports Autopilot activity on this machine from `~/.local/state/pdd/autopilot/` (or `$PDD_STATE_DIR/autopilot/`).

## Views

- `pdd metrics` prints the unified Overview across active Autopilot repositories on this machine for `Last 24h` and `Week (Mon-Sun)`, showing live `Open` GitHub issues, `Taken`, `PR Created`, and `M/WM (Conv%)` (merged or `observe` `would-merge` count and conversion rate). Add `--repos` to break each window down per repository with a `Total` row.
- `pdd metrics stages` prints the Autopilot gate funnel (`Taken`, `PR`, `Runtime`, `Vectors`, `Formal`, `Suite`, `Review`, `CI`, `M/WM`, `Reopen`), showing each check gate as `passed/applicable` (`-` when 0 runs needed that gate) plus one `Non-merged` status summary line.
- `pdd metrics skills` prints the work mix across `small-change`, `bug`, `feature`, and `Total` with `Taken`, `PR Created`, `M/WM (Conv%)`, and `Median Time` in minutes across merged or would-merge runs (`n/a` when none merged).
- `pdd metrics full` prints Overview, Stages, and Skills together.

## Filters and output formats

- `--repo OWNER/REPO` scopes any view to one repository.
- `--date YYYY-MM-DD` (with optional `--timezone IANA`, defaulting to the local system timezone) scopes any view to one local calendar day.
- `--json` prints the structured `pdd.autopilot.metrics.v1` JSON report.
- `--html [--file PATH]` writes a self-contained HTML dashboard of all three views and opens it in your browser.
- Live `Open` issue counts come from one batched GitHub GraphQL query (`gh api graphql`); when offline or unauthenticated, `Open` displays `?` (`null` in JSON) and exits `0`.

## Turning recording on and off

Autopilot metrics recording is enabled by default whenever Autopilot runs on this machine:

- `pdd metrics off` (or `pdd metrics off --repo OWNER/REPO`) pauses recording new Autopilot runs while preserving existing history.
- `pdd metrics on` (or `pdd metrics on --repo OWNER/REPO`) resumes recording.
