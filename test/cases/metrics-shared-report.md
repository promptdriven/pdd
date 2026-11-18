# Autopilot metrics native verification cases

These are requirement-derived native cases for `pdd metrics`, `src/autopilot-metrics.mjs`, and `src/metrics-model.mjs`.

- Unified overview reports `Last 24h` and `Week (Mon-Sun)` across active Autopilot repositories on the local machine; `--repos` breaks each window down per repository with a `Total` row, and `--repo OWNER/REPO` filters to one repository.
- Distinct issue deduplication within a window ensures `0 <= M/WM <= Taken` and `0 <= PR Created <= Taken` even when Autopilot retries an issue, and totals reconcile identically across Overview, Stages, and Skills.
- `pdd metrics stages` computes `passed/applicable` for `Runtime`, `Vectors`, `Formal`, `Suite`, `Review`, and `CI` (`-` when 0 runs had a pass/fail verdict on that gate), counts post-merge `Reopen`, and summarizes non-merged runs by status.
- `pdd metrics skills` groups runs into `small-change`, `bug`, `feature`, and `Total` with conversion percentage and integer-minute `Median Time` across merged or would-merge runs (`n/a` when none merged).
- `--date YYYY-MM-DD` with optional `--timezone IANA` scopes all views to that local calendar day, and offline or unauthenticated GitHub lookup shows `?` (`null` in JSON) for `Open` while exiting 0.
- `pdd metrics off` and `pdd metrics on` (globally or per `--repo OWNER/REPO`) pause and resume recording new runs while keeping earlier Autopilot history readable; `--json` and `--html [--file PATH]` emit structured JSON and a self-contained HTML dashboard.
