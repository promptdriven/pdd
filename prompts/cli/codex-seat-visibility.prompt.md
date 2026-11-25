# Codex active seat visibility

Own `src/accounts/codex-seat-visibility.mjs`. Export pure deterministic functions `resolveCodexSeatNotice(input)` and `summarizeCodexRuntimeStatus(input)` that classify interactive `pdd-codex` launches, format the single-line startup seat notice, and normalize/format active `pdd-codex` runtime lease status for `pdd accounts status [--json]`. Perform no filesystem, network, process, or clock I/O, and never mutate caller inputs.

## Domain decisions

- **Interactive notice eligibility (`resolveCodexSeatNotice`):** Determine whether `pdd-codex` should emit a 1-line startup notice on `stderr` in strict precedence order:

  | Priority | Condition | `shouldPrint` | `reason` | `notice` |
  |---|---|---|---|---|
  | 1 | `isInteractiveTty !== true` | `false` | `"non_interactive_tty"` | `null` |
  | 2 | First non-flag positional token before `"--"` matches a non-interactive Codex subcommand | `false` | `"non_interactive_subcommand"` | `null` |
  | 3 | Any option token before `"--"` (outside value-flag operands) is a machine-output or quiet flag | `false` | `"machine_output_flag"` | `null` |
  | 4 | Otherwise (bare TUI launch, `resume`, `fork`, or interactive initial prompt) | `true` | `"interactive"` | 1-line notice string |

  - Scan `codexArgs` (default `[]`) strictly before `"--"` so tokens after `"--"` (such as `pdd-codex -- -prompt` or `pdd-codex -- --json`) are treated as positional prompt operands rather than flags or subcommands.
  - Skip the following argument after global Codex value flags (`-c`, `--config`, `--enable`, `--disable`, `--remote`, `--remote-auth-token-env`, `-i`, `--image`, `-m`, `--model`, `--local-provider`, `-p`, `--profile`, `-s`, `--sandbox`, `-C`, `--cd`, `--add-dir`, `-a`, `--ask-for-approval`, `--color`; `--flag=value` consumes only one token) so value operands such as `-C exec` or `-p review` are never misclassified as subcommands.
  - Non-interactive subcommands (exact match on first positional token before `"--"`): `"exec"`, `"e"`, `"review"`, `"app-server"`, `"mcp-server"`, `"exec-server"`, `"login"`, `"logout"`, `"mcp"`, `"features"`, `"apply"`, `"a"`, `"archive"`, `"unarchive"`, `"delete"`, `"migrate-rollouts"`, `"migrate-nfs-db"`, `"completion"`, `"help"`, `"cloud"`, `"doctor"`, `"update"`, `"sandbox"`, `"debug"`, `"queue"`.
  - Machine-output or quiet option flags before `"--"` (outside value-flag operands): `--json`, `--experimental-json`, `--quiet`, `-q`, `-o` / `--output-last-message` (and `=` form, consuming separate value operand), `--output-schema` (and `=` form, consuming separate value operand), and `--format` / `--output-format` when paired with case-insensitive `"json"` (`--format=json`, `--output-format=json`, or separate `"json"` operand; non-`"json"` values still consume their operand without triggering `machine_output_flag`).
  - When both a non-interactive subcommand and a machine-output flag appear before `"--"` (for example `["exec", "--json", "hi"]` or `["--json", "exec", "hi"]`), priority 2 (`"non_interactive_subcommand"`) wins deterministically.
- **Single-line sanitization and notice formatting:** Strip ANSI CSI escape sequences and replace ASCII control characters (`0x00–0x1F`, `0x7F`, including `\r`, `\n`, `\t`) with spaces, collapse repeated whitespace to one space, and trim `label`, `accountId`, and `ownerLogin` before formatting so every emitted notice or status line is guaranteed to be a single clean line.
  - Resolve `seatLabel` as sanitized `seat.label`, else sanitized `seat.accountId`, else `"unknown"`.
  - Resolve seat access (`accessType`): `"owner"` or `"shared"` from explicit `seat.accessType`; else from boolean `seat.isOwner` (`true` -> `"owner"`, `false` -> `"shared"`); else from boolean `seat.shared` (`true` -> `"shared"`, `false` -> `"owner"`); else `"unknown"`.
  - Resolve `pinned` (`seat.pinned === true`) and `autoRotate` (`typeof seat.autoRotate === "boolean" ? seat.autoRotate : !pinned`).
  - Format parenthetical details: `accessPart` is `"owner"` when `accessType === "owner"`, `"shared by <ownerLogin>"` when `accessType === "shared"` with non-empty `ownerLogin`, `"shared"` when `accessType === "shared"` without `ownerLogin`, and omitted (`null`) when `accessType === "unknown"`. `rotatePart` is `"auto-rotate on"` when `autoRotate` is `true`, else `"auto-rotate off"`. Combine as `accessPart ? "${accessPart}, ${rotatePart}" : rotatePart`.
  - Emit `pdd-codex: pinned to "${seatLabel}" (${details})` when `pinned` is `true`, else `pdd-codex: using PDD Cloud seat "${seatLabel}" (${details})` (no trailing newline).
- **Runtime status aggregation, enrichment, and formatting (`summarizeCodexRuntimeStatus`):**
  - Filter `runtimeLeases` (default `[]`): keep only plain objects whose `live_sessions` is a finite integer `>= 1` and that carry at least one non-empty identifier (`lease_id`, `account_id`, or `label`). Ignore stale or 0-session entries completely.
  - Enrich missing `label`, `access_type`, and `owner_login` without cross-seat contamination: look up matching Codex accounts in `accounts` (entries with `provider === "codex"` or absent `provider`) by exact `account_id` first, else exact `label` only when neither record carries a conflicting non-empty `account_id`; if still missing `access_type`, `owner_login`, or `label`, fall back to `cachedActiveCodex` ONLY when the resolved `account_id` is non-empty and equals `cachedActiveCodex.account_id`.
  - Drop all unwhitelisted fields (never copy tokens, grants, or gateway URLs). Emit exact lease fields: `mode` (`"pinned"` when `entry.pinned === true || entry.mode === "pinned"`, else `"shared"`), `lease_id`, `account_id`, `label`, `access_type` (`"owner" | "shared" | "unknown"`), `owner_login`, `auto_rotate` (boolean `entry.auto_rotate`, defaulting to `!pinned`), `pinned`, `live_sessions` (positive integer), and `expires_at` (trimmed non-empty string or `null`).
  - Sort `leases` deterministically: `"shared"` before `"pinned"`, then `label.toLowerCase()` ascending, then `account_id ?? ""` ascending, then `lease_id ?? ""` ascending.
  - Summary invariants: `codex_runtime.active` equals `leases.length > 0`; `codex_runtime.live_sessions` equals the exact sum of `live_sessions` across `leases` (`0` when empty); when `active` is `true`, top-level `label`, `account_id`, `access_type`, `owner_login`, `auto_rotate`, `pinned`, and `expires_at` mirror `leases[0]`; when `active` is `false`, all seven top-level summary fields are `null`, `live_sessions` is `0`, `leases` is `[]`, and `lines` is `[]`.
  - Format one human-readable line per active lease in `lines`:
    - `prefix`: `"Active pdd-codex (pinned)"` when `pinned` is `true`, else `"Active pdd-codex"`.
    - `accessDisplay`: `"owner (<owner_login>)"` / `"owner"` for `"owner"`, `"shared (<owner_login>)"` / `"shared"` for `"shared"`, or `"access: unknown"` for `"unknown"`.
    - `rotateDisplay`: `"auto-rotate: on"` when `auto_rotate` is `true`, else `"auto-rotate: off"`.
    - `sessionsDisplay`: `"1 live session"` when `live_sessions === 1`, else `"${live_sessions} live sessions"`.
    - Line: `"${prefix}: ${label} (${accessDisplay}, ${rotateDisplay}, ${sessionsDisplay})"`.

## Public contract

- `resolveCodexSeatNotice({ codexArgs?, isInteractiveTty?, seat? })`
  - Input: `{ codexArgs?: string[], isInteractiveTty?: boolean, seat?: { label?: string | null, accountId?: string | null, pinned?: boolean, autoRotate?: boolean | null, isOwner?: boolean | null, shared?: boolean | null, accessType?: "owner" | "shared" | "unknown" | null, ownerLogin?: string | null } | null }`
  - Output: `{ shouldPrint: boolean, reason: "interactive" | "non_interactive_tty" | "non_interactive_subcommand" | "machine_output_flag", notice: string | null }`
- `summarizeCodexRuntimeStatus({ runtimeLeases?, accounts?, cachedActiveCodex? })`
  - Input: `{ runtimeLeases?: Array<{ mode?: "shared" | "pinned" | null, pinned?: boolean | null, lease_id?: string | null, account_id?: string | null, label?: string | null, is_owner?: boolean | null, shared?: boolean | null, access_type?: "owner" | "shared" | "unknown" | null, owner_login?: string | null, auto_rotate?: boolean | null, expires_at?: string | null, live_sessions: integer }>, accounts?: Array<{ account_id?: string | null, label?: string | null, provider?: string | null, is_owner?: boolean | null, shared?: boolean | null, owner_login?: string | null }>, cachedActiveCodex?: { account_id?: string | null, label?: string | null, is_owner?: boolean | null, owner_login?: string | null } | null }`
  - Output: `{ codex_runtime: { active: boolean, live_sessions: integer, label: string | null, account_id: string | null, access_type: "owner" | "shared" | "unknown" | null, owner_login: string | null, auto_rotate: boolean | null, pinned: boolean | null, expires_at: string | null, leases: Array<{ mode: "shared" | "pinned", lease_id: string | null, account_id: string | null, label: string, access_type: "owner" | "shared" | "unknown", owner_login: string | null, auto_rotate: boolean, pinned: boolean, live_sessions: integer, expires_at: string | null }> }, lines: string[] }`

## Dependencies

None. This module is pure classification, normalization, and formatting.
