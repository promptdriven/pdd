# Autopilot issue claims

Own `src/autopilot/claims.mjs`. It provides the standalone GitHub issue-claim reader,
heartbeat updater and takeover-limit policy for the Autopilot core engine, with no
dependency on workflow sessions, Herdr or issue-sorting adapters.

## Domain decisions

- **Winning claim (`winningClaim`).** An issue is claimed only while it carries the
  `pdd:working` label. Claim eras are read from the issue timeline in service order:
  an `unlabeled` event for `pdd:working` ends the current era, and the first `labeled`
  event after a removal (or from the start) opens a new era and defines its winning
  label event.
- **Trusted claim comment.** Within an era, a comment matches only when its JSON block
  names `repository` (case-insensitive match), `coordinatorId`, `machine` and
  `labelEventId` (matching the winning label event ID), its author matches the label
  event actor (case-insensitive), and `authority.read` returns `trusted`. Exactly one
  matching comment identifies the era's owner; zero or multiple matches leave owner
  fields empty.
- **Heartbeat and legacy expiry.** A claim record with a top-level `lastSeen` member
  uses only the GitHub server time of that comment (`updated_at`, else `created_at`),
  clamped to at most `now`, and expires 4 hours (`4 * 60 * 60 * 1000` ms) after that
  time. A record without `lastSeen`, a bare label, an unmatched claim or a comment
  with no server time uses the latest finite issue/comment/timeline timestamp and
  expires after 24 hours (`24 * 60 * 60 * 1000` ms). An unknown clock or unknown
  timestamp never expires a claim.
- **Takeover ceiling (`takeoverLimited`).** An expired era followed within 10 minutes
  by a `pdd:working` label added by the same actor as the removal continues the chain;
  switching owner increments `takeovers`, while re-claiming by the same
  `(coordinatorId, machine)` keeps the chain without incrementing. Any normal release
  resets `takeovers` to `0` and restarts the chain. Removing `pdd:stuck` while a claim
  is takeover-limited also resets `takeovers` to `0`. `takeoverLimited(claim, self)`
  forbids a 4th takeover (`> 3`), except when `self` matches the expired claim's own
  `coordinatorId` and `machine`.
- **Single-member heartbeat edit (`refreshClaimHeartbeat`, `withoutClaimHeartbeat`).**
  `refreshClaimHeartbeat` edits only the top-level `lastSeen` member of the owning
  coordinator's active winning claim comment (verified via a fresh GET and confirmed
  by PATCH readback), preserving all other bytes of the comment body.
  `withoutClaimHeartbeat(body)` strips only top-level `lastSeen` and
  `longRunningAlertedAt` members from a claim record.
- **Minimal read ports (`createDependencyReadPorts`).** Builds `{ github, authority,
  clock, owners }` for claim inspection using injected `execFile`, `now`, optional
  `githubCache` (ETag conditional GET with `githubFullLastPage` guard), optional
  `githubFloor` (bypassed on live claim safety reads) and optional `authority`
  (defaulting to repository owner, push/maintain/admin collaborators, and optional
  `pdd.json` `autopilot.trust` when `cwd` is supplied). When `owners.read` checks
  multiple issues on native GitHub reads, a complete GraphQL `labels` batch skips
  issues that lack `pdd:working`; incomplete or failed batches fall back to per-issue
  REST reads.

## Public contract

- `CLAIM_EXPIRES_AFTER` (`4 * 60 * 60 * 1000`)
- `claimRecord(body) -> { value: object, text: string } | null`
- `editClaimRecord(body, record, expected, name = 'lastSeen') -> string | null`
- `heartbeatTimeForComment(comment) -> number`
- `takeoverLimited(claim, self) -> boolean`
- `withoutClaimHeartbeat(body) -> string`
- `winningClaim(repository, key, github, authority, now = NaN, safety = false, observedIssue = null) -> Promise<object | null>`
- `setOwnClaimTime(name, { cwd, repository, claim, coordinatorId, machine, at }, ports = {}) -> Promise<string | null>`
- `refreshClaimHeartbeat({ cwd, repository, claim, coordinatorId, machine, at }, ports = {}) -> Promise<{ state: 'skipped' } | { state: 'refreshed', lastSeen: string }>`
- `createDependencyReadPorts({ cwd = '' } = {}, supplied = {}) -> { cwd, github, authority, clock, owners, ... }`

## Dependencies

- [GitHub calls](github-calls.prompt.md)
