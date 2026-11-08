# Shared GitHub write budget

Own `src/github-writes.mjs`. Count and admit Autopilot content writes across
repositories and processes on one machine, per GitHub host and authenticated
identity. Preserve the existing read budget and workflow authority. This is a
local guard, not a distributed lock or permission to write.

## Public boundary

- `githubWriteCost(args, options={})` returns a conservative integer count of
  content requests. REST GET/HEAD/OPTIONS and GraphQL queries cost zero. REST
  mutations cost one. GraphQL documents containing any mutation reserve conservatively for all
  mutation fields, even when the document starts with a query. Ambiguous
  documents are never classified as free reads. Unparseable input costs one.
  Accept gh compact and equals method/field option spellings. Known gh read commands
  cost zero. High-level gh writes reserve conservative request counts, including
  each label operation; unknown commands reserve one. Never use the purpose tag
  to decide whether an operation writes. A POST GraphQL query is a read.
- `githubWriteBudget({root, identity, host='github.com', fs, now, machine})`
  returns `{reserve(count), observe(outcome), observeClaims(repository,claims),
  usage()}`. `fs` is the synchronous file port, `now` a millisecond clock;
  native defaults use node:fs, Date.now and hostname. Identity is a login or App
  identity supplied by the caller; case is ignored. Unknown identities use one
  shared conservative bucket. No token is stored or printed.
- `reserve(count)` returns the current usage after reserving before dispatch.
  Zero makes no reservation. Failed and uncertain attempts consume their full
  reservation. Concurrent processes serialize read/check/save with an atomic
  host-wide PID lock. An unknown identity counts reservations from every
known identity on that host; a known identity also counts unknown reservations.
Both admission paths use the same lock so an identity lookup failure cannot
create a fresh allowance. A dead owner is reclaimable; a live or unreadable lock defers.
  Unreadable state and save failures stop writes. Never drop events on a race.
- `usage()` returns `{identity,host,minute,hour,minuteLimit,hourLimit,machines,
  retryAt,state}`, plus `unavailable:true` when state cannot be read. That
  status reports usage as unavailable rather than claiming zero use. Counts use rolling windows `now-window < at <= now`.
  Defaults are 60/minute and 350/hour, leaving 20/minute and 150/hour for people
  against the stated 80/500 limits. Divide both defaults by the active machine
  count, rounding down, with a minimum of one. Each distinct active machine in
  observed claims counts, plus this machine. Keep observations from all local
  repositories. A claim must be active with a server-derived lastSeen less
  than four hours old. Expired observations leave the divisor. Count all seen
  machines conservatively when their GitHub identity is unknown. These are
  observations, not knowledge of machines on unseen repositories.
- At a full window or a shared cooldown, `reserve` throws an Error with
  `code='github_write_budget'`, millisecond `retryAt`, and `usage`. No request
  runs. `retryAt` is the first expiry that admits the whole reservation, or the
  shared cooldown if later. Requests larger than a window cannot run. A live
  lock or storage fault also defers safely with this code. Do not sleep inside
  admission. The caller keeps progress and retries later.
- `observe(outcome)` shares a 403/429 cooldown when Retry-After is present, or a
  secondary/abuse limit is reported. Use Retry-After seconds or HTTP date; absent
  valid guidance, wait at least one minute. Preserve the original outcome and
  never retry an uncertain write automatically.
- `githubWriteStatus(usage)` returns one plain status line with identity, rolling
  minute/hour counts, limits, machine count, state, and retry time when deferred.

## Dependencies

The injected file port owns local persistence and locking. The process adapter
supplies identity and actual GitHub outcomes. The clock supplies milliseconds.
The call counter is a consumer, not required context. No network or model call is made by this module.
