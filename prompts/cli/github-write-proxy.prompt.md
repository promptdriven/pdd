# Autopilot gh transport

Own `src/github-write-proxy.mjs` and the private gh executable it prepares.
Autopilot coordinator and worker chats use the same write guard as native pdd
calls. Manual shells are unchanged. Exports:

- `githubOriginalExecutable({env,fs})` returns the executable gh after removing
  private wrapper directories from PATH, or null. Native counters use it when
  already inside the private route, so adapters that ignore env cannot charge
  a nested wrapper twice.
- `githubWriteRunner(exec,{root,env,fs,now,identity,machine})` returns an async
  `(file,args,options)` runner. Other programs pass through. Resolve identity
  lazily once per runner from `gh api user` (login), or injected identity. An
  unavailable identity uses the conservative unknown bucket. Include the gh
  host in the bucket. Prefer the active gh account for the selected host from
  local `gh auth status --active --json hosts` (no token output); use user as a
  fallback. An injected identity can supply the canonical App identity.
  Reads need no reservation. Mutations use the shared write budget before any
  effect, and share cooldown outcomes. Do not store credentials.
- `githubWriteEnvironment({root,env,fs})` returns `{PATH,PDD_GITHUB_ROOT}`.
  Prepare a private executable named gh under root, bound to this package.
  The executable delegates to the original gh found after removing private
  wrapper directories from PATH. Forward stdin, stdout, stderr and exit status;
  no shell interpolation of arguments. Do not alter the person's gh or config.
  Marked `PDD_GITHUB_COUNTED=1` calls pass through without duplicate accounting.
- `githubWriteUsages({root,env,fs,now,machine})` returns all locally recorded
  host/identity budget statuses, or the unknown bucket when none exists.
- `githubWriteUsage({root,env,fs,now})` returns the last known identity's budget
  status, or the conservative unknown bucket, without network calls.
- `observeGithubWriteClaims({root,env,fs,now,machine,repository,claims})` records
  observed machines for subsequent reservations, without a GitHub request.

## Reduce content writes

For a REST issue-comment POST whose body contains
`<!-- pdd:autopilot:status -->`, list all comments, follow pagination, and find
one by this authenticated identity with that marker. Change it with PATCH;
when the bytes already match, return the existing comment without writing.
Otherwise POST one initial comment. Intercept only calls that request --include
and have no output transform flags; other output contracts pass through. Never edit another actor's comment. A
failed listing stops the effect. Unmarked comments, claims, dependency records,
checker verdicts and merge evidence keep their existing append behavior. An
uncertain POST is reconciled by a fresh listing on retry. Unknown identity may
not create a marked status comment because safe ownership is unavailable.

Serialize local status reconciliation across runners and processes for the
same canonical host, identity, repository and issue. Hold the lock from before
the fresh listing until the write result is known. A waiting caller lists again
after it acquires the lock. Lock contention may wait briefly (at most one second)
and then defer with `github_write_budget`; no request may bypass the lock.
Process death must not leave a permanent lock. Different issues and identities
have separate locks. This is local serialization; claim ownership and claim-era
checks still govern work across machines and are unchanged by comment reuse.

For labels-only `gh issue edit N --repo O/R --add-label A --remove-label B`,
read current labels and repository label IDs. Send one GraphQL request with
atomic addLabelsToLabelable and removeLabelsFromLabelable mutations for the
requested differences. Preserve concurrent unrelated label changes. Never
replace the whole label set from a stale read. Skip unchanged requests. A
missing label ID stops without a write. Preserve gh issue edit stdout: the
issue URL followed by a newline, for both changed and unchanged labels.
Preserve an explicit GitHub hostname, including --hostname=HOST, on every
derived read and write through gh arguments as well as environment. Absolute
API URLs select their canonical host for accounting. Keep the claim era's remove-then-add
operations separate; never combine a removal and addition of the same label.
Other gh commands pass through with conservative per-command reservations.
This transport is a usage guard for cooperative agents, not a security sandbox.

## Dependencies

[Shared write budget](github-writes.prompt.md) supplies reservation and cooldown
rules. [GitHub calls](github-calls.prompt.md) supplies classification, ledger and
reply parsing. Injected process, files, environment and clock supply external
operations. Native execution uses child_process and node:fs.
