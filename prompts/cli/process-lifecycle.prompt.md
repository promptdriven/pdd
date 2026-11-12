# Process lifecycle facts

Own `src/process-lifecycle.mjs`. This small native helper supplies process-table
facts to the live agent-job stop path and the old-engine retirement path. It makes
no scheduling, worktree, or repository ownership decision.

`parseProcessTable(text)` reads rows emitted as `pid ppid pgid rss lstart command` or
with a stable `@START` identity from Linux `/proc`. It returns
`{pid, ppid, pgid, rss, start, args}` rows only when every nonblank row is readable;
a malformed row makes the inventory unavailable.
`sameProcess(saved, current)` is true only when pid, start identity and command
text all match. A pid alone is never process identity.

`descendants(rows, roots)` returns the saved root rows and all rows below them by
parent pid, once each. Its non-enumerable `incomplete` flag is true when its bounded
walk cannot cover the tree. A malformed or incomplete inventory is never evidence that
a process has ended.

`terminateCaptured(captured, ports)` first re-reads the inventory. It sends TERM
only to captured rows that still have the same identity, waits through the supplied
grace period, and sends KILL only to survivors with that same identity. It returns
`{confirmed, stopped, killed, remaining}`. `confirmed` is false when either
inventory cannot be read or a captured process remains. A different process that
reused a pid is treated as gone and is never signalled. `ports` supplies `list`,
`signal`, `sleep`, `grace` and `poll`; native callers provide the platform process
table and signal ports.

## Dependencies

Node process inventory and signals are native effects. Callers own which processes
are eligible to capture and retain their records when cleanup is not confirmed.
