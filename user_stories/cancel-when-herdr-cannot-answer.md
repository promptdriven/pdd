# Cancel or replace when Herdr cannot answer

I can free my issue after its chat tab closes or Herdr stops, with the machine checked before another run starts.

Issues: https://github.com/promptdriven/pdd/issues/2445 and https://github.com/promptdriven/pdd/issues/2446

## Acceptance criteria

1. After I confirm cancel or replace when the run tab is closed or Herdr is down, a complete machine inspection finding no live process inside its worktree lets the request proceed.
2. A successful cancellation keeps all old work and PRs, saves cancelled state before releasing its claim, and replacement then starts a distinct run with its own worktree and branch.
3. Any live process inside the worktree makes cancel and replace refuse with its PID, observed command, how to stop it and the exact retry command, while the saved run and claim stay and no replacement starts.
4. An incomplete machine inspection makes cancel and replace refuse with the actual cause and recovery advice, without saving cancelled state, releasing the claim or starting a replacement.
5. The fallback counts an ordinary command, detached writer, idle shell, calling process and another user's process inside the worktree; it neither exempts them nor stops them automatically, and a sibling directory is outside.
6. An unconfirmed failed start without a saved pane can be cancelled or replaced after a complete native inspection proves the worktree has no live process; an old PID or an unreadable or changed identity never proves absence.

## Rules to check

Confirmation precedes inspection; positive stopped/absence evidence precedes durable cancellation, matching claim release and replacement startup. A live process or unknown inspection forbids cancellation writes, claim release, tab closure and replacement. Preserve every old worktree, branch, journal, artifact, decision and PR. Native fallback counts every live process in the physical worktree or its descendant directories, across users; a terminal inside it must leave that directory and retry from outside. Current-user-only or partially visible inspection cannot prove absence across users. Do not kill an unknown process automatically or treat PID reuse as safe termination.

The cases are independent owner unit checks. Code verification must replay each unchanged approved case at its named public boundary with the same declared resource semantics as the Runtime: runner cases intentionally receive synthetic stop receipts, while direct stop-owner cases execute real `stopChats` with synthetic Herdr/native observations. Do not substitute native effects for a runner unit's synthetic receipt or demand effects outside that unit's declared fixture. These replays do not prove that the runner obtains its receipt from native inspection or forwards its diagnostics. The write-input ledger does not prove status/index/C3 durability.

Separately, code verification must exercise the real runner calling real `stopChats`, with injected native observations and real temporary records and claims, to verify effect order, diagnostic propagation and retained files/PRs. Separate disposable-process checks must cover actual OS visibility, stale/reused PID, unreadable cwd, malformed/partial inspection, process birth and command identity, caller and idle-shell blockers, no automatic signals, and exact retry advice. A simulated empty inventory is not native machine proof or a guarantee against unrelated processes starting after observation.
