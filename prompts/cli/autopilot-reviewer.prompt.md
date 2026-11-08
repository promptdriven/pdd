# Shared repository reviewer

Own `src/autopilot-reviewer.mjs`. A repository has one live reviewer lease on
GitHub. It permits sorting, grouping and dependency analysis only. Existing issue
claims remain the shared lock for issue work and merges. Preserve their winner,
heartbeat, takeover and merge policies. No new service or user setting is needed.

Export module functions `reviewerLease({repository,identity,acquire},ports)`,
`reviewerIdentity({cwd,repository},ports)`, `repositoryMachines({lease,claims},now)`
and `repositoryMachineLines(view)`. Outside calls use injected `execFile` (the
ordinary gh process contract), `now` and `uuid` ports. Identity is
`{machine,coordinatorId,login}`; login is the authenticated GitHub account, never
an ownership key. Native identity comes from the saved repository launcher state;
no state means null and preserves manual dependency commands. A carried
PDD_AUTOPILOT_CONTEXT must resolve to a matching saved coordinator, including
when a command runs from an issue worktree; missing carried custody is unknown. A malformed existing
state or failed identity observation must not grant manual authority.

## Lease protocol

Store `.pdd-reviewer.json` on branch `pdd/autopilot-reviewer`, never on the default
or issue branch. Bootstrap the branch from the repository default head only when
absent. Competing branch creation is harmless. Read the file live, without a
saved snapshot or ETag. The JSON lease has `repository` (lowercase owner/name),
`machine`, `coordinatorId`, `login`, `generation` (opaque unique acquisition id),
`lastSeen` (UTC ISO time) and `expiresAt` (UTC ISO time). The lifetime is 90 minutes.
Only the exact machine and coordinator pair may renew a live lease. Renew only
when lastSeen is at least 30 minutes old; preserve generation. An expired lease
cannot be renewed: any contender, including its old owner, must acquire a fresh
generation. Equality at expiresAt means expired. Recheck the injected clock after each
lease response; a slow read or write must not return expired authority. A future lastSeen, malformed
record, unavailable clock, permission failure or unknown read grants no authority.

Acquire or renew with the Contents API, supplying the exact current blob SHA;
create supplies no SHA. A conflict never grants ownership. Reread the winner once
and do not loop. A successful update with a returned content SHA confirms the written lease
without another read. An uncertain write result grants no authority for that call.
Each effect checks a current unexpired exact generation; stale requests remain
pending after takeover even if the same machine later acquires again. Local
clocks must be synchronized; the lease does not fence an already in-flight GitHub
write atomically with an expiry. Never claim that passing fakes proves that case.

Return `{state,held,lease}`: state is `held`, `other`, `absent` or `unknown`, held
is Boolean, lease is the validated stored lease or null. Read-only calls
(`acquire:false`, the default) never bootstrap, write or renew. A read with no
identity can observe the lease but cannot hold it. A missing file is absent;
an invalid record is unknown. Do not expose token or raw process errors.

## Repository view

`repositoryMachines` returns `{reviewer,machines,sharedLogins}`. reviewer is the
live lease or null. machines is ordered by machine then coordinator id; each row
has `machine`, `coordinatorId`, `login`, `issues` (sorted unique issue URLs),
`reviewer` (Boolean), and `lastSeen` (latest known claim or lease UTC time, or an
empty string). Include live claims and the live lease only. Keep separate
coordinators on the same machine separate. Unknown identities are not invented.
sharedLogins lists sorted case-insensitive accounts seen on at least two distinct
coordinators. The view must not infer ownership from a shared account.
`repositoryMachineLines` formats a reviewer line and one machine/coordinator line
with its issue numbers, login and last seen time. No exact English sentence is an
API guarantee.

## Dependencies

- [GitHub call ledger](github-calls.prompt.md): required native context for counted
  execFile calls. Callers supply their existing counted process port.
- [Workflow repository](workflow-runs.prompt.md): required native context for
  resolving a checkout's Git common directory before reading its launcher state.
