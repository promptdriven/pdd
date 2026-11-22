# Read and open the shared dependency graph

Own `src/autopilot/graph/cli.mjs` (re-exported via compatibility facade `src/issue-dependency-graph.mjs`). Export module functions
`readIssueGraph({cwd,repository,issue},ports)`,
`refreshIssueGraph({cwd,repository},ports)` and
`runIssueGraph({cwd,repository,issue,open},ports)`.
These read-only functions share the pure model with intake. They own a replaceable
private local cache, text formatting, requested viewer lifetime and local opening.
No path, including background refresh, calls AI, intake, GitHub writes, setup,
login, clone or workflow start. No silent agent/model choice exists here.

## Cache first, refresh behind it

Resolve the selected repository before cache lookup. With an explicit OWNER/REPO,
work outside a checkout and bind every authority lookup to that repository.
An omitted repository uses current checkout discovery; no checkout gives a finite
instruction to name a repository or open a chat in one. Never pick the first folder.
Cache keys use canonical repository identity. A cache from A cannot supply B.

`cache.read({repository})` returns JSON `{graph,lastSync}` or null. A cached read
returns it before waiting for network and calls `refresh.schedule({cwd,repository})`
to refresh in the background. This is an owned, requested loopback-view process or
bounded read job, never an installed service. `refreshIssueGraph` obtains current
canonical snapshot through the adapter, projects it with the model and atomically
writes a successful complete cache. On a partial/offline refresh with a cache, return
the cached graph and lastSync unchanged, including all nested graph fields; do not
project partial data over them or write the cache. Report sync offline and optional body-free, model-derived resource warnings
separately from the saved graph; expose these in the graph CLI report and ephemeral
viewer refresh data and status announcement. The cached first paint cannot know
the outcome of a later refresh; preserve unknown facts as unknown. With no cache, the initial read returns sync empty and shows `No saved graph` while background refresh starts; never claim current empty readiness. A completed refresh with a same-repository incomplete snapshot that the shared model can project returns that exact projection ephemerally, sync offline, empty lastSync and safe body-free model-derived warnings. Never write a partial projection. A failed read, wrong repository or unprojectable partial returns null/empty and any safe error. Background updates reach
the open viewer without reopening it, and preserve selection and viewport.

## Public read actions

For the text command only, when the initial read has no saved graph, do not schedule a duplicate background refresh: await one existing refresh and print its result. A same-repository incomplete projection is ephemeral, offline, and has empty lastSync and safe warnings; never cache it. A failed or unprojectable refresh prints the honest empty result. Cached text reads remain immediate, and readIssueGraph and viewer behavior are unchanged.

`pdd graph` prints selected scope, capture/last successful sync, review/dependency/
execution counts and useful issue links. Say `no recorded open blocker` unless the
model's full dependency handoff is current; even then do not promise account room
or automatic start. `pdd graph --issue 42` includes direct blockers, relevant chain,
plain reasons, evidence and unknown facts. Selection stays in the root repository;
cross-repo linked nodes retain their full identities. All graph forms accept the
graph-only `--repo OWNER/REPO`, including outside a checkout.

`pdd graph --open [--issue 42]` opens the bundled interactive viewer on the command's
local desktop. Keep generated HTML/model in a user-private cache. The requested
viewer may run a read-only loopback process for refresh. Bind only 127.0.0.1; validate
Host/Origin and serve only bundled assets and the selected graph. Do not expose
arbitrary files, command execution, credentials or mutation endpoints. Use no CDN.
Closing the owned viewer process ends that process, not a permanent service.
`viewer.open({repository,issue,graphJson})` returns `{opened,url}`. Its opened flag
means launcher invocation only, not proof that a person saw the screen. A failed
opener reports prepared-but-not-opened with an actionable local URL/command.

`host.read({})` identifies headless operation before any opener call. On a headless
VM, return summary and exactly `pdd graph --open --repo OWNER/REPO` (plus --issue N
when selected) as `handoff`. Never invoke a VM opener or claim it opened the laptop.
The laptop reads canonical GitHub data, not unpublished VM-only facts; label missing
VM facts honestly. No SSH bridge, tunnel, remote daemon or cloud receiver is added.

Every nonempty message ends with one newline. `runIssueGraph` returns exitCode 0
for prepared read/handoff, nonzero for finite failure, plus message and read facts.
Read functions return `{graph,sync,lastSync}`; the initial read has null graph when no graph is saved, while a completed refresh may return an uncached partial projection as described above.
For --open, serialize that null unchanged to viewer.open; the bundled renderer
accepts it with sync empty and returns its honest no-cache state.
Sync is refreshing, current, offline or empty. No cache freshness label confers
review authority; projection still follows the model.

## Dependencies

- [Pure model](issue-dependencies.prompt.md): required for authoring, generation,
  runtime and verification; owns the only graph/readiness rules (`src/autopilot/graph/dag.mjs`).
- [GitHub adapter](issue-dependencies-github.prompt.md): required for generation,
  runtime and verification; default `snapshots.read` binds readDependencySnapshot.
- [Autopilot issue claims](autopilot-claims.prompt.md): required for read-only claim ports (`createDependencyReadPorts`).
- [Viewer](issue-dependency-graph-view.prompt.md): generation/verification context
  for bundled rendering (`src/autopilot/graph/view.mjs`); no read or mutation policy is delegated to the browser.
- Layer-0 `src/shared/github-repo.mjs`: default local repository identity discovery (`resolveRepository`).
