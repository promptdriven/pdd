# Repository and run layout in Herdr

Own `src/workflow-herdr-layout.mjs`: shared session naming, owned repository and run workspace allocation, and run workspace closure. Export `PDD_HERDR_SESSION` (`pdd`), `withHerdrLayoutLock(action, ports)`, `openHerdrRunLayout(input, ports)` and `closeHerdrRunLayout(input, ports)`. This is behavioral refinement of the authorized 0.1.0 layout: stage acceptance and Git worktree allocation remain with their existing owners.

All new runs use the explicit session `pdd`, never the person's `default` or a per-run server. The [area chat owner](workflow-chat.prompt.md) owns compatible-server startup. Serialize session bootstrap and layout mutations across processes in the same HOME; unrelated repositories may have concurrent active agents. A live owner remains exclusive. Recover a lock only when its recorded process is proved absent; a normal Ctrl+C must not block all later runs. When a live owner holds the lock, fail at once with `herdr_layout_busy`; never wait or poll. Serialize owner inspection/replacement in a synchronous claim section; malformed or interrupted claims fail finitely and require inspection.

Inputs identify the run UUID, canonical repository (`owner/repo`) verified against the Git origin remote by the worktree assignment owner, source checkout, common Git directory, assigned run cwd, issue number, workflow and stage. Ports supply a Herdr command function already bound to `pdd`, an awaited checkpoint, and optionally a state directory (normally the person's local PDD state). No credential/configuration reads or tool-version checks belong here.

## Repository parent and confirmed pre-agent recovery

Resolve input sourceRoot through the worktree owner's read-only verified repository-parent lookup before
allocating. Use that root for Herdr's repository workspace, including a verified bare primary; retain the
actual invoking sourceRoot separately from the assigned run cwd. Never treat a linked caller as a parent.
Pass the optional execFile port through to that identity lookup; no bypass or independently guessed path.

A structured `linked_worktree_source` rejection of worktree open is confirmed before any child workspace or
native launch. Persist that run as refused with the code, retaining its original cwd/runId and repository binding.
On a later explicit open, retry only this refused action after inventory shows no workspace for that cwd.
Other failures/lost replies retain uncertain intent and must never authorize another allocation.

For an affected saved run, optional input preAgentRefusal=`linked_worktree_source` conveys the runner's
confirmed original pre-agent refusal. A legacy intent without a returned workspace/root identity can become
refused only with this evidence and no inventory workspace at its cwd.
Always reassert the refused run's saved common directory, assigned cwd and issue/workflow label before
any recovery persistence or mutation; a refusal does not authorize rebinding those identities.
For a legacy repository workspace created at the linked caller, require same saved common directory and sourceRoot, no other run sharing it,
and this one confirmed refused run. Archive the old repository entry, preserve its workspace untouched,
create a verified parent workspace under an unused label, and rebind only that refused run to it. Never
adopt, close or rename the old workspace. Unknown child allocation or an unrelated identity blocks recovery.
A further confirmed refusal stays retryable. Before retrying, durably mark the new attempt; a lost retry reply
is uncertain even when an earlier startup warning records a refusal. Never reuse that warning to retry again.
Pin the parent workspace root tab/pane/terminal returned at creation. If parent inventory lacks Git metadata,
reuse only with those same root identities and exact parent cwd, one tab and one pane; conflicting metadata refuses.
Apply that same repository-parent identity rule to reuse, name qualification and idle cleanup. Parent Git metadata
must identify a non-linked parent; absent metadata cannot justify accepting changed root identities.

## Allocation and identity

Keep a durable, private ownership registry. Select a repository workspace by both canonical repository identity and verified common Git directory; independent clones of the same repository get separate owned workspaces. Search all matching entries, including hand-edited registries with repeated repository keys, rather than selecting the first repository-name match. More than one entry for the same repository and common directory is uncertain and must refuse before mutation. A saved run keeps its original repository workspace binding; never rebind it to a peer checkout.

Choose a new repository workspace's unused short repo name first, even when another checkout's registry entry remains after its workspace closed. If that label is occupied in session `pdd`, use `owner/repo` from the verified origin, not the checkout folder name (HD2). With a peer checkout of the same repository, an occupied `owner/repo` falls back to `owner/repo@` plus the first 12 lowercase SHA-256 hex characters of the canonical common Git directory. Refuse an occupied final label. Starting another clone of the same repository does not rename its peers.

When a different repository has the same short name, qualify the existing owned repository workspaces too. Verify each workspace's ownership before renaming it. Use its own `owner/repo` when free, otherwise its own common-directory-qualified label, even when an unrelated workspace holds `owner/repo`. Preserve that holder and any peer already using its selected qualified label; refuse if the final label is occupied by another workspace. Each choice must reflect confirmed earlier renames in this allocation. Never rename or adopt a workspace outside the ownership registry. This different-repository qualification may rename an owned clone's short label; same-repository clone creation alone must preserve peer labels.

Each run gets one `worktree open --workspace <repo-id> --path <assigned-cwd> --label '<repo name>#<issue> <workflow>' --no-focus` workspace (the repository name keeps runs with the same issue number in two repositories apart; a saved run with the older label `#<issue> <workflow>` still matches). PDD's Git worktree already exists; never ask Herdr to create or remove the Git checkout. Every area chat gets a fresh tab inside that workspace, named after its area (input `stageId`). Preserve the worktree's initial shell tab so closing a stage tab cannot close the run workspace. Return actual `repoWorkspaceId`, `workspaceId`, `tabId`, `paneId`, and `terminalId`; never predict opaque IDs.

Checkpoint and persist allocation intent before mutations and returned ownership before proceeding. Lost replies or interrupted intents remain uncertain; do not repeat allocation or adopt unrelated workspaces by label. Validate actual owned inventory before reuse: require worktree checkout path, common Git directory and linked-worktree kind; pin the returned initial root tab, pane and terminal identities and reassert them through pane list. Require exactly the initial tab and its one original pane before run closure; an added or unknown tab or split pane prevents closure. Registry labels describe ownership but do not authorize closing a workspace with changed checkout identity. A closed run cannot silently reopen.

## Cleanup

The caller invokes run cleanup after it closed the run's area tabs (for example on cancel). Close exactly the saved run workspace using `workspace close`, never `worktree remove` or group close. Require the documented close acknowledgement and a valid inventory proving absence. Preserve repository workspaces, peer runs, unrelated workspaces and the Git checkout. Uncertain close must not be blindly repeated. Git removal, permitted only after merge or cancellation, remains the Git-worktree owner's responsibility.

Export `closeHerdrRepoLayoutIfIdle({repository, commonDir}, ports)`. Select the repository entry by both repository identity and commonDir, refusing ambiguous entries before mutation. After the last open run of that checkout is closed, close that checkout's own repository workspace too, so no empty shell workspace stays after cancel. Close it only when no saved run of it is open, its identity still matches, and it holds exactly its one tab and one pane (a person may use more). Remove the repository from the registry, so a later run opens a new repository workspace. Return true when it closed or was already gone, false when it stays.

## Dependencies

Load [Prompting guide](../../docs/prompting-guide.md) for authoring and generation. The installed Herdr CLI's public workspace/worktree/tab commands and JSON identities supply runtime transport, with 0.9.1 as the capability baseline and no version pin. The [worktree assignment owner](workflow-worktree.prompt.md) supplies origin-verified repository identity and canonical checkout paths; load its contract for generation and verification. Node filesystem primitives provide durable local ownership and cross-process serialization. The area chat owner supplies a session-bound command function; it keeps native-agent identity and prompt delivery.
