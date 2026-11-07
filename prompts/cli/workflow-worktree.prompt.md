# Isolated issue workflow worktrees

Own `src/workflow-worktree.mjs`, exporting the module functions `allocateIssueWorktree`, `lookupIssueWorktree`, `releaseIssueClaim` and `lookupRepositoryParent`. Give each issue run an actual separate Git worktree without switching, resetting, stashing or otherwise changing the person's checkout. The helper owns durable allocation and exclusive issue claims; the runner owns its per-worktree journal and workflow stages. Preserve the literal interfaces and identity below. All claims and uncertain work persist: there is no cleanup, release, delete, retry or native/GitHub operation in this slice.

`allocateIssueWorktree({cwd,repository,issueNumber,runId,workflowName,baseRef},ports={execFile})` returns `{state,assignment,message}`. States are ready, conflict or recovery_required; assignment is null unless the actual owned worktree is verified. Conflict means an invalid/colliding request or an issue claimed by another run. Missing, incomplete, changed or unreadable durable/physical identity yields recovery_required without another allocation. A refusal before durable intent creation leaves no run allocation record or issue claim; distinguish it in the diagnostic from an unconfirmed allocation whose saved intent must be preserved.

`lookupIssueWorktree({cwd,runId},ports={execFile})` uses the same result envelope. It reads the common-repository run index from the original checkout or another checkout sharing that common repository. It performs only filesystem/Git reads; missing or uncertain identity remains recovery_required. Never repair metadata or repeat add while looking up or resuming an existing intent.

`releaseIssueClaim({cwd,runId,issueNumber},ports={execFile})` frees an issue for a new run after the runner cancelled the old run. It removes only the issue claim link `<commonDir>/pdd/worktree-assignments/issues/<N>.json`, and only when that claim names the same run and issue. It keeps the run record, the worktree and the branch. A missing claim is already released. It returns `{state:'released'|'conflict'|'recovery_required',message}` and never throws.

## Verified repository parent

Export `lookupRepositoryParent({cwd,repository,commonDir},ports={execFile})` as a read-only lookup returning
`{state:"ready",root,bare}` or `{state:"recovery_required",root:null,bare:null}`. Reuse the exact primary
registration/origin/common-directory validation that owns external allocation. `root` is Git's primary
registration R from the [layout table](#supported-git-layouts): the primary checkout for a normal clone, otherwise
the verified bare R. `bare` is true only for a bare R. Never substitute a linked caller, change Git/configuration,
or alter sourceRoot in an existing assignment.

## Supported Git layouts

pdd supports exactly the four layouts in the table below: a normal clone and its linked worktrees, a bare `project.git`, a bare repository in `P/.git`, and a bare `P/.bare` named by a `P/.git` file, each from any of its checkouts. It identifies the repository only from what Git reports for the invoking checkout: the canonical absolute common Git directory C (`rev-parse --path-format=absolute --git-common-dir`), Git's primary registration R (the first record of `worktree list --porcelain -z`), `core.bare` for a bare R, and the origin. Every origin that pdd reads must name the same GitHub repository. When these facts agree, allocation uses the same intent, claim and `git worktree add` in every layout. Run Git commands that need a work tree only in the invoking checkout or the run worktree. In a bare R, run only reads that need no work tree.

| Layout | R | C | Run worktrees folder |
|---|---|---|---|
| Normal clone, or a linked worktree of it | the primary checkout root | `R/.git` | `R.pdd-worktrees` |
| Bare `project.git`, with linked worktrees | `project.git` | R | `project.git.pdd-worktrees` |
| Bare repository stored in `P/.git`, with linked worktrees | P | `P/.git` | `P.pdd-worktrees` |
| Bare `P/.bare`, named by a file `P/.git` that holds `gitdir: ./.bare` | `P/.bare` | R | `P.pdd-worktrees` |

- R and the run worktrees folder must have no control character (the `plain` path rule). Check both before creating any directory or saving any record, so a refusal leaves nothing behind.
- A normal R must resolve, through Git run in R, to its own checkout root, the same C and the same origin.
- A bare R must be marked bare in the registration, and R must be C, or the folder that holds C when C is `R/.git`. Git run in R must report a bare repository whose Git directory and common directory are both C, `core.bare=true` and the same origin.
- A bare C is inside a project folder P when Git, run in P = the parent folder of C, reports C as its Git directory: P holds C as `P/.git`, or P has a `.git` file that names C. Then the run worktrees folder is `P.pdd-worktrees` beside P. Otherwise it is `<C name>.pdd-worktrees` beside C. A folder inside P would be inside Git's discovery area of P's `.git` and is hidden from the person; beside P, it is in the same place as for a normal clone.
- Lookup also accepts an assignment saved in `<R name>.pdd-worktrees` beside R, so a `.bare` run that an earlier version saved in `P/.bare.pdd-worktrees` stays valid. New allocations always use the table.

A separate Git directory (`git clone --separate-git-dir`) is refused, from its main checkout and from its linked checkouts. Git registers the Git directory itself as the primary worktree, not the main checkout, and Git records no path to the main checkout. So pdd can verify no primary checkout, and a run worktrees folder chosen from the caller would differ between checkouts of one repository. The refusal says that Git finds no work tree at R and names the next step: run the workflow from a normal clone or from a linked worktree of a bare repository.

Any other or inconsistent layout returns recovery_required before saving an allocation record or issue claim or attempting worktree add; the runner exits 1. The diagnostic starts with "Cannot establish repository or allocation metadata identity." When a layout fact disagrees, the next sentence names that fact and both values (for example the origin repositories of R and of the invoking checkout, or R and C), and one sentence gives the next step. The refusal never tells the person to change `core.bare`. It ends with the existing no-record/no-claim/no-confirmed-worktree diagnostic. Other metadata identity failures before durable intent creation keep the same first and last sentences. Preserve the existing unconfirmed-allocation diagnostic once intent is saved.

## Allocate once, then reconcile the original

```mermaid
flowchart TD
  R[Actual repository and common directory] --> E{Run already indexed?}
  E -->|Yes| L[Read-only reconciliation of same assignment]
  E -->|No| C{Issue already claimed?}
  C -->|Yes| X[Conflict]
  C -->|No| I[Durably save unique intent and exclusive issue claim]
  I -->|Collision or failure| U[Conflict or recovery required]
  I -->|Both fsynced| A[One worktree add at pinned SHA]
  A -->|Returned or uncertain| L
  L -->|Exact owned identity| Q[Ready]
  L -->|Absent or inconsistent| U
```

The exclusive key is the actual canonical Git common directory plus issue number, across workflow names. Run IDs are nonempty safe ASCII identifiers (letters/digits/dot/underscore/hyphen, maximum160); issue numbers are positive safe integers. Workflow names are safe identifiers, maximum80. Require a saved canonical owner/repo matching the checkout's actual GitHub origin, with ordinary HTTPS or Git SSH origin, no embedded credentials or alternate host. Repository comparison ignores case; retain the supplied canonical repository spelling. Resolve the actual source root and common directory through Git and canonical filesystem paths. Dirty user files are permitted and must remain byte/status unchanged.

A new allocation pins an existing local baseRef to its actual40hex commit SHA; never fetch. Persist the complete intended assignment before add, including an independently generated UUIDv4 worktree directory `<UUID>` in the run worktrees folder of the [layout table](#supported-git-layouts), unique safe branch `pdd/<safeName>-<issueNumber>-<uuidshort>`, and intended Git metadata directory `<commonDir>/worktrees/<UUID>`. Refuse preexisting paths, branch refs, symlinks/redirected metadata directories and unowned worktrees. The branch name derives from workflowName but issue ownership is independent of it. Every checkout of one repository uses the same run worktrees folder, independent of which checkout calls. Never change `core.bare` or choose an arbitrary linked checkout as the primary. The folder's full path must have no `.git` ancestor, so ordinary project loaders and test discovery do not treat source as Git metadata. Metadata and journals remain in their existing common-repository and per-worktree Git directories. Refuse a symlink, non-directory or redirected external allocation parent rather than writing through it. Use ordinary `git worktree add -b <branch> <worktreePath> <baseSha>` once. Never reuse the current worktree, switch branches, reset/stash, adopt another allocation or remove a failed add.

Durable run metadata and issue ownership must be exclusive across concurrent processes, not just promises in one process. The common-repository run index is a directory of immutable exclusively created per-run files, not a read/modify/replace shared JSON object; concurrent different-issue entries must both persist. Issue claims atomically link their run intent, serializing the contested issue name across all linked checkouts. The run index and claim precede add, so no post-add index registration is needed. File creation, file content and containing-directory entries are fsynced before add. A partial write, missing claim/index, interrupted add or lost reply never authorizes another add. Read the same saved path/branch afterward; actual matching state may prove ready even if the add reply was lost. Otherwise preserve uncertainty. No automatic overwrite, rollback, deletion, release or second generated identity is permitted for an existing run.

<details>
<summary>Assignment schema, identity checks and command port</summary>

A verified assignment has exactly `{version:1,runId,repository,issueNumber,workflowName,commonDir,sourceRoot,worktreePath,gitDir,branch,baseRef,baseSha}`. All paths are absolute canonical paths. Bind the run index and exclusive issue claim to the same durable intent. Validate their complete closed schema, exact UUID paths and branch, canonical repository, common-repository identity and original source root. The same version1 schema accepts both the new external path and the original exact `<commonDir>/pdd/worktrees/<UUID>` layout. Existing assignments always use their saved path and Git directory: lookup/resume neither creates an external parent nor moves, migrates, rebinds, repairs or deletes an old worktree/claim/journal. New allocations exclusively use the external layout. For external assignments verify the saved parent equals the current run worktrees folder of the layout, or the accepted earlier folder beside R; arbitrary outside paths are not adopted. Validate actual registered worktree path, ordinary `.git` file, actual Git directory/common directory/root, exact named branch, and actual HEAD descending from the pinned baseSha. New commits and dirty files inside an assigned worktree are allowed on later lookup; the pinned base is never moved to a newer ref. Unknown/multiple/mismatched Git registration refuses. Git's initializing lock can coexist with matching path, HEAD, branch and Git directory before checkout has completed; that state remains recovery_required. Neither lookup nor existing-run allocation unlocks, repairs, repeats add or deletes it. A completed original can recover ready, including later dirt/commits. Ordinary protective locks after checkout (with no reason or a noninitializing reason) do not by themselves invalidate a completed worktree. An unrelated existing worktree or directory is never adopted.

`ports.execFile(file,args,{cwd})` optionally replaces ordinary subprocess execution, returning/resolving `{stdout,stderr?,code?}`. Missing code is successful execFile-style completion; nonzero or rejection fails, including rejected numeric code zero. Normal nonzero process exit data can distinguish absent refs; operational rejection cannot become success. Production uses Node execFile, argv arrays, shell:false, normal inherited environment/cwd, no timeout and bounded output. No auth copies, private dependencies or bypass options. Capture public inputs before awaits. Use finite messages without raw subprocess output; outcome never implies workflow execution, publication or merge.

</details>

## Dependencies

- Load the complete [Prompting guide](../../docs/prompting-guide.md) for authoring/generation; it owns module contracts and preservation.
- Runtime: Node `child_process.execFile`, `crypto.randomUUID`, `fs/promises`, `fs.constants`, `path`, `util`, and installed normal Git. Filesystem metadata creation/reads/fsync are helper-owned; execFile is the sole injected port. Tests use disposable real local repositories and injected command failures, with no live GitHub/native actions.
