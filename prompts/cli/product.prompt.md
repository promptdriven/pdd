# Product plans and progress

Own the Layer-1 core product modules under `src/core/product/` (`markdown-utils.mjs`, `documents.mjs`, `plan-audit.mjs`, `pr-matching.mjs`, `github-state.mjs`, `progress.mjs`, `product-cli.mjs`) together with thin compatibility facades at `src/product.mjs` and `src/product-documents.mjs`. Read a product plan, audit prompt inventory and boundary wiring, compute topological waves and Story progress, and prepare scoped GitHub issues with workflow-free `/pdd` handoff. Product commands never call the PDD interpreter, import legacy `src/workflow-*.mjs` modules, approve gates, merge, or commit evidence.

Export `parseProductDocuments({ mapText, planText = '' })`, `parseProductWorldWriters({ worldText })`, `computeProductWaves(runs)`, `auditProductPlan({ mapText, planText, promptFiles })`, `resolveProductRepository({ cwd }, ports)`, `recordedRuntimeLines(text)`, `sourceFingerprint(root)`, `storyEvidence(run, options)`, `readProduct({ cwd }, ports)`, `productStatus({ cwd, through, base }, ports)`, `productNext({ cwd, through, base }, ports)`, `productStart({ cwd, run, noRun = false, agent = 'codex', through, base, packageRoot }, ports)` and `runProduct({ command, run, noRun, agent, through, base, json, cwd, packageRoot }, ports)`. `runProduct` returns `{ exitCode, message }` for the CLI, catches finite input/dependency failures, and never retries a mutation automatically.

## Read the durable plan (`src/core/product/documents.mjs`, `markdown-utils.mjs`, `plan-audit.mjs`)

For these functions, `cwd` is the explicit product repository root (or the logical root supplied by an injected `readFile` callback). The default native reader opens only regular in-root files without following symlinks (`O_NOFOLLOW`), enforces a bounded size (`2 MiB`), and refuses symlinked map/plan files with `invalid-product`. Missing `product/plan.md` is allowed for the `small` single-part path.

Parse Markdown tables by heading and column name, trimming cells, handling escaped pipes (`\|`), ignoring separator rows, unwrapping single-backtick-wrapped cell tokens while keeping inline multi-backtick prose intact, and preserving row order. Split comma lists (`-` or empty is `[]`). Ignore unrelated headings.

- Map heading supplies `name` without `: map`; `Size:` supplies `small`, `medium`, or `large`.
- Optional `product/plan.md` preamble lines (before the first `## ` heading):
  - `Through: prompt-pr|code`: default completion target (reject duplicate or invalid values with `invalid-product`).
  - `Base: <branch>`: default integration base branch (reject duplicates with `invalid-product`).
  - `Issue: #<N>`: optional parent product issue number for `Part of #N (product).`.
- Required tables: `Parts`, `Stories` (`CORE` vs `LATER`), `Journeys`, `Questions` (return unanswered IDs), `Runs`, and `Boundaries`.
- Optional sections:
  - `product/map.md` `## Rules to check`: structured table(s) (`Id`, `Owner`, `Rule`, `Verified By`) or bullet/prose fallback, exposed as `product.rulesToCheck`.
  - `product/plan.md` `## Runs` shared surfaces: optional `Shared surfaces` / `Updates` / `Also updates` column, secondary comma parts in `Part`, or per-run `Shared surfaces (RUN): ...` / `### RUN` lines; deduplicated, validated against `## Parts`, exposed as `run.sharedSurfaces`.
  - `product/plan.md` `## Prompts`: table, bullet, or `### <part>` prompt inventory, exposed as `product.prompts`. Require a non-empty filename stem containing at least one alphanumeric character before `.prompt.md` so bare prose tokens like `` `.prompt.md` `` or `` `*.prompt.md` `` are never extracted as declared prompts.
  - `product/plan.md` `## Boundaries` operations: dotted `<part>/<prompt>.<op>` or `<prompt>.<op>` tokens in `What crosses` / `Operations` (skipping file extensions, versions, and `Never crosses` blocks).
- `computeProductWaves(runs)` groups runs into deterministic topological waves (`Wave 1`, `Wave 2`, ...), ignoring the special `plan PR` need and appending any cyclic tail with `cyclic: true`.
- `parseProductWorldWriters({ worldText })` selects the single non-fenced table containing `Key` and `Writer`, rejects duplicate tables or conflicting writers (`world-writer-conflict`), and returns ordered `{ key, writer }` records.
- `auditProductPlan({ mapText, planText, promptFiles })` deterministically checks `## Prompts` inventory drift (`product-prompt-inventory-drift`) under tracked part folders (skipping `examples/` unless tracked) and checks `## Boundaries` dotted operations (`product-boundary-unwired`) using strictly linear scans.

Reject missing maps, missing required columns, duplicate part/Story/journey/run/rule IDs, or unknown part/Story/need references with `invalid-product` naming the file and offending token. Never reject an oversized run (>12 Stories emits an advisory warning).

## GitHub state, PR matching, and progress (`src/core/product/github-state.mjs`, `pr-matching.mjs`, `progress.mjs`)

Resolve repository identity from `git remote get-url origin` (via Layer-0 `src/shared/github-repo.mjs`) and `gh repo view`, counting native `gh` calls via `nativeGithubCounter`.

- **Trusted issue lookup:** Read version-2 repository-scoped state under `<git-common-dir>/pdd/products/<sha256(repo)>.json` (migrating version-1 folder-keyed files once, using an observed exclusive `.lock` with dead-PID `ESRCH` and 30s stale recovery that never unlinks a successor's lock). Validate saved bindings directly via `issueByNumber`; isolate bad hints to their own run (`unverified` + repair action). Confirm 404/foreign/untrusted hints drop the binding; transient failures retain it and fail closed on `start`. Search unresolved runs with one bounded paginated query (`per_page <= 10`) for `<!-- pdd-product: run=`, caching complete snapshots for `60,000 ms`, refreshing once before creation from a cached negative. Trust only `OWNER`/`MEMBER`/`COLLABORATOR` or the authenticated `currentActor` login (case-insensitive). Prefer an issue with a matching local run record under `<git-common-dir>/pdd/runs/*/status.json`, then oldest `created_at`, then lowest issue number.
- **Same-repo PR eligibility & completion:** Read bounded timeline pages (`cross-referenced` events only) and inspect each PR's metadata. Reject forks, foreign head owners/repositories, and mismatched canonical URLs. Accept PRs carrying an unambiguous own-run marker (`<!-- pdd-product: run=<RUN> -->` or `<!-- pdd-product: run=<RUN> stage=prompt-pr|prompt|code -->`), matching a saved local branch, or carrying a GitHub closing reference (`Closes/Fixes/Resolves #<issue>` outside code spans/fences) without a foreign `pdd-product:` marker.
- **Completion target:** Resolve target as explicit `--through` ?? `product.through` ?? `'code'`.
  - Under `code`, a merged eligible PR completes the run when matched by canonical `<!-- pdd-product: run=<RUN> stage=code -->`, a normal closing reference (`Closes #<issue>`) without a prompt-only stage marker, read-only legacy `<!-- pdd-workflow:<id>:code -->`, or local `stage: 'code'` + matching `headRefName`. Prose alone never completes a run.
  - Under `prompt-pr`, a merged eligible prompt PR (`stage=prompt-pr|prompt`, legacy `:prompt-pr|:prompt`, or local `prompt-pr`/`prompt` stage + matching branch) or any merged `code` PR completes the run.
- **Story evidence & base-source comparison:** Combine local `storyEvidence` (matching `git-content-v1` via Layer-0 `gitFiles` or `runtime-capture-v1` via `runtime-seam.mjs`), `savedStoryEvidence` from `createSavedStoryEvidenceReader()` (one reader per invocation), and `recordedRuntimeLines` from the most recently updated eligible PR with named `Prompt tests` / `Runtime check` lines (reading only the top block / details block, never agent notes). For merged runs, compare local evidence against the current base branch view (`openBaseSource` / `closeBaseSource` in `finally`), preferring a checked-out worktree then local ref then `origin/<base>` without fetching. Pin the integration base commit SHA (`baseSha`) when a real Git checkout is present.
- **Closed-unbuilt recovery:** When a trusted issue is `CLOSED` while the run is not merged, has no active local run, has no open or merged same-repo PR, has incomplete Story passes, and lacks its planned Story files on `cwd` or `baseBranch`, report `issue closed (PASS of TOTAL pass)` and treat the run as unstarted so `productStart` can reopen it.
- **Cycle diagnostics:** Detect `Needs` cycles (excluding `plan PR`) and surface a closed path warning (`Needs form a cycle: A → B → A`) without blocking unrelated ready runs or explicit starts.

## Start and CLI formatting (`src/core/product/product-cli.mjs`)

- Validate `--through` (`prompt-pr` | `code`), `--base` (strict Git branch ref-format rules), `--agent` (built-ins `codex`/`claude`/`gemini`/`agy` or `~/.config/pdd/agents.json` via Layer-0 `src/agent-config.mjs`, refusing shell-reserved env names), and run name before any GitHub read or write.
- Issue body includes optional `Part of #N (product).`, plan path, run, slice, Story IDs/texts, leading Story-ID filename guidance, `Folder`, `Contracts` (covering primary part + `sharedSurfaces` + `contracts/world.md`, omitted for `small` products), `Shared surfaces to update`, matching `## Rules to check`, and exactly one `<!-- pdd-product: run=<RUN> -->`.
- **Single-part vs cross-part journey integration guidance:** Emit `Other parts are fakes from their contracts. Do not change contracts/ in this run.` ONLY for single-part runs (`planned.part !== 'all'`) with contracts. For `planned.part === 'all'` (journey/integration runs), emit real unmocked cross-part integration guidance requiring `pdd sim --product` and no fake parts while retaining `Do not change contracts/ in this run.` when contracts apply.
- Shorten overlong titles to fit GitHub's 256 Unicode code-point limit while keeping every Story in the body and emitting a warning.
- After persisting the issue binding (or reopening a closed-unbuilt issue):
  - `--noRun` returns `{ exitCode: 0, issue, created, started: false }`.
  - If an explicit `startRun` callback was injected via `ports`, invoke it once with `{ name: 'feature', issue, agent, cwd, ... }`.
  - Otherwise (default workflow-free mode), return `{ exitCode: 0, issue, created, started: false, handoff: '/pdd' }` with a concise message showing wave, base branch/SHA, and `/pdd` / `pdd autopilot start --issue N` next step.
- `runProduct` prints waves (`Wave 1: ...`), ready runs, waiting needs, status tables, optional `Base: <branch> (<sha7>)`, local comparison base hints, and all warnings; `--json` emits structured JSON for `status`.

## Dependencies

- Layer-0 `src/shared/git-context.mjs`, `src/shared/github-repo.mjs`, `src/shared/safe-read.mjs`, `src/github-calls.mjs`, `src/agent-config.mjs`.
- Layer-1 `src/prompt-tests-words.mjs`, `src/runtime-seam.mjs` (read-only `savedStoryEvidence` and `captureSource`).
- [Product guide](../../skills/pdd/references/product.md) and [command catalog](command-catalog.prompt.md).
