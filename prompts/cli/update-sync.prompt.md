# Changed-file ownership map

Own `src/core/changed-map.mjs` and the read-only compatibility wrapper `src/update-sync.mjs`. Export `analyzeChangedMap`, `extractDiffSummary`, `formatChangedMapText`, and `formatChangedMapJson` from `src/core/changed-map.mjs`, and `runUpdate`, `analyzeUpdate`, `extractDiffSummary`, `formatUpdateText`, and `formatUpdateJson` from `src/update-sync.mjs`.

Map touched repository files (explicit paths, a Git `--from RANGE`, `--branch`, `--all`, or working-tree changes) to their owning `.prompt.md` contracts through [File owner lookup](file-owner.prompt.md), summarize unified diff line counts and changed top-level symbols across JS/TS, Python, Go, and Rust, report genuine unowned product source files without noisy non-product clutter, and perform instant offline structural checks with zero file writes and zero AI or network calls.

## Domain decisions

- **Strictly read-only offline core.** Inspect local Git metadata and working-tree files only. Spawn zero AI subprocesses, make zero network or interpreter calls, and never write `.pdd/sync/` sidecars, `.prompt.md` files, source headers, or `pdd-bindings.json`.
- **Scoped target selection (mutually exclusive modes).**
  - Explicit `files`: scope strictly to those repository-relative regular files. Reject combining `files` with `--from`, `--branch`, or `--all` (`exit 2`). Detect untracked explicit files so newly added files report full line additions and symbols.
  - Range `from`: accept `<base>..<head>` or `<base>` (normalized to `<base>..HEAD`). Reject empty strings, length `> 256`, whitespace, ASCII control characters, `...`, multiple `..`, or any segment starting with `-` (`exit 2`) before calling Git. Resolve touched paths with `--literal-pathspecs`, `core.quotepath=false`, and `--no-ext-diff`.
  - Branch mode (`branch: true` / `--branch`): resolve the local default base ref (`origin/HEAD`, `origin/main`, `origin/master`, `main`, or `master`), compute `merge-base(defaultBranch, HEAD)..HEAD` merged with working-tree changes, and compute unified diff stats against that merge base.
  - Full-repo mode (`all: true` / `--all`): inspect all Git-tracked non-secret regular files merged with working-tree status (distinguishing unmodified tracked entries from working-tree changes) so every prompt-owned module is audited without silent skips.
  - Default working-tree mode: resolve modified, staged, renamed, deleted, and untracked non-ignored files from `git diff --name-status -z -M HEAD` merged with `git status --porcelain=v1 -z -uall` (falling back cleanly on unborn branches), ignoring `.pdd/**`. When working-tree has 0 touched files on a clean committed branch ahead of the default branch (`merge-base(defaultBranch, HEAD) !== HEAD`), automatically widen to `branch` (`scope.widened_from = "working-tree"`).
  - Outside a Git repository, exit `2`. Empty scope exits `0` with empty arrays and `ok: true`.
- **Security, secret isolation, binary probing, and fail-closed bindings.**
  - Reject paths starting with `-`, containing control characters or `\`, using `..` traversal, resolving outside the canonical Git root, or traversing symlinks (`lstat` + `O_NOFOLLOW`, `exit 2`).
  - Reject secret-looking paths (`isSecretPath` or `.env*`, `credentials*`, `.aws-credentials`) before reading them (`exit 2`); in `--all` mode skip non-canonical/secret paths safely, fail closed (`exit 2`) if a bound module in `pdd-bindings.json` is a symlink or non-regular entry, and record eligible unowned symlinks/non-regular entries as `symlink (skipped)` / `non-regular entry (skipped)` while filtering out non-product paths.
  - Fail closed (`exit 2`) if `pdd-bindings.json` exists and is a symlink, unreadable, exceeds 64 KiB, is invalid JSON, or fails the `pdd.bindings.v1` schema. Also refuse symlinked `pdd-workspace.json` or `pdd.json` (`exit 2`).
  - Probe binary content with a bounded 8 KiB prefix read: reject explicit or owned binary files (`exit 2`) and report eligible unowned binary files under `unowned` with reason `binary file (skipped)`. Bound full text reads to 10 MiB.
- **Owner mapping, prompt touches, and structural status classification.**
  - Delegate ownership lookup to `findOwners` (`pdd-bindings.json` and `Prompt:` / `Generated from` headers, treating both identically for comment-less languages).
  - In `--all` scope, and whenever `pdd-bindings.json` is touched in implicit scopes (`working-tree`, `from`, `branch`), audit every `pdd-bindings.json` module entry (failing closed with `exit 2` on non-canonical/secret/symlink/non-regular targets, and adding missing/committed-deleted bound targets with `status: 'deleted'`) so dangling or newly broken bindings never pass silently.
  - When a touched path is a `.prompt.md`, refuse active misplaced test prompts (`isTestPromptPath`, `exit 1`) and gather owned modules from bindings, `promptClaims`, and eligible non-secret production code files.
  - Refuse missing/unreadable owning prompts for active modules, invalid or non-`.prompt.md` prompt paths, prompt-less `pdd-bindings.json` entries, and misplaced test prompt owners (`exit 1`).
  - Extract `+added`/`-removed` line counts and changed top-level symbols across JS/TS, Python, Go, and Rust (`added`, `removed`, `updated`).
  - Track which owning prompts actually changed in the inspected scope (`changedPromptTargets`: touched/renamed prompts in `working-tree`, `from`, and `branch` scopes; working-tree-modified prompts in `all` scope; diff-touched or added prompts in `files` scope).
  - Classify each `(module, owner)` pair in strict precedence order:
    1. `deleted`: a bound module path is missing/deleted on disk while still bound in `pdd-bindings.json`.
    2. `prompt-stale`: strictly when a leftover legacy `(sha256: ...)` / `sha256=` code header exists and its hash disagrees with the current prompt (`headerState === 'stale'`).
    3. `reconciled`: the code module changed in scope (`diff.added > 0 || diff.removed > 0 || renamedFrom || untracked || status === 'A'`) AND its owning prompt also changed in the same scope (`changedPromptTargets.has(owner)`).
    4. `changed`: the code module changed in scope AND its owning prompt did NOT change in scope. This is an informational advisory status (valid for pure code bugfixes or 2-PR prompt/code workflows), NEVER a hard `--check` failure.
    5. `current`: valid modern hashless `// Prompt:` headers (`headerState === 'none'`), matching legacy hashes (`headerState === 'current'`), and `pdd-bindings.json` entries (`headerRow === null && promptText !== null`) pointing to an existing prompt when the code module did not change. Never emit failing `unpinned`.
  - Aggregate each prompt group's `status` by precedence `prompt-stale` > `deleted` > `changed` > `reconciled` > `current`, and include `prompt_changed: boolean`.
- **Clean `unowned` filtering.**
  - In implicit scopes (`working-tree`, `from`, `branch`, `all`), exclude intentionally non-prompt-owned files from `unowned`: test files (`isTestOwnedPath`), `docs/**` / `doc/**`, `user_stories/**`, `prompts/**`, `fixtures/**`, `examples/**`, `.github/**`, `.pdd/**`, dotfiles and files inside dot-directories (such as `.local/config`), `pdd*.json`, `package*.json`, manifests/lockfiles/build configs (`Makefile`, `Dockerfile`, `tsconfig*.json`, etc.), non-code doc/data/config/asset extensions, paths excluded by `pdd-workspace.json` (`allowed_paths`), and configured ignore globs in `pdd.json` (`ignore`, `workspace.ignore`, `update.ignore`).
  - Still report genuine unowned product source code files (for example `src/legacy.py`) and eligible unowned binary files, and in explicit `files` scope report queried unowned files directly.
  - Keep `scope.files` listing all touched paths in scope so `pdd status --changed` remains unaffected.
- **Read-only compatibility wrapper (`src/update-sync.mjs`) and offline `--check` semantics.**
  - Forward `{ cwd, files, from, all, branch, check, write }`.
  - Refuse `--write` (`write: true`) or `--check --write` with `exit 2`, zero writes, and a 4-part diagnostic naming location, read-only invariant, fix, and rerun command.
  - In default working-tree `--check` mode (`check: true`, no `files`/`--from`/`--all`/`--branch`), whenever `modules.length === 0 && prompts.length === 0` (regardless of whether `scope.files` contains untracked non-module files such as `.local/config`), automatically widen to `all: true` (`scope.widened_from = "working-tree"`) and propagate any widening error (`exit 1` / `exit 2`) fail-closed instead of swallowing it.
  - Populate `drifted` ONLY with objectively broken/stale module entries (`status === 'prompt-stale' || status === 'deleted'`). Populate `reminders` with advisory code-only changes (`status === 'changed'`), each with message `Verify <prompt> still matches <module> (OK for pure bugfixes or split prompt/code PRs).` and include clear per-prompt `instructions` and human text `reminder:` lines.
  - In `--check` mode, return `ok: false, exitCode: 1` ONLY when `drifted.length > 0` (or on structural ownership errors such as missing prompt, invalid prompt path, or misplaced test prompt); return `ok: true, exitCode: 0` for valid hashless/binding `current`, co-changed `reconciled`, and code-only `changed` reminders.
  - In plan mode (`check: false, write: false`), return `schema_version: "pdd.update-sync.v1"` with `ok: true, exitCode: 0`, `updated: []`, and zero writes.

## Public contract

- `src/core/changed-map.mjs`:
  - `analyzeChangedMap({ cwd, files, from, all, branch }, ports) -> { ok, exitCode, error, root, report }` (`schema_version: "pdd.changed-map.v1"`, `report: { schema_version, ok, scope, prompts, modules, unowned }`)
  - `extractDiffSummary(diffText) -> { added, removed, changed_symbols }`
  - `formatChangedMapText(report, heading?) -> string`
  - `formatChangedMapJson(report) -> string`
- `src/update-sync.mjs`:
  - `analyzeUpdate({ cwd, files, from, all, branch, check, write }, ports) -> { ok, exitCode, error, root, report }` (`schema_version: "pdd.update-sync.v1"`, `report: { schema_version, ok, mode, scope, prompts, modules, unowned, drifted, reminders, updated }`)
  - `runUpdate({ cwd, files, from, all, branch, check, write, json }, streamsAndPorts) -> exitCode`
  - `formatUpdateText(report) -> string`, `formatUpdateJson(report) -> string`, re-exported `extractDiffSummary`

## Dependencies

- [File owner lookup](file-owner.prompt.md): `findOwners`, `headerEntries`, `headerHashState`, `isTestOwnedPath`, `isTestPromptPath`, `promptClaims`, and `promptHeaderHash`.
- Layer-0 shared primitives: `src/shared/git-context.mjs` (`gitFiles`), `src/shared/safe-read.mjs` (`isSecretPath`), and `src/shared/workspace-policy.mjs` (`allowsRuntimePath`).
- Layer-1 core helpers: `src/core/lint/diagnostics.mjs` (`resolveDefaultBaseRef`) and `src/core/lint/regex-safety.mjs` (`compileGlobMatcher`).
