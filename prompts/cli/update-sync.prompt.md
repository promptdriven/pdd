# Changed-file ownership map

Own `src/core/changed-map.mjs` and the read-only compatibility wrapper `src/update-sync.mjs`. Export `analyzeChangedMap`, `extractDiffSummary`, `formatChangedMapText`, and `formatChangedMapJson` from `src/core/changed-map.mjs`, and `runUpdate`, `analyzeUpdate`, `extractDiffSummary`, `formatUpdateText`, and `formatUpdateJson` from `src/update-sync.mjs`.

Map touched repository files (explicit paths, a Git `--from RANGE`, or working-tree changes) to their owning `.prompt.md` contracts through [File owner lookup](file-owner.prompt.md), summarize unified diff line counts and changed top-level symbols across JS/TS, Python, Go, and Rust, and report unowned touched files offline with zero file writes and zero AI or network calls.

## Domain decisions

- **Strictly read-only offline core.** Inspect local Git metadata and working-tree files only. Spawn zero AI subprocesses, make zero network or interpreter calls, and never write `.pdd/sync/` sidecars, `.prompt.md` files, source headers, or `pdd-bindings.json`.
- **Scoped target selection (mutually exclusive modes).**
  - Explicit `files`: scope strictly to those repository-relative regular files. Reject combining `files` with `--from` (`exit 2`). Detect untracked explicit files so newly added files report full line additions and symbols.
  - Range `from`: accept `<base>..<head>` or `<base>` (normalized to `<base>..HEAD`). Reject empty strings, length `> 256`, whitespace, ASCII control characters, `...`, multiple `..`, or any segment starting with `-` (`exit 2`) before calling Git. Resolve touched paths with `--literal-pathspecs`, `core.quotepath=false`, and `--no-ext-diff`.
  - Default working-tree mode: resolve modified, staged, renamed, deleted, and untracked non-ignored files from `git diff --name-status -z -M HEAD` merged with `git status --porcelain=v1 -z -uall` (falling back cleanly on unborn branches), ignoring `.pdd/**`.
  - Outside a Git repository, exit `2`. Empty scope exits `0` with empty arrays and `ok: true`.
- **Security, secret isolation, binary probing, and fail-closed bindings.**
  - Reject paths starting with `-`, containing control characters or `\`, using `..` traversal, resolving outside the canonical Git root, or traversing symlinks (`lstat` + `O_NOFOLLOW`, `exit 2`).
  - Reject secret-looking paths (`isSecretPath` or `.env*`, `credentials*`, `.aws-credentials`) before reading them (`exit 2`).
  - Fail closed (`exit 2`) if `pdd-bindings.json` exists and is a symlink, unreadable, exceeds 64 KiB, is invalid JSON, or fails the `pdd.bindings.v1` schema.
  - Probe binary content with a bounded 8 KiB prefix read: reject explicit or owned binary files (`exit 2`) and report unowned binary files under `unowned` with reason `binary file (skipped)`. Bound full text reads to 10 MiB.
- **Owner mapping, prompt touches, and diff summaries.**
  - Delegate ownership lookup to `findOwners` (`pdd-bindings.json`, `Generated from` / `Prompt:` headers, opening-sentence prose claims, and unique path/stem matches).
  - When a touched path is a `.prompt.md`, refuse active misplaced test prompts (`isTestPromptPath`, `exit 1`) and gather owned modules from bindings, `promptClaims`, and eligible non-secret production code files.
  - Extract `+added`/`-removed` line counts and changed top-level symbols across JS/TS, Python, Go, and Rust (`added`, `removed`, `updated`).
  - Classify each `(module, owner)` pair as `deleted`, `prompt-stale` (when an existing code header hash lags the prompt), `changed` (when the diff or rename touched the module), or `current`.
- **Read-only compatibility wrapper (`src/update-sync.mjs`).**
  - In plan mode (`check: false, write: false`), return `schema_version: "pdd.update-sync.v1"` with `exit 0` and zero writes.
  - In `--check` mode (`check: true`), return `exit 1` when any owned module has non-`current` status (`drifted.length > 0`), else `exit 0`.
  - Refuse `--write` (`write: true`) with `exit 2`, zero writes, and a 4-part diagnostic naming the location, read-only invariant, concrete fix, and rerun command.

## Dependencies

- [File owner lookup](file-owner.prompt.md): `findOwners`, `headerEntries`, `headerHashState`, `isTestOwnedPath`, `isTestPromptPath`, `promptClaims`, and `promptHeaderHash`.
- Layer-0 shared primitives: `src/shared/git-context.mjs` (`gitFiles`) and `src/shared/safe-read.mjs` (`isSecretPath`).
