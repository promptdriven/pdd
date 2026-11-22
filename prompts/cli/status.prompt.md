# Offline repository status and Feature Map overview

Own `src/core/status.mjs`. Export `inspectStatus({ cwd, paths, changed }, ports)` and `runStatus({ cwd, paths, changed, json }, ports)`.

Provide a fast, 100% offline, zero-AI overview merging PDD inventory (`prompts`, `stories`, `tests`, `orphans`), file ownership (`findOwners`), repository init block state (`has_pdd_block`), and the `pdd.json` Feature Map (`verify.test`, `verify.paths[]`).

## Domain decisions

- **Offline & read-only:** never touch network, tokens, AI models, or repository files.
- **Git root resolution:** resolve the canonical Git repository root via Layer-0 `resolveRepoRoot(cwd)` (`src/shared/git-context.mjs`). Outside Git, write a finite diagnostic to stderr and return exit code `2`.
- **Path validation:** resolve explicit `paths` relative to `cwd` and reject paths escaping the repository with exit code `2`.
- **`--changed` mode:** when `changed: true`, inspect working-tree changes via an optional sibling `src/core/changed-map.mjs` module when present, falling back to the union of `git status --porcelain -z --untracked-files=all` and `git diff --name-only -z HEAD`, and merge with any explicit `paths`. Report each path with its honest owner (`binding`/`header`/unowned) and matching `verify.paths` Feature Map entries.
- **Feature Map (`pdd.json` `verify`):** safely read root `pdd.json` with `readBoundedUtf8` (`noFollow: true`). Parse optional `verify.test` and `verify.paths[]` (`id`, `name`, `when`, `run`, `needs`) and match queried/changed paths against `when` globs (`*`, `**`, `?`).
- **Instruction block detection:** report `has_pdd_block` (`true` when repo-root `CLAUDE.md` or `AGENTS.md` — including an in-repo symlink such as `CLAUDE.md -> AGENTS.md` resolving to a regular file inside `root` — contains both `<!-- pdd:start -->` and `<!-- pdd:end -->`) and `instruction_file` so `/pdd` can offer `pdd init` once after a first prompt-backed win.
- **Compact human output & stable JSON (`pdd.status.v1`):** print a concise overview (`<= 12` lines when no explicit path list is passed), or valid JSON with `--json`. Handle `EPIPE` cleanly with exit code `0`.

## Public contract

- `inspectStatus({ cwd, paths, changed }, ports) -> Promise<StatusView>` (`schema_version: 'pdd.status.v1'`)
- `runStatus({ cwd, paths, changed, json }, ports) -> Promise<number>` (`0` on success, `2` outside Git or invalid path)

## Dependencies

- Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before changing this prompt.
- Layer-0 `src/shared/git-context.mjs` and `src/shared/safe-read.mjs`; Layer-1 `src/file-owner.mjs` and `src/runtime-seam.mjs` (`runtimePreflightSlice`).
