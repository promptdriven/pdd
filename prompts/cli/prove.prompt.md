# Unified stateless proof and feature map verification

Own `src/core/prove.mjs` and `src/core/verify-paths.mjs`. Provide one stateless, repository-agnostic and language-agnostic proof engine (`runProve`) backed by the universal `pdd.json` `"verify"` feature map (`loadVerifyConfig`, `parseVerifyConfig`, `matchVerifyPaths`, `detectHostCapabilities`, `matchCapabilities`).

## Domain decisions

- **Three distinct outcomes:** Every invocation resolves cleanly to `Proved` (exit `0`), `Failed` (exit `1`), or `Not proved` (exit `3`); invalid CLI arguments return exit `2`. Missing recipes or absent host capabilities produce `Not proved` with explicit reasons and never report `Proved`.
- **Universal Feature Map (`pdd.json` `"verify"`):** Declares optional `test` command, optional `report` path, and `paths[]` entries `{id, name?, when, run, needs?}` (max 100 entries, unique IDs). `when` globs compile via the strictly linear DP glob matcher (`compileGlobMatcher`). `needs` accepts open capability strings (`tty`, `browser`, `docker`, `ios-simulator`, `account:<name>`, or custom strings) matched lazily against detected or injected host capabilities with zero hardcoded capability schema fields or repository names.
- **Base-trusted config:** Zero-flag `runProve` executes `verify` recipes strictly from the merge base (`git show <baseSha>:pdd.json`), never from untrusted working-tree or branch edits. Uncommitted or branch-only `verify` additions or edits are reported as `Not proved` so unreviewed recipes cannot self-authorize merge.
- **Zero-flag verification mode:** Resolves the local merge base offline (failing closed as `Not proved` if base comparison is unavailable), runs deterministic offline `lintRepoProject` + `runDiffSpotlight`, runs `verify.test` (or auto-detects Node/Vitest, Go, Rust, or Pytest), runs every base-trusted `verify.paths[]` recipe whose `when` globs match touched files and whose `needs` are satisfied, and emits a structured `pdd.prove.v1` provenance JSON receipt (`--json`) or human summary.
- **Bug-contrast mode (`--test CMD --expect TEXT`):**
  1. Overlays colocated test files (`src/**/*.test.*`, `*.spec.*`, `*_test.go`, `test_*.py`, `*_test.py`, `*_test.rs`, `test/**`, `tests/**`, `__tests__/**`, `fixtures/**`) plus any explicit `--overlay GLOB` matches, mirroring deleted test files into the base worktree so deleting a failing test never yields a fake pass.
  2. Resolves `--base REF` strictly offline from local Git refs without network fetches.
  3. Mirrors modified, deleted, and untracked files into isolated disposable base and head worktrees (`git worktree add --detach`) while validating every path segment against symlink escapes and opening destinations with `O_NOFOLLOW`, so the caller's checkout is never mutated.
  4. Scrubs credential and session environment variable families (`GH_*`, `GITHUB_*`, `CLAUDE*`, `ANTHROPIC_*`, `OPENAI_*`, `CODEX_*`, `HERDR_*`, `PDD_*`, `AWS_*`, `*_TOKEN`, `*_SECRET`, `*_API_KEY`, `*_PASSWORD`) before running `--setup` and `--test` in the disposable base and head worktrees, always removing both worktrees on exit.
  5. Detects setup, missing-dependency, import, syntax, compile errors, and signalled processes on base or head (`ERR_MODULE_NOT_FOUND`, `Cannot find module`, `ModuleNotFoundError`, `ImportError`, `SyntaxError`, `ENOENT`, `command not found`, exit `126`/`127`, `[build failed]`, `ERROR collecting`, `error[E...]`, non-timeout signals) and classifies them as `Not proved` (`setup-error`), never as a causal proof. Only a non-setup base failure whose output contains `--expect` paired with a passing head run yields `Proved`.

## Public contract

- `parseVerifyConfig(raw, {sourcePath})`: pure parser returning `{configured, source, test, report, paths, errors}`.
- `loadVerifyConfig(rootOrObject, {gitRef})`: loads `pdd.json` safely from disk (no symlinks) or from `git show <gitRef>:pdd.json`.
- `matchVerifyPaths(verifyConfig, touchedFiles)`: returns `{matched, changedSurfaces, unmappedSurfaces}`.
- `detectHostCapabilities(requiredNeeds, {env, capabilities, probe, isTTY})`: lazily checks only requested capabilities and returns `{available, checked}`.
- `matchCapabilities(needs, capabilityState)`: returns `{satisfied, missing}`.
- `runProve({cwd, base, test, expect, overlay, setup, timeoutMinutes, json, capabilities, env}, ports)`: returns `{exitCode, outcome, receipt}` and writes human text or JSON receipt to `stdout`/`stderr`.

## Dependencies

- [Repo hygiene and offline PDD lint](repo-hygiene-lint.prompt.md): `lintRepoProject`, `runDiffSpotlight`, `resolveDefaultBaseRef`, `compileGlobMatcher`, and safe file read helpers.
- [File owner lookup](file-owner.prompt.md): `isTestOwnedPath`.
