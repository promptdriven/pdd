# Unified stateless proof and feature map verification

Own `src/core/prove.mjs` and `src/core/verify-paths.mjs`. Provide one stateless, repository-agnostic and language-agnostic proof engine (`runProve`) backed by the universal `pdd.json` `"verify"` feature map (`loadVerifyConfig`, `parseVerifyConfig`, `matchVerifyPaths`, `detectHostCapabilities`, `matchCapabilities`).

## Domain decisions

- **Three distinct outcomes:** Every invocation resolves cleanly to `Proved` (exit `0`), `Failed` (exit `1`), or `Not proved` (exit `3`); invalid CLI arguments return exit `2`. Missing recipes or absent host capabilities produce `Not proved` with explicit reasons and never report `Proved`.
- **Universal Feature Map (`pdd.json` `"verify"`):** Declares optional `test` command, optional `report` path, and `paths[]` entries `{id, name?, when, run, needs?}` (max 100 entries, unique IDs). `when` globs compile via the strictly linear DP glob matcher (`compileGlobMatcher`). `needs` accepts open capability strings (`tty`, `browser`, `docker`, `ios-simulator`, `account:<name>`, or custom strings) matched lazily against detected or injected host capabilities with zero hardcoded capability schema fields or repository names.
- **Base-trusted config:** Zero-flag `runProve` prefers `pdd.json` from the merge base (`git show <baseSha>:pdd.json`). When a branch introduces a `verify` block absent on merge base, it still runs the check locally and records a `Not proved` reason so unreviewed recipes cannot self-authorize merge.
- **Zero-flag verification mode:** Resolves the local merge base offline, runs deterministic offline `lintRepoProject` + `runDiffSpotlight`, runs `verify.test` (or auto-detects Node/Vitest, Go, Rust, or Pytest), runs every `verify.paths[]` recipe whose `when` globs match touched files and whose `needs` are satisfied, and emits a structured `pdd.prove.v1` provenance JSON receipt (`--json`) or human summary.
- **Bug-contrast mode (`--test CMD --expect TEXT`):**
  1. Overlays colocated test files (`src/**/*.test.*`, `*.spec.*`, `*_test.go`, `test_*.py`, `*_test.py`, `*_test.rs`, `test/**`, `tests/**`, `__tests__/**`, `fixtures/**`) plus any explicit `--overlay GLOB` matches.
  2. Resolves `--base REF` strictly offline from local Git refs without network fetches.
  3. Reads modified and untracked test files directly from the working tree (refusing symlinks and escaping paths) and overlays them onto a disposable `git worktree add --detach` at `baseSha`.
  4. Scrubs credential and session environment variables before running `--setup` and `--test` in isolated base and head contexts, always removing the disposable base worktree on exit.
  5. Detects setup, missing-dependency, import, syntax, and compile errors on base or head (`ERR_MODULE_NOT_FOUND`, `Cannot find module`, `ModuleNotFoundError`, `ImportError`, `SyntaxError`, `ENOENT`, `command not found`, exit `126`/`127`, `[build failed]`, `ERROR collecting`, `error[E...]`) and classifies them as `Not proved` (`setup-error`), never as a causal proof. Only a non-setup base failure whose output contains `--expect` paired with a passing head run yields `Proved`.

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
