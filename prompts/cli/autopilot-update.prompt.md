# Safe between-tick Autopilot self-update and CLI upgrade

Own `src/autopilot-update.mjs`. Export `validAutoUpdateMode(mode)`, `detectGlobalInstallPrefix(packageRoot, ports)`, `hasLegacyUnscopedPdd(prefix, ports)`, `hasMidWriteJobs(coreRoot, ports)`, `autoUpdateStatusLine({stateRoot}, ports)`, `maybeAutoUpdateAutopilot({state, packageRoot, coreRoot, stateRoot, env}, ports)`, `resolveReleaseUpgradeTarget({fetchImpl, spawnSyncImpl, env})`, `resolveMainCommitTarget({fetchImpl, spawnSyncImpl, env})` and `runCliUpgrade({env, stdout, stderr, main, spawnSyncImpl, fetchImpl, packageRoot, home, cwd}, ports)` (#2710, #3424, #3474). Keep an active global `pdd` Autopilot installation and its PDD skills current between ticks without interrupting jobs that are publishing or merging, and provide the explicit `pdd upgrade [--main]` command that updates a user-owned global `pdd` installation and its installed PDD skills together.

## Channels and safety guards

- `validAutoUpdateMode` accepts `'release'` (default when `state.autoUpdate` is unset), `'main'` and `'off'`.
- When mode is `'off'`, or `env.CI` or `env.PDD_AGENT_SESSION` is set, do nothing and return `{action: 'disabled'}`.
- Throttle checks to at most once every hour (`3600000` ms) using `<stateRoot>/autopilot-update.json` (`checkedAt`, written atomically with mode `0600`).
- `hasMidWriteJobs(target, ports)` accepts a `coreRoot` path or `{coreRoot, stateRoot}` and inspects `<coreRoot>/jobs/*.json` plus every active `<repo>-core/jobs/*.json` directory under `stateRoot`. Return `true` when any job has `phase === 'ending'`, `lane?.state === 'final'`, or an active Runtime check child (`runtimeWait?.state === 'sent'` or `runtime?.state === 'running'`). When `true`, defer without advancing `checkedAt` so the next idle tick checks immediately.
- `detectGlobalInstallPrefix(packageRoot)` accepts only a real directory inside `<prefix>/lib/node_modules/@promptdriven/pdd`, `<prefix>/lib/node_modules/pdd`, `<prefix>/node_modules/@promptdriven/pdd`, or `<prefix>/node_modules/pdd`, owned by the current user (`stat.uid === uid` when `uid` is available) and containing no `.git` entry (never update a source checkout or root-owned prefix).
- `hasLegacyUnscopedPdd(prefix, ports)` returns `true` when `<prefix>/lib/node_modules/pdd/package.json` or `<prefix>/node_modules/pdd/package.json` has `"name": "pdd"`, or when `<prefix>/bin/pdd` is a symbolic link pointing into `node_modules/pdd/` rather than `@promptdriven/pdd` (#3474). Never pass `--force` to overwrite `bin/pdd`; explicitly uninstall the unscoped `pdd` package before installing `@promptdriven/pdd`, and load `skills-install` helpers in memory before uninstalling so post-install skill synchronization succeeds even when the running process started from `node_modules/pdd`.

## Update execution

1. Query the target version, failing whenever `gh api` exits non-zero or returns no valid release/commit:
   - `'release'`: fetch `repos/promptdriven/pdd/releases?per_page=10`, pick the newest non-draft release with a valid version tag (`pickLatestRelease`, supporting prerelease-only `alpha-v*` repositories), throw when none is valid, and compare `version` against `<packageRoot>/package.json` `version` via `isNewerRelease`. Target spec: `github:promptdriven/pdd#<tag>`.
   - `'main'`: fetch `repos/promptdriven/pdd/commits/main` (`sha`), throw when `sha` is missing, and compare against saved `installedSha` in `autopilot-update.json`. Target spec: pinned `github:promptdriven/pdd#<sha>` (never mutable `#main`).
2. When no update is needed and `hasLegacyUnscopedPdd(prefix)` is `false`, save `{checkedAt: now, action: 'up-to-date', channel: mode, version}` and return. When `hasLegacyUnscopedPdd(prefix)` is `true`, still migrate unscoped `pdd` to `@promptdriven/pdd`.
3. Acquire `ports.claimUpdateLock` (if supplied) and re-check `hasMidWriteJobs({coreRoot, stateRoot})`.
4. If `state.cwd` is on `state.baseBranch` with clean `git status --porcelain`, run best-effort `git pull --ff-only origin <baseBranch>`; never reset or touch dirty files.
5. When `hasLegacyUnscopedPdd(prefix)` is `true`, run `npm uninstall -g --prefix <prefix> --ignore-scripts --no-audit --no-fund pdd` (60-second timeout) before installing `@promptdriven/pdd` so `<prefix>/bin/pdd` does not fail with `EEXIST` (#3474). Then run `npm install -g --prefix <prefix> --ignore-scripts --no-audit --no-fund <targetSpec>` (120-second timeout).
6. Locate the installed package folder under `<prefix>` (`@promptdriven/pdd` or `pdd`) and lazily load [skills install](skills-install.prompt.md) `setupSkills` (passing `codexHome` when `env.CODEX_HOME` is set) to refresh user-folder PDD skills.
7. Save `{checkedAt: now, updatedAt: now, action: 'updated', channel: mode, fromVersion, toVersion, target, ...(installedSha ? {installedSha} : {})}` in `autopilot-update.json`. On failure, record `lastError` with the 1-hour `checkedAt` backoff and never fail the tick.
8. `autoUpdateStatusLine({stateRoot})` formats one summary line from `autopilot-update.json` when an update or update error is recorded, else `''`.

## Explicit CLI upgrade (`runCliUpgrade`)

`runCliUpgrade({env, stdout, stderr, main = false, spawnSyncImpl, fetchImpl, packageRoot, home, cwd}, ports)` upgrades a user-owned global `pdd` installation and refreshes installed PDD skills in one step (#3424):

1. Check `detectGlobalInstallPrefix(packageRoot, {fs, uid: ports.uid})`. When null (such as a Git checkout or root-owned prefix) or when `<packageRoot>/package.json` has no valid version, write an actionable message with `npm install -g github:promptdriven/pdd && pdd setup` to `stderr` and return `{exitCode: 1, ...}`.
2. Resolve the upgrade target using GitHub API `fetchImpl` (falling back to `gh api` via `spawnSyncImpl` when needed):
   - Default (`main: false`): `resolveReleaseUpgradeTarget` queries `repos/promptdriven/pdd/releases?per_page=10`, selects `pickLatestRelease`, and returns `{channel: 'release', ref: tag, version, spec: 'github:promptdriven/pdd#' + tag}`.
   - `--main` (`main: true`): `resolveMainCommitTarget` queries `repos/promptdriven/pdd/commits/main`, validates the 40-hex `sha`, and returns `{channel: 'main', ref: sha, sha, spec: 'github:promptdriven/pdd#' + sha}` (never mutable `#main`).
   - On lookup failure, write the error and manual recovery command to `stderr` and return `{exitCode: 1, ...}`.
3. Let `legacyUnscoped = hasLegacyUnscopedPdd(prefix, {fs})`. When `main` is true, `legacyUnscoped` is true, or `isNewerRelease(target.version, currentVersion)` is true: first, when `legacyUnscoped` is true, run `npm uninstall -g --prefix <prefix> --ignore-scripts --no-audit --no-fund pdd` via `spawnSyncImpl` (reporting a manual `npm uninstall -g --prefix <prefix> pdd && npm install -g --prefix <prefix> --ignore-scripts <target.spec> && pdd setup` migration command on non-zero exit without `--force`), then run `npm install -g --prefix <prefix> --ignore-scripts --no-audit --no-fund <target.spec>` via `spawnSyncImpl`. On non-zero install exit, report the failure and recovery command to `stderr` (including `npm uninstall -g --prefix <prefix> pdd && ...` without `--force` when `EEXIST` or unscoped `pdd` owns `bin/pdd`) and return `{exitCode: 1, ...}`. When already at the latest `@promptdriven/pdd` release version with `legacyUnscoped === false`, skip reinstalling the CLI binary and still run step 4 so stale skills are repaired in one command.
4. Resolve `<targetPkgRoot>` under `<prefix>`, remove stale `<stateHome>/pdd/release-check.json` fail-open, and refresh `.pdd-skill.json`-marked user skills against `<targetPkgRoot>`:
   - Call `syncOwnedUserSkills({packageRoot: targetPkgRoot, home, claudeConfigDir: env.CLAUDE_CONFIG_DIR, codexHome: env.CODEX_HOME, stateRoot, force: true, onError})` to update all `.pdd-skill.json`-marked user skill folders (`.agents/skills`, `.codex/skills`, `$CODEX_HOME/skills`, and Claude's user folder), install missing `PDD_SKILL_NAMES` skills into partial older marked folders, and remove `.pdd-skill.json`-marked `RETIRED_SKILL_NAMES` folders while never modifying unmarked folders or symlinks.
   - Inspect remaining noncurrent user and project skill folders with `findSkills` against `<targetPkgRoot>`. Never spawn `npx skills add` or modify unmarked, customized (`'differs'`) or symlinked copies; preserve them untouched and report each skipped folder (with affected skill names and versions) on `stdout` along with `To update unmarked skills, run: npx skills add promptdriven/pdd -g --skill '*'` (or without `-g` for project folders).
   - Report CLI updates and `Updated PDD skills` on `stdout` only for folders actually updated on disk. When any marker-owned skill folder update fails, report the failed folder and actionable recovery command (`pdd setup`) on `stderr` and return `exitCode: 1` (else `0`).

## Dependencies

- Read the full [Prompting guide](../../docs/prompting-guide.md) before authoring.
- [Cached CLI release notice](release-notice.prompt.md) for release tag version parsing and comparison.
- [Skills install](skills-install.prompt.md) for refreshing user-folder PDD skills after a self-update.
