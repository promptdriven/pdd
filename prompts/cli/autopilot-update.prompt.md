# Safe between-tick Autopilot self-update and CLI upgrade

Own `src/autopilot-update.mjs`. Export `validAutoUpdateMode(mode)`, `detectGlobalInstallPrefix(packageRoot, ports)`, `hasMidWriteJobs(coreRoot, ports)`, `autoUpdateStatusLine({stateRoot}, ports)`, `maybeAutoUpdateAutopilot({state, packageRoot, coreRoot, stateRoot, env}, ports)`, `resolveReleaseUpgradeTarget({fetchImpl, spawnSyncImpl, env})`, `resolveMainCommitTarget({fetchImpl, spawnSyncImpl, env})` and `runCliUpgrade({env, stdout, stderr, main, spawnSyncImpl, fetchImpl, packageRoot, home, cwd}, ports)` (#2710, #3424). Keep an active global `pdd` Autopilot installation and its PDD skills current between ticks without interrupting jobs that are publishing or merging, and provide the explicit `pdd upgrade [--main]` command that updates a user-owned global `pdd` installation and its installed PDD skills together.

## Domain decisions

- `validAutoUpdateMode` accepts `'release'` (default when `state.autoUpdate` is unset), `'main'` and `'off'`.
- When mode is `'off'`, or `env.CI` or `env.PDD_AGENT_SESSION` is set, do nothing and return `{action: 'disabled'}`.
- Throttle checks to at most once every hour (`3600000` ms) using `<stateRoot>/autopilot-update.json` (`checkedAt`, written atomically with mode `0600`).
- `hasMidWriteJobs(target, ports)` accepts a `coreRoot` path or `{coreRoot, stateRoot}` and inspects `<coreRoot>/jobs/*.json` plus every active `<repo>-core/jobs/*.json` directory under `stateRoot`. Return `true` when any job has `phase === 'ending'`, `lane?.state === 'final'`, or an active Runtime check child (`runtimeWait?.state === 'sent'` or `runtime?.state === 'running'`). When `true`, defer without advancing `checkedAt` so the next idle tick checks immediately.
- `detectGlobalInstallPrefix(packageRoot)` accepts only a real directory inside `<prefix>/lib/node_modules/@promptdriven/pdd`, `<prefix>/lib/node_modules/pdd`, `<prefix>/node_modules/@promptdriven/pdd`, or `<prefix>/node_modules/pdd`, owned by the current user (`stat.uid === uid` when `uid` is available) and containing no `.git` entry (never update a source checkout or root-owned prefix).
- The GitHub package installs as `@promptdriven/pdd`. npm does not replace the unscoped `pdd` package when installing it; both claim the `pdd` executable and npm can refuse with `EEXIST`. To migrate manually, uninstall `pdd` from the same global npm prefix, then install `github:promptdriven/pdd` and verify `pdd --version`. Never recommend forcing the install over the existing executable.
- Both updaters require manual migration when the admitted running package is at an unscoped `node_modules/pdd` location, or when `<prefix>/bin/pdd` resolves to the unscoped package's `bin/pdd.mjs` in that prefix. A leftover unscoped directory by itself does not block updating a scoped installation. A missing or unresolvable executable link is not evidence of unscoped ownership.
- For a migration refusal, explain `The unscoped npm package pdd can block @promptdriven/pdd from installing its pdd executable (EEXIST). To migrate, run: npm uninstall -g --prefix '<prefix>' pdd && npm install -g --prefix '<prefix>' --ignore-scripts github:promptdriven/pdd`. Shell-quote the actual prefix as one POSIX argument in both commands. Neither updater runs those commands itself or refreshes skills on refusal. An admitted scoped installation without the collision keeps its normal update path.

## Update execution

After the mode, throttle, mid-write and global prefix checks, but before lookup or any subprocess, check for required migration. If required, save the recovery message as `lastError` with the normal `checkedAt` backoff and return `{action: 'failed', error: <recovery message>}`. `autoUpdateStatusLine` ends with the entire migration command, without truncation or trailing punctuation.

1. Query the target version, failing whenever `gh api` exits non-zero or returns no valid release/commit:
   - `'release'`: fetch `repos/promptdriven/pdd/releases?per_page=10`, pick the newest non-draft release with a valid version tag (`pickLatestRelease`, supporting prerelease-only `alpha-v*` repositories), throw when none is valid, and compare `version` against `<packageRoot>/package.json` `version` via `isNewerRelease`. Target spec: `github:promptdriven/pdd#<tag>`.
   - `'main'`: fetch `repos/promptdriven/pdd/commits/main` (`sha`), throw when `sha` is missing, and compare against saved `installedSha` in `autopilot-update.json`. Target spec: pinned `github:promptdriven/pdd#<sha>` (never mutable `#main`).
2. When no update is needed, save `{checkedAt: now, action: 'up-to-date', channel: mode, version}` and return.
3. Acquire `ports.claimUpdateLock` (if supplied) and re-check `hasMidWriteJobs({coreRoot, stateRoot})`.
4. If `state.cwd` is on `state.baseBranch` with clean `git status --porcelain`, run best-effort `git pull --ff-only origin <baseBranch>`; never reset or touch dirty files.
5. Run `npm install -g --prefix <prefix> --ignore-scripts --no-audit --no-fund <targetSpec>` (120-second timeout).
6. Locate the installed package folder under `<prefix>` (`@promptdriven/pdd` or `pdd`) and lazily load [skills install](skills-install.prompt.md) `setupSkills` (passing `codexHome` when `env.CODEX_HOME` is set) to refresh user-folder PDD skills.
7. Save `{checkedAt: now, updatedAt: now, action: 'updated', channel: mode, fromVersion, toVersion, target, ...(installedSha ? {installedSha} : {})}` in `autopilot-update.json`. On failure, record `lastError` with the 1-hour `checkedAt` backoff and never fail the tick.
8. `autoUpdateStatusLine({stateRoot})` formats one summary line from `autopilot-update.json` when an update or update error is recorded, else `''`.

## Explicit CLI upgrade (`runCliUpgrade`)

`runCliUpgrade({env, stdout, stderr, main = false, spawnSyncImpl, fetchImpl, packageRoot, home, cwd}, ports)` upgrades a user-owned global `pdd` installation and refreshes installed PDD skills in one step (#3424):

1. Check `detectGlobalInstallPrefix(packageRoot, {fs, uid: ports.uid})`. For an admitted prefix that requires migration, write the recovery message with a `pdd upgrade: ` prefix and trailing newline via `stderr.write(text)`, leave stdout empty and return `{exitCode: 1, cliUpdated: false, updatedSkills: [], skippedSkills: [], failedSkills: []}` before reading a version, looking up GitHub, running a subprocess or clearing caches. When the detected prefix is null (such as a Git checkout or root-owned prefix) or when `<packageRoot>/package.json` has no valid version, write an actionable message with `npm install -g github:promptdriven/pdd && pdd setup` to `stderr` and return `{exitCode: 1, ...}`.
2. Resolve the upgrade target using GitHub API `fetchImpl` (falling back to `gh api` via `spawnSyncImpl` when needed):
   - Default (`main: false`): `resolveReleaseUpgradeTarget` queries `repos/promptdriven/pdd/releases?per_page=10`, selects `pickLatestRelease`, and returns `{channel: 'release', ref: tag, version, spec: 'github:promptdriven/pdd#' + tag}`.
   - `--main` (`main: true`): `resolveMainCommitTarget` queries `repos/promptdriven/pdd/commits/main`, validates the 40-hex `sha`, and returns `{channel: 'main', ref: sha, sha, spec: 'github:promptdriven/pdd#' + sha}` (never mutable `#main`).
   - On lookup failure, write the error and manual recovery command to `stderr` and return `{exitCode: 1, ...}`.
3. When `main` is true or `isNewerRelease(target.version, currentVersion)` is true, run `npm install -g --prefix <prefix> --ignore-scripts --no-audit --no-fund <target.spec>` via `spawnSyncImpl`. On non-zero exit, report the failure and recovery command to `stderr` and return `{exitCode: 1, ...}`. When already at the latest release version, skip reinstalling the CLI binary and still run step 4 so stale skills are repaired in one command.
4. Resolve `<targetPkgRoot>` under `<prefix>`, remove stale `<stateHome>/pdd/release-check.json` fail-open, and refresh `.pdd-skill.json`-marked user skills against `<targetPkgRoot>`:
   - Call `syncOwnedUserSkills({packageRoot: targetPkgRoot, home, claudeConfigDir: env.CLAUDE_CONFIG_DIR, codexHome: env.CODEX_HOME, stateRoot, force: true, onError})` to update all `.pdd-skill.json`-marked user skill folders (`.agents/skills`, `.codex/skills`, `$CODEX_HOME/skills`, and Claude's user folder), install missing `PDD_SKILL_NAMES` skills into partial older marked folders, and remove `.pdd-skill.json`-marked `RETIRED_SKILL_NAMES` folders while never modifying unmarked folders or symlinks.
   - Inspect remaining noncurrent user and project skill folders with `findSkills` against `<targetPkgRoot>`. Never spawn `npx skills add` or modify unmarked, customized (`'differs'`) or symlinked copies; preserve them untouched and report each skipped folder (with affected skill names and versions) on `stdout` along with `To update unmarked skills, run: npx skills add promptdriven/pdd -g --skill '*'` (or without `-g` for project folders).
   - Report CLI updates and `Updated PDD skills` on `stdout` only for folders actually updated on disk. When any marker-owned skill folder update fails, report the failed folder and actionable recovery command (`pdd setup`) on `stderr` and return `exitCode: 1` (else `0`).

## Dependencies

- Read the full [Prompting guide](../../docs/prompting-guide.md) before authoring.
- [Cached CLI release notice](release-notice.prompt.md) for release tag version parsing and comparison.
- [Skills install](skills-install.prompt.md) for refreshing user-folder PDD skills after a self-update.

## Ports for global-install admission

- The injected filesystem in `ports.fs` takes string `path` for `fs.realpathSync` (returns the canonical path string), `fs.statSync` (stat with integer `uid` when known and directory flag `isDirectory`, a method in native Node), and `fs.existsSync` (returns Boolean).
- The injected `stderr.write` takes string `text` and the updater ignores its return value.
- `process.spawnSync` represents the `spawnSyncImpl` port for subprocesses; it takes a command string, a string array of arguments and process options, and returns the exit status and output. Migration refusal never calls it.
