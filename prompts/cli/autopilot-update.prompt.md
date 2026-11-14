# Safe between-tick Autopilot self-update

Own `src/autopilot-update.mjs`. Export `validAutoUpdateMode(mode)`, `detectGlobalInstallPrefix(packageRoot, ports)`, `hasMidWriteJobs(coreRoot, ports)`, `autoUpdateStatusLine({stateRoot}, ports)` and `maybeAutoUpdateAutopilot({state, packageRoot, coreRoot, stateRoot, env}, ports)` (#2710). Keep an active global `pdd` Autopilot installation and its PDD skills current between ticks without interrupting jobs that are publishing or merging.

## Channels and safety guards

- `validAutoUpdateMode` accepts `'release'` (default when `state.autoUpdate` is unset), `'main'` and `'off'`.
- When mode is `'off'`, or `env.CI` or `env.PDD_AGENT_SESSION` is set, do nothing and return `{action: 'disabled'}`.
- Throttle checks to at most once every hour (`3600000` ms) using `<stateRoot>/autopilot-update.json` (`checkedAt`, written atomically with mode `0600`).
- `hasMidWriteJobs(target, ports)` accepts a `coreRoot` path or `{coreRoot, stateRoot}` and inspects `<coreRoot>/jobs/*.json` plus every active `<repo>-core/jobs/*.json` directory under `stateRoot`. Return `true` when any job has `phase === 'ending'`, `lane?.state === 'final'`, or an active Runtime check child (`runtimeWait?.state === 'sent'` or `runtime?.state === 'running'`). When `true`, defer without advancing `checkedAt` so the next idle tick checks immediately.
- `detectGlobalInstallPrefix(packageRoot)` accepts only a real directory inside `<prefix>/lib/node_modules/@promptdriven/pdd`, `<prefix>/lib/node_modules/pdd`, `<prefix>/node_modules/@promptdriven/pdd`, or `<prefix>/node_modules/pdd`, owned by the current user (`stat.uid === uid` when `uid` is available) and containing no `.git` entry (never update a source checkout or root-owned prefix).

## Update execution

1. Query the target version, failing whenever `gh api` exits non-zero or returns no valid release/commit:
   - `'release'`: fetch `repos/promptdriven/pdd/releases?per_page=10`, pick the newest non-draft release with a valid version tag (`pickLatestRelease`, supporting prerelease-only `alpha-v*` repositories), throw when none is valid, and compare `version` against `<packageRoot>/package.json` `version` via `isNewerRelease`. Target spec: `github:promptdriven/pdd#<tag>`.
   - `'main'`: fetch `repos/promptdriven/pdd/commits/main` (`sha`), throw when `sha` is missing, and compare against saved `installedSha` in `autopilot-update.json`. Target spec: pinned `github:promptdriven/pdd#<sha>` (never mutable `#main`).
2. When no update is needed, save `{checkedAt: now, action: 'up-to-date', channel: mode, version}` and return.
3. Acquire `ports.claimUpdateLock` (if supplied) and re-check `hasMidWriteJobs({coreRoot, stateRoot})`.
4. If `state.cwd` is on `state.baseBranch` with clean `git status --porcelain`, run best-effort `git pull --ff-only origin <baseBranch>`; never reset or touch dirty files.
5. Run `npm install -g --prefix <prefix> --ignore-scripts --no-audit --no-fund <targetSpec>` (120-second timeout).
6. Locate the installed package folder under `<prefix>` (`@promptdriven/pdd` or `pdd`) and lazily load [skills install](skills-install.prompt.md) `setupSkills` to refresh user-folder PDD skills.
7. Save `{checkedAt: now, updatedAt: now, action: 'updated', channel: mode, fromVersion, toVersion, target, ...(installedSha ? {installedSha} : {})}` in `autopilot-update.json`. On failure, record `lastError` with the 1-hour `checkedAt` backoff and never fail the tick.
8. `autoUpdateStatusLine({stateRoot})` formats one summary line from `autopilot-update.json` when an update or update error is recorded, else `''`.

## Dependencies

- Read the full [Prompting guide](../../docs/prompting-guide.md) before authoring.
- [Cached CLI release notice](release-notice.prompt.md) for release tag version parsing and comparison.
- [Skills install](skills-install.prompt.md) for refreshing user-folder PDD skills after a self-update.
