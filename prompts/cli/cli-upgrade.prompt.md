# Global PDD CLI updater

Own `src/setup/cli-upgrade.mjs`. Export `detectGlobalInstallPrefix(packageRoot, ports)`, `classifyInstallKind(packageRoot, ports)`, `hasLegacyUnscopedPdd(prefixOrInstall, ports)`, `resolveReleaseUpgradeTarget(options)`, `resolveMainCommitTarget(options)`, and `runCliUpgrade(options, ports)`.

## Domain decisions

- **Zero Autopilot dependency:** lives in Layer-1 `setup` (`src/setup/cli-upgrade.mjs`), importing only `src/setup/*`, `src/shared/*`, `src/release-notice.mjs`, and Node stdlib.
- **Install safety guards & Volta support (via `src/shared/install-kind.mjs`):**
  - Never mutate a Git checkout (`packageRoot/.git` present), PyPI `pdd-cli` wheel (`site-packages/(pdd|pdd_cli|pdd-cli)` or `dist-packages/...` → advise `pip install -U pdd-cli`), `pnpm` global store (`/.pnpm/` or `/pnpm/global/` → advise `pnpm add -g @promptdriven/pdd@latest`), ephemeral `npx` cache (`/_npx/` → advise `npm install -g @promptdriven/pdd && pdd setup`), local project `node_modules/` (parent directory holds `package.json` → advise `npm install @promptdriven/pdd@latest`; never check `prefix/.git` because Apple Silicon Homebrew `/opt/homebrew/.git` is a valid global npm prefix!), or foreign/root-owned prefix.
  - Accept both user-owned `npm-global` and user-owned Volta (`<voltaHome>/tools/image/packages/(@promptdriven/pdd|pdd)(?:/...)?`) installations.
  - Return a clear 4-part remediation message on refusal and exit `1` without invoking `npm`.
- **Volta-safe upgrade and legacy unscoped migration:**
  - For Volta installations, invoke `<voltaHome>/bin/npm` (or `<voltaHome>/bin/npm.cmd` on Windows) **without `--prefix`** and with `_VOLTA_TOOL_RECURSION`, `VOLTA_UNSAFE_GLOBAL`, and `npm_config_prefix` stripped from child env (and `VOLTA_HOME` set to `<voltaHome>`) so Volta updates `tools/user/{packages,bins}/*.json` and `<voltaHome>/bin/` shims atomically.
  - When a Volta install is legacy unscoped `pdd` (`packages/pdd`), trigger migration even at the same version: first uninstall `pdd` via Volta `npm uninstall -g --ignore-scripts --no-audit --no-fund pdd` (no `--prefix`), then install `@promptdriven/pdd` (no `--prefix`), and re-resolve `targetPkgRoot` under `<voltaHome>/tools/image/packages/@promptdriven/pdd`.
  - All manual recovery commands for Volta omit `--prefix` (never print `--prefix <volta-image-dir>`).
- **npm-first install with GitHub tag fallback:**
  - On the release channel (`main: false`), resolve the newest version via `pickLatestRelease` and install `@promptdriven/pdd@<version>` first. If npm registry install fails (and is not an `EEXIST` collision), fall back once to `github:promptdriven/pdd#<tag>`.
  - On `--main`, resolve the 40-hex commit SHA of `promptdriven/pdd` `main` and install `github:promptdriven/pdd#<sha>`.
- **Clean `EEXIST` remediation (no legacy backup/rollback):**
  - When `npm install` fails with `EEXIST`, print a clear 4-part remediation naming the conflicting `bin/pdd` path, the `npm uninstall -g pdd` fix, and the retry command without running destructive backup/rollback logic.
- **Skill refresh and honest reporting:**
  - Clear stale `release-check.json` under `resolvePddStateBase(env)`.
  - Run `syncOwnedUserSkills({ packageRoot: targetPkgRoot, home, claudeConfigDir, codexHome, stateRoot, force: true, onError })`.
  - Report updated skill folders, preserved/skipped unmarked stale folders (via `findSkills`), and any failed folders accurately without misleading `0 skills` wording.
- **Proactive dual-install and login-shell check:**
  - After upgrade and skill refresh, invoke `formatHostInstallWarnings` (from [PATH & host install diagnostics](path-diagnostic.prompt.md), or optional injected `ports.hostInstallWarnings`) fail-open and write any competing-install or login-shell split warnings (with exact cleanup commands) to `stderr` without altering the upgrade exit code.

## Dependencies

- Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before changing this prompt.
- Uses [install kind](install-kind.prompt.md), [skills install](skills-install.prompt.md), [PATH & host install diagnostics](path-diagnostic.prompt.md), [cached release notice](release-notice.prompt.md), and Layer-0 `src/shared/{state-dir,package-root}.mjs`.
