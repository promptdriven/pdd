# Global PDD CLI updater

Own `src/setup/cli-upgrade.mjs`. Export `detectGlobalInstallPrefix(packageRoot, ports)`, `classifyInstallKind(packageRoot, ports)`, `resolveReleaseUpgradeTarget(options)`, `resolveMainCommitTarget(options)`, and `runCliUpgrade(options, ports)`.

## Domain decisions

- **Zero Autopilot dependency:** lives in Layer-1 `setup` (`src/setup/cli-upgrade.mjs`), importing only `src/setup/*`, `src/shared/*`, `src/release-notice.mjs`, and Node stdlib.
- **Install safety guards (`classifyInstallKind` / `detectGlobalInstallPrefix`):**
  - Never mutate a Git checkout (`.git` present), PyPI `pdd-cli` wheel (`site-packages/pdd_cli` or `dist-packages/pdd_cli` → advise `pip install -U pdd-cli`), `pnpm` global store (`/.pnpm/` or `/pnpm/global/` → advise `pnpm add -g @promptdriven/pdd`), ephemeral `npx` cache (`/_npx/` → advise `npm i -g @promptdriven/pdd`), local project `node_modules/` (parent directory holds `package.json` or `.git` → advise `npm install @promptdriven/pdd@latest`), or foreign/root-owned prefix.
  - Return a clear 4-part remediation message on refusal and exit `1` without invoking `npm`.
- **npm-first install with GitHub tag fallback:**
  - On the release channel (`main: false`), resolve the newest version via `pickLatestRelease` and install `@promptdriven/pdd@<version>` via `npm install -g --prefix <prefix> --ignore-scripts --no-audit --no-fund @promptdriven/pdd@<version>` first. If npm registry install fails (and is not an `EEXIST` collision), fall back once to `github:promptdriven/pdd#<tag>`.
  - On `--main`, resolve the 40-hex commit SHA of `promptdriven/pdd` `main` and install `github:promptdriven/pdd#<sha>`.
- **Clean `EEXIST` remediation (no legacy backup/rollback):**
  - When `npm install` fails with `EEXIST`, print a clear 4-part remediation naming the conflicting `bin/pdd` path, the `npm uninstall -g pdd` fix, and the retry command without running destructive backup/rollback logic.
- **Skill refresh and honest reporting:**
  - Clear stale `release-check.json` under `resolvePddStateBase(env)`.
  - Run `syncOwnedUserSkills({ packageRoot: targetPkgRoot, home, claudeConfigDir, codexHome, stateRoot, force: true, onError })`.
  - Report updated skill folders, preserved/skipped unmarked stale folders (via `findSkills`), and any failed folders accurately without misleading `0 skills` wording.

## Dependencies

- Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before changing this prompt.
- Uses [skills install](skills-install.prompt.md), [cached release notice](release-notice.prompt.md), and Layer-0 `src/shared/{state-dir,package-root}.mjs`.
