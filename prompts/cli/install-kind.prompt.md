# Global installation kind and Volta detection

Own `src/shared/install-kind.mjs`. Export `quoteShellArg(text)`, `resolveVoltaNpmBin(voltaHome, ports)`, `scrubVoltaEnv(env, voltaHome)`, `classifyInstallKind(packageRoot, ports)`, `detectGlobalInstallPrefix(packageRoot, ports)`, `isLegacyUnscopedPddDir(pkgDir, fs, uid)`, `hasLegacyUnscopedPdd(prefixOrInstall, ports)`, `resolveInstalledRoot(installOrPrefix, fallbackRoot, fs)`, `resolveInstalledBinEntry(pkgRoot, fs)`, `npmCommandForInstall(install, action, spec, env)`, `formatNpmInstallCommand(install, spec)`, and `formatNpmUninstallCommand(install)`.

## Domain decisions

- **Layer-0 shared module:** imports only Node standard library (`node:fs`, `node:path`) so both `src/setup/cli-upgrade.mjs` and `src/autopilot-update.mjs` share one source of truth with zero layer violations.
- **Install safety guards and precedence (`classifyInstallKind`):**
  1. Reject non-string, missing, or non-directory `packageRoot` (`kind: 'invalid'`).
  2. Git checkout (`packageRoot/.git` exists) → `kind: 'git-checkout'`.
  3. PyPI `pdd-cli` wheel (`site-packages` or `dist-packages` containing `pdd`, `pdd_cli`, or `pdd-cli`) → `kind: 'pypi'`.
  4. `pnpm` global store (`/.pnpm/` or `/pnpm/global/`) → `kind: 'pnpm'`.
  5. Ephemeral `npx` cache (`/_npx/`) → `kind: 'npx'`.
  6. **Volta-managed global install (checked BEFORE generic `node_modules`!):** match `<voltaHome>/tools/image/packages/(@promptdriven/pdd|pdd)(?:/.*)?` (case-sensitive package path, preserving native path separators in `voltaHome`). Verify user ownership (`uid`) of both `realPackageRoot` and `voltaHome` (else `kind: 'unowned-prefix'`). Resolve `npmBin` to `<voltaHome>/bin/npm` on POSIX or `<voltaHome>/bin/npm.cmd` (falling back to `npm.exe` if present) on Windows (`platform === 'win32'`). Return `{kind: 'volta', prefix: voltaHome, voltaHome, npmBin, packageName, isLegacyUnscoped: packageName === 'pdd', realPackageRoot}`.
  7. Classic global npm (`<prefix>/[lib/]node_modules/(@promptdriven/pdd|pdd)`): reject local project installs whose `<prefix>/package.json` exists (`kind: 'local-project'`; never inspect `<prefix>/.git` so Apple Silicon Homebrew `/opt/homebrew` remains valid), verify user ownership (`uid`) of both `realPackageRoot` and `<prefix>` (else `kind: 'unowned-prefix'`), and return `{kind: 'npm-global', prefix, realPackageRoot}`.
  8. Anything else returns `kind: 'unknown'`.
- **Backward-compatible `detectGlobalInstallPrefix`:**
  - Returns `{prefix, realPackageRoot}` for `'npm-global'`, the full Volta install descriptor (`{kind: 'volta', prefix, voltaHome, npmBin, packageName, isLegacyUnscoped, realPackageRoot}`) for `'volta'`, and `null` for all other kinds.
- **Volta execution and env scrubbing:**
  - `scrubVoltaEnv(env, voltaHome)` returns a cloned environment object with `_VOLTA_TOOL_RECURSION`, `VOLTA_UNSAFE_GLOBAL`, and any case-variant of `npm_config_prefix` deleted, and `VOLTA_HOME` set to `voltaHome`.
  - `npmCommandForInstall(install, action, spec, env)` invokes `<voltaHome>/bin/npm` (or `npm.cmd`) with `[action, '-g', '--ignore-scripts', '--no-audit', '--no-fund', spec]` (NEVER `--prefix`) and scrubbed env for `'volta'`, and `npm` with `[action, '-g', '--prefix', install.prefix, '--ignore-scripts', '--no-audit', '--no-fund', spec]` for `'npm-global'`.
  - `formatNpmInstallCommand` and `formatNpmUninstallCommand` omit `--prefix` for Volta installs and single-quote `--prefix '<prefix>'` for classic npm-global installs.
- **Legacy unscoped `pdd` and post-install root resolution:**
  - `hasLegacyUnscopedPdd` checks classic `<prefix>/[lib/]node_modules/pdd` and Volta `<voltaHome>/tools/image/packages/pdd[/[lib/]node_modules/pdd]` directories via `isLegacyUnscopedPddDir` (real non-symlink user-owned directory, no `.git`, `package.json` `"name": "pdd"` owning regular file `bin/pdd.mjs`).
  - `resolveInstalledRoot` checks Volta image paths (`@promptdriven/pdd` before `pdd`) for Volta installs and classic `[lib/]node_modules/` paths for npm-global installs.
  - `resolveInstalledBinEntry(pkgRoot, fs)` reads `package.json`'s `bin` (`bin.pdd` or string `bin`, defaulting to `bin/pdd.mjs`) under `pkgRoot`, rejects absolute paths or `..` traversal/symlinks escaping `pkgRoot`, and returns the resolved path when it exists as a regular file inside `pkgRoot`, else `null`.

## Dependencies

- Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before changing this prompt.
