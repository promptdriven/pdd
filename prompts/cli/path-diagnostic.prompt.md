# PATH, multi-manager, and cross-shell install diagnostics

Own `src/path-diagnostic.mjs`, exporting:

- `pathDiagnostic({ packageRoot, cwd, env, mode })`
- `diagnoseHostInstalls(options, ports)`
- `formatHostInstallWarnings(options, ports)`
- `formatDualInstallWarnings(diagnosis, options)`
- `resolveCanonicalPddTarget(binPath, options)`
- `shortenHomePath(targetPath, home)`

All exported functions are strictly read-only: they never write files, delete binaries, modify `PATH`, ask questions, or invoke package managers.

## Domain decisions

- **Backward-compatible fast `pathDiagnostic({ packageRoot, cwd, env, mode })`:**
  - Read this package's version and executable identity locally. Discover executable `pdd` paths in order with `which -a pdd`; if `which` is unavailable, enumerate executable files in `PATH` with the same relative/empty-directory semantics. Deduplicate repeated paths; recognize symlinks to this `pdd` executable, matching Volta shims, and matching shell/cmd wrapper shims (such as `pnpm` global wrappers) as the same program.
  - Probe only a shadowed first candidate with `--version` (bounded to 2 seconds and 64 KiB, with both `PDD_PATH_PROBE=1` and `PDD_PATH_DIAG_DONE=1` recursion guards). Sanitize child text to one readable line.
  - **Quiet when clean:** for `mode: 'version'` and `mode: 'setup'`, emit `[]` when `PATH` cleanly selects this `pdd` with no conflict, no extra distinct `pdd`, and no unscoped npm `"pdd"` package. For `mode: 'workflow'`, emit a one-line shadowing warning only when shadowed (including `"$PDD_BIN"`).
  - **Fast `--version` path:** `pathDiagnostic` NEVER spawns login shells (`zsh -lc` / `bash -lc`) or scans unrelated version-manager directories so `pdd --version` stays instant.
  - **Unscoped npm `"pdd"` remediation:** when an unrelated or legacy unscoped npm `"pdd"` package is detected next to a `PATH` directory, recommend `npm uninstall -g pdd && npm install -g @promptdriven/pdd` (never `--force` and never the old `github:promptdriven/pdd` URL).
- **Universal host install probing (`diagnoseHostInstalls(options, ports)`):**
  - Accepts `options`: `{ packageRoot, currentBin, cwd, env, home, checkLoginShells = true, probeTimeoutMs = 1500, systemRoots, loginShells, maxVersionDirs = 32, maxProbes = 12 }` plus optional injected ports (`fs`, `spawnSync`, `platform`, `uid`, `homedir` accepted on either `ports` or `options`).
  - **Pure filesystem discovery (zero subprocesses for discovery):** probes `PATH` entries in order plus common multi-manager roots:
    - Volta (`$VOLTA_HOME/bin/pdd`, `~/.volta/bin/pdd`, and Volta `tools/image/packages/{@promptdriven/pdd,pdd}`)
    - nvm (`$NVM_DIR/versions/node/*/bin/pdd`, `~/.nvm/versions/node/*/bin/pdd`, bounded to `maxVersionDirs` sorted newest-first)
    - fnm (`$FNM_DIR`, `~/.local/share/fnm`, `~/Library/Application Support/fnm` under `node-versions/*/installation/bin/pdd`, `aliases/*/bin/pdd`, `current/bin/pdd`, bounded)
    - mise & asdf (`$MISE_DATA_DIR/shims/pdd`, `~/.local/share/mise/shims/pdd`, `installs/node/*/bin/pdd`; `$ASDF_DATA_DIR/shims/pdd`, `~/.asdf/shims/pdd`, `installs/nodejs/*/bin/pdd`, bounded)
    - pnpm (`$PNPM_HOME/pdd`, `~/Library/pnpm/pdd`, `~/.local/share/pnpm/pdd`)
    - Global npm / Homebrew / user bin (`~/.npm-global/bin/pdd`, `$NPM_CONFIG_PREFIX/bin/pdd`, `~/.yarn/bin/pdd`, `~/.local/bin/pdd`, `/usr/local/bin/pdd`, `/opt/homebrew/bin/pdd`)
    - Python / conda / uv / pipx (`~/miniconda3/bin/pdd`, `~/anaconda3/bin/pdd`, `~/miniforge3/bin/pdd`, `~/mambaforge/bin/pdd`, `/opt/homebrew/anaconda3/bin/pdd`, `$CONDA_PREFIX/bin/pdd`, `$VIRTUAL_ENV/bin/pdd`, `~/.local/share/uv/tools/pdd-cli/bin/pdd`, `~/.local/pipx/venvs/pdd-cli/bin/pdd`).
  - **Deduplication without false alarms:** resolve realpaths (case-insensitively on `win32`) AND recognize matching Volta shims (prioritizing `<binParent>` / `$VOLTA_HOME` / `~/.volta` ahead of Homebrew Cellar `volta-shim` targets via `<voltaHome>/tools/user/bins/pdd.json` or `tools/image/packages/...`), pnpm/npm POSIX (`$basedir` / `${basedir}`) and Windows (`%dp0%` / `%~dp0`) wrappers, and mise/asdf shims (including custom `$MISE_DATA_DIR` / `$ASDF_DATA_DIR`) targeting the currently running install. Merge aliases pointing to the same canonical target while preserving PATH order and `isCurrent`. Use the same canonical target resolution in fast `pathDiagnostic` so clean Volta/pnpm installs stay quiet on `--version` and `setup`.
  - **Install kind classification:** classify each discovered binary into `'npm-global'`, `'volta'`, `'pnpm'`, `'homebrew'`, `'pypi'`, `'legacy-unscoped-pdd'`, `'git-checkout'`, or `'other'`, reusing [install kind](install-kind.prompt.md) plus Homebrew formula (`Cellar/pdd`) and Python/conda/shebang detection (keeping `Cellar/node/.../node_modules/@promptdriven/pdd` as `'npm-global'`, not `'homebrew'`).
  - **Bounded version lookup and recursion guard:** read `package.json` version directly with zero subprocesses whenever available; otherwise probe `--version` (skipping direct Windows `.cmd`/`.bat` spawns) with `timeout: probeTimeoutMs` (default `1500` ms, clamped `100..5000`), `maxBuffer: 65536`, `stdio: ['ignore', 'pipe', 'pipe']`, and `PDD_PATH_DIAG_DONE: '1'` + `PDD_PATH_PROBE: '1'` + `PDD_NO_UPDATE_CHECK: '1'`. When `env.PDD_PATH_DIAG_DONE === '1'` or `env.PDD_PATH_PROBE === '1'`, skip all subprocess probes (both version probes and login-shell probes).
  - **Login non-interactive subshell parity:** when `checkLoginShells` (accepted on `options` or `ports`) is `true` and recursion guards are absent, probe available POSIX login shells (`/bin/zsh`, `/bin/bash` by default; skipped on `win32` or when shell binary is absent) with a constant argv `['-lc', LOGIN_PROBE_CMD]` (zero path or user-data interpolation into shell strings; rejects aliases/functions in-shell!) and bounded `probeTimeoutMs` (`1500` ms). Require exit status `0`, the tagged `__PDD_WHICH__=` marker with a path value, and (when `spawnSync` is not injected) an existing executable file. Resolve the reported path using the same deduplication rules and mark `status` as `'match'`, `'mismatch'`, `'not-found'`, `'timeout'`, or `'skipped'`. Any `'mismatch'` records the conflicting path, version, kind, and safe remediation command.
  - **Actionable single-command remediation & output sanitization:** compute a copy-pasteable, shell-safe cleanup command for every non-current install based on kind (`volta uninstall @promptdriven/pdd` / `volta uninstall pdd`, `npm uninstall -g @promptdriven/pdd [--prefix '...']`, `npm uninstall -g pdd [--prefix '...']`, `pnpm remove -g @promptdriven/pdd`, `brew uninstall pdd`, `uv tool uninstall pdd-cli`, `pipx uninstall pdd-cli`, `pip uninstall pdd-cli`, Git-checkout PATH removal hint, or `rm -f <quoted-path>`). Never wrap `~` inside single quotes; quote paths safely (using ANSI-C `$'...'` escaping when control characters are present) and strip ANSI/control characters from all formatted warning lines. Handle missing or empty `$HOME` cleanly without scanning relative `cwd` paths.
- **Proactive warnings (`formatDualInstallWarnings` & `formatHostInstallWarnings`):**
  - Return `[]` when `diagnosis.hasConflict` is `false`.
  - Otherwise return concise warning lines naming each duplicate install, login-shell split, or unscoped npm `"pdd"` conflict with its single-command remediation and a pointer to `pdd doctor`. Used by `pdd setup` and `pdd upgrade` (never by `pdd --version`).

## Public contract

`diagnoseHostInstalls(options, ports)` returns:

- `current`: `{ path, realPath, packageRoot, version, kind, prefix, packageName }`
- `installs`: array of deduplicated install records `{ path, aliases, realPath, version, versionTimedOut, kind, prefix, packageName, source, onPath, pathIndex, isCurrent, shadowsCurrent, remediation }`
- `pathSelected`: `{ path, realPath, version, isCurrent, kind } | null`
- `shadowedOnPath`: boolean
- `duplicates`: array of non-current install records
- `unscopedNpm`: `{ foreign: string | null, legacy: string | null, remediation: string | null }`
- `loginShells`: array of `{ shell, name, status, resolvedPath, realPath, version, kind, remediation }`
- `shellSplits`: array of login shell records where `status === 'mismatch'`
- `hasConflict`: boolean (`shadowedOnPath || duplicates.length > 0 || shellSplits.length > 0 || Boolean(unscopedNpm.foreign || unscopedNpm.legacy)`)

## Dependencies

- Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before changing this prompt.
- Uses [install kind](install-kind.prompt.md) (`classifyInstallKind`, `quoteShellArg`, `resolveInstalledRoot`) and `src/shared/package-root.mjs`.
- Navigation only: [CLI](pdd-cli.prompt.md), [Host doctor](doctor.prompt.md), and [CLI upgrade](cli-upgrade.prompt.md) consume these helpers.
