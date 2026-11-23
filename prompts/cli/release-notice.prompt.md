# Cached CLI release notice

Own `src/release-notice.mjs`. Export `parseReleaseVersion(value)`, `isNewerRelease(candidate, current)`, `pickLatestRelease(payload)` and `checkReleaseNotice({currentVersion, isVersionCommand, interactive, env}, ports)`.

## Domain decisions

- **Version parsing and semver sorting:**
  - `parseReleaseVersion(value)` extracts `MAJOR.MINOR.PATCH` from `X.Y.Z`, `vX.Y.Z`, or `alpha-vX.Y.Z` (returning `null` when malformed).
  - `isNewerRelease(candidate, current)` compares numeric `MAJOR`, `MINOR`, `PATCH` parts and returns `true` only when `candidate` is strictly greater than `current`.
  - `pickLatestRelease(payload)` excludes drafts (`draft === true`) and malformed tags. When non-prerelease (`prerelease !== true`) releases exist, exclude prereleases (`prerelease === true` and tags with semver `-prerelease` suffixes); fall back to non-draft releases only when a repository publishes exclusively prereleases. Sort remaining candidates by **semver descending** (breaking ties by `published_at` descending) so older backport releases never shadow newer versions.
- **Unified state directory and cache budget:**
  - Resolve the cache path as `join(ports.stateHome, 'pdd', 'release-check.json')` when `ports.stateHome` is explicitly injected, else `join(resolvePddStateBase(env), 'release-check.json')` (honoring `PDD_STATE_DIR` > `XDG_STATE_HOME/pdd` > `HOME/.local/state/pdd`). Write atomically (`0600` file, `0700` dir).
  - Return `null` immediately with zero writes or network calls when `PDD_NO_UPDATE_CHECK=1`, `PDD_PATH_PROBE=1`, `CI`, `PDD_AGENT_SESSION`, or `PDD_AUTOPILOT_CONTEXT` is set.
  - Refresh from `https://api.github.com/repos/promptdriven/pdd/releases?per_page=10` (1s timeout) at most once every 24h (`86400000` ms), and only when `ports.fetchLatestRelease` is injected or `interactive` is true outside `NODE_TEST_CONTEXT`. Record a 1-hour error backoff on failure.
- **Notice rule:** emit `A newer PDD release is available (CURRENT -> LATEST). To update, run: pdd upgrade` on `isVersionCommand: true` whenever newer, or at most once per 24h on interactive commands.

## Dependencies

- Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before changing this prompt.
- Uses Layer-0 `src/shared/state-dir.mjs` (`resolvePddStateBase`) and `src/shared/atomic-fs.mjs` (`writeAtomicPrivate`).
