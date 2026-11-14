# Cached CLI release notice

Own `src/release-notice.mjs`. Export `parseReleaseVersion(value)`, `isNewerRelease(candidate, current)`, `pickLatestRelease(payload)` and `checkReleaseNotice({currentVersion, isVersionCommand, interactive, env}, ports)` (#2710). Tell a person running an older installed `pdd` when a newer GitHub release is available, without slowing down commands, changing stdout, or making network calls in CI, agent sessions, or non-interactive runs.

## Version comparison

`parseReleaseVersion` extracts `MAJOR.MINOR.PATCH` from `X.Y.Z`, `vX.Y.Z` or `alpha-vX.Y.Z` (returning `null` when malformed). `isNewerRelease(candidate, current)` compares numeric `MAJOR`, `MINOR`, `PATCH` parts and returns `true` only when `candidate` is strictly greater than `current`. `pickLatestRelease(payload)` accepts a GitHub releases array (or single release object), excludes drafts and malformed tags, sorts by `published_at` descending so prerelease-only repositories work without 404s, and returns `{tag, version}` or `null`.

## Cache and network budget

- Store the cache at `<stateHome>/pdd/release-check.json`, where `stateHome` is `ports.stateHome`, `env.XDG_STATE_HOME`, or `<home>/.local/state`. Write atomically with mode `0600` (directory mode `0700`).
- Return `null` immediately with no disk write or network call when `env.PDD_NO_UPDATE_CHECK === '1'`, `env.PDD_PATH_PROBE === '1'`, `env.CI`, `env.PDD_AGENT_SESSION`, or `env.PDD_AUTOPILOT_CONTEXT` is set.
- Read any saved cache file first. Never write to disk when only reading an existing cache on a non-interactive check.
- Refresh from `https://api.github.com/repos/promptdriven/pdd/releases?per_page=10` (1-second timeout, `Accept: application/vnd.github+json`) at most once every 24 hours (`86400000` ms), and only when either `ports.fetchLatestRelease` is injected or `interactive` is true outside `env.NODE_TEST_CONTEXT`.
- On a network, timeout, HTTP, JSON, empty, or draft-only failure, record a 1-hour retry backoff (`checkedAt = now - 23 * 3600 * 1000`) and never throw or change the command exit code.

## Notice rule

When the cached or freshly fetched `latestVersion` is newer than `currentVersion`:
- Format: `A newer PDD release is available (CURRENT -> LATEST). To update, run: npm install -g github:promptdriven/pdd && pdd setup`
- On `isVersionCommand: true`, always return the line.
- On other interactive commands (`interactive: true`), return the line at most once every 24 hours (`notifiedAt`), updating `notifiedAt` in the cache.

## Dependencies

- Read the full [Prompting guide](../../docs/prompting-guide.md) before authoring. Follow [public alpha boundary](public-boundary.prompt.md).
