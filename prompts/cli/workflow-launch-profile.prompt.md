# Run chat launch profiles

Own `src/workflow-launch-profile.mjs`. A launch profile selects settings for the
next chat without changing the person's account configuration. Preserve existing
agent kind, account isolation, full-access and agents.json login behavior.

`launchProfile(run, chat?)` returns a fresh profile with exactly `agent`,
`configDir` (folder or null), `model` (string or null), `herdrAgentName` (name
prefix), and `codexThreads` (integer or null). Prefer the chat's saved profile,
else the run's profile. A legacy chat without a snapshot uses its own agent and
configDir, with unset model and threads. A legacy run uses its saved fields.
Unset model and threads leave native defaults in effect. Default name prefix is
`pdd-` plus the first 12 hex SHA256 characters of repository and run identity.
`chatAgentName(profile, area, run)` appends `-` and the first six hex SHA256
characters of repository, run identity and area. Thus peer areas and independent runs have different names, while a
replacement of one area's closed chat keeps its name.

`selectLaunchProfile({run, configDir, model, herdrAgentName, codexThreads}, ports)`
merges explicitly supplied values into the run profile. Model must be a nonempty
trimmed string without controls or a leading dash. Name prefix must match
`[a-z][a-z0-9_-]{0,24}`. A requested Codex thread limit is a whole decimal number
from 4 through 8; reject it for other agents. Malformed options throw
`invalid_launch_profile` before effects. Omitted values retain saved settings.

When a Codex thread limit is selected, read only that account's `config.toml`
through `ports.profileFs` (default node:fs), using the expanded explicit folder or
`HOME/.codex`. Parse TOML with the bundled parser. Preserve a higher positive
integer `features.multi_agent_v2.max_concurrent_threads_per_session` by taking
the maximum. Missing file means no account override. Malformed TOML, invalid
configured limits, and other read errors refuse with `invalid_launch_profile`;
never include file contents or credentials in an error. Read settings only when
selecting a profile; snapshots pin the effective limit for later native effects.
Never read authentication files, sign out, reset usage or write account files.

`validLaunchProfile(value)` checks the saved shape and types; saved effective
Codex limits may exceed 8 to retain a person's higher setting. Null model and
threads represent omitted options. A profile contains no login values.

## Dependencies

- Node crypto supplies deterministic SHA256 names; filesystem reads use the
  injected profileFs port. The bundled `src/vendor/smol-toml/parse.js` supplies
  TOML parsing; no external service or model is required.

Native module only. Prompt interpretation is not configured for these effects.
