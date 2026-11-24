# Autopilot first-start doctor

Own `src/autopilot-doctor.mjs`. Export asynchronous `runAutopilotDoctor(input,
ports = {})`. Input carries cwd, packageRoot and env, and an optional saved profile binding
(agent id/kind, home, definitionHome, configHome). Preserve existing launcher
behavior except the authorized required preflight before startup effects.
The doctor is read-only: no GitHub writes, agent generation, interpreter jobs,
state files, timer changes, workspace allocation, cleanup or approvals.

The core engine is the only Autopilot engine. Its jobs run headless, so doctor
has no Herdr check and makes no Herdr call. The launcher can also pass `engine`,
`coordinatorPaneId` and a `coordinatorHealth` port. Doctor ignores them.

Return {exitCode, message, checks}. Checks are ordered records with exactly id,
status (pass, warn, fail), detail and fix. Every record has a fix, also a pass
record. Exit 1 for critical preflight failures — unsupported Node (`< 22.20.0`),
missing `git`, missing `gh` (`github-cli`), corrupt `agents.json` (`agent-config`),
missing or signed-out agent (`agent` / `agent-signin`), or unsupported OS
(`platform`) — and exit 0 otherwise. Non-critical advisory findings (`path`,
`repository`, `github-auth`, `github-permission`, `merge-method`, `merge-rules`,
`git-identity`, `agent-usage`, `codex-sandbox`, `setup-block`, `setup-skills`,
`retired-skills`, `setup-mode`, `settings-github`, `draft-prompts`, `interpreter`,
`user-timers`, `linger`, `sleep`) report WARN with a fix command and permit
readiness. Preserve native start admission,
cleanup, parking and recovery decisions. Start displays advisory lines and
continues to its native guards; doctor advisory findings must not add other refusals.
Message has one line per record. A pass line is `PASS id: detail`: it shows no
fix. A warn or fail line is `STATUS id: detail; fix: command`.
Collapse control characters and newlines in details. Never echo auth payloads,
tokens or provider diagnostics. Each fix is a concrete shell command, safely
quoted for paths, with a diagnostic command for successful checks or conditions
that need inspection. Report unavailable evidence, never invent a successful read.

Resolve the selected definition before prerequisite probes. Load definitions from
saved definitionHome when a profile is supplied, restrict selection to its agent
id/kind, and preserve saved HOME and provider config home after definition overrides.
Otherwise merge the selected definition's env over the caller environment; for a
Codex definition without an explicit saved `profile.configHome`, explicit `CODEX_HOME`, or explicit `poolPath` (`input.pool`), bind
`CODEX_HOME` to `pddManagedCodexHome(env)` whenever
`isCloudAccountsActive({env, poolPath: input.pool, provider: "codex"}, {fs: files})` is true and
`managedCodexAuthPath(env)` exists as a regular non-symlink file on disk (inside a non-symlink directory) so Cloud-only
teammates (including `pdd autopilot start --agent codex`) pass `codex login status`, `readCodexLimits`, and launcher startup without emitting a `CODEX_HOME=<managed>` login fix command when sign-in fails. Likewise, for a Claude definition without an explicit saved `profile.configHome`, explicit `CLAUDE_CONFIG_DIR`, or explicit `poolPath`, when `isCloudAccountsActive({env, poolPath: input.pool, provider: "claude"}, {fs: files})` is true and `managedClaudeSettingsPath(env)` exists as a regular non-symlink file on disk (inside a non-symlink directory), probe `claude --settings <managedClaudeSettingsPath(env)> auth status --json` (falling back to plain `claude auth status --json` if not ready, and including `--settings <managedClaudeSettingsPath(env)>` in the passing diagnostic command when managed settings succeeded) so isolated Cloud Claude accounts pass `doctor` and `autopilot start` without touching `~/.claude/settings.json`. Use
this invocation environment for every prerequisite, including PATH, GitHub,
provider sign-in, usage, skills, interpreter and scheduling. Claude user skills
live under CLAUDE_CONFIG_DIR/skills when set; HOME overrides select user roots.
Keep the caller environment unchanged. An agents.json read or parse failure fails with its own `agent-config` check naming the actual file path and an editor repair command; never echo raw errors or configuration values.

Export resolveAutopilotAgent(input, ports = {}) for the launcher's same selection
policy. Return agent (definition or null), preferred (definition or undefined),
installed (probed definitions), env (effective invocation environment), and
configurationError (caught load error or null). Program/file/config selection ports
match the doctor. A saved binding wins over conflicting definition profile values.

Printed commands must target that invocation environment. Compare it with the
caller environment for HOME, PATH, CODEX_HOME, CLAUDE_CONFIG_DIR, GEMINI_CLI_HOME,
ANTIGRAVITY_APP_DATA_DIR and each override name of the selected definition. Bind only the names that
differ: an explicit unset (`-u NAME`) when the caller has NAME and the invocation
environment does not, and `NAME=value` when the value differs. Such a fix is
`env BINDINGS /bin/sh -c 'COMMAND'`. When no name differs, the fix is the plain
command. Non-secret values are literal and safely quoted;
credential-named bindings and URLs with credentials, query or fragment use shell
variable references, never literal secret values.
Report no raw provider/configuration error or auth payload. A failed inspection
must also name the repair action (enable a merge method, edit config, restore the
user service/session, or sign in); a status command alone is insufficient.

Check these boundaries in order and continue after failures:
- PATH: first executable pdd resolves to packageRoot/bin/pdd.mjs and its help
  advertises autopilot. A different install warns even at the same
  version; include its path and safe version. Fix with an absolute Node plus
  this CLI doctor command, so source checkouts work too.
- Node >=22.20.0, Git present, and `gh` present are critical (`fail` when absent/unsupported); Git checkout, `gh` auth, write permission (`ADMIN`, `MAINTAIN` or `WRITE`), and enabled merge methods warn when missing. Read effective
  rules for the default branch separately (`repos/REPO/rules/branches/BRANCH`).
  When `gh repo view` confirmed `REPO` and `BRANCH`, an HTTP 403 reply stating
  `Upgrade to GitHub Pro or make this repository public` or an HTTP 404 reply
  (when `gh` sign-in passed or the reply states `Branch not protected`) means no
  branch rulesets are enforced (`pass` with `Branch rules: none...; required
  reviews and checks still apply` and the `gh api` read command, never `gh auth
  login`). Other unreadable rules warn; list rule types and say required
  reviews/checks still apply. Do not claim merge eligibility.
- Git identity (`git-identity`): Autopilot jobs commit, so they need a name and an
  email. Read the effective `git config user.name` and `git config user.email` in
  the repository folder with the invocation environment. In that environment, a
  nonblank GIT_AUTHOR_NAME and GIT_COMMITTER_NAME also give the name, and a nonblank
  GIT_AUTHOR_EMAIL and GIT_COMMITTER_EMAIL (or EMAIL) also give the email, as Git
  reads them. A missing value warns: `Git user.name and user.email are needed for
  Autopilot commits; missing: NAMES`, where NAMES is `user.name`, `user.email` or
  both. The fix sets only the missing values, joined with ` && `:
  `git config --global user.name "Your Name"` and
  `git config --global user.email "you@example.com"`. With both values, pass with
  `Git user.name and user.email are set for Autopilot commits` and the fix
  `git config user.name && git config user.email`.
- Choose a signed-in configured agent using the launcher's normal provider order
  and invocation environment. Probe only Codex login status or Claude auth status
  --json (preserve supported agy/Gemini launcher selection through its read-only readiness/credential ports, mapping saved agy `configHome` to `ANTIGRAVITY_APP_DATA_DIR` and accepting Gemini `--version` with `GEMINI_API_KEY`, `GOOGLE_API_KEY`, `GOOGLE_GENAI_USE_VERTEXAI=true`, `GOOGLE_GENAI_USE_GCA=true`, or a `refresh_token` in `.gemini/oauth_creds.json` or `oauth_creds.json` under `GEMINI_CLI_HOME || HOME`). When sign-in is missing or signed out, fail with the installed agent's sign-in
  command. A configuration read error is advisory; it does not establish missing
  sign-in and must not create a failing agent check. Missing CLIs name their install command. Read Codex limits using its
  read-only account port. Limited and unknown are warnings. For Claude,
  unsupported read-only usage evidence is warning with `claude` and /usage advice;
  no generation call to discover allowance, and no credit/reset advice. On Linux when Codex is selected, `/proc/sys/kernel/apparmor_restrict_unprivileged_userns` is `1`, and `bwrap` is missing on `PATH`, emit an advisory `WARN codex-sandbox` with fix `sudo apt-get install -y bubblewrap` so read-only Codex sandboxes have Ubuntu's system AppArmor profile.
- Setup: require a complete PDD block in AGENTS.md or CLAUDE.md, all seven skill
  entrypoints in one selected provider's supported project/user skill root (fix:
  `pdd setup`), and valid pdd.json autopilot mode/trust. Also scan user skill roots
  (`~/.agents/skills` and `CLAUDE_CONFIG_DIR/skills` or `~/.claude/skills`) for
  unmarked non-symlink retired skill folders (`pdd-autopilot`, `pdd-check`,
  `pdd-merge` lacking `.pdd-skill.json` and carrying `pdd-skills:` in `SKILL.md`
  frontmatter): when any are present, emit a `WARN retired-skills` advisory naming
  the folder(s) and a safely quoted `mkdir -p '<root>/.pdd-retired' && mv ...`
  backup command without deleting anything or blocking readiness. Off warns; native
  start owns mode admission. Describe observe versus auto authority,
  owner/write-access trust even with [], and explicit trusted users
  in plain words. Never change mode or trust.
- GitHub settings (`settings-github`): Autopilot job worktrees and other machines
  start from GitHub, so they read `pdd.json` of the default branch there. Read it
  with `gh api repos/REPO/contents/pdd.json?ref=BRANCH` (REPO and BRANCH from the
  `gh repo view` read above; the branch is URL-encoded) and decode its base64
  content. A gh reply with `(HTTP 404)` means that GitHub has no file. The settings
  differ as [Autopilot settings on GitHub](autopilot-github.prompt.md#publish)
  defines: the effective mode or the trust names, ignoring case and order. SETTINGS
  is that prompt's `MODE, trust NAMES` form. The first matching row decides:

  | Observation | Status | Detail | Fix |
  |---|---|---|---|
  | No REPO or BRANCH, a failed read, or a file that is not a base64 JSON object | warn | `Autopilot settings on GitHub are unproved; doctor could not read pdd.json of the default branch` | `gh auth login && ` plus the read command, or `gh auth login` without REPO or BRANCH |
  | This checkout has a `pdd.json` that is not a JSON object | warn | `pdd.json in this checkout is not a JSON object; the GitHub comparison is unproved` | `vi pdd.json` |
  | No file on GitHub and none in this checkout | warn | `pdd.json is missing in this checkout and on GitHub (BRANCH)` | `pdd setup` |
  | No file on GitHub | warn | `pdd.json is only in this checkout; GitHub (BRANCH) has none, so other machines and Autopilot job worktrees do not see it` | `git add pdd.json && git commit -m "Add PDD settings" && git push`, plus ` # or pdd autopilot MODE` when the local mode is observe or auto |
  | No file in this checkout | warn | `pdd.json is only on GitHub (BRANCH): SETTINGS; this checkout has none` | `git fetch origin && git checkout origin/BRANCH -- pdd.json` |
  | The settings differ | warn | `GitHub: SETTINGS; this checkout: SETTINGS; Autopilot jobs use the GitHub copy` | The publish commands of that prompt's Check, joined with ` && `: `pdd autopilot MODE` (the local mode) when the modes differ, `pdd autopilot trust NAMES` and `pdd autopilot untrust NAME` |
  | The same settings | pass | `GitHub (BRANCH) has the same Autopilot settings: SETTINGS` | the read command |

  The read command is `gh api 'repos/REPO/contents/pdd.json?ref=BRANCH' -H
  'Accept: application/vnd.github.raw'`. A trust name or `origin/BRANCH` in a fix
  is shell-quoted unless it has only letters, digits and `_ . @ / -`. Doctor
  makes no GitHub write here: only the printed fix publishes.
- Enumerate tracked *.prompt.md and report embedded Runtime interface blocks whose
  status is not approved as advisory drafts that may need approval on first check
  (plain Markdown prompts without an embedded Runtime interface block are ready as
  is). Malformed or unreadable embedded blocks warn. Never approve them or block
  doctor solely for drafts.
- Read interpreter access through the [Runtime seam](runtime-seam.prompt.md) `health` check (`checkRuntimeHealth`)
  with the selected environment and injected gh/fetch/clock ports. No upload or job.
  Preserve its health rules, including a JSON 404 from an interpreter without the
  optional capacity endpoint. Missing auth, denial, maintenance or unreachable
  access warn with gh auth login, the platform browser sign-up command or a doctor
  retry as appropriate. Validate the origin even with an injected health port. An
  invalid PDD_RUNTIME_URL names that setting and advises an HTTPS origin or unsetting
  it to use the default, with an executable unset-and-retry command. No auth body
  or token appears in the report.
- Linux checks for a readable systemd user session; lingering is advisory for logout
  persistence and names loginctl enable-linger. macOS checks for a readable launchctl
  user domain; read pmset and warn when sleep can pause work, with caffeinate -i.
  Other platforms warn. All checks have exact commands for diagnosis or repair.

## Dependencies

- [Secret redaction](secret-redaction.prompt.md): register invocation secrets and
  gh/Gemini credentials read here in the in-memory value inventory.

- [Agent adapters](agent-adapters.prompt.md): sign-in parsers and non-model process port.
- [Agent config](agent-config.prompt.md): provider definitions and profile environment.
- Workflow worktree: canonical GitHub origin normalization.
- Workflow agents: read-only agy readiness.
- [Codex limits](codex-limits.prompt.md): read-only account usage states.
- [Multi-harness login pool](login-pool.prompt.md): `isCloudAccountsActive`, `pddManagedCodexHome`, `managedCodexAuthPath` and `managedClaudeSettingsPath` for isolated Cloud Codex and Cloud Claude sign-in detection.
- [PDD to Runtime seam](runtime-seam.prompt.md#public-contract): required `health` (`checkRuntimeHealth`) classification and `runtimeOrigin` address rules.
- [Autopilot settings on GitHub](autopilot-github.prompt.md): owns when two
  Autopilot settings differ, the `MODE, trust NAMES` form and the publish commands.
  Doctor reads GitHub with its own read-only run port, not with that module's ports.

All program, file, network, environment/platform/version/uid and account reads
have injected ports. Native defaults are adapter bindings only. Files provides
readFileSync, realpathSync, accessSync and statSync; run accepts executable,
argv and cwd/env options and returns code/stdout/stderr. agentDefinitions,
selectAgent, codexLimits, runtimeHealth, fetch and spawn are independently
replaceable ports. onSelection observes the resolved selection before checks;
the launcher uses its env and agent for startup after a passing report.
Do not use a GitHub ledger that writes reads to disk. Do not mutate arrays returned by definition ports.
