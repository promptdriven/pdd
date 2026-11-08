# GitHub App identity

Own `src/github-app.mjs` and the executables `bin/github-app/gh` and `bin/github-app/git`. This native
adapter supplies one installation identity to Autopilot and its chats. Preserve
personal gh login when `autopilot.github.app` is absent. An explicitly present
but invalid App setting must fail closed, before a claim, timer or chat starts.
No prompt approval or human review authority changes.

Before obtaining credentials or injecting them into a subprocess environment,
refuse App transport when the spawning Node process has child_process diagnostics
enabled, including wildcard NODE_DEBUG. Check the parent's active diagnostic mode;
clearing only the child's environment cannot protect the parent stderr. Apply this
boundary to native transport and both bundled wrappers. Refuse with the existing
github_app_invalid error and no credential disclosure. Personal mode is unchanged.

## Settings and ports

`githubAppSettings({cwd,env,fs})` returns null when no App is selected, otherwise
`{root,id,privateKeyFile}`. Read pdd.json at `PDD_GITHUB_APP_ROOT` when present,
else find it by walking cwd ancestors. `app` must be an object with a positive
numeric App `id` (integer or decimal string) and an absolute `privateKeyFile`.
The key must resolve to a regular RSA private key outside the checkout. Reject
unreadable files and malformed settings without displaying their contents.
A bound chat whose App setting disappears fails rather than changing identity.
A JSON syntax refusal also carries `configurationRoot`, the absolute directory of
the unreadable JSON configuration, without its contents. This permits a manual
repair chat to bind the refusing transport while retaining the same error code;
it does not permit a native GitHub call or automatic startup to bypass validation.

`createGithubApp(settings, ports)` returns `{credentials(),preflight()}`.
Ports are `fs` (node:fs), `fetch` (global fetch), `now` (Date.now), `env`
(process.env), and `apiUrl` (https://api.github.com; override only by an injected
port for a local fake server). Effects remain behind these ports. Credentials
returns `{token,expiresAt,identity,repository,bot}` for internal transport only;
`identity` is `app:APP_ID:installation:INSTALLATION_ID`, `repository` is the
lowercase origin owner/name and `bot` is the App slug with `[bot]`. Read the
origin through the injected `exec` runner, using the shared GitHub origin parser.

Sign an RS256 JWT with iss the configured App id, iat 60 seconds before now,
and exp nine minutes after now. Get the repository installation with
GET /repos/OWNER/REPO/installation; verify the App id and require Issues,
Pull requests and Contents write, and Metadata, Checks, Commit statuses and
Actions read. Mint a repository-scoped token with POST
/app/installations/ID/access_tokens and repositories:[NAME]. Trust no token
with an invalid expiry or less than five minutes left. Cap reuse at one hour.
Refresh before the final five minutes; coalesce concurrent refresh in one process.

Keep the token only in process memory and a dedicated private credential cache
under HOME/.cache/pdd/github-app, outside the checkout (directory 0700, files 0600, owned by the current
user, no symlinks). The cache is separate from workflow state, logs and packets.
Key it by the App, repository and private key bytes so rotation cannot reuse an
old credential. Atomic replacement permits concurrent processes to mint safely.
On read corruption refresh; on an unsafe cache directory fail. Never emit a
JWT, PEM or installation token in output, errors, arguments, state or logs.
Do not use remote error bodies in diagnostics.

`preflight()` returns `{identity,repository,bot,rate}` after GET /repos/O/R and
GET /rate_limit succeed with the installation token. `rate` is
the gh-style included response text for the rate_limit reply. The launcher
records its limit headers before evaluating the budget. Failure gives an
Error with code `github_app_invalid` and an actionable reason identifying the
failed stage or HTTP status. Never fall back to the person's login.

`githubAppRunner(exec, ports)` returns a process runner. Local Git commands and
other programs keep their behavior. Personal calls keep exact process options
when PATH has no wrapper. App calls authenticate gh and Git push, fetch, pull,
clone and ls-remote. The child gh also receives Git authentication because PR
creation can push through a Git subprocess.

Set GH_TOKEN and GITHUB_TOKEN in the child only. For Git, supply a host-scoped
HTTPS Authorization Basic header (x-access-token plus token) through environment
config, overriding inherited authorization and credential helpers. The App header
must win for the actual GitHub URL, including more-specific path or user scopes
in repository, included, or environment config, and clone's own `-c`/`--config`
options (which take effect in the destination before its first request).
Clone must not acquire headers from the invoking checkout's local config or
includes selected by that checkout; clone does not inherit those settings.
Read effective Git config through
the injected exec port in the command's directory and Git option context; fail
closed with a safe App error if that read fails. Override each GitHub header scope
only in the child, retaining its non-Authorization headers and unrelated config.
The same overrides must reach Git started by gh. Keep stored config unchanged.
Preserve unrelated environment config entries. Rewrite GitHub SSH URL prefixes to HTTPS
only for the child, refuse HTTP redirects and disable credential prompts.
Strip the wrapper directory from child PATH for both gh and Git, including local
Git calls, to avoid recursion. Forward input and other process options.

In App mode, disable inherited Git tracing and curl verbosity before any Git
configuration probe or authenticated child runs. Override trace2 targets from
Git config as well as environment settings, including config and environment
dumps, and force HTTP trace redaction. Apply this to direct Git, both worker
wrappers and Git started by gh. Git must not write the token or its Basic
encoding to trace files; output redaction cannot protect files Git writes itself.
Keep the parent environment, stored Git config and personal-mode tracing intact.

Redact the token and its Basic encoding from stdout, stderr and thrown errors;
discard raw exception details. Reject gh auth token and credential-changing auth
commands. Annotate outcomes and transport errors with non-secret `githubIdentity`
(the canonical installation key) and `githubBot` (the verified installation's bot
login). These are separate values: budgets use the key; comment ownership uses
the login. Never retry a write
after a refusal.

`githubAppEnvironment({root,env})` returns only non-secret PATH and
PDD_GITHUB_APP_ROOT for a bound chat, placing the bundled wrapper directory first.
Both wrappers use the same runner on every call, read current settings and
refresh the shared credential cache. They forward stdin and redacted output,
keep the child exit status, and print only a safe error on failure. Standalone
gh calls use the same GitHub accounting as pdd. There is no command to print a
credential. A long chat never receives a fixed installation token.

## Dependencies

- [GitHub worktree identity](workflow-worktree.prompt.md): required native
  generation and verification context for `githubOriginRepository`.
