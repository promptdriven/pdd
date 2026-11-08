# A GitHub App for Autopilot

Autopilot uses the current `gh` login by default. An organization can create one
GitHub App, **PDD Autopilot**, and install it on its repositories. With App
settings, pdd and the coordinator and worker chats use installation tokens for
`gh` calls. Claim labels, claim comments, discussion comments and PRs then show
`APP-SLUG[bot]`. An installation has its own API allowance. pdd reads that limit
from GitHub. It does not use the person's limit for the App budget.

The organization owner must create the App. pdd does not register an App or
install one on GitHub. No webhook or hosted coordinator is needed.

## Create and install the App

1. Open the organization's **Settings → Developer settings → GitHub Apps → New
   GitHub App**. Name it PDD Autopilot. Use an organization name in the App name
   if GitHub requires a unique name. Select the organization as its owner.
2. Set a homepage URL for your organization. Disable **Active** under Webhook.
   The local tick polls GitHub. No OAuth callback or user authorization flow is
   needed for installation authentication.
3. Set these repository permissions. Leave organization and account permissions
   unset.

   | Permission | Access | Purpose |
   |---|---|---|
   | Metadata | Read | Repository identity and metadata |
   | Contents | Read and write | Read source, update settings and merge PRs |
   | Issues | Read and write | Read issues, claim labels and comments |
   | Pull requests | Read and write | Create PRs, read and write reviews, merge |
   | Checks | Read | Read required checks |
   | Commit statuses | Read | Read commit status checks |
   | Actions | Read | Read Actions runs and failure evidence |

   Add **Workflows: read and write** only if your approved work includes changes
   to workflow files. Branch rules and required person reviews still apply. An
   App review does not replace a required person review.
4. Create the App. Record its numeric **App ID** and its URL slug. Generate a
   private key. Move the PEM file to a private location outside every checkout.
   Give only the local operator access, for example mode `0600`. Do not commit
   the PEM file or copy its contents into settings, chat or an issue.
5. Select **Install App** and install it on the organization. Choose **Only
   select repositories** and select each repository where PDD will work. Accept
   the requested permissions. Enable the organization's policy that permits the
   App to create PRs if required. Use this same App across the organization.

See GitHub's [registration instructions](https://docs.github.com/en/apps/creating-github-apps/registering-a-github-app/registering-a-github-app)
and [installation instructions](https://docs.github.com/en/apps/using-github-apps/installing-your-own-github-app).

## Configure each checkout

Edit `pdd.json` in the source checkout. Preserve the other settings:

```json
{
  "autopilot": {
    "mode": "auto",
    "trust": ["your-app-slug[bot]"],
    "github": {
      "share": 30,
      "floor": 1000,
      "app": {
        "id": "123456",
        "privateKeyFile": "/secure/pdd-autopilot.pem"
      }
    }
  }
}
```

Use your App ID and the absolute local key path. Each machine needs access to
that key path. The setting contains a path, never the key bytes. Add the actual
App bot name to `autopilot.trust` so its claim comments and saved dependency
reviews pass the existing trust checks. Keep all other required trusted names.
pdd does not grant the App extra trust or merge authority.

Run `pdd autopilot start` from the checkout. No personal `gh` login is needed
for App repository API calls. Hosted prompt checks keep their separate personal
GitHub sign-in and interpreter access. Interpreter sign-in selects the personal
`gh` behind the App and write wrappers, including in automatic workers. The App
does not replace that sign-in. pdd validates the key, resolves the repository installation,
checks the grants and verifies repository access before starting a timer or
chat. It reads the installation API limit before admitting work. A failure
names the failed stage or HTTP status and starts no work. It does not try the
person's login. A failed refresh also stops the tick before work.

Use `pdd autopilot status` to see the saved bot and installation identity. Status
makes no authentication request. An identity change causes the coordinator to
use a fresh chat when it is idle. Stop Autopilot before switching identities on
an active repository; let existing work reach a safe stopping point first.

App mode also authenticates Git push, fetch, pull, clone and remote branch reads.
The child process uses HTTPS with an installation credential. GitHub SSH remote
addresses are rewritten to HTTPS for that process. pdd does not edit stored Git
remotes or credential helpers. An App-only checkout can publish its branches
without a person's Git credential.
Repository-specific GitHub authorization headers, including headers from included
files, inherited Git environment settings, or clone's `-c` and `--config` options,
use the App credential in the child.
Non-authorization headers and settings for other hosts stay in place. pdd stops
the command if it cannot read the effective Git configuration.
Clone keeps source checkout headers out of its requests, including headers in
global includes that apply only inside that source checkout.

To check this transport locally, use Node.js 22.16 or newer, Git and OpenSSL:

```sh
node --test test/github-app-git-auth.test.mjs
```

The test creates temporary checkouts, a fake token endpoint, and a loopback HTTPS
server and proxy. It observes the headers sent by real Git and returns HTTP 403
before Git transfers data. It checks native calls, worker wrappers, nested gh
calls and personal mode. It removes its temporary files and servers. It needs
no App, personal credential, GitHub access or Herdr session.

## Token handling and API budget

pdd signs an RS256 JWT with the private key and exchanges it for an installation
token scoped to the repository. GitHub issues installation tokens with a
one-hour lifetime. pdd refreshes when five minutes remain. Coordinator and
worker shells use bundled `gh` and `git` wrappers. Each call reads the current settings
and obtains a fresh or cached credential, so a long chat does not retain an
expired token. pdd also applies this authentication to its native `gh` calls.
Codex launches pass the non-secret routing values through its invocation-only
shell policy. A profile `include_only` filter must permit `PATH` and
`PDD_GITHUB_APP_ROOT`; Codex applies that filter after the overrides.

The credential cache is `~/.cache/pdd/github-app/`. Its directory is private
(mode `0700`), and each credential file is private (mode `0600`). It is separate
from Autopilot state. Key rotation uses a separate cache entry. Cached tokens
expire in at most one hour. To revoke access at once, suspend the installation
or revoke its tokens on GitHub; deleting a signing key alone does not revoke an
issued installation token. Keep the cache out of shared backups and logs.

Tokens reach only the child transport environment. Git receives its authorization
header through environment config; gh receives GH_TOKEN. pdd does not print them, put them
in arguments, save them in workflow records or send them to chats. Transport
output and errors redact the active token. Credential-printing and login-changing
`gh auth` commands are refused in App mode. Removing App settings from a bound
chat stops its `gh` route rather than silently switching to a person.

App transport disables inherited Git tracing and curl verbosity. It also disables
trace2 targets set in Git configuration and forces HTTP trace redaction. This
applies to native commands, worker wrappers and Git started by gh. Git trace files
must not receive installation credentials. Personal-mode tracing is unchanged.
The local transport tests inspect trace files and check that only the private
credential cache contains a synthetic token.

The local ledger marks App calls with the App ID and installation ID. The
budget and reserve floor select that installation's entries. Personal calls
and other installations stay separate. Repositories in one installation share
its measured allowance on this machine. The wrapper counts its shell calls
when the repository already has an Autopilot ledger. Other machines share the
GitHub installation allowance, but their local call ledgers are separate. The
local budget is not a global quota broker. GitHub's secondary limits still
apply. Conditional response caches are separated by authentication identity.

The reserve guard uses the selected installation's saved limit before the first
non-safety dependency read. Safety reads and writes can still use the reserve.
The guard stops using an observation when its reset time arrives. To check these
boundaries with local fakes, run `node --test test/github-app-floor.test.mjs`.

See GitHub's [JWT rules](https://docs.github.com/en/apps/creating-github-apps/authenticating-with-a-github-app/generating-a-json-web-token-jwt-for-a-github-app),
[installation token rules](https://docs.github.com/en/apps/creating-github-apps/authenticating-with-a-github-app/generating-an-installation-access-token-for-a-github-app)
and [rate limit reference](https://docs.github.com/en/rest/rate-limit/rate-limit).
