# PDD Alpha

Describe software behavior in prompts, Stories and independent test cases, then use your installed coding agent to implement and test it. PDD supplies one canonical Prompting guide, a skill, local native sessions and local GitHub workflow stages.

**Runner preview:** `pdd workflow run`, `pdd workflow resume` and `pdd workflow attach` are preview commands. A real workflow PR is not yet proven.

**Full access:** PDD starts all agents launched by `pdd session` and preview workflow stages with full access. Codex receives `--dangerously-bypass-approvals-and-sandbox`; Claude receives `--dangerously-skip-permissions`. Codex stages also retain `--no-daemon`. Claude requires accepting bypass mode once per machine and refuses this mode when run as root on Linux. Native installation and login are still required.

## Start locally

Get this source repository and open a terminal at its root. Use **Node.js 22.16.0 or newer**. The CLI and code tests need no dependency installation or global command replacement:

```sh
node bin/pdd.mjs --help
node bin/pdd.mjs --version
node --test examples/ticket-status/test/status.test.mjs
```

The example test exercises real JavaScript against independent expected cases. It is not prompt execution or formal proof. See the [complete synthetic ticket-status example](examples/ticket-status/README.md).

## Run a workflow on your GitHub issue

Have Git, authenticated GitHub CLI (`gh`), Herdr and an installed `codex` or `claude` executable available. Herdr 0.9.1 is the inspected capability baseline, not a promise about older releases; the owned target server must expose compatible APIs. Background native lookup/login/settings follow that server's normal environment and shell startup, not necessarily a later PDD caller's environment. Native access can use your existing account and provider settings; no PDD enrollment or separate company/personal eligibility check is required. Follow official [Codex CLI](https://developers.openai.com/codex/cli/) or [Claude Code](https://code.claude.com/docs/en/overview) setup only if your native tool is not already usable. PDD does not copy credentials or change global native settings.

From the project's actual Git checkout root, run the source package by its real absolute path. For example, replace `/actual/package` and issue `123` with your package location and actual issue in that repository:

```sh
node /actual/package/bin/pdd.mjs workflow run feature 123 --agent codex
```

Keep using that actual package entrypoint inside the native tool and in other terminals, preserving an absolute Node executable path too when one is supplied. The native tool's login shell can resolve bare `pdd` to another installation even when the outer terminal finds this alpha first on PATH.

Bundled workflows are `feature`, `bug` and `small-change`. You can also select a validated project workflow by its safe name; see [editable workflows](docs/workflows.md#edit-workflows). `--agent claude` selects your installed Claude Code; omitting the option defaults to Codex. ISSUE accepts a positive issue number, `owner/repo#number` or an HTTPS GitHub issue URL. The runner uses Git/GitHub to bind it to the current repository; cross-repository issues and PR numbers are not substitutes.

PR stages require a GitHub `origin`, an existing local `refs/remotes/origin/<default-branch>` ref, and clean committed topic-branch work. PDD does not fetch missing refs.

**This command starts work and can push branches and create real GitHub PRs.** Each issue receives a separate Git worktree and branch. Agent stages run in that assigned worktree, preserving your original checkout and its existing work. The full canonical [Prompting guide](docs/prompting-guide.md) is supplied first in every fresh stage conversation, with skill/references, the selected workflow snapshot and current issue/step evidence. The agent must read and apply the guide before any Story.

The PDD `run` or `resume` controller stays in your foreground terminal while native Codex/Claude stages run in an owned background Herdr session. After the same fresh agent works and becomes ready, PDD independently checks its exact handoff, revision, file hashes and required test results before accepting the stage and starting the next one. Readiness alone is not success. You do not need to exit the native CLI after every successful stage.

Each running stage is a full Codex or Claude session on your computer. PDD keeps one run per issue and one active stage per run; it does not set a fixed repository stage limit.

From another terminal in the same repository, use `node /actual/package/bin/pdd.mjs workflow attach RUN_ID` to inspect or interact with the actual active stage. Attachment pauses acceptance and cleanup; earlier candidates must be freshly validated afterward. Completed stage panes can be closed after accepted evidence is saved, so they are not permanent live attach targets. See [background stages and attachment](docs/workflows.md#background-stages-and-attachment).

Keep the PDD controller running for automatic progression. If it exits, native work may remain in Herdr, but PDD does not keep advancing in a daemon. Use the saved run ID to resume/reconcile that original work; do not blindly start another attempt.

The runner follows agent stages, human decisions, optional steps, PR creation and merge waits. A native exit code of zero alone is not proof that required artifacts or tests exist. It retains stage evidence and reports the actual state. PR stages require actual branch/commit inputs and save an intent before effect; returned PR links must be verified results. **The runner never merges a PR.** Merge waits advance only when GitHub reports the actual PR merged.

### How many stages?

| Workflow | Listed steps | Agent sessions | Other steps |
|---|---:|---|---|
| [Feature](.pdd/workflows/feature/WORKFLOW.md) | 12 | 5 required, up to 7 with optional visual/preview work | Human approval, prompt/code PR stages and merge waits; the prompt PR is optional |
| [Bug](.pdd/workflows/bug/WORKFLOW.md) | 11 | 5 required, up to 6 with an optional preview | Human approval, prompt/code PR stages and merge waits; the prompt PR is optional |
| [Small change](.pdd/workflows/small-change/WORKFLOW.md) | 5 | 3 | One PR stage and its merge wait |

These counts describe the bundled definitions; a validated project override can change them. Each executed **agent** stage gets its own fresh native session. Human choices, PR stages and merge waits are not additional agent sessions. Skipping an optional prompt PR also skips its conditional merge wait. Preview steps use ordinary project tools; they do not provide PDD Runtime Try.

### Continue the same saved run

Keep the printed UUIDv4 run ID and current stage. The runner retains each issue's assigned worktree, branch/base and saved state outside tracked project files. A common-repository index finds the same run from the original or linked checkout. The original source workflow and canonical context must still match the saved snapshot; edits refuse progress rather than silently replacing it. Issue ownership and controller locks coordinate those linked checkouts, not independent clones. Do not delete or edit state to force progress.

For an actual waiting run, substitute its returned ID:

```sh
node /actual/package/bin/pdd.mjs workflow resume RUN_ID
node /actual/package/bin/pdd.mjs workflow attach RUN_ID
node /actual/package/bin/pdd.mjs workflow resume RUN_ID --decision approve
node /actual/package/bin/pdd.mjs workflow resume RUN_ID --decision skip
```

Without a decision, resume only inspects or reconciles saved evidence and reads merge state; it does not launch another agent, push or create a PR. `approve` explicitly advances eligible work, accepts the current human decision or chooses an optional step; `skip` applies only to optional work. Approval must match the current saved revision. Merge waits read GitHub state and do not merge. After a separate prompt PR merges, prepare the existing assigned issue branch so it is clean and contains that exact merge commit, preserve the approved contract files, then resume with approve. Do not switch the assigned branch; PDD does not check out or reset it for you. Resume keeps the saved workflow, issue, repository and agent; there is no agent override.

Completed returns exit 0; waiting returns 2; failed or `recovery_required` returns 1 with the actual run/stage message. After interrupted native work or uncertain PR delivery, inspect that saved state and the actual outcome. Do not restart a stage, create another run or resend a PR as a blind retry. Recovery must reconcile the saved branch/base/marker identity; an unknown result remains unknown. See [workflow details](docs/workflows.md).

## Open an ordinary native session

For open-ended prompt work in this package, choose one of these alternatives:

```sh
node bin/pdd.mjs session "Help me review the ticket-status example. Show drafts before implementation."
node bin/pdd.mjs session --agent codex "Help me draft a behavior contract."
node bin/pdd.mjs session --agent claude "Help me draft a behavior contract."
```

`session` uses Codex by default and supplies the complete guide, skill/references and all bundled workflow Markdown in one initial native prompt. It opens one ordinary conversation. The companion `workflow feature|bug|small-change [--agent codex|claude] [request text]` opens one conversation with a selected recipe; use `workflow run NAME ISSUE` for separate agent stages and PR effects. Native flags are not passed through; `--` ends PDD option parsing for literal request text. Missing native executables exit 127, with no installation or private fallback.

You can also open your normal agent directly and have it read the entire guide and skill, including relevant references and recipe steps, in that actual conversation. `node bin/pdd.mjs --skill` prints the full guide first and all skill references. If output is clipped, read the complete files in sections before authoring. Keep the single guide at `docs/prompting-guide.md`; do not create a second authority.

### Try useful prompt work first

Ask the actual conversation:

> Read the full Prompting guide and skill, then explain the relevant method before drafting any Story. Inspect the synthetic ticket-status example. Preserve its existing statusLabel(status) API: open/blocked/done return Open/Blocked/Done; other strings and null give Unknown; other types throw TypeError; matching is exact with no trimming. Show prompt, Story and independent expected-case drafts for review before implementation.

Then ask for a real correction, such as explicit cases for `Open`, ` open `, an unknown string, null and invalid non-string input. Review the revised diff. When ready, request implementation and native tests, and a local PR summary without publication. If existing code already satisfies the contract, report that rather than inventing a change. This is a fictional teaching example, not proof that a workflow or PR has run for you.

## Discover local tools

```sh
node bin/pdd.mjs --help
node bin/pdd.mjs --skill
node bin/pdd.mjs workflow list --json
node bin/pdd.mjs completion bash
node bin/pdd.mjs completion zsh
```

`workflow list` validates and lists executable project and bundled definitions. JSON is `{ "workflows": [{ "name": "feature", "source": "bundled" }], "default": null }`, with the actual discovered entries. An invalid project override refuses instead of silently falling back. Listing starts no native work. Completion reads that local list as data and prints shell text without editing configuration. See [CLI details](docs/cli.md), [native conversations](docs/prompt-sessions.md) and [what checks mean](docs/checks.md).

## Scope

This is a local native-agent and GitHub workflow tool. Runtime/server/mobile implementation, private Host/gateway, PDD company-auth delivery and account pools remain outside the package. No hosted CHECK, standalone PDD lint, Runtime Try/replay/call or general formal verifier is supplied. Project tests, written expectations, manual observations and PR state are distinct evidence.

Native tools own their normal login, provider, model and conversation controls; PDD selects the full access launch flags described above. Agent and workflow work can consume your provider allowance. Actual native/platform and GitHub acceptance must be established on the released source; CLI stand-ins do not prove guide-aware Stories or real PR creation. No npm registry release, website switch or global install is part of this source package.

## Contribute

Read [AGENTS.md](AGENTS.md), [CONTRIBUTING.md](CONTRIBUTING.md) and the full [Prompting guide](docs/prompting-guide.md). Source is [MIT licensed](LICENSE). Keep one guide and a complete referenced skill bundle.
