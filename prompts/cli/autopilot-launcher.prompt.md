# Autopilot launcher

Own `src/autopilot-launcher.mjs`. Export module functions `runAutopilotLauncher(input, ports)` and
`tickAutopilot(stateFile, ports)`. This launcher connects a repository to the
person's interactive coding agent in a dedicated Herdr session. It adds no
approval, merge, quota-reset or headless execution route. Preserve existing
setup, workflow and interpreter behavior.

`runAutopilotLauncher` accepts command start, stop, status or add, cwd, packageRoot, env,
issues (argv issue references), and optional runs text. Return `{exitCode,message}`.
The CLI owns streams. Outside programs, timer installation, clock and state I/O
are injectable ports; native defaults implement these on macOS and Linux.

## Start and stop

Resolve the Git root, repository identity and package version before starting.
Check gh sign-in, Herdr availability and installed agent sign-ins, without making
an AI request. Prefer the current agent family when signed in, then Codex,
Claude, agy and Gemini. Use configured local launchers from agent-config for the
supported families, preserving their environment. For Gemini, a version alone
is not sign-in evidence: inspect its existing OAuth credential presence locally;
never display credential bytes. For agy use its non-model agent listing; its CLI has no auth-status command.
Missing dependencies produce a single actionable line; no question or installer.
Check the pdd version from the invoked package and warn about PATH shadowing.

Read only the `autopilot` key of root pdd.json: the #2852 seam accepts a mode
string off/observe/auto or an object with mode and trust names. Missing/invalid
mode means off with a one-line explanation. Off starts no agent or timer. This
launcher does not write that key or invent a setup answer. Both active modes use
the same launcher; skill policy decides later gates.

Start persists a repo/machine state outside the checkout, installs a 30-minute
user timer and runs the first tick immediately. Repeated start reuses the timer
and saved activation time; stopping/restarting does not admit old backlog.
Optional --runs is a positive safe integer with no product maximum. Omission
means no fixed cap. Persist only the selected launcher identity/config-folder
paths, not credentials or the whole environment. A named user timer runs the
Node script with absolute paths and the launcher's PATH and agent config paths.
Linux uses a systemd user timer; macOS uses a LaunchAgent. No controller process
or polling loop remains running between ticks. Timer failure is actionable and
does not leave status claiming it is running.

Use a dedicated Herdr session `pdd-autopilot`, isolated from the default session.
Open its repo workspace at start; launch the interactive agent only for work.
Reuse its saved pane for later prompts; if it no longer exists, recreate the
repo workspace/pane and preserve the queued work. Never send interrupt/kill/close to stop:
stop disables this repo's timer and queued ticks and removes its persistent
timer definition, leaving the current step to
finish. Repeated stop is harmless. Status reads local state and timer activity;
show repo, agent, running/stopped, and next tick (or none), without waking AI or
querying GitHub. Concurrent ticks for one local state serialize with a local
lock; independent machines have separate state.

## Tick and the skill boundary

The newest R6 decision takes precedence over the earlier unconditional Claude
/loop request: all providers use a user timer so an empty tick wakes no AI.

```mermaid
flowchart TD
    T[Timer or immediate first tick] --> S{Enabled locally and in repo?}
    S -->|No| E[Return without AI]
    S -->|Yes| Q[Conditional GitHub issues request]
    Q --> W{Recipe or eligible work?}
    W -->|No| E
    W -->|Yes| P[Prepare trusted packet]
    P --> A[Start or wake interactive pdd-autopilot skill]
```

Each tick makes one conditional issues-list query with its saved ETag, following
pagination only when GitHub supplies another page (never truncate a queue). Cache
and revalidate each page separately, so a close on a later page is seen even
when the first page is unchanged.
HTTP 304 reuses metadata, not a model turn. On changed candidates only, fetch
comments needed to identify trusted consent and filter their text. Rate-limit
responses save the reset time; intervening timer firings do not retry. Other
failures warn and leave the next scheduled tick available.

Only issues created at/after the original activation time, or explicitly labeled
`pdd:autopilot`, can start. `add` creates that label if absent and applies it to
all named issues, including old ones; it never changes the issue body. Ignore
pull requests and closed issues. Issues carrying pdd:working remain owned by the
skill and are not offered as new work. The skill, not a local launch, makes the
cross-machine D52 claim (pdd:working plus one comment). A failed delivery is
retryable: do not record it as delivered. Unclaimed eligible work remains work on later ticks: delivery is not evidence
that the skill scheduled it. A conditional cache hit with eligible work wakes the
skill again; a hit with no eligible work or recipe does not.

A trusted author/commenter is the repo owner, appears in configured trusted
names, or has write/maintain/admin permission confirmed by GitHub. Association
alone does not establish write permission. Resolve needed permissions without AI;
a failed or unavailable lookup defers that candidate without replying or
forwarding that person's text. A rate-limit response defers the whole tick until
reset; do not follow it with more GitHub calls. This trust test applies to
comments too. An outsider issue waits until a trusted person comments. Before
that, send the literal non-AI reply "thanks, a maintainer will look" once,
identified by its exact static body and pdd HTML marker from a trusted author;
that acknowledgement never counts as consent. A stranger copying the marker
cannot suppress the reply or establish consent.
Forward only trusted people's title/body/comment text; outsider metadata may
include the issue number and URL but never its title, body or comments. A trusted
comment admits an outsider issue without admitting the outsider's text. Stored
poll metadata stays local; model input is a separately filtered packet. Recheck
comments on updated issues, including after a conditional cache hit if needed.

The first task on the first launch is the repo's start-up recipe (R5), before
issues, even on an empty repo. Request the installed pdd-autopilot skill with a
JSON packet containing repository, activation time, optional runs, trusted issues
and the recipe-first flag. State that further issue/comment reads must use the
same trust boundary. This is the #2890 seam: the skill owns recipe execution,
room scheduling (account 5-hour/weekly quota, no credits/resets, CPU, memory and a
free test slot), two runs per prompt file with a third waiting while other work
starts, D52 claims, and progress tracking (pdd:stuck after 30M tokens or 60 minutes
without progress, then another issue). These are instructions to that skill,
not duplicate implementations or evidence of live execution. No fixed count,
time-based run termination or new refusal is introduced by the launcher.

## Dependencies

- [Agent configuration](agent-config.prompt.md): required native generation and
  verification context for existing configured launcher identities/environment.
- [Agent adapters](agent-adapters.prompt.md): required native generation and
  verification context for non-model process execution and auth-status parsing.
- [PATH diagnostics](path-diagnostic.prompt.md): required native generation and
  verification context for the optional version shadowing warning.

This module has native Node tests. Timer services, real sign-ins, cross-machine
skill claims and the unmerged #2852/#2890 contracts need integration verification;
no syntax-only interpreter entry stands in for those effects.
