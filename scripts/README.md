# Team maintenance scripts

## Runtime issue routing

`route-runtime-issues.mjs` reads all open issues using `gh api`. Inputs to Runtime
(prompts, interface blocks, Stories, test vectors and tests) stay with PDD. Reports
about execution inside Runtime after the call go to the configured Runtime owner.
Mixed or unclear reports print a manual-review decision without GitHub writes.
This tool runs independently of Autopilot.

Use Node.js 22 or newer, authenticated `gh`, and an installed headless agent.
Create an operator config outside the repository:

```json
{
  "owner": "runtime-owner",
  "agentCommand": ["/absolute/path/to/tool-free-classifier"]
}
```

The trusted executable receives instructions and JSON issue evidence on stdin.
It must run without tools, read no repository or account files, perform no writes,
and emit only `{"ownership":"runtime|pdd|uncertain","reason":"one short line"}`
on stdout (choose one ownership value). Configure its own agent authentication;
the router removes `GH_*` and `GITHUB_*` environment variables and runs it in an
empty temporary directory. An arbitrary command is **not** sandboxed by this
script: the operator must supply a tool-free agent invocation or wrapper.
Do not put credentials in the command array or config. Raw process diagnostics
are suppressed. Each uncached issue version makes one agent call, even in dry
run, and may consume the agent's normal usage or credits. There is no automatic
retry, usage reset or agent installation.
SIGTERM/SIGINT stop further issues, kill active process groups on POSIX, wait for
children to close and remove the agent directory and cache lock before exiting
143/130. Interrupted calls remain cached. SIGKILL cannot run this cleanup, and
agents must not detach descendants into another process group.

```sh
node scripts/route-runtime-issues.mjs --repo OWNER/REPO --config /path/to/router.json
node scripts/route-runtime-issues.mjs --repo OWNER/REPO --config /path/to/router.json --apply
```

Dry run prints the full JSON plan and saves classifications locally. `--apply`
adds `pdd:runtime`, adds the configured owner without removing other assignees,
and posts one short reason comment. It does not close, transfer or edit issues.
Prepare the label and ensure the configured owner is assignable in the repository.
Returned label and assignment data must confirm each write before a completion
receipt is saved; a silently ignored assignment leaves the version retryable.
Uncertain and PDD decisions produce no actions. Any failed issue yields exit 1;
other issues are still processed. Reads are paginated; pull requests are ignored.

The default cache is `.cache/runtime-issue-router`; choose another directory with
`--cache-dir DIR`. Each filename is the content hash printed as `version` in the
plan. Title/body and human comment changes invalidate classification; router
comments, labels, assignees and issue timestamps do not. Successful application
receipts suppress rerouting the same version after a person undoes it. Undo by
removing the label, assignment and/or comment in GitHub. Changed content receives
a fresh decision. A comment marker prevents duplicate comments across versions.
Keep the cache: deleting it permits reclassification and rerouting. Failed or
interrupted attempts are also cached; inspect the issue and explicitly remove
that version's JSON to allow one new attempt. Cache format and classifier policy
changes require operator review before deliberately clearing the cache.

Concurrent local runs sharing a cache fail with a lock message. Remove a stale
`.lock` directory only after checking no router is running. Apply rereads content
before writing; GitHub writes cannot be transactional with later human edits.
After partial failure, retry uses the cached decision and fresh metadata to skip
successful effects. A lost response after GitHub accepted a write is reconciled
on the next run through metadata and the comment marker.

The **Route Runtime issues** GitHub Actions workflow has only `workflow_dispatch`.
Prepare a dedicated Linux self-hosted runner with the label `runtime-router`,
Node.js 22+, `gh`, and the tool-free agent configured and authenticated. Set
repository variables `RUNTIME_ROUTER_OWNER` (login) and
`RUNTIME_ROUTER_AGENT_COMMAND` (JSON executable/argument array, absolute executable
path recommended). The workflow's GitHub token has issue write permission and is
passed only to the routing step. Dispatch defaults to dry run; select `apply` for
writes. Workflow concurrency serializes runs and Actions cache preserves decisions
and receipts per ref, including failures. Cache eviction or running another ref
can cause another classification; use one ref and preserve its cache. A killed run
may leave a lock requiring manual inspection. No schedule is installed.

Offline checks:

```sh
node --import ./test/helpers/test-home.mjs --test test/route-runtime-issues.test.mjs
```

These fixtures check parsing, plans, cache/retry behavior and the CLI with fake gh
and agent processes. They do not establish real-agent classification quality,
live GitHub authorization or runner provisioning.

## Release benchmark and Autopilot daily observe runner

`scripts/benchmark/` measures PDD authoring and Runtime behavior across release candidates, runs daily read-only Autopilot `--observe` checks across configured repositories with zero GitHub writes, and renders a self-contained HTML + inline SVG scorecard tracking the two North-Star targets:

1. **Bar 1 — PDD vs. Direct Coding (`pdd_vs_direct_coding`)**:
   - **Small builds (`snake`, `2048`, `task-manager`):** speed ratio `&le; 1.0x` and cost ratio `&le; 1.0x` vs. direct AI coding, with `100%` first-try hosted Runtime pass.
   - **Larger brownfield codebases (`brownfield-repo-sync`):** `2.0x–3.0x` faster feature iteration, `&gt; 50%` lower rework cost vs. direct AI coding (`30–60+ min` rework baseline), and step-by-step incremental repository sync readiness.
2. **Bar 2 — Autopilot End-to-End Zero-Edit Completion (`autopilot_zero_edit`)**:
   - `90%–95%` end-to-end completion (`prompts -> Runtime verification -> merged code` with zero human edits and zero 7-day reopens).

### Entrypoints

Evaluate release candidate metrics against a baseline release (advisory warnings by default):

```sh
node scripts/benchmark/run-release-benchmark.mjs \
  --candidate /path/to/candidate.json \
  --baseline /path/to/baseline.json \
  --history /path/to/history.json \
  --out /path/to/release-report.json
```

Run a live read-only Autopilot `--observe` pass across one or more repositories (strictly `GET`-only GitHub reads with local `If-None-Match` ETag caching and zero issue/PR mutations):

```sh
node scripts/benchmark/run-autopilot-observe.mjs --observe \
  --repo promptdriven/pdd \
  --state-dir ~/.local/state/pdd/observe \
  --out ~/.local/state/pdd/observe/observe-runs.jsonl
```

Or pass an operator config file outside the repository (`--config ~/.local/state/pdd/observe/config.json`) listing repositories and optional local checkouts:

```json
{
  "repos": [
    { "repo": "promptdriven/pdd", "checkout": "/path/to/pdd" }
  ]
}
```

Render the self-contained HTML + inline SVG dashboard. By default, only `promptdriven/pdd` is shown by repository slug and linked; any other repository in `observe-runs.jsonl` is automatically redacted to a generic `private-repo-N` label without a GitHub link unless explicitly allowlisted via repeatable `--public-repo OWNER/REPO`. Output hygiene also scrubs and rejects commit hashes, UUIDs, and common credential tokens:

```sh
node scripts/benchmark/render-benchmark-report.mjs \
  --release-json /path/to/release-report.json \
  --observe-jsonl ~/.local/state/pdd/observe/observe-runs.jsonl \
  --public-repo promptdriven/pdd \
  --out ~/.local/state/pdd/observe/latest-benchmark.html
```

### Daily user-level systemd timer (Linux)

Keep daily read-only observe telemetry accumulating under `~/.local/state/pdd/observe/` with a user `systemd` unit (`~/.config/systemd/user/pdd-autopilot-observe.service` and `.timer`):

```ini
# ~/.config/systemd/user/pdd-autopilot-observe.service
[Unit]
Description=Run daily read-only PDD Autopilot observe scorecard

[Service]
Type=oneshot
ExecStart=/bin/bash %h/.local/state/pdd/observe/run-daily-observe.sh
TimeoutStartSec=10min
```

```ini
# ~/.config/systemd/user/pdd-autopilot-observe.timer
[Unit]
Description=Daily read-only PDD Autopilot observe timer

[Timer]
OnCalendar=*-*-* 08:00:00 UTC
Persistent=true
AccuracySec=1min

[Install]
WantedBy=timers.target
```

Offline unit tests:

```sh
node --import ./test/helpers/test-home.mjs --import ./test/helpers/test-net-guard.mjs --test test/release-benchmark.test.mjs
```
