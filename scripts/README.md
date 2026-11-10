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
