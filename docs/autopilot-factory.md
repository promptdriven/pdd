# Autopilot factory test

## Fresh release smoke sandbox

From a source checkout, preview a fresh private GitHub repo under your chosen
owner, then create it explicitly:

```sh
scripts/autopilot-smoke.sh --owner OWNER
scripts/autopilot-smoke.sh --owner OWNER --apply
scripts/autopilot-smoke.sh --check OWNER/PRINTED-REPO-NAME
```

Dry run is the default and calls neither GitHub nor Git. Apply needs authenticated
`gh`, Git, Node 22+, and permission to create private repos under OWNER. Every
invocation chooses a fresh name. The vendored `fixtures/autopilot-smoke/base/`
is a dependency-free Node package with three helpers and three passing tests.
Three fixed issues cover a doc example, a zero-bound clamp bug with its missing
failing case, and an optional starting total for sum. Each gets `pdd:autopilot`.
The script prints repo identity and each created issue URL, including recovery
instructions before remote writes; a partial failure is not retried.

The repo starts with Autopilot off and automatic reports off. Configure and start
the candidate Autopilot separately in a disposable environment; this script does
not start agents or change local Autopilot state. Check only reads GitHub and
prints per-issue `merged`, `ended` or `open`, creation/finish UTC timestamps and
elapsed seconds. Merged needs a closed issue and a merged closing PR. Ended means
a core end marker or closure without a merged closing PR; it does not establish
whether a retry is active. Missing issues or incomplete reads fail the command.
Repos are never deleted: the script prints `gh repo delete OWNER/REPO --yes`
for manual cleanup. Check reports outcomes, not a release approval.

## Offline factory

Run the offline factory from a source checkout:

```sh
scripts/factory-test.sh
```

The factory runs the native CLI, the workflow runner and the durable stores in a
disposable project, with real Git commits, branches, worktrees and a local bare
origin. Only GitHub, the interpreter and agent reasoning are fake. It checks the
native check plan: a full batch with a target Story and an unrelated baseline
obligation saves its plan before dispatch, keeps the target and baseline results
apart, and blocks paid dispatch with one named prerequisite when an interface,
an entry limit, a nested call bound or a recursion bound is missing. After the
owner repairs the named declaration, a fresh check reaches a verdict.
