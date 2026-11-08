# Offline Autopilot comparison

This development harness runs the real launcher and tick modules from two local
source trees. It uses the repo's counting GitHub fake, a fake Herdr coordinator,
a fake timer, and separate temporary repositories and state. It makes no model
or network calls. It needs Node 22.16 or later and local Git. It needs no install,
sign-in, running Herdr session, or service. Use trusted local source trees.

Run from this checkout:

```sh
node scripts/autopilot-compare.mjs --old /path/to/main-source --new .
node scripts/autopilot-compare.mjs --old /path/to/main-source --new . --json
node --test test/autopilot-compare.test.mjs
```

Both roots must contain the full source tree, including `package.json` and
`src/`. No checkout is fetched or changed. Use a local export of a pinned main
commit for the baseline. Record both commit IDs outside the repo. A package
version alone does not identify autopilot-next. Passing the same root twice is
a useful control; the table labels it as a self comparison.

The default replay is `test/fixtures/autopilot-compare-backlog.json`. It is
synthetic. It has eight independent issues and seven frames: intake, no change,
a trusted body edit, a trusted comment, a claim by another machine, issue closure,
and no change after those events. One issue is from an untrusted author. Fake
dependency answers say that each issue is independent. No agent produces them.
The first frame includes fake launcher setup. Each later frame calls the selected
version's real tick. Each temporary world is removed after the run.

To supply sanitized external observations, pass `--replay FILE`. The JSON envelope
has `schema_version: "pdd.autopilot-compare.v1"`, `synthetic`, and `frames`.
Each frame has a unique safe `name`, an increasing millisecond `at`, and a native
saved snapshot with `v: 1`, `repository`, `refreshedAt`, `list` (`rows`, `since`,
`readAt`), `issues`, and `invalid`. Issue entries have `version`, `observedAt`,
`kinds`, and optional `raw` for closed referenced issues. All four page kinds
(`comments`, `blockedBy`, `blocking`, `timeline`) must be complete. Comment counts
and native link counts/directions must agree. Duplicate page identities are
rejected. These checks establish internal consistency, not capture truth. A partial snapshot must first be completed in an
authorized capture; the harness rejects it. Snapshot cache validity timestamps
describe the external observations served by the fake. Each implementation builds
its own private cache from those observations. Saved invalidation state is metadata,
not permission to fabricate missing pages.

The current repo fake counts full linked pages in all four dependency summary
fields. The adapter accepts that convention. A real recording with different
active and total counts, such as a closed-blocker variant, needs a fake adapter
first. This harness does not claim coverage for that variant.

Keep the same synthetic identities through the recording. Preserve issue links,
trust roles, claim relationships, timing and comment IDs. Remove secrets and
private content before the file enters this command. Keep real recordings and
reports outside this repo. This harness is not a sanitizer. It does not print
snapshot bodies. External recordings leave AI requests pending. Only synthetic
inputs without native blockers may set `completeIndependent: true` to use the
bounded fake review answer. Replaying a real backlog this way does not execute
the AI's backlog decisions.

The table compares delivery decisions, eligibility and pending state. It counts
all attempted REST calls, REST writes, GraphQL queries and mutations, and fake
prompt deliveries. POST GraphQL queries are reads. Ordered call and write traces
compare routes and statuses. Write traces also compare canonical request-body
hashes. Only the fake reviewer's generated coordinator ID, lease generations,
and lease-blob SHAs are normalized. Head SHAs, labels, comment text and evidence
remain part of the hash. No payload text is printed. JSON retains
the per-frame structured decisions and traces. Each delta is new minus old.
Differences need review. Exit 0 means the replay completed. It is not a safety
verdict. Invalid options return 2. Data or source failures return 1 without a
comparison table.

The replay does not measure issues finished per hour, AI tokens or spend, CI
minutes, person effort, actual stuck runs, duplicate workflow claims, wrong
merges, false-green evidence, or reverts. It does not run workflow workers,
checkers, a merge queue, or CI. Those need the separately approved two-repository
trial and backlog review. Send that comparison to Serhan before any decision to
merge autopilot-next into main.
