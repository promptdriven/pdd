# Verify stopping by a saved Story path

Authority: [approved Story](../../user_stories/stop-simulation-by-story-path.md)
and [unchanged case inventory](stop-simulation-by-story-path-cases.json).

Run from the checkout root with Node >=22.16 and Git on PATH:

```sh
git rev-parse HEAD
git status --short
node --test test/stop-simulation-by-story-path.vectors.test.mjs
node --test test/runtime-try.test.mjs test/runtime-try-recovery.test.mjs
```

No installation, compilation, credentials or hosted service is needed. The replay
loads the checkout's public `runTry` from `src/runtime-client.mjs`. Its shared
helpers are `test/runtime-fake.mjs` and `test/helpers/test-home.mjs`. The checkout's
`package-lock.json` records package metadata; these tests need no installed
dependencies or build artifact. Test collection alone is not a behavior pass.

The replay reads every expectation in the inventory at execution. Each of its nine
named case groups maps to the inventory's criterion IDs. It exercises saved Story
paths, short names, saved test selectors, a distinct test basename, absent Story
and test files, DELETE 404/410, an unconfirmed stop, an unknown selector and an
ambiguous short name. Repeated variants get fresh Git roots and private state.
Additional tests retain leading `./` selectors and start a Try from an authored
Story path before stopping it through the same public boundary.

The native Git lookup and saved-state reads/writes are real. Injected ports supply
synthetic authentication, clock, waits, UUIDs and service replies. The startup
case uses a local HTTP fake. Assertions check output, exit status, selected DELETE,
stop-job reads, state before confirmation, retained fields, and no authentication
or service calls for unknown and ambiguous selectors. The failed-stop case keeps
the original saved bytes. A passed local replay establishes these native behavior
cases with simulated external dependencies. It proves no hosted operation or
interpreted prompt result. The Runtime interface/scenario gap remains blocked.

A fresh verifier records the candidate revision, diff, UTC time, command, exit
status, case results and cleanup outside the checkout. Repeat the same test and
expectations against old code in a throwaway checkout. The saved Story path must
fail the assertion marked `STOP-STORY-PATH saved-story-path` on old code and pass
on corrected code. Setup failures are not defect evidence. Report skipped,
blocked or unexecuted stages explicitly. Hosted author-scenario verification and
independent formal/review work remain separate.

Test teardown removes its temporary repositories, state and homes, and closes the
local HTTP fake. Keep cleanup failures separate from behavior results. Preserve
evidence outside these temporary folders. The existing recovery tests cover the
owner's unknown-session behavior without changing its expectations.
