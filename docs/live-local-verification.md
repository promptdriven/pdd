# Verify owner-local CLI integration

Use Node.js 22.16 or later and install the dependency from this checkout's
manifest and lockfile. Public installation uses anonymous npm fetches without
substituting an older package or symlinking another worktree.

```sh
npm ci --ignore-scripts
node --import ./test/helpers/test-home.mjs --import ./test/helpers/test-net-guard.mjs --test --test-concurrency=2 test/live-local-host.test.mjs test/live-local-consent.test.mjs test/live-local-cancel.test.mjs test/command-catalog.test.mjs test/docs-commands.test.mjs test/runtime-seam.test.mjs test/ci-install.test.mjs
```

These tests need no provider credentials. They exercise public CLI option
validation, lazy package delegation, host primitives, shorthand and expanded
manifest compilation, redaction, and real pseudo terminals. Scratch effects stay
under owned temporary directories. The committed helpers route through PDD's
Runtime seam and the installed package. Each pending write needs its own
affirmative test answer. Active and queued cancellation must settle without an
answer; a late answer must not launch a command. Automated answers are test
inputs, not human approval. Teardown closes terminals, removes scratch files and
terminates children.

The matching runtime-client package carries the 26-check Story replay, shorthand
manifest and long-polling tests, and bounded consent, permit and privacy tests
in its offline suite. Run those against the same installed source revision. No
transport-only result establishes a passing Story.

Run `npm test` separately on the runner for the full offline PDD suite. An
independent checker repeats the native verification recipe with semantic fault
controls and records actual assertion failures rather than import or setup
errors.

For live interpreter integration, invoke this CLI with an owner-reviewed
manifest stored outside uploaded source. Verify physical command launches,
fresh terminal answers for writes, redacted outbound output, and owner-only
report visibility. Stop the session and confirm that registrations, processes
and scratch effects are cleaned up. Keep receipts and raw logs outside the
product repository.
