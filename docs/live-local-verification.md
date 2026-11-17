# Verify owner-local CLI integration

Use Node.js 22.16 or later and install the exact dependency from this checkout's
manifest and lock. The public package route uses anonymous npm installation;
a commit-pinned integration dependency requires read access to that repository
and the referenced commit must be published before remote installation works.
Do not substitute an older package or a symlink to a different worktree.

```sh
npm ci --ignore-scripts
node --import ./test/helpers/test-home.mjs --import ./test/helpers/test-net-guard.mjs --test --test-concurrency=2 test/live-local-host.test.mjs test/live-local-consent.test.mjs test/live-local-cancel.test.mjs test/command-catalog.test.mjs test/docs-commands.test.mjs test/runtime-seam.test.mjs test/ci-install.test.mjs
```

These tests need no provider credentials. They exercise public CLI option
validation, lazy package delegation, host primitives, redaction, and actual
pseudo terminals. Scratch effects stay under owned temporary directories.
The committed helpers route through PDD's Runtime interface and the installed
package. Each pending write needs its own affirmative test answer. Active and
queued cancellation must settle without an answer; a late answer must not
launch a command. Automated answers are test inputs, not human approval.
Teardown closes terminals, removes scratch files and terminates children.

The matching runtime-client repository has the original 26-check Story replay
and bounded consent, permit and privacy tests in its normal package suite.
Run those against the same installed source revision. The server repository's
`docs/owner-local-check-verification.md` covers genuine scenario evaluation,
including original checks that fail after physical command behavior changes.
No transport-only result establishes a passing Story.

Run `npm test` separately for the full offline PDD suite. An independent checker
must repeat the relevant native recipe and use semantic fault controls. Record
actual assertion failures rather than treating import or setup errors as proof.

For actual AI integration, install the candidate server locally and invoke this
changed CLI with an owner-reviewed manifest outside uploaded source. Retain the
CLI, installed client and engine revisions, package byte identity, request and
report IDs, original scenario outcomes, physical launches, provider accounting,
fresh terminal answers, redacted outbound output and owner-only report checks.
Use bounded owned scratch writes for write tests. Stop the session and confirm
that registrations, processes and scratch effects are cleaned up. Keep receipts
and raw logs outside the product repository. Publication requires the separate
repository review and full-suite gates.
