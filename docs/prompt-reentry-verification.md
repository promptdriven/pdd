# Verify prompt and code changes

Use Node.js 22.16.0 or newer. No hosted service is needed for offline verification. Run offline checks from the repository root with a temporary `HOME` and `PDD_STATE_DIR` when isolating local state:

```sh
pdd lint
pdd lint --diff origin/main
pdd prove --base origin/main
```

For bug-fix contrast proofs, verify that the regression test fails on the merge base with the expected defect text and passes on `HEAD`:

```sh
pdd prove --base origin/main --test "node --test test/regression.test.mjs" --expect "expected failure text"
```

## What `pdd prove` checks

- Runs offline structural and diff lint (`pdd lint` / `pdd lint --diff`).
- Detects and runs the repository test command (`npm test`, `pytest`, `go test ./...`, `cargo test`) in your checkout, marking the receipt `proofScope: "working-tree"` (`dirty: true`) when uncommitted changes exist or `proofScope: "commit"` (`dirty: false`) when clean.
- Runs merge-base trusted `verify.paths` recipes from `pdd.json` whose globs match changed files, reporting host capability requirements clearly.
- In bug-contrast mode (`--base`, `--test`, `--expect`), creates isolated temporary worktrees for merge-base and `HEAD`, overlays changed tests plus any `--overlay` matches onto base, runs the test command in each, verifies base failure matches `--expect` (rejecting setup/import crashes as not proved), verifies `HEAD` passes, and removes both temporary worktrees when execution finishes.

For prompt-space checks against the PDD interpreter, run `pdd test --files STORY && pdd test STORY`. Native tests and `pdd prove` establish native code behavior; interpreter checks establish prompt-space behavior. Report both clearly without treating one as a substitute for the other.
