# CI Tiers

The public repository runs three default GitHub Actions jobs on pull requests:

- `unit-tests`: pytest coverage that excludes tests marked or known to require real LLMs, cloud resources, or private prompts.
- `public-cli-regression`: deterministic CLI regression coverage through `make regression-public`.
- `story-regression`: the user-story regression lane, `make regression-stories`, which runs `pytest -m story` with the deterministic/offline config and reports a per-story pass/fail summary (number of stories, number of story regression tests, per-story result) via the `pytest_terminal_summary` hook in `tests/conftest.py`. Like `public-cli-regression` it is fork-safe and runs with no API keys. It is **blocking**: a failing or stale story test fails the job (the generated tests hard-assert the story hash, and the lane has no `continue-on-error`). An empty suite (no `@pytest.mark.story` tests collected) is treated as a green no-op.

Both `make regression-public` and `make regression-stories` must remain safe for public forks. They must not require API keys, cloud authentication, Infisical, GCP, private repositories, or live LLM calls. Put live model and cloud checks in separate secret-gated workflows or in `pdd_cloud`, not in the default public PR path.

Longer suites remain separate:

- `make regression` and `make sync-regression` exercise LLM-backed CLI flows.
- `make cloud-regression` and cloud batch targets require cloud authentication and should run only in protected or private CI.

Projects with critical modules may add a **snapshot reproducibility** check that rejects unsnapshotted nondeterministic prompt context. Use **`pdd checkup snapshot`** only (there is no top-level `pdd policy` command). The check fails when a protected prompt uses `<shell>`, `<web>`, or `<include ... query="...">` without a replayable snapshot under `.pdd/evidence/`. Keep this separate from public fork-safe regression jobs if it requires private snapshot artifacts or secret-gated web access.

```bash
pdd checkup snapshot prompts/critical_python.prompt
```

The command exits non-zero when active nondeterministic tags are declared but `.pdd/evidence/` contains no replayable snapshot manifest for that prompt.

**`pdd checkup snapshot` vs `pdd checkup gate`:** `checkup snapshot` enforces that prompts declaring dynamic tags have a captured, replayable expanded-prompt manifest (from `pdd preprocess --snapshot` or `pdd generate|sync --snapshot-context`). `checkup gate` enforces dev-unit evidence policy (validation, contracts, cost limits) on `.pdd/evidence/devunits/*.latest.json`. Run both in protected CI when you use nondeterministic prompts and evidence receipts.

**Replay path:** `pdd replay` accepts the schema v1 snapshot manifest at `.pdd/evidence/runs/<run_id>.json` or an evidence manifest (schema v2) that links `context_snapshot.manifest_path`. Preprocess with `--snapshot` without `--recursive` when the prompt uses `<shell>` or `<web>` (recursive mode defers those tags).

## Verification Requirement Transition Rotation

Requirement-transition authority in
`.pdd/verification-profile-rotations.json` must be installed and consumed in two
separate protected changes. This prevents a candidate from granting itself
authority for prompt or verification-profile bytes introduced by the same
change.

### Phase A: install dormant rows

Phase A may add only dormant `requirement_rotations`, or make the narrow
append-only stale-authority retirement described below. The prompt named by each
new row and `.pdd/verification-profiles.json` must remain byte-for-byte
identical to the protected base. Every other managed prompt must likewise remain
byte-identical, resolving approved aliases to their protected canonical prompt
path. The rest of the policy envelope, including
`rotations`, must preserve the protected authority exactly. A retirement/reissue
may advance only the transition envelope from schema 2 to schema 3 to append its
retirement record; it cannot otherwise replace policy authority.

For schema 2, every surviving protected row must retain its exact JSON token and
relative order, ahead of newly added rows. A consumed row may still be removed or
replaced after the loader proves consumption, without permitting any surviving
protected row to be reformatted, re-escaped, or reordered.

Each row records the SHA-256 identities of the current prompt/profile bytes and
the prepared Phase B prompt/profile bytes. Review those exact prepared bytes
before landing Phase A. Phase A must merge and become part of the protected base
before Phase B begins. Installing and consuming a row in the same pull request
is forbidden.

### Retire and reissue an unreachable dormant row

Schema-3 policy may retain an obsolete row in `requirement_rotations` and append
one `requirement_rotation_retirements` record with exact `obsolete` and
`replacement` rows. This is only for a protected dormant row whose prompt and
profile entry still hold its source state, but whose complete protected profile
bytes match neither of that row's bound policy digests. That proves the row
cannot be consumed from the current base.

The record and replacement are exact: the obsolete row must remain unchanged in
the protected history, the replacement must be a new dormant row for the same
prompt/language identity, and both full byte-bound rows are embedded in the
record. Protected rows and retirement records retain their exact JSON token
representation: do not reformat, reorder keys, change escaping, or rewrite a
lexically equivalent path. Duplicate JSON member names are invalid. Records are
append-only; they cannot omit or edit historical rows, target a live or consumed
row, fork, chain, cycle, or use wildcard identity.
The authority-only candidate must leave all managed prompt and profile bytes
unchanged. Its fresh replacement remains dormant until this retirement/reissue
candidate itself is protected, and only a later Phase B can consume it.

### Repository-bound legacy llm-invoke retirement (#2316)

One older `pdd/prompts/llm_invoke_python.prompt` row became unreachable before
schema 3 existed: subsequent protected releases had already moved both its
prompt and profile source bytes forward. It may be retired only by the
repository-bound verifier bridge for repository
`3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0`, and only with the complete protected
rotation-policy digest
`3b5117e0ef31b19b68d7190f0753e7aacaef3f75133cabfe4c2470afe87c0a95`,
the exact prepared schema-3 candidate digest
`4e3ca5e64238e7137fedc7c562b2dd5a2e61db61dae422f85c0aaebbc86cb6bb`,
and unchanged protected/candidate verification-profile bytes
`ffd7a11fb15a7aebb20c8199d506cf2deb8bb405b952dcda8444563c24e7a912`.
The historical rollout replay is even narrower: it is bound to both complete
policy/profile pairs and both complete managed-prompt trees. Reformatting,
reordering, replacement-field substitution, a target-prompt change, an
unrelated managed-prompt change, or use by another repository is rejected.

The later Phase-B consumer has a separate, equally exact verifier binding. It
recognizes only repository `3b4d7b1c-d6cc-4752-ba93-6b98d1a710e0` with the
stationary prepared policy digest
`4e3ca5e64238e7137fedc7c562b2dd5a2e61db61dae422f85c0aaebbc86cb6bb`, the
complete transition verification-profile pair
`ffd7a11fb15a7aebb20c8199d506cf2deb8bb405b952dcda8444563c24e7a912` to
`a2071278af121c6b41b93a2630041541292d70a4acec40751c34dcfdb1b77a9f`, and
the complete transition managed-prompt-tree pair
`b1ea7718f06089e9f1d9edcb611c8483f495478958e85e8ee65d320cd14d714f` to
`637087072d0cb5357b99348b962844b4c8da054b3dd382fc2798728995353bd4`.
After consumption, it recognizes only the corresponding stationary profile
pair `a2071278af121c6b41b93a2630041541292d70a4acec40751c34dcfdb1b77a9f` to
itself and stationary prompt-tree pair
`637087072d0cb5357b99348b962844b4c8da054b3dd382fc2798728995353bd4` to
itself.
This state recognition restores only the historical overlay needed to validate
the already protected rows; the ordinary row bindings still require the two
prepared target prompt/profile updates. Any policy, profile, target-prompt, or
unrelated managed-prompt substitution is rejected.

This exception requires four separately protected changes, in this order:

1. A governance prerequisite that installs only the verifier binding,
   documentation, and negative tests. It must not change the rotation policy,
   verification profile, or either target prompt.
2. The exact JSON-only schema-3 Phase A policy candidate named above. It retires
   the unreachable llm-invoke row and installs the llm-invoke and model-tester
   replacements while all prompts and the verification profile remain unchanged.
3. A Phase-B verifier prerequisite that binds the stationary Phase-A policy,
   exact Phase-B profile pair, and complete managed-prompt trees. It must leave
   the Phase-A policy and profiles and all Phase-B product files unchanged.
4. A later Phase B that consumes only those now-protected replacement rows by
   changing their exact prepared prompt/profile bytes. It cannot alter the
   Phase-A policy or install new authority.

If any byte of the prepared Phase-A JSON changes, prepare a new reviewed
four-change sequence; do not update the in-code digest or combine phases.

The one-time legacy bootstrap is narrower: an exact in-code bootstrap row may
install the first schema-2 envelope over an absent or schema-1 protected source.
A schema-1 source's active `rotations` authority must be preserved exactly; an
old-format schema-1 `requirement_rotations` list is validated but grants no
authority. An absent source has no active rotations to add. After schema 2 is
protected, the normal Phase A rules above apply.

### Phase B: consume protected authority

Phase B may update only the prompt and verification-profile bytes authorized by
the now-protected row. Every other managed prompt must remain byte-identical,
resolving approved aliases to their protected canonical prompt path. Authorized
bytes must match the row's prepared
`head_prompt_sha256` and `head_policy_sha256` exactly, including formatting and
line endings. Any byte drift after Phase A was prepared invalidates the
transition: do not edit the digests in Phase B or combine replacement authority
with consumption. Prepare and protect a new dormant row in a new Phase A
instead.

Run the deterministic verification-profile and rollout-policy suites for both
phases. Do not use a staging registry item to prepare or validate either phase.

```bash
pytest -q tests/test_sync_core_verification_profiles.py
pytest -q tests/test_sync_core_pdd_rollout_policy.py
```

## Story Regression Coverage

What the `story-regression` job does **today** is run the executable
`@pytest.mark.story` suite (`make regression-stories` → `pytest -m story`) and
fail on any failing or stale story. This is a pass/fail gate — it does not yet
emit a machine-readable coverage artifact.

The deterministic (no-LLM) coverage emitter is a **library capability that CI
does not yet invoke.** `pdd/story_coverage.py` can compute a `StoryCoverage`
result, print a one-line summary, append it to `$GITHUB_STEP_SUMMARY`, and write
the durable contract to `.pdd/evidence/stories/coverage.latest.json` (schema:
`pdd/schemas/story_coverage.schema.json`) plus a per-run snapshot under
`.pdd/evidence/stories/runs/`. Its shape is:

```text
story regression: 142 tests across 96/110 stories (87% covered), 142 passing
```

But nothing in the CI path calls it: `make regression-stories` /
`tests/story_regression.sh` only run `pytest -m story`, and the `story-regression`
job writes no summary line, no JSON, and uploads no artifact. The only in-tree
caller is the demonstration script `context/story_coverage_example.py`. Wiring
the emitter into the lane (the summary line, the `coverage.latest.json` upload,
and the pass/fail + freshness verdicts that let it emit `status: "ok"` or an
honest failure instead of the current `status: "not_applicable"`,
`pass_rate: null`, `passing_test_count: 0`) is tracked in issue #1909.

Until then, treat the coverage artifact the way
[docs/evidence_manifest.md](evidence_manifest.md) describes it — a schema-versioned
contract with a `not_applicable` degraded mode — and read that document for the
field definitions. Trend is computed downstream in `pdd_cloud` from the stateless
per-run snapshots once the lane emits them; the emitter itself does no trend math.
