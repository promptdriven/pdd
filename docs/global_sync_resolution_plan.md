# Global Sync Execution Plan

Status: active replacement plan; execution contract must pass before feature work
Last updated: 2026-07-23
Tracking epic: [promptdriven/pdd#1932](https://github.com/promptdriven/pdd/issues/1932)
Primary consumer: `promptdriven/pdd_cloud`
Historical plan: [`archive/global_sync_resolution_plan_history_2026-07-22.md`](archive/global_sync_resolution_plan_history_2026-07-22.md)

<!-- global-sync-ledger-source: global_sync_evidence_ledger_source.yaml -->

The existing evidence ledger remains an append-only status and provenance
record. It does not override this plan's milestones, command registry, or
current-main preflight. M0 must reconcile its stale current-state rows without
rewriting historical evidence. Until M0 passes, its active blocker, command, and
promotion rows are quarantined: they are historical claims, not execution
authority or proof of a current milestone.

## 1. Decision and success levels

The current canonical sync implementation is a useful fail-closed detector and
validator, but it is not yet a working canonical repair system. When canonical
policy is active, legacy mutators intentionally stop before generation because a
generate-to-staging repair executor is absent. Releasing or certifying the
checker before closing that loop would package a blocker rather than deliver
global sync.

This plan separates three outcomes that were previously conflated:

1. **Working Global Sync (M1):** one complete PDD unit and one real pdd_cloud
   unit can detect, repair, validate, transactionally finalize, recover, and
   rerun with zero writes. Ambiguous conflicts block with zero unattended
   writes.
2. **Production Global Sync (M4):** every production mutator uses the canonical
   APIs, both repositories run the released checker in protected CI, and every
   expected-managed unit is enforced with current trusted semantic evidence.
   Units removed through the protected ownership/denominator process are no
   longer expected-managed; rollout exclusions do not satisfy M4.
3. **Certified Global Sync (M5):** the optional high-assurance supply-chain,
   independent-verifier, coverage, and temporal predicates pass.

M1 is the first delivery target. M4 is the issue's production target. M5 is a
separate assurance program and must not block implementation, dogfooding, or
production rollout unless the operator explicitly makes certification a release
requirement.

The non-negotiable functional invariant is:

```text
classify current state
-> produce an explicit repair or conflict plan
-> generate only into isolated staging
-> validate staged outputs
-> crash-durably commit artifacts + shared metadata + evidence + report + fingerprint
   while canonical readers hold a transaction barrier
-> recover after process death to a complete old or complete new state
-> rerun with zero writes
```

No baseline reset, ledger entry, report, signature, or certificate substitutes
for that loop.

## 2. Execution authority and minimal human involvement

When the operator tells Codex to **execute this plan**, that instruction
authorizes the following actions within dedicated task worktrees without
additional confirmation:

- Fetch refs and inspect local/remote state.
- Create named worktrees and task branches from the recorded protected-main SHA.
- Edit files within the assigned track's write set.
- Install development dependencies in an isolated environment.
- Run tests, linters, builds, local containers, and failure injections.
- Make local commits, rebase task branches, and resolve non-semantic merge
  conflicts.
- Push task branches, open or update draft PRs, rerun existing CI, and attach
  generated evidence when the execution request includes remote delivery.
- Spawn parallel implementation and review agents with the ownership boundaries
  in section 5.

Codex must batch work and ask only at these decision boundaries:

1. Publishing a package or OCI image for the first time, or changing a protected
   release alias.
2. Enabling or strengthening protected-branch enforcement, changing secrets,
   signing identities, branch protection, or production credentials.
3. Choosing the winner for a real prompt/code conflict when the choice changes
   product intent. Multiple conflicts are presented in one batch.
4. Reducing the expected-managed denominator, permanently changing ownership, or
   deleting unique branches/worktrees. The coverage sample in M0 supplies one
   batched scoping decision; silence defaults to **no denominator reduction**.

Normal technical choices, test fixes, refactors within the declared design,
branch pushes, draft PR updates, CI reruns, evidence recording, and safe rebases
do not require a question. If the execution environment itself requires tool
approval, request the narrowest reusable approval once per action class rather
than once per command.

Standard CODEOWNERS review and required hosted checks remain repository controls;
they are not reasons to pause local work. Exact-SHA adversarial review is used at
M4 enforcement and M5 certification, not for documentation-only changes or every
leaf implementation PR.

## 3. M0: executable-baseline gate

No A-E feature work starts until M0 passes. A bounded **M0-bootstrap track** is
the explicit exception: it exists to create the verifier/state files, reconcile
the active ledger/workflow, and close the focused current-main failure needed for
M0 itself. M0 prevents work on a stale diagnostic branch and prevents a prose
command from being mistaken for a real interface.

The integration owner also owns the M0-bootstrap track. Its write set is limited
to:

- `scripts/verify_global_sync_execution_contract.py` and its tests.
- `docs/global_sync_execution_state.yaml`.
- `docs/global_sync_evidence_ledger_source.yaml` and its generated ledger.
- The protected ledger-check step in `.github/workflows/unit-tests.yml`.
- The smallest runner/finalizer/test delta needed to close
  `tests/test_sync_core_reporting.py::test_trusted_finalizer_commits_artifact_closure_evidence_and_fingerprint`,
  whose observed failure is `pytest=COLLECTION_ERROR`.

If closing that node requires a production-interface change rather than a
bounded baseline correction, M0 remains red and ownership transfers to Track A
or B through a reviewed interface proposal. After M0, those production files
return to their section 5 owners.

### 3.1 Fresh-main and worktree preflight

The integration owner must:

1. Fetch `origin/main` and record `GLOBAL_SYNC_BASE_SHA="$(git rev-parse
   origin/main)"`.
2. Verify the source checkout is clean.
3. Verify the selected base is the protected remote head at kickoff.
4. Create a fresh integration worktree and one worktree per active track. Never
   implement from frozen PR #1995 or from the documentation-plan worktree.
5. Record every worktree, branch, owner, base SHA, and write set in
   `docs/global_sync_execution_state.yaml`.
6. Re-run the base-SHA check before each integration PR. Base movement triggers a
   bounded rebase and affected-test rerun, not a restart of unrelated tracks.

### 3.2 Command-contract verifier

The first implementation deliverable is
`scripts/verify_global_sync_execution_contract.py`. It must fail when:

- A validation command names a missing module, script, test, workflow, or console
  entry point.
- A Click command is shown under the wrong parent. Canonical commands are
  currently top-level (`pdd certify`, `pdd validate`, `pdd baseline`, and
  `pdd recover`); `pdd sync certify` and `pdd sync-core certify` are invalid.
- A documented option is not accepted by the installed source and built-wheel
  CLIs.
- A step marked executable has an empty validation command list.
- Generated ledger state disagrees with this active plan or the recorded base
  SHA.
- A command labeled `TO_BUILD` is used before the PR that implements it merges
  into the integration branch.

The verifier owns a small machine-readable command registry. Every entry has one
of `EXISTS`, `TO_BUILD`, `EXTERNAL_PROTECTED`, or `ARCHIVED`. Each entry records
its exact argv, owner, introducing milestone/PR, earliest invocable milestone,
and last source/wheel SHA on which it was validated.

- `TO_BUILD` may appear only as a declaration. It is invalid in an invoked
  validation list, promotion bundle, passed predicate, or current blocker.
- `ARCHIVED` preserves an old command string but is never executable.
- `EXTERNAL_PROTECTED` must bind an installed artifact digest and control-plane
  identity before invocation.

During M0 bootstrap, move obsolete ledger command strings and attempt history to
explicitly archived/non-executable fields. Replace the checker-release blocker
with `m0-executable-baseline`, and make active ledger rows use the same
M0-M5 milestone IDs, order, current base SHA, and executable-state vocabulary as
this plan. A future command may remain declared as `TO_BUILD`; it may not be
claimed as executed or passed.

The protected unit-test workflow must run both:

1. Generated ledger byte-drift and remote promotion verification.
2. The command-contract verifier's semantic plan/ledger concordance check.

Byte equality alone is insufficient.

The following previously referenced components begin as `TO_BUILD` and are
explicit deliverables, not presumed commands:

- `pdd.sync_core.vertical_slice_verifier`
- `pdd.sync_core.production_routing_verifier`
- `pdd.sync_core.scan_verifier`
- `pdd.sync_core.consumer_ownership_verifier`
- `pdd.sync_core.nightly_ledger_verifier`
- `pdd-sync-reference-verifier`
- `pdd-sync-certificate-finalizer`
- `.github/workflows/global-sync-merge-group.yml`
- `.github/workflows/global-sync-shadow-nightly.yml`
- `tests/test_sync_core_runner_pytest.py`
- `tests/test_global_sync_vertical_slice.py`

Only components needed by M0-M4 are built before production rollout. M5-only
components remain deferred.

### 3.3 Green baseline

Fix every failure in the focused current-main suite before feature work. The
trusted-finalizer node named in the M0-bootstrap write set must reproduce with a
captured runner command, collection output, config/plugin closure, interpreter,
and environment digest, then pass in source and built-PDD-wheel environments. It
cannot be relabeled as expected failure or release evidence.

M0 validation:

```bash
python -m pdd --help
python -m pytest -q \
  tests/test_sync_core_cli.py \
  tests/test_sync_core_transaction.py \
  tests/test_sync_core_reporting.py \
  tests/test_sync_core_standalone_package.py
python scripts/verify_global_sync_execution_contract.py \
  --plan docs/global_sync_resolution_plan.md \
  --state docs/global_sync_execution_state.yaml
```

M0 exits only when all commands return zero in the supported development
environment and the built-wheel CLI exposes the same declared command surface.

### 3.4 Early scope and scale samples

Run these non-production samples during M0 bootstrap, in parallel with
command-contract work:

- Partition the current PDD human-attestation-only units into obligations
  derivable from existing tests, genuinely missing tests, and units whose
  ownership/scope needs a product decision.
- In disposable clean clones, generate and validate migration patches for a
  representative sample of ten units: nested config, include closure, duplicate
  basename, human-owned test, multi-file example/test, executable artifact,
  architecture override, runtime dependency, and a historically problematic
  unit. Do not commit sample migrations to production metadata during M0.
- Inventory one real pdd_cloud subtree and select the M1 canary before changing
  upstream production APIs.
- Benchmark a full read-only inventory/classification and a 20-unit affected
  closure. Record time, peak memory, subprocess count, and report size.
- Inventory package-index, OCI-registry, protected-environment, signer, anchor,
  and pdd_cloud access. Missing credentials block only their dependent milestone,
  not local M1 engineering.

The single human scope report contains counts, examples, estimated effort, and a
recommended default. If no decision is supplied, continue with no denominator
reduction and do not let unresolved certification coverage block M1-M4.

## 4. Risk order

Work is selected by the earliest falsifiable product risk, not by evidence
bookkeeping.

| Priority | Risk | Earliest proof |
| --- | --- | --- |
| 1 | Repair writes incorrect or mixed state | M1 crash-injected staged repair |
| 2 | Current test/CLI baseline is not reproducible | M0 source and wheel gate |
| 3 | PDD abstractions do not fit pdd_cloud | M0 inventory plus M1 real canary |
| 4 | Pytest evidence can miss or misreport execution | M0/M1 runner contract |
| 5 | Source behavior differs from the PDD application wheel | M1 built-wheel vertical slice |
| 6 | Canonical APIs cannot replace every legacy mutator | M2 routing verifier |
| 7 | Inventory/profile migration is too large or ambiguous | M0 ten-unit sample |
| 8 | Protected CI/release infrastructure is unavailable | M0 access inventory, M3 shadow |
| 9 | High-assurance certificate construction is flawed | M5, after production works |

Any observed data loss, unexpected destination write, false clean result,
source/wheel divergence, or pdd_cloud semantic mismatch is a stop-the-line event.
The owning track writes a minimal reproduction before continuing.

## 5. Parallel worktree topology

Use one integration owner and up to five concurrent implementation tracks. Every
worker is responsible for its declared files, is not alone in the repository,
must preserve other edits, and must not revert unrelated changes.

### Track A: repair and transaction vertical slice

Owns:

- `pdd/sync_core/planner.py`
- `pdd/sync_core/transaction.py`
- `pdd/sync_core/finalize.py`
- New `pdd/sync_core/repair.py`
- New `pdd/commands/resolve.py`
- Transaction, repair, recovery, and vertical-slice tests

Delivers:

- Generate-to-staging for one canonical prompt-side repair.
- A typed repair plan with complete read/write sets and CAS preconditions.
- Crash-durable artifact/shared-metadata/evidence/report/fingerprint commit.
  Canonical readers acquire a shared transaction barrier and never consume a
  unit while its journal is `COMMITTING`; they retry or return
  `RECOVERY_REQUIRED`. Raw filesystem readers are outside this guarantee and the
  product must not describe sequential multi-file installation as filesystem
  atomicity.
- Explicit prompt-wins, code-wins, and three-way-review plans; unattended
  conflicts perform zero writes.
- Recovery and immediate no-op rerun.

Track A is the critical path.

### Track B: pytest authority and finalizer stability

Owns:

- `pdd/sync_core/runner.py`
- `pdd/sync_core/verification.py`
- `pdd/sync_core/pytest_probe.py`
- `tests/test_sync_core_runner.py`
- New `tests/test_sync_core_runner_pytest.py`
- Verification-profile and runner-focused tests

Delivers:

- Deterministic protected/candidate collection and executed-node comparison.
- Binding of config-loaded plugins, `conftest.py`, local executable support, and
  exact runner configuration.
- Fail-closed skip, xfail, deselection, zero-test, collection-error, timeout, and
  dirty-support behavior.
- A source/wheel-stable runner contract used by Track A.

Only profile-demanded adapters are implemented. Jest, Vitest, Playwright, and
isolated-black-box work are deferred unless the protected pdd_cloud registry
demands them.

### Track C: standalone checker packaging

Owns:

- `pdd/sync_core/standalone_package.py`
- `pdd/sync_core/checker_cli.py`
- `pdd/sync_core/released_checker.py`
- Standalone package source, build configuration, lock generation, and package
  tests
- Checker-release workflow files that do not change protected policy

Delivers:

- A non-`pdd` import boundary with checker-only dependencies.
- Reproducible wheel, strict lock/RECORD validation, compatible-wheel tag tests,
  clean-install smoke, and exact digest output.
- A draft release manifest.

Track C may build locally after M0 and continue alongside M1. The standalone
checker is read-only and is not an M1 repair runtime. Publication waits for M1
and M2's release-relevant routing checks.

### Track D: production routing and compatibility

Owns:

- `pdd/sync_core/capabilities.py`
- `pdd/continuous_sync.py`
- `pdd/sync_determine_operation.py`
- `pdd/sync_orchestration.py`
- `pdd/sync_main.py`
- `pdd/update_main.py`
- `pdd/ci_drift_heal.py`
- Other legacy mutator adapters assigned in the capability registry
- New `pdd/sync_core/production_routing_verifier.py`

Track D begins read-only inventory during M0, then implements against Track A's
frozen repair interface after M1. It removes independent identity, include,
hash, classification, and canonical metadata-write logic without changing
public behavior accidentally.

### Track E: consumer, profiles, and CI shadow

Owns:

- PDD inventory/profile generation and migration data
- pdd_cloud integration branches and consumer-owned orchestration
- New scan and consumer-ownership verifiers
- Shadow merge-group/nightly workflows
- Canary fixtures and protected-policy proposals

Track E runs the M0 sample and prepares shadow infrastructure concurrently, but
does not bulk-migrate profiles or enable enforcement before M1.

### Shared-file rule

Only the integration owner edits:

- `pdd/sync_core/__init__.py`
- `pdd/commands/__init__.py`
- `pyproject.toml`
- Generated architecture/ownership/expected-managed registries shared by tracks
- `docs/global_sync_execution_state.yaml`
- `docs/global_sync_evidence_ledger_source.yaml`
- `docs/global_sync_evidence_ledger.yaml`

Tracks expose integration patches or requested symbols rather than editing these
files. Integration order is M0 bootstrap, A interface, B runner contract, A+B
vertical slice, built PDD application wheel, D routing, C standalone checker,
then E consumer/shadow. Independent tests continue while earlier commits
integrate.

The dependency graph is:

```text
M0 executable baseline
├── A repair core ───────────────┐
├── B pytest authority ─────────┼── M1 working vertical slice
├── built PDD application wheel ┤
└── E pdd_cloud canary/sample ──┘
├── C standalone checker build ────────────────┐
                                  ├── D production routing ── M2
                                  ├── C protected release ─── M3
                                  └── E shadow migration ──── M3
                                       └── M4 enforcement
                                            └── M5 optional certification
```

## 6. Milestones and executable exit gates

### M1: Working Global Sync

Implement the smallest complete repair loop before broad routing or release.
The lifecycle fixture uses a fake/deterministic generator for exhaustive fault
injection, and one bounded credentialed run through the real production
generator is mandatory. Missing credentials leave M1 red; they do not convert
the canary to optional evidence.

Required scenarios:

1. Included-doc edit finds and repairs all affected units in dependency order.
2. Prompt-only edit stages and commits the expected code/example/test changes.
3. Code-only edit produces a requirement-preserving review patch or blocks; it
   never stamps the baseline.
4. Prompt+code edit reports conflict and performs zero unattended writes.
5. Test-only and example-only edits preserve ownership and run the real runner.
6. Missing/corrupt artifact or fingerprint fails or repairs from an unambiguous
   source; it never becomes silently current.
7. Validation failure leaves destination artifacts and baseline unchanged.
8. Process death and a late install failure at every
   prepare/journal/install/finalize phase, including a multi-unit shared-resource
   closure, recover to the complete old or complete new state.
9. A concurrent canonical reader encountering `COMMITTING` never observes or
   reports mixed state; it waits, retries, or returns `RECOVERY_REQUIRED`.
10. Concurrent external content, mode, or symlink change becomes a conflict and
    is not overwritten.
11. Immediate rerun writes zero files.
12. All scenarios pass from a source checkout and a clean installed **PDD
    application wheel containing the repair/finalizer modules**. The standalone
    read-only checker wheel is not used as the repair runtime.
13. One real PDD unit and one real pdd_cloud unit pass the same loop.

M1 deliverables:

- `tests/test_global_sync_vertical_slice.py`
- `pdd.sync_core.vertical_slice_verifier`
- `pdd resolve`
- Public JSON report fields for plan, transaction, validation, recovery, and
  no-op status

M1 validation is defined by the newly added tests and verifier. The command
contract must prove their presence before invoking them. M1 is complete when the
fixture, credentialed production-generator canary, PDD canary, pdd_cloud canary,
source run, and PDD application-wheel run all pass. `pdd resolve` is integrated
and registered in PR B as part of M1.

### M2: Complete canonical production routing

Freeze the Track A interfaces after M1, then route every registered mutator:

- generate, example, test, auto-deps, update single/all, fix, sync, change
- metadata and architecture sync
- CI heal and repair entry points
- server, agentic, and subprocess launchers

The capability registry enumerates every entry point and derives the mutation
property suite. An unregistered mutator or undeclared managed/shared write fails
CI. Compatibility modules may orchestrate but may not independently resolve
units, parse includes, hash fingerprints, classify drift, or write canonical
metadata.

M2 exit:

- Production-routing verifier reports zero independent implementations and zero
  mutators outside canonical APIs.
- Canonical `pdd sync` and the already-integrated `pdd resolve` route through the
  same repair API and are usable public paths, not placeholders.
- Full mutation property suite passes.
- Full 500-unit read-only benchmark and 20-unit affected repair meet recorded
  budgets or trigger a design correction before rollout.
- Source/wheel parity and immediate no-op reruns remain green.

### M3: released checker and nonblocking shadow rollout

After M1 and the relevant M2 routing checks:

1. Present one release-approval packet containing the exact wheel, dependency
   lock, RECORD proof, source SHA, source/wheel vertical-slice results, rollback
   version, and intended protected alias.
2. On one approval, publish and pin the checker.
3. Run clean installed-wheel verification against exact-SHA PDD and pdd_cloud
   clones.
4. Enable nonblocking PR/merge-group/post-merge/nightly shadow checks.
5. Migrate profiles and fingerprints by bounded PDD/pdd_cloud subtrees. Expiring,
   visible rollout exclusions may defer enforcement for a subtree; they never
   produce `IN_SYNC` or count toward M5.

M3 does not require OCI sealing, an independent reference verifier, an external
anchor, seven nights, five organic merges, or 100% profile coverage.

M3 exit:

- Released digest is pinned and rollback-tested.
- The real pdd_cloud canary passes.
- At least three consecutive complete exact-SHA shadow runs, including a
  synthetic merge-group/post-merge lifecycle run and one injected
  drift/recovery run, are green with zero unexplained writes.
- Policy-tamper and forged-evidence fixtures remain red.

### M4: Production Global Sync

Present one enforcement-approval packet containing:

- Exact released checker and repository SHAs.
- M1/M2/M3 results and current shadow history.
- Gross inventory and every non-`IN_SYNC`/excluded subtree.
- Rollback command and responsible owner.
- Expected merge impact and performance.

After one approval, enable enforcement for migrated subtrees first, then expand.
Partial enforcement is M3 rollout progress, not M4 completion. Rollback changes
enforcement to report mode and never rewrites baselines.

M4 exit:

- Manual, agent, PDD, CI repair, and hotfix channels cannot land managed drift
  for any expected-managed unit.
- Every production mutator finalizes transactionally and reruns with zero writes.
- Both repositories have complete honest inventory; every expected-managed unit
  is enforced, semantic `VERIFIED` from current trusted evidence, and baseline
  `CURRENT`.
- Human-owned subjects remain honestly inventoried but are outside the
  expected-managed denominator. A former expected-managed unit is outside M4
  only after the approved ownership/denominator process records its tombstone or
  transition; rollout exclusions and waivers do not satisfy this condition.
- pdd_cloud retains orchestration only; upstream owns identity, discovery,
  include graph, affected closure, path resolution, hashing, classification, and
  transaction semantics.
- Post-merge and nightly scans are complete even after ledger/cursor deletion.

M4 closes the production functionality program only at full expected-managed
enforcement. There may be additional human-owned or explicitly decommissioned
coverage work, but no expected-managed profile/evidence debt remains.

### M5: optional Certified Global Sync

Start M5 only after M4 is stable and the operator explicitly requests the
high-assurance certificate. Once requested, the following predicates are
normative and may not be weakened by implementation convenience:

- Sealed, digest-pinned OCI runtime with SBOM/package provenance.
- Separately implemented and released reference verifier sharing no code with
  `pdd.sync_core`.
- Protected signer, replay controls, rotation/revocation, and external append-only
  anchor.
- Complete inventory for PDD and pdd_cloud, with 100% of expected-managed units
  machine verified by current trusted evidence; human-only, excluded, waived,
  unaccounted, and red managed counts are zero.
- pdd_cloud owns no sync identity, discovery, include, graph, affected-closure,
  path, hashing, classification, or transaction semantics.
- All 18 protected lifecycle rows pass from clean exact-SHA clones and installed
  artifacts, including crash/race/tamper injections and zero-write reruns.
- Seven consecutive qualifying UTC nights contain at least five organic protected
  merges, zero check-failure nights, no more than two named/checksummed
  infrastructure-void nights, and at least 25 seeded mutations per night with
  every injected mutation detected.
- Nightly rows use immutable external anchoring, complete scans after
  ledger/cursor deletion, and verified repository/SHA temporal continuity.
- Candidate-controlled verifier, expectation, signer, scenario, checker, PATH,
  wheelhouse, or time inputs accepted: zero.
- Independent exact-payload adversarial review and a separately released,
  digest-pinned certificate finalizer.
- Primary and reference verifiers accept the unchanged payload and detached
  final evaluation using protected repository identities, SHAs, issuer material,
  expectations, anchor configuration, and trusted time.

These predicates describe the certificate, not whether global sync works in
production. The active certificate schema, lifecycle scenario set, exact
night/organic-merge thresholds, verifier CLIs, and trust expectations must be
ratified in a protected M5 annex before implementation and before the first
qualifying night. The annex may strengthen but not omit the predicates above.

M5 commands and schemas must be added to the command-contract registry and pass
source/wheel/external-input validation before the first qualifying night. No
historical command string is authoritative merely because it appears in the
archived plan or evidence ledger.

## 7. Integration PRs

Use at most six integration PRs for M0-M4. Parallel track commits may be reviewed
as stacked leaf PRs, but bookkeeping-only PRs do not become critical-path gates.

1. **PR A — executable baseline:** command-contract verifier, current-main
   execution state, focused-suite fix, ten-unit/profile sample, pdd_cloud canary
   selection.
2. **PR B — working vertical slice:** Track A repair/transaction loop plus Track B
   pytest authority and all M1 scenarios.
3. **PR C — production routing:** capability completeness, compatibility adapters,
   routing verifier, scale benchmark, and canonical sync routing. Public resolve
   was already integrated in PR B.
4. **PR D — checker release:** standalone package, clean wheel proof, protected
   release manifest and pin.
5. **PR E — PDD/pdd_cloud shadow rollout:** bounded profile/data migrations,
   consumer ownership retirement, real canary, shadow workflows.
6. **PR F — enforcement:** separately reviewed policy-only activation with tested
   rollback.

Each PR is based on current protected main, contains one coherent behavior change,
passes affected tests plus the command contract, and receives independent review.
Documentation and generated evidence travel with the behavior they describe
unless a protected control-plane update must be separate.

## 8. Testing policy

Test layers:

| Layer | Required proof |
| --- | --- |
| Pure | Identity, include graph, hash, classifier, planner, schema |
| Component | Runner authority, transaction phases, recovery, routing guards |
| Lifecycle | Real Git repo and CLI subprocess through live mutation path |
| Package | Clean installed wheel with no source-checkout imports |
| Consumer | Real PDD and pdd_cloud canaries |
| Protected shadow | PR, merge-group, post-merge, nightly, stale-head, tampering |

An E2E test must cross a real process or repository boundary and exercise the
live mutation path. Wrapper-only tests do not count.

Required mutation assertions:

- Exact exit code and structured verdict.
- Destination bytes and modes before and after.
- Journal/recovery state.
- Base/head or merge-group SHA.
- Complete planned and actual write sets.
- Validation evidence binding.
- Second-run write count.

Path filters may provide a fast-fail lane but never replace the complete
shared-core suite for a release or enforcement PR.

Flaky retries preserve the first result and cannot convert a failure into trusted
pass. Required skips, xfails, deselections, collection errors, timeouts, and
quarantines remain non-pass outcomes.

## 9. Safety, rollback, and stop conditions

- All fault injection occurs in disposable fixtures or canary branches, never on
  protected branches.
- No track writes through symlinks or outside the checkout.
- Read-only commands report `RECOVERY_REQUIRED`; they do not recover implicitly.
- Bot repair uses sandbox -> patch -> narrow applier -> head-SHA CAS -> recheck.
- No bot force-pushes, chooses a conflict winner, or baseline-resets to obtain
  green.
- Release rollback pins the previous trusted checker; enforcement rollback changes
  `enforce -> report`.
- Schema migration preserves the prior readable state until all trusted writers
  meet the minimum version.
- A stale base invalidates only evidence bound to that base. It does not discard
  passing pure/component work whose inputs are unchanged.

Stop and replan immediately for:

- Any data loss or old/new mixed transaction state.
- Any external edit overwritten after planning.
- A successful exit with incomplete validation/finalization.
- Source/wheel or PDD/pdd_cloud semantic divergence.
- A candidate-controlled policy, runner, expectation, or verifier input accepted
  as trusted.
- A scale result that makes normal PR checks impractical.

## 10. Progress reporting

Use one scoreboard generated from `docs/global_sync_execution_state.yaml`:

```text
base SHA: <sha>
milestone: M0|M1|M2|M3|M4|M5
working vertical slice: pending|pass
source/wheel parity: pending|pass
pdd canary: pending|pass|fail
pdd_cloud canary: pending|pass|fail
canonical mutators routed: N/total
focused/full tests: passed/failed/skipped
shadow runs: N consecutive, injected recovery pass|fail
released checker digest: pending|sha256:...
enforcement: off|report|partial|full
active stop-the-line risk: none|<one risk>
human decision needed: none|release|enforcement|conflicts|scope
track status: A=... B=... C=... D=... E=...
next integration: <one concrete artifact or PR>
```

Progress is measured by executable exit predicates, not document length, commit
count, evidence-row count, or local implementation claims.

## 11. Immediate next actions

1. Merge or rebase this replacement plan onto current protected main.
2. Create the fresh integration and track worktrees; record their exact base SHA,
   owners, and write sets.
3. In the M0-bootstrap track, implement the command-contract verifier, reconcile
   active ledger/workflow semantics, reproduce and fix the focused
   trusted-finalizer collection failure, and run the disposable ten-unit and
   pdd_cloud scope samples. Track D may inventory legacy mutators read-only in
   parallel.
4. Run the complete M0 gate and record its exact source/wheel SHAs.
5. After M0 passes, in parallel:
   - Track A builds the staged repair vertical slice.
   - Track B closes the pytest authority contract.
   - Track C builds, but does not publish, the standalone checker wheel.
   - Track E turns the disposable scope results into bounded migration patches
     and the real pdd_cloud canary fixture.
   - Track D implements routing against Track A's frozen interface.
6. Integrate A+B+E into the source vertical slice, then build and test the PDD
   application wheel. Continue Track C's standalone checker independently for
   M3 release.
7. Do not start OCI, anchor, independent reference-verifier, seven-night, or
   finalizer work until M4 is complete and M5 is explicitly authorized.
