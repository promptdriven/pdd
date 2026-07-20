# Frozen PR #1995: global-sync extraction manifest

Status: ratified extraction boundary for the first checker release.

## 2026-07-19 Gate 2 package-boundary disposition

This supersedes the Gate 2 release path below without reclassifying frozen #1995
history. Protected main is `e072e09e4cfb7fa0224e75a11fbf1ffbd61ec347`.

| Disposition | Evidence and extraction rule |
| --- | --- |
| `already-merged-prerequisite` | [#2228](https://github.com/promptdriven/pdd/pull/2228), reviewed at `aa32884363e383745e878770a247e4897977de59`, had all 12 checks green, and merged as `c2575db6cfd3f5144081bb517724043a057d0f9c`. It preauthorizes only the literal five package-boundary paths: the standalone-checker module manifest, `standalone_package.py`, `checker_cli.py`, and their two tests. It is neither a release nor a pin. |
| `landed-package-boundary` | [#2229](https://github.com/promptdriven/pdd/pull/2229) landed the standalone non-`pdd` checker distribution with checker-only dependencies, strict lock/`RECORD` validation, and the exact z3 compatible-wheel regression. Prior reviewed head `be90cbdc7e5280eae19db02d041fd05467315b11` had only the two `_VITEST_RUNTIME_SOURCE` reserved-prefix assertions fail in Unit [29705890972/job 88242687030](https://github.com/promptdriven/pdd/actions/runs/29705890972/job/88242687030); a bounded correction received Sol HIGH approval at `ff95e9d31f8029f8f9cb1c55edb1ec328b006c16`. The final 12 checks were green and the protected squash merge is `e072e09e4cfb7fa0224e75a11fbf1ffbd61ec347` at `2026-07-20T00:17:55Z`. This is package-boundary evidence only, not release evidence. |
| `release-required-delta` | Implement the checker-specific release workflow and protected publication of the standalone wheel with its exact released digest. PR [#2230](https://github.com/promptdriven/pdd/pull/2230) is reviewed/local evidence only at `842b73e93d0d2e275726d0755f6b0b3347a13488`; its initial and rerun GitHub 503/504 failures are external-service evidence, not product-pass evidence. OCI and protected pins remain later release-required deltas. |
| `excluded-diagnostic` | Keep #2225 workflow/bootstrap commits and hosted lanes as diagnostic evidence only. Head `09015bcc79c00575262e8c23d9b14693ae8be80f` ended in a build-version failure at [job 88224039194](https://github.com/promptdriven/pdd/actions/runs/29698754085/job/88224039194); head `d060da1cc1d6c81abf0c42cf5df69ac81d79a75e` ended in a read-only build-source failure at [job 88224395133](https://github.com/promptdriven/pdd/actions/runs/29698879393/job/88224395133); and closed head `0bae19c2fb9575d8b8edccaeee3c5d9420e00e9f` ended in the eager `pdd.__init__` → `update_main.py` → GitPython/no-git failure at [job 88224752678](https://github.com/promptdriven/pdd/actions/runs/29699017734/job/88224752678). No artifact upload or target lock completed, and `GIT_PYTHON_REFRESH=quiet` is rejected. |

The standalone checker boundary is landed on protected main. The next same-day,
under-24-hour deliverable is the checker-specific release workflow and protected
publication of the standalone wheel with its exact released digest. It excludes
`pdd/__init__` refactoring, OCI, certificates, and scenario expansion. A later
sealed OCI layer supplies Git/system closure; a final protected pin-wiring layer
binds released checker/OCI digests and prevents candidate control of checker,
scenarios, PATH, wheelhouse, expectations, or verifier inputs.

The OCI layer is cryptographically downstream of the release: provenance binds
the exact released checker wheel digest and exact checker dependency-lock digest
alongside image, Dockerfile/source SHA, SBOM, and dpkg inventory. Protected
pre-launch verification proves installed checker files and `RECORD` equivalent
to that pinned wheel. Execution uses only the verified absolute protected
interpreter and installed entrypoint with `-I -S`; it cannot resolve a module
from candidate checkout or CWD. Signed evidence carries wheel, lock, image,
SBOM/dpkg inventory, interpreter, and entrypoint identities. These are future
acceptance contracts, not executable commands or completed Gate 2 evidence.

## Fixed comparison and decision rule

| Name | SHA |
| --- | --- |
| Diagnostic base | `39776aa9bb027c638812a01b8dabbe03cab92f64` |
| Frozen diagnostic head | `d334266680881cbda59de4ecd4df967c92159fa7` |
| Protected main | `e072e09e4cfb7fa0224e75a11fbf1ffbd61ec347` |

This is a three-way, hunk-level manifest, not a proposal to merge the frozen
branch.  The only permitted classifications are:

- `already-merged-prerequisite` — a patch-equivalent prerequisite is already on
  protected main;
- `release-required-delta` — absent from protected main and necessary for the
  first checker release; or
- `excluded-diagnostic` — intentionally retained only with frozen #1995.

Protected release profiles demand exactly `{pytest}`.  Therefore no Vitest,
Jest, Playwright, native-addon, Stage A0/A, JavaScript-toolchain, workflow, or
diagnostic-script hunk is a release-required delta.  “Shared fail-closed” below
means profile-invalidity handling before stale evidence reuse or finalization;
it does not authorize an adapter.

Reproducible inventory and equivalence checks:

```bash
base=39776aa9bb027c638812a01b8dabbe03cab92f64
head=d334266680881cbda59de4ecd4df967c92159fa7
main=c712cbb7e08c157757a238cb8e49d65a9a3a2239
git diff --name-only "$base" "$head" | sort -u | wc -l       # 48
git diff --check "$base" "$head"                              # clean
comm -12 \
  <(git diff --name-only "$base" "$main" | sort) \
  <(git diff --name-only "$base" "$head" | sort)             # exact six paths
for ref in "$main" "$head"; do
  git diff --unified=0 "$base" "$ref" -- \
    .pdd/sync-ownership.json \
    .pdd/verification-profile-rotations.json \
    docs/global_sync_evidence_ledger.yaml \
    docs/global_sync_resolution_plan.md \
    pdd/sync_core/verification.py \
    tests/test_sync_core_pdd_rollout_policy.py
done
git diff --unified=0 "$base" "$head" -- pdd/sync_core/finalize.py \
  pdd/sync_core/reporting.py tests/test_sync_core_reporting.py
```

`git merge-base "$head" "$main"` is the diagnostic base. Protected main now
also contains `2c917fde4`, the docs-gate squash merge `e7735e0f3`, and the
#2216 ownership-prerequisite squash merge `c712cbb7e`; the latter contributes
exact absent-path preauthorizations for the four Gate 1 artifacts. The
hunk-level comparison below, rather than commit-level `git cherry`, finds zero
direct changed hunks with a patch-equivalent foundation already merged. The
`already-merged-prerequisite` net is deliberately zero, rather than treating an
overlapping filename or the common base as equivalence.

### Hunk-level reconciliation of the six intersecting paths

The paths below are the complete intersection of `git diff --name-only "$base"
"$main"` and `git diff --name-only "$base" "$head"`.  Hunk headers come from
the `--unified=0` command above; the changed operands/rows were then compared,
not just their enclosing filenames.

| Path | Base to protected main | Base to frozen head | Resolution of frozen-head hunks |
| --- | --- | --- | --- |
| `.pdd/sync-ownership.json` | eight additions at base lines 173, 277, 368, 374, 393, 3002, 5906, and 13325: six `.pdd/meta/*` PR #2017 absent-metadata rules plus four exact #2216 Gate 1 preauthorizations | two additions at base lines 9821 and 13605: one Vitest provenance script and four Vitest verifier-test rules | operands and locations are disjoint; both frozen-head hunks are `excluded-diagnostic` |
| `.pdd/verification-profile-rotations.json` | one `+22` hunk after base line 263 adding `get_test_command` and `fix_error_loop` PR #2017 rotations | one `-1/+1` hunk at base line 261 changing the story rotation's head-policy digest for four Vitest diagnostic profiles | adding rotation rows is not equivalent to changing the existing row's digest; the frozen-head hunk is `excluded-diagnostic` |
| `docs/global_sync_evidence_ledger.yaml` | 78 hunks, `+920/-143`: the merged #2213 current-state ledger, governance, gate predicates, and historical preservation | 34 hunks, `+190/-67`: frozen hosted Vitest/Stage A0/A evidence and replay records | both documents are evidence ledgers but their reviewed heads, predicates, and operands differ; every frozen-head hunk remains `excluded-diagnostic` and the merged ledger is not a frozen-head prerequisite |
| `docs/global_sync_resolution_plan.md` | 42 hunks, `+793/-120`: the merged #2213 ratified critical path, lifecycle/certificate program, and historical boundary | 29 hunks, `+390/-62`: frozen diagnostic protocol and status material | both documents describe global-sync work, but no frozen diagnostic hunk is patch-equivalent to the merged plan; every frozen-head hunk remains `excluded-diagnostic` |
| `pdd/sync_core/verification.py` | five hunks at base lines 379, 635, 819, 1418, and 2127: two bootstrap rows plus formatting-only changes | nine hunks at base lines 19, 73, 455, 495, 541, 549, 1755, 2069, and 2074: assurance import/input/parser/digest/merge | no changed symbol or operand is equivalent; all nine frozen-head assurance hunks are `excluded-diagnostic` |
| `tests/test_sync_core_pdd_rollout_policy.py` | 20 hunks: PR #2017 constants/path sets/rotation assertions/tests plus #2216 exact-four-path preauthorization and offline composition coverage, including an insertion after the PDD-1989 test | six hunks at base lines 34, 36, 49, 161, 757, and 759: diagnostic managed-unit/profile digests and PDD-1989 count split | the nearby PDD-1989 insertion and later protected preauthorization coverage on main do not change the frozen head's count assertions; all six frozen-head hunks are `excluded-diagnostic` |

This also explains why none of these six rows is
`already-merged-prerequisite`: main contains different additions, not a
patch-equivalent form of any frozen-head hunk.

## Net result

`git diff --stat "$base" "$head"` is 48 paths, `+39468/-5130` lines.
The bounded fresh-main release candidate is `+125/-0` lines before rebase
adjustments: four finalizer lines, thirteen reporting lines, and 108 focused
pytest test lines.  Everything else is `excluded-diagnostic`: `+39343/-5130`.
No changed hunk is `already-merged-prerequisite`.

## Exhaustive path and hunk inventory

In the hunk column, semicolon-separated entries are independently classified
hunk groups.  “All” means every direct base-to-head hunk in that path has the
stated classification.  Large mixed files name the affected symbols or test
families rather than hiding a classification behind the filename.

| Path | Direct hunk inventory and classification |
| --- | --- |
| `.github/toolchains/playwright_manifest.py` | all: Playwright external-toolchain manifest (`excluded-diagnostic`) |
| `.github/workflows/unit-tests.yml` | 30 workflow hunks: Playwright manifest, Vitest source/wheel, Stage A0/A evidence, review bindings, Node/toolchain checks (`excluded-diagnostic`) |
| `.pdd/expected-managed.json` | four `verify_vitest_*` prompt registrations (`excluded-diagnostic`) |
| `.pdd/sync-ownership.json` | Vitest provenance script and four Vitest verifier-test ownership rows (`excluded-diagnostic`) |
| `.pdd/verification-profile-rotations.json` | Vitest diagnostic profile digest rotation (`excluded-diagnostic`) |
| `.pdd/verification-profiles.json` | four Vitest diagnostic human-attestation profiles (`excluded-diagnostic`) |
| `architecture.json` | four Stage A0/A Vitest verifier architecture entries (`excluded-diagnostic`) |
| `docs/global_sync_evidence_ledger.yaml` | 34 hosted Vitest/Stage A0/A evidence and replay hunks (`excluded-diagnostic`) |
| `docs/global_sync_resolution_plan.md` | 29 frozen diagnostic protocol/status hunks (`excluded-diagnostic`) |
| `pdd/commands/sync_core.py` | `_protected_playwright_command`, Playwright CLI options, identity construction (`excluded-diagnostic`) |
| `pdd/prompts/verify_vitest_no_result_observation_python.prompt` | Stage A0 observation prompt (`excluded-diagnostic`) |
| `pdd/prompts/verify_vitest_package_attestation_python.prompt` | installed-wheel Vitest prompt (`excluded-diagnostic`) |
| `pdd/prompts/verify_vitest_stage_a_evidence_python.prompt` | Stage A native-evidence prompt (`excluded-diagnostic`) |
| `pdd/prompts/verify_vitest_termination_evidence_python.prompt` | termination-evidence prompt (`excluded-diagnostic`) |
| `pdd/sync_core/__init__.py` | `AssuranceLevel` export; paired with broad assurance/adapters work, not needed for invalid-profile stop (`excluded-diagnostic`) |
| `pdd/sync_core/evidence_store.py` | Playwright toolchain identity serialization/parse/binding hunks (`excluded-diagnostic`) |
| `pdd/sync_core/finalize.py` | `_reusable_result` `playwright_toolchain_identity` in runner identity (`excluded-diagnostic`); binding field propagation (`excluded-diagnostic`); `finalize_unit` `profiles.invalid_reasons` guard (`release-required-delta`) |
| `pdd/sync_core/git_io.py` | `read_git_mode`, introduced for diagnostic toolchain closure (`excluded-diagnostic`) |
| `pdd/sync_core/lifecycle.py` | candidate venv transaction, bounded receipt/output, timeout and lifecycle-supervisor semantics (`excluded-diagnostic`) |
| `pdd/sync_core/native/vitest_fd_cloexec.c` | fixed Stage A Vitest seal-result enum/native addon (`excluded-diagnostic`) |
| `pdd/sync_core/reporting.py` | `_invalid_profile_verdict` (`release-required-delta`); `_evidence` Playwright identity binding (`excluded-diagnostic`); `_unit_verdict` invalid-profile short circuit (`release-required-delta`) |
| `pdd/sync_core/runner.py` | all 239 direct hunks are exhaustively partitioned by numbered semantic family in “Runner hunk partition” below; every family is `excluded-diagnostic` |
| `pdd/sync_core/supervisor.py` | termination evidence, executable/ELF closure, sandbox/process identity, descriptor/result FIFO, cgroup and Playwright/Vitest supervision hunks (`excluded-diagnostic`) |
| `pdd/sync_core/trust.py` | Playwright toolchain identity attestation validation (`excluded-diagnostic`) |
| `pdd/sync_core/types.py` | `AssuranceLevel`, profile assurance field/digest, and Playwright attestation-binding field (`excluded-diagnostic`) |
| `pdd/sync_core/verification.py` | assurance parse/digest/anti-downgrade profile merge (`excluded-diagnostic`); it is broader than, and not a dependency of, existing `ProfileSet.invalid_reasons` fail-closed reporting/finalization |
| `scripts/build_vitest_fd_cloexec_addon.py` | Vitest native-addon build helper (`excluded-diagnostic`) |
| `scripts/verify_vitest_no_result_observation.py` | Stage A0 verifier (`excluded-diagnostic`) |
| `scripts/verify_vitest_package_attestation.py` | installed-wheel Vitest attestation verifier (`excluded-diagnostic`) |
| `scripts/verify_vitest_package_provenance.sh` | Vitest package provenance diagnostic script (`excluded-diagnostic`) |
| `scripts/verify_vitest_stage_a_evidence.py` | Stage A native-evidence verifier (`excluded-diagnostic`) |
| `scripts/verify_vitest_termination_evidence.py` | Vitest termination-evidence verifier (`excluded-diagnostic`) |
| `tests/test_ci_detect_changed_modules.py` | diagnostic verifier ownership/module detection expectation (`excluded-diagnostic`) |
| `tests/test_sync_core_evidence_store.py` | Playwright toolchain identity encoding/decoding tests (`excluded-diagnostic`) |
| `tests/test_sync_core_lifecycle_scenarios.py` | candidate venv, wheel transaction, output/timeout lifecycle scenarios (`excluded-diagnostic`) |
| `tests/test_sync_core_pdd_rollout_policy.py` | four diagnostic Vitest managed-unit/profile-count and rotation expectations (`excluded-diagnostic`) |
| `tests/test_sync_core_reporting.py` | `_durable_state`/`_invalid_candidate_profile` helper and `test_invalid_profile_reconciliation_cannot_reuse_verified_evidence` (`release-required-delta`); `test_validate_command_rejects_unpaired_playwright_command` (`excluded-diagnostic`); `test_trusted_finalizer_rejects_invalid_profile_before_trusted_state` (`release-required-delta`); three Linux-only skip decorators for diagnostic finalizer/lifecycle execution (`excluded-diagnostic`) |
| `tests/test_sync_core_runner.py` | assurance adapter matrix, checker-owned FIFO result channel, Jest descriptor test (`excluded-diagnostic`) |
| `tests/test_sync_core_runner_jest.py` | Jest descriptor/FIFO transport changes (`excluded-diagnostic`) |
| `tests/test_sync_core_runner_playwright.py` | all 4,530 added Playwright adapter/topology tests (`excluded-diagnostic`) |
| `tests/test_sync_core_runner_vitest.py` | all 130 hunk groups: Vitest worker/addon/toolchain/Stage A0/A diagnostic tests (`excluded-diagnostic`) |
| `tests/test_sync_core_supervisor.py` | all 237 hunk groups: sandbox, descriptor, ELF, cgroup, Vitest/Playwright supervisor diagnostic tests (`excluded-diagnostic`) |
| `tests/test_sync_core_verification_profiles.py` | assurance parse/digest/downgrade tests; broader assurance change, not needed to consume existing invalid-profile reasons (`excluded-diagnostic`) |
| `tests/test_unit_tests_workflow.py` | all workflow/Playwright/Vitest Stage A contract tests (`excluded-diagnostic`) |
| `tests/test_verify_vitest_no_result_observation.py` | Stage A0 verifier tests (`excluded-diagnostic`) |
| `tests/test_verify_vitest_package_attestation.py` | installed-wheel Vitest attestation tests (`excluded-diagnostic`) |
| `tests/test_verify_vitest_stage_a_evidence.py` | Stage A native-evidence verifier tests (`excluded-diagnostic`) |
| `tests/test_verify_vitest_termination_evidence.py` | Vitest termination-evidence verifier tests (`excluded-diagnostic`) |

The table names exactly the 48 paths from `git diff --name-only "$base"
"$head"`; each row and every identified mixed hunk has exactly one permitted
classification.

### Runner hunk partition: all 239 hunks

Hunk numbers are the stable ordinal output of:

```bash
git diff --unified=0 "$base" "$head" -- pdd/sync_core/runner.py \
  | rg '^@@' | nl -ba
```

The ordinal ranges below are disjoint and sum to 239.  Each family has exactly
one classification.  Shared or pytest-facing code is not release-required:
the invalid-profile reporting guard returns before evidence loading, and the
finalization guard returns before `run_profile`, so the bounded correction does
not depend on any runner transport change.

| Hunks | Named symbols or semantics | Classification and rationale |
| --- | --- | --- |
| 1–14 | imports, runner constants, diagnostic dataclasses, `VitestPhaseToolchain`, `RunnerConfig` fields | `excluded-diagnostic`; scaffolding for assurance and JavaScript/native diagnostic adapters |
| 15–26 | `_resolve_javascript_specifier`, `_vitest_config_references`, validator/support digests, `_jest_support_digest`, `_vitest_support_digest`, plugin detection | `excluded-diagnostic`; JavaScript adapter/toolchain closure |
| 27–36 | `_managed_subprocess`, path containment, file/tree identity helpers | `excluded-diagnostic`; shared process/identity refactor supporting descriptor-based JavaScript diagnostics, not needed before the invalid-profile guards |
| 37–116 | Vitest member/header capture, descriptor closure, native compiler/ELF closure, coordinator addon identity/load/verify, phase preparation | `excluded-diagnostic`; Vitest and native-addon implementation |
| 117–136 | command-part and validator identity, adapter capture/verification, measured runtime, checker artifact/runtime manifest, Git path/change helpers | `excluded-diagnostic`; shared diagnostic identity/closure refactor with no proof of necessity for the existing protected pytest path |
| 137–151 | `_junit_outcome`, `_pytest_environment`, `_trusted_probe_plugin`, `_checker_probe_digest`, `_trusted_collection_runner`, `_trusted_execution_runner`, `_pytest_exit_outcome` | `excluded-diagnostic`; pytest-facing JUnit/result transport and collection-probe rewrite is behaviorally broader than stale-profile rejection and protected main's pytest adapter remains the release authority |
| 152–178 | `_jest_environment`, `_jest_command`, Jest toolchain/checkout validation, protected command checks, reporter/result parsing, `_run_jest` | `excluded-diagnostic`; Jest adapter and descriptor transport |
| 179–220 | Vitest command/environment/result/termination/reporter, result-pipe drain, `_run_vitest` | `excluded-diagnostic`; Vitest adapter and Stage A transport |
| 221–225 | `_run_test_node` result FIFO, descriptor, containment and dispatch changes | `excluded-diagnostic`; shared test-node transport was introduced for JavaScript diagnostics and is not reached by the invalid-profile release behavior |
| 226 | `_dirty_vitest_support` | `excluded-diagnostic`; Vitest support closure |
| 227–228 | `_obligation_preflight` assurance/adapter preflight changes | `excluded-diagnostic`; broader runner policy, while the release guard rejects the invalid profile before obligation preflight |
| 229 | `_collect_jest_at_base` | `excluded-diagnostic`; Jest collection |
| 230 | `_run_vitest_at_commit` | `excluded-diagnostic`; Vitest execution |
| 231–233 | `_run_obligation_in_tree` and `run_obligation` adapter/assurance dispatch | `excluded-diagnostic`; adapter dispatch is downstream of the finalization guard |
| 234–239 | `run_profile` assurance rejection, adapter identity/toolchain binding and result assembly | `excluded-diagnostic`; broader profile-runner behavior is downstream of the finalization guard |

In particular, `_junit_outcome`, pytest result transport, and `_run_test_node`
are explicitly excluded, not silently treated as required by `{pytest}`.  They
may be evaluated in a later runner release only with an independent protected
pytest regression and necessity proof.

## Exact finalizer and reporting resolution

The direct `finalize.py` diff has exactly six added lines relative to protected
main's foundation:

```text
_reusable_result: playwright_toolchain_identity=...              # 2 lines
finalize_unit: if profiles.invalid_reasons: raise ValueError(...) # 4 lines
```

The first two lines are Playwright identity propagation and are
`excluded-diagnostic`.  The four-line `profiles.invalid_reasons` guard is
`release-required-delta`: it must run before profile lookup, snapshotting,
reusable-attestation verification, `run_profile`, or a transaction manager can
write trusted state.

`reporting.py` is independently resolved as follows.  Keep the 11-line
`_invalid_profile_verdict` and the two-line `_unit_verdict` early return.  They
mark each affected managed unit `CORRUPT`/`UNKNOWN`, leave evidence incomplete
and not in sync, and return before `_evidence` can verify a stale attestation.
Exclude its one Playwright runner-identity line.  The focused tests are the two
release-required test functions named in the inventory: one proves report
counts/evidence cannot reuse stale trust; the other parametrizes malformed,
deleted, and changed-requirement invalid profiles and proves finalization makes
no reusable-evidence, runner, transaction, or durable-state call.

On fresh main, retain those test meanings but use a pre-existing invalidity
stimulus (for example, remove the protected `pytest` obligation, which current
`load_verification_profiles` already reports as “removed protected obligation”).
Do not extract the new assurance grammar merely to preserve the frozen test's
`unrecognized_assurance` stimulus.

## Proposed fresh-main release layer and order

One bounded layer is sufficient, in this order:

1. Rebase/cherry-pick only the shared fail-closed behavior into fresh protected
   main: the four `finalize_unit` lines, the thirteen reporting lines, and
   focused pytest tests rewritten to a current-main invalid profile transition.
2. Run the focused tests and the existing verification-profile invalidity test,
   then the normal pytest checker suite and the public-CLI E2E gate below.  The
   profile authority is `{pytest}`; no JavaScript command, manifest, adapter,
   native compiler, workflow, or diagnostic script is invoked or added.
3. Re-run the three-way inventory against the exact release SHA.  If it needs
   any excluded dependency, stop rather than widening this layer.

Suggested validation commands after extraction:

```bash
pytest -q tests/test_sync_core_reporting.py \
  -k 'invalid_profile_reconciliation or finalizer_rejects_invalid_profile'
pytest -q tests/test_sync_core_verification_profiles.py \
  -k 'cannot_delete_protected_obligation'
git diff --check
git status --short
```

### Required invalid-profile public-CLI E2E gate

Pytest is necessary but not sufficient.  The release must exercise the same
top-level commands a user invokes: `pdd certify` for canonical reporting and
`pdd validate` for validation/finalization.  Because the checker is distributed
as a wheel, both the source console script and an installed-wheel console script
are required; there is no installed-wheel exemption for this behavior.

Prepare two independent clones of one fixture repository.  In each, commit a
valid managed Python unit with only a required `pytest` obligation, finalize a
trusted baseline, then make and commit an invalid candidate transition that
removes that protected `pytest` obligation.  Record `base_sha`, `head_sha`, and
a sorted SHA-256 inventory of `.pdd/evidence/v2` and `.pdd/meta/v2`.  Keep replay
ledgers, trust roots, signer sentinel, reports, wheel, and virtual environment
outside the candidate repositories.  Configure the required remote-signer
environment with a valid public key and a reviewed sentinel command that would
create `signer-invoked` if executed; the invalid-profile guard must prevent that
command from running.

Build/install the exact release candidate and prove import provenance before
testing it.  The protected runtime lock and wheelhouse must be the reviewed,
digest-pinned release inputs; the clean environment may not resolve packages
from an index:

```bash
python -m build --wheel --outdir "$external/wheel"
python -m venv "$external/installed"
"$external/installed/bin/pip" install \
  --no-index \
  --find-links "$protected_wheelhouse" \
  --require-hashes \
  --requirement "$protected_runtime_lock"
"$external/installed/bin/pip" install \
  --no-index \
  --no-deps \
  "$external"/wheel/*.whl
"$external/installed/bin/python" -c \
  'import pathlib,pdd; print(pathlib.Path(pdd.__file__).resolve())'
# Expect a path beneath $external/installed, never the source checkout.
```

For each independent repository, run this matrix once with the source-built
`pdd` console script and once with `$external/installed/bin/pdd`:

```bash
set +e
"$pdd_cli" certify \
  --base-ref "$base_sha" \
  --head-ref "$head_sha" \
  --module prompts/widget_python.prompt \
  --replay-ledger "$external/$lane-report-replay.json" \
  --output "$external/$lane-certify.json"
certify_status=$?

PDD_ATTESTATION_ISSUER=trusted-ci \
PDD_ATTESTATION_PUBLIC_KEY="$public_key_base64" \
PDD_ATTESTATION_SIGNER_COMMAND="$sentinel_command_json" \
PDD_ATTESTATION_REPLAY_LEDGER="$external/$lane-validate-replay.json" \
"$pdd_cli" validate \
  --module prompts/widget_python.prompt \
  --base-ref "$base_sha" \
  --head-ref "$head_sha" \
  >"$external/$lane-validate.stdout" \
  2>"$external/$lane-validate.stderr"
validate_status=$?
set -e
```

The source and installed-wheel expectations are identical and fail closed:

- `certify_status` is nonzero; its JSON has `ok: false`, `invalid: 1`,
  `unknown: 1`, `trusted_current_evidence: 0`, and `trusted_in_sync: 0`; the
  unit is `CORRUPT`/`UNKNOWN`, `evidence_complete: false`, and `in_sync: false`.
- `validate_status` is nonzero and reports `canonical finalization requires
  valid protected verification profiles`; it emits no success JSON.
- `signer-invoked` is absent, proving the public finalization path did not reach
  signing.  The before/after durable-state SHA-256 inventories are byte-for-byte
  equal, and no transaction/evidence/fingerprint path is added.
- Source and installed-wheel `certify` JSON are equal after removing only
  intentionally external path names; validation has the same stable error in
  both lanes.  Neither lane receives a Jest, Vitest, or Playwright option.

This gate covers the report short circuit and the validation/finalization short
circuit through public command registration and packaging, satisfying the
runbook's end-to-end boundary without widening the release to runner changes.

## Explicit no-extraction and preservation statement

There is no extraction of a Playwright, Vitest, Jest, JavaScript toolchain,
native addon, Stage A0/A artifact, workflow, prompt, profile, script, or its
tests.  This manifest does not alter, cherry-pick, reset, rebase, close, merge,
or otherwise rewrite frozen PR #1995.  All excluded diagnostic material remains
preserved on `d334266680881cbda59de4ecd4df967c92159fa7` for its separate
evidence protocol.
