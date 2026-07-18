# Global Sync Resolution Plan

Status: implementation in progress; acceptance gates remain red
Last updated: 2026-07-18
Tracking epic: [promptdriven/pdd#1932](https://github.com/promptdriven/pdd/issues/1932)
Primary consumer: `promptdriven/pdd_cloud`

## 1. Executive decision

The global sync guarantee is not complete. The merged implementation in PR #1954
adds useful deterministic reporting and protects some conflict cases, but it does
not establish the invariant that prompts, included documentation, code, examples,
tests, architecture metadata, and fingerprints remain mutually consistent across
all edit channels.

The program must be completed as a sequence of foundations, repair semantics, and
enforcement. The order is mandatory:

1. Define one unit identity and dependency model.
2. Define one pure drift classifier.
3. Make artifact and fingerprint finalization transactional.
4. Route every command and automation path through those primitives.
5. Implement non-destructive repair and conflict resolution.
6. Enforce the invariant at PR, merge, and nightly boundaries.
7. Backfill consumer repositories only after the upstream implementation passes
   lifecycle end-to-end tests.

No bulk baseline, hook, or CI stamper may silently declare an arbitrary working
tree synchronized. A baseline can say what bytes were observed; it cannot, by
itself, prove that those bytes express the same intent.

## 2. Evidence and current state

### Current critical-path unblock (2026-07-18)

This immediate runner prerequisite is a PR gate only. It does not authorize a
release, merge #1995, or claim global certification; the ten-step sequence below
remains controlling.

#### Authoritative execution snapshot

The following snapshot supersedes the historical attempt details retained below.
It distinguishes evidence collection from hosted acceptance and from merge or
release state.

| Verification boundary | Exact evidence | State |
| --- | --- | --- |
| Locally validated | PR #1995 exact reviewed head [`08cc80e0ab752414eb1527a1652181ef9b4e2679`](https://github.com/promptdriven/pdd/commit/08cc80e0ab752414eb1527a1652181ef9b4e2679) contains protected base [`39776aa9bb027c638812a01b8dabbe03cab92f64`](https://github.com/promptdriven/pdd/commit/39776aa9bb027c638812a01b8dabbe03cab92f64). Focused workflow, observation-verifier, and termination-verifier suites passed 170 tests. Exact source and installed-wheel artifact replays each passed the observation verifier with `cause_eligible: false` and each produced the required termination-verifier exit `1` with exact text `Vitest termination evidence rejected`. YAML, embedded Bash, sidecar mode/byte, clean-tree, remote-head, and ancestry checks passed before the guarded push. | local validation passed for the reviewed head and downloaded hosted bytes |
| Independently reviewed | Sol HIGH approved exact head `08cc80e0ab752414eb1527a1652181ef9b4e2679` with `NO_BEHAVIORAL_FIX`; review evidence digest `85b804359bf0035f610002402ab47e442961d3eea9a5f114e7caac5c247ff0e4` binds producer `fd02005eb5367c9990aae94d515041686f37f6cee5dc6e28e4b03cdd2eb1e51d`, termination verifier `fa20e7b2a8cb3d258154e1cc8d760c5e6906080458674e15f93461697aa5e681`, observation verifier `c129c0271e410faf2ee68930ef198b8a3075634b9c4752f6a0b16c55dfea479f`, Package verifier `b6e923061ea73ed46af4d03e497aa9ed4e538129f85b1c0eabc1bd47d45e177e`, Package provenance `0c0304e13e370f42ae70ff92a4a05a69394abe92af99cc0ffb2e369b6bf63f15`, and protected base `39776aa9bb027c638812a01b8dabbe03cab92f64`. | exact-composite approved |
| Hosted evidence collected | Exact-head [run 29649405805](https://github.com/promptdriven/pdd/actions/runs/29649405805) passed 10 non-diagnostic checks, including CodeQL, both auto-heal checks, Public CLI Regression, Story Regression, and Repo Bloat Docker E2E. Source [job 88093035447](https://github.com/promptdriven/pdd/actions/runs/29649405805/job/88093035447) and installed-wheel [job 88093035441](https://github.com/promptdriven/pdd/actions/runs/29649405805/job/88093035441) each printed `Vitest no-result observation verified; cause_eligible: false`, asserted the exact termination-verifier rejection, uploaded the expected artifact, and only then exited `1` with the intentional candidate test status. Source artifact [`8431053984`](https://github.com/promptdriven/pdd/actions/runs/29649405805/artifacts/8431053984) has payload digest `daeb1f9e0d97888a0e2634378d73c4395b08f3b125139954ded4412bcdccb02f`; installed-wheel artifact [`8431093575`](https://github.com/promptdriven/pdd/actions/runs/29649405805/artifacts/8431093575) has payload digest `e69d0f124d2f23790659d22fac4dabe962c4c6ff654bf549e2973da0ec8f6c4e` and Package-attestation digest `43187c6768a858bc1e6d05234ea82196fc65d8f4bc87bad98ca5f0dc1ecd179c`, binding wheel `1c4bfd9305a35b4772c7c880b03822bce3c702cb17456d709d6cdb2dfa7f775b` to installed runner `fd02005eb5367c9990aae94d515041686f37f6cee5dc6e28e4b03cdd2eb1e51d`. | hosted Stage A0 passed; overall diagnostic jobs remain intentionally red |
| Artifact predicates | Both hosted observation verifiers accepted their exact-lane artifacts. Independent replay of the downloaded bytes, after restoring archive-normalized mode `0600` and protected parent mode `0700`, reproduced both accepts and both exact termination-verifier rejections. Both traces are identical through `reporter-addon-load-succeeded`, `reporter-authority-seal-start`, `reporter-authority-seal-failed`, `coordinator-explicit-exit`, and `coordinator-exit`; supervisor exit is `0` and no result frame exists. | Stage A0 closed; evidence is explicitly non-causal |
| Hosted blocker | Stage A0's review-sidecar blocker is closed. The first unresolved boundary is now inside native `sealResultAuthority`: add a trusted fixed-enum failure reason that identifies the exact native operation without exposing raw error text or changing candidate behavior. Reconcile the same reason across source and installed-wheel hosted evidence before creating a cause-specific RED. | in progress; owned by PR #1995 |
| Merged to protected `main` | [PR #2208](https://github.com/promptdriven/pdd/pull/2208) merged the prior plan update as [`39776aa9bb027c638812a01b8dabbe03cab92f64`](https://github.com/promptdriven/pdd/commit/39776aa9bb027c638812a01b8dabbe03cab92f64). That SHA is an ancestor of reviewed head `08cc80e0ab752414eb1527a1652181ef9b4e2679`. PR #1995 is not merged. | runner prerequisite remains unmerged |
| Released checker | No protected reviewed checker release or pinned wheel digest exists. | pending |
| Globally certified | No protected merge-group certificate or seven-night streak exists. | pending |

#### Ordered unblock from current evidence

1. Stage A0 is closed on exact reviewed head `08cc80e0ab752414eb1527a1652181ef9b4e2679`:
   both hosted observation verifiers accepted and both termination verifiers
   rejected the artifacts as cause proof. The overall Unit and Package failures
   are the preserved candidate baseline and do not close Stage A.
2. Add a separately reviewed Stage A diagnostic that reports a trusted native
   fixed-enum reason for `sealResultAuthority` failure. Do not parse
   `error.message`, infer cause from exit `0`, or treat the broad authority-seal
   boundary as the behavioral fix. The trusted native operation has multiple
   fail-closed paths, so the reason must distinguish at least argument/identity,
   procfs seal, descriptor-table open/read/inspection/close, descriptor
   `CLOEXEC` set/verification, alias-not-found, and response failures.
3. Recollect source and installed-wheel Stage A evidence on one exact reviewed
   SHA. Require exact head/base/toolchain/package bindings, authenticated
   fixed-enum reason, process role, failure stage, no result frame, and
   reconciliation of the two lanes before writing a cause-specific RED.
4. Only after Stage A passes, add one RED that reproduces the collected native
   reason, implement one bounded behavioral correction, and have the same Sol
   reviewer verify the finding and affected behavior.
5. Require every hosted check to pass on that exact reviewed SHA, refetch main,
   recheck remote-head and ancestry guards, and merge #1995 only from the main
   clone. Then advance to the released-checker gate. No downstream step may use
   the diagnostic branch as a released or certified implementation.

#### Historical attempt ledger

The table below is retained for evidence lineage. Where it conflicts with the
authoritative execution snapshot above, the snapshot above controls.

| Verification boundary | Exact evidence | State |
| --- | --- | --- |
| Locally validated | PR #2164 exact reviewed head `5f6d747aa75a0629f33d0900489a613a3f1e2b8d` passed its affected suites. PR #1995 exact head [`07d3d7d71d1dd308984d349d6751da9378579cf1`](https://github.com/promptdriven/pdd/commit/07d3d7d71d1dd308984d349d6751da9378579cf1) contains protected base `0e22fe9f4`. Terra reported 305 affected passes and 36 platform skips for the protected Package authority correction; post-main integration verifier/package/tamper tests passed 44. YAML, 45 embedded shell scripts, bash syntax, pycompile, pylint, and diff checks passed. | local evidence green for both diagnostic lanes |
| Independently reviewed | Sol approved exact head `07d3d7d71`, producer digest `146919c7c1c2bbd09c9d0577723638b41591f09c301a7467d0ab5bb96fc2394b`, termination verifier `e371cd4d12a6b4d64ea3488d773054b2dfc51320db892e7019d1f20db393d1f2`, Package verifier `b6e923061ea73ed46af4d03e497aa9ed4e538129f85b1c0eabc1bd47d45e177e`, Package provenance `36f27b84f21b62b80dd5f2ad826e2fde395d986a5eec35936f9462335faa8ff1`, protected base `0e22fe9f4`, and verdict `NO_BEHAVIORAL_FIX`. | exact-composite approved |
| Hosted green | #2164 exact-head [run 29622818907](https://github.com/promptdriven/pdd/actions/runs/29622818907) passed all required checks. On #1995 prior head `daa67f2044`, [run 29635743590](https://github.com/promptdriven/pdd/actions/runs/29635743590) had green CodeQL, Story/Public CLI regressions, and Docker E2E, but Unit failed in silent preflight; Package passed all seven installed-wheel Playwright variants, then reproduced the installed-wheel Vitest exit with untrusted diagnostic `340afd630c05209f62419c312abe3aeb7464262e3c5d8367e8d28fec22428471`. On exact head `84b19758f`, [Unit job 88061484993](https://github.com/promptdriven/pdd/actions/runs/29637193871/job/88061484993) uploaded checksummed failure artifact `aec9faa5a2c27cfdaddfb0b82135493d7cafb594728ac22a897a738da0f8cbee`: predicate `runner-provisioner-version-count`, expected 1, actual 0, command exit 0, decoded observation `version=20260707.563`, full-output digest `1e40203d955c084de9ec279dbe867aa074eb9697c4549b763eb753e048536840`. On exact head `07d3d7d71`, [run 29639041827 attempt 1](https://github.com/promptdriven/pdd/actions/runs/29639041827/attempts/1) failed both lanes at `review-evidence-decode` because the protected base64 variable was missing one trailing padding character; the corrected value decodes to reviewed digest `c8ad0ae8e96806928d971e710be64bb5648fe7ed96fc5235a0e31561e5cff39c`. [Attempt 2](https://github.com/promptdriven/pdd/actions/runs/29639041827/attempts/2) passed provenance, all pre-Vitest Unit sandbox/transport checks, the Package wheel attestation, and all seven installed-wheel Playwright variants. Both source and wheel candidates then returned `COLLECTION_ERROR: Vitest reporter produced no result` without an eligible fixed-enum cause artifact. Source preflight PASS digest is `e9b33d7c02f55a9361ba74a1fd908d948bd60c5d6e288926e6822a8aa6d014c7`; wheel attestation digest is `52726db19e9ec485e8be54406c8629a0433f40739842409a57df667086be07a5`, binding wheel `41b528e5ebad9b25818d7cc89036ebaa4b3542401d7e0524792b4e051053cadd` to the reviewed runner. CodeQL, Story, Public CLI, and Docker E2E passed; Unit, Package, heal, and auto-heal remain red. | #1995 Stage A red at one shared unclassified coordinator exit |
| Merged to protected `main` | #2164 merged with ancestry preserved at [`d91b07a9002be895556b38c5bafff18a420b256e`](https://github.com/promptdriven/pdd/commit/d91b07a9002be895556b38c5bafff18a420b256e). #1995 is not merged. Remote PR head `07d3d7d71` contains its reviewed protected base `0e22fe9f4`, but does not contain minimum required ancestor `301b3cab9`; the next cycle must resolve and integrate live `origin/main`, which may be later. | exact hosted checks, live-main ancestry, and cause gates remain pending |
| Plan and ledger | [PR #2199](https://github.com/promptdriven/pdd/pull/2199) exact reviewed head `0d1d7919f763eee5fb96db17d43cd437e7ff03c7` passed its 12-check PR rollup. The contributing hosted evidence includes [Unit Tests run 29639929336](https://github.com/promptdriven/pdd/actions/runs/29639929336), [CodeQL run 29639928377](https://github.com/promptdriven/pdd/actions/runs/29639928377), [auto-heal run 29639928801](https://github.com/promptdriven/pdd/actions/runs/29639928801), and the exact-head aggregate CodeQL and auto-heal checks. It merged as [`301b3cab9e72123eaa66dc31babb9d49eab84918`](https://github.com/promptdriven/pdd/commit/301b3cab9e72123eaa66dc31babb9d49eab84918). [PR #2207](https://github.com/promptdriven/pdd/pull/2207) then passed 12/12 checks on exact reviewed head `54a2a8d8b67c682a940884c749ae60b684738fde` and merged the status correction as [`8c5ac0d556e64b8f660336795f740bec7431b402`](https://github.com/promptdriven/pdd/commit/8c5ac0d556e64b8f660336795f740bec7431b402). | hosted green and merged; no global exit gate closed by either documentation merge |
| Released checker | No protected reviewed checker release or pinned wheel digest exists. | pending |
| Globally certified | No protected merge-group certificate or seven-night streak exists. | pending |

The first exact hosted diagnostic attempt was useful negative evidence: trigger
head, checkout head, reviewed head, Python, Node, runner image, runner
provisioner, ancestry, and reviewed file/package digests were all bound, and the
job failed before it could create candidate evidence. It is not evidence of the
remaining Vitest cause. It exposed a preflight-observability defect in which a
shell predicate could terminate the job without naming the predicate or writing
a machine-readable failure artifact. That defect and the observed provisioner
parser mismatch are closed in the exact reviewed code. Current Stage A evidence
is governed by the authoritative snapshot and ordered unblock above.

#### Historical dependency sequence

This sequence records how the current gate was reached. Its stale head and base
identifiers are superseded by the authoritative execution snapshot.

1. **Passed:** [#2164](https://github.com/promptdriven/pdd/pull/2164) at
   `H2164 = 5f6d747aa` passed Unit, Package, all hosted checks, exact Sol review,
   and clean-tree/main/remote-head guards; ancestry-preserving merge result
   `M2164 = d91b07a90` is on protected `main`.
2. **Passed locally and reviewed; hosted parser RED closed in code:** exact head
   `07d3d7d71` contains reviewed protected base `0e22fe9f4`, has exact Sol
   approval, and is the remote PR head. Protected main advanced at least through
   `301b3cab9` after that review, so the fresh cycle must resolve live
   `origin/main`, integrate it, and rotate all exact review bindings before
   recollection. Its
   preflight emits canonical checksummed PASS or named failure evidence without
   changing candidate behavior. Hosted evidence proves the provisioner command
   succeeds and emits the pinned version as exact machine form
   `version=20260707.563`; the parser rejected that form.
3. **Current gate, integrate then observe without classifying:** fetch and resolve
   live `origin/main` under a guarded remote-head check, integrate that exact SHA
   into the one canonical #1995 implementation branch, and obtain fresh
   exact-composite review. Then add Stage A0. Exact-head attempt 2 proves
   that both source and installed-wheel lanes reach the same no-result exit after
   their identity and environment gates, but the protected coordinator emits no
   eligible fixed-enum cause. Reviewed control flow reaches this branch only
   after supervised exit `0`; that is a diagnosis from the reviewed code and
   hosted symptom, not a cause artifact. Add a distinct, checksummed observation
   artifact containing only authenticated fixed-enum progress, supervisor exit,
   and result-frame presence. Its verifier must reject it as Stage A cause proof.
4. **Then recollect observation and cause evidence:** run the source and installed-wheel
   diagnostic lanes. Stage A passes only when a
   checksummed source preflight PASS artifact exists, the installed-wheel package
   attestation binds its wheel and imported runner to the reviewed source, and
   protected coordinator artifacts identify fixed-enum process role, failure
   stage, and cause for both lanes on that exact SHA. A preflight failure or an
   unclassified lane leaves Stage A red; the two lanes may report different
   trusted causes.
5. If the observation identifies a concrete protected operation boundary, add
   the minimum cause-eligible authenticated frame and recollect both lanes. A
   generic lifecycle event, natural exit, or `no result` string is still not a
   cause.
6. **Only then specify behavior:** add one cause-specific RED that fails against
   the collected baseline behavior, implement at most one bounded correction,
   and have the same reviewer verify the finding and affected behavior.
7. Require Unit, Package Preprocess Smoke, CodeQL, auto-heal, and every other
   required hosted check to pass on one exact reviewed SHA. Merge #1995 only from
   the main clone after clean-tree, remote-head, ancestry, and no-main-drift
   guards.
8. After #1995 merges, update the ledger with its merge SHA and begin the
   protected checker release gate. Do not substitute narrative status for the
   machine-readable evidence fields.

The immediate non-human predicate is strict:

```text
H2164 = the exact final reviewed proposed PR #2164 head
M2164 = the protected-main merge result of H2164
H1995 = the exact proposed integrated PR #1995 SHA

required_checks(H2164) == success
and sol_high_exact_composite_approval(H2164) == approved
and merge_result(H2164) == M2164
and is_ancestor(H2164, M2164)
and protected_main_contains(M2164)
and is_ancestor(M2164, H1995)
and required_checks(H1995) == success
and sol_high_exact_composite_approval(H1995) == approved
and merge_result(H1995) is on protected main
```

For #2164, the complete first half of the predicate is true. For #1995,
`H1995 = 08cc80e0ab752414eb1527a1652181ef9b4e2679` is reviewed, pushed, and
contains protected-main ancestor `39776aa9bb027c638812a01b8dabbe03cab92f64`.
Its 10 non-diagnostic hosted checks passed, but Unit and Package remain red and
no Stage A cause artifact or merge result exists. Therefore the #1995 predicate
remains false. Stage A0 is closed because both hosted observation verifiers
accepted and both termination-verifier rejection assertions passed. The single
next gate is a separately reviewed native fixed-enum reason for the exact
`sealResultAuthority` failure path, reconciled across source and installed-wheel
hosted evidence. The current observation remains ineligible as cause proof; it
is not a retry, a behavioral fix, or a relaxation of the certificate predicate.
All required hosted checks must eventually pass on one corrected exact SHA
before merge.
This predicate closes only the
runner prerequisite/current PR gate, not global certification. It forbids
retries-as-pass, timeout or resource increases, preload or authority weakening,
waivers, local-for-hosted substitution, and merging diagnostic-only heads.

#### Pinned Vitest cause-evidence gate

The next cycle has three ordered stages. Stage A0 observes the protected hosted
path without claiming a cause. Stage A collects a protected fixed-enum cause.
Stage B specifies and corrects that cause. The known failing behavior and the
evidence-producing code are separate identities. The protected workflow pins
both before execution:

```yaml
failure_baseline_sha: b09b6bef2c8c4bee762965be463527cd0b050154
protected_base_sha: 39776aa9bb027c638812a01b8dabbe03cab92f64
diagnostic_head_sha: $PDD_REVIEWED_DIAGNOSTIC_HEAD_SHA
diagnostic_producer_sha256: $PDD_REVIEWED_PRODUCER_SHA256
diagnostic_verifier_sha256: $PDD_REVIEWED_VERIFIER_SHA256
observation_verifier_sha256: $PDD_REVIEWED_OBSERVATION_VERIFIER_SHA256
package_attestation_verifier_sha256: $PDD_REVIEWED_PACKAGE_VERIFIER_SHA256
package_provenance_sha256: $PDD_REVIEWED_PACKAGE_PROVENANCE_SHA256
runner_image: ubuntu-24.04/20260714.240.1
runner_provisioner: 20260707.563
python: 3.12.13
node: 22.23.1
vitest_package_sha256: 63b0ce64263ea3acaed934e5fb5fbbb98d7fcd7673acd40e164dea2a648f2da5
vitest_lock_sha256: bfc69a55d08997f553a0901c2ec0b7830cb01d6c6cc81257d150dcc79d20783c
test_node: tests/test_sync_core_runner_vitest.py::test_real_vitest_runs_copied_entrypoint_without_candidate_result_access
```

Stage A0 writes canonical `vitest-no-result-observation-v1` only for the exact
reviewed no-result path. It contains exact head/base/review/toolchain bindings,
an authenticated `lane` enum (`source` or `installed-wheel`), `runner_origin`,
`supervisor_exit_code`, `result_frame_present`, and an ordered bounded list of
authenticated fixed-enum progress frames. The source form requires
`runner_origin: source-checkout` and forbids wheel/Package-attestation fields.
The installed-wheel form requires `runner_origin: installed-wheel` and binds the
exact Package-attestation digest, wheel digest, and installed-runner digest. It
contains no raw stderr, paths, candidate bytes, inferred cause, or cause-specific
RED. A separately reviewed observation verifier digest is protected and bound
into the Sol review evidence. The verifier must prove each expected lane and its
distinct identity bindings and must explicitly return `cause_eligible: false`.
Both artifacts must also be submitted to the Stage A termination verifier and
produce its exact stable rejection. Stage A0 does not close any Stage A
predicate; it only supplies the evidence needed to add a concrete cause-eligible
frame, if one exists.

Stage A must first prove preflight and then run the pinned failing node. A
failure writes `vitest-preflight-v1` with `status: failed`, the stable predicate,
nonsecret expected/actual values, exact command exit, first 4096 output bytes,
full-output digest, and truncation flag. Success writes
`vitest-preflight-pass-v1` with `status: passed`, exact trigger/checkout/reviewed
head, baseline/protected-base SHAs, reviewed file/evidence/package digests, and
measured runtime/toolchain pins. Both forms use canonical JSON, mode 0600 atomic
writes, a SHA-256 sidecar, and `if: always()` upload. The cause artifact must not
claim a cause-specific RED:

```bash
failure_baseline=b09b6bef2c8c4bee762965be463527cd0b050154
protected_base=39776aa9bb027c638812a01b8dabbe03cab92f64
diagnostic_head="$(git rev-parse HEAD)"
test "$diagnostic_head" = "$PDD_TRIGGER_PR_HEAD_SHA"
test "$diagnostic_head" = "$PDD_REVIEWED_DIAGNOSTIC_HEAD_SHA"
git merge-base --is-ancestor "$failure_baseline" "$diagnostic_head"
git merge-base --is-ancestor "$protected_base" "$diagnostic_head"
producer_sha256="$(sha256sum pdd/sync_core/runner.py | cut -d' ' -f1)"
verifier_sha256="$(sha256sum scripts/verify_vitest_termination_evidence.py | cut -d' ' -f1)"
package_verifier_sha256="$(sha256sum scripts/verify_vitest_package_attestation.py | cut -d' ' -f1)"
package_provenance_sha256="$(sha256sum scripts/verify_vitest_package_provenance.sh | cut -d' ' -f1)"
test "$producer_sha256" = "$PDD_REVIEWED_PRODUCER_SHA256"
test "$verifier_sha256" = "$PDD_REVIEWED_VERIFIER_SHA256"
test "$package_verifier_sha256" = "$PDD_REVIEWED_PACKAGE_VERIFIER_SHA256"
test "$package_provenance_sha256" = "$PDD_REVIEWED_PACKAGE_PROVENANCE_SHA256"
jq -e \
  --arg baseline "$failure_baseline" \
  --arg protected "$protected_base" \
  --arg head "$diagnostic_head" \
  --arg producer "$producer_sha256" \
  --arg verifier "$verifier_sha256" \
  --arg package_verifier "$package_verifier_sha256" \
  --arg package_provenance "$package_provenance_sha256" \
  '(.verdict == "APPROVE") and
   (.behavioral_verdict == "NO_BEHAVIORAL_FIX") and
   (.failure_baseline_sha == $baseline) and
   (.protected_base_sha == $protected) and
   (.diagnostic_head_sha == $head) and
   (.producer_sha256 == $producer) and
   (.verifier_sha256 == $verifier) and
   (.package_verifier_sha256 == $package_verifier) and
   (.package_provenance_sha256 == $package_provenance)' \
  "$PDD_REVIEW_EVIDENCE_PATH"
set +e
PDD_VITEST_DIAGNOSTIC_OUTPUT="$RUNNER_TEMP/vitest-termination-v1.json" \
pytest -q tests/test_sync_core_runner_vitest.py::test_real_vitest_runs_copied_entrypoint_without_candidate_result_access --timeout=180
test_status=$?
set -e
test "$test_status" -eq 1
python scripts/verify_vitest_termination_evidence.py \
  --evidence "$RUNNER_TEMP/vitest-termination-v1.json" \
  --failure-baseline-sha "$failure_baseline" \
  --diagnostic-head-sha "$diagnostic_head" \
  --producer-sha256 "$producer_sha256" \
  --verifier-sha256 "$verifier_sha256" \
  --package-verifier-sha256 "$package_verifier_sha256" \
  --package-provenance-sha256 "$package_provenance_sha256" \
  --runner-image ubuntu-24.04/20260714.240.1 \
  --python 3.12.13 --node 22.23.1 \
  --vitest-lock-sha256 bfc69a55d08997f553a0901c2ec0b7830cb01d6c6cc81257d150dcc79d20783c \
  --test-node tests/test_sync_core_runner_vitest.py::test_real_vitest_runs_copied_entrypoint_without_candidate_result_access
```

`vitest-termination-v1.json` is written only by the protected coordinator from
fixed-enum frames received over its authenticated FIFO. Schema version 1 must
contain the exact pinned fields above plus `process_role`, `failure_stage`,
`cause_code`, `exit_code`, all three cgroup deltas, and `diagnostic_sha256`.
Stage A records `cause_red_status: pending`; it must not invent a RED node from
an unobserved cause. The diagnostic head must be an exact reviewed,
evidence-only descendant of `failure_baseline_sha`; its review evidence binds
the permitted diff, producer digest, termination verifier digest, both Package
authority digests, and `NO_BEHAVIORAL_FIX` verdict. The protected workflow hashes
the Package provenance script before executing it; that script then hashes the
attestation and termination verifiers before either can execute. The termination
verifier exits zero only when both SHAs and all four digests match the protected
pins, `process_role`, `failure_stage`, and `cause_code` are known enum
values other than `UNKNOWN`, and the cgroup deltas are nonnegative integers. The
artifact and its SHA-256 must be uploaded by the protected job and linked in the
ledger. Stage B starts only after Stage A passes: it adds a distinct RED bound to
the observed fixed-enum cause, proves that RED fails before the fix, and then
requires the RED plus source and installed-wheel hosted Vitest checks to pass on
one exact reviewed correction head. No behavioral fix, rerun-as-pass, or PR
merge is allowed before these ordered predicates are true.

This plan originated from an audit of `origin/main` at `c255f3bf` and the open
global-sync branches on 2026-07-09. The execution state and ledger were refreshed
against protected `main` `0e22fe9f42f72a70fc85cb6f9c289fd8187df451` and the
open PRs on 2026-07-18.

- `origin/main` tracks 42 non-run-report fingerprint files. The in-progress
  inventory in PR #1969 identifies 223 stampable units, leaving 181 intended
  units without tracked fingerprints on `main`.
- A clean-checkout `pdd reconcile` on `origin/main` classified those 42 visible
  units as 9 current, 7 stale, 20 conflicts, and 6 failures.
- Once any metadata exists, the merged discovery path defaults to metadata-backed
  units. It therefore reports `unbaselined=0` while omitting prompt-backed units
  that have no fingerprint.
- The issue #1932 test suite passed 13 tests before PR #1954 merged, but it drives
  reporting-only forms of `sync`, `update`, `change`, and CI heal through the same
  `build_report` helper. Its heal assertion re-stamps changed bytes; it does not
  verify semantic propagation.
- Live mutation still relies on `sync_determine_operation`, command-specific
  wrappers, and CI-only reclassification.
- There are ten direct `save_fingerprint` call sites in the open integration
  branch. The base writer performs a direct write and reports persistence failure
  as a warning.
- PR #1969 is blocked. Its required unit and auto-heal checks fail. A local run of
  the merged issue #1932 acceptance suite against its head produced 9 failures and
  4 passes.
- PR #1937 sketches transactional finalization in prompt files but does not yet
  contain the complete generated implementation and invariant test harness.
- `pdd_cloud` PR #3013 merged a deterministic prompt-side nightly reconciler, but
  pdd_cloud issue #2994 remains open for code-side coverage and cleanup. The
  historical consumer baseline was 377 stale fingerprints out of 788.

These facts make PR #1954 a partial delivery, not completion of issue #1932.

### 2.1 Execution ledger (2026-07-10)

This ledger records implementation progress; it does not replace the Definition
of Done or authorize a partial green certificate.

| Workstream | Current evidence | State |
| --- | --- | --- |
| Canonical core | Identity, immutable Git manifest, include closure, hashing, classifier, profiles, trust, reporting, transaction WAL, and compatibility routing implemented under `pdd/sync_core/` | implemented, not rolled out |
| Exact certification | Independent exact-SHA clones, clean-tree/ancestry checks, strict fresh green certificate verification, exact issuer/repository refs, and remote-signature verification without local private keys | implemented and unit tested; protected signer service absent |
| Trusted test runner | Strict pytest invocation; ambient options/plugins disabled; config, `conftest.py`, and transitive local helper closure signed; protected and candidate node IDs compared before each protected node executes independently; candidate-only profiles rejected and actual pytest config digest checked | implemented for pytest only; non-pytest and threshold-human adapters remain |
| Temporal proof | Signed rows require complete predicates, repository identity, SHA ancestry, consecutive UTC dates, deleted-ledger full scans, normal no-op observations, injected canary outcomes, and zero-write reruns; exact immutable attestation rechecks are idempotent while nonce rebinding fails | implemented locally; protected timestamped storage and seven real nights absent |
| Lifecycle harness | A released checker installs the exact candidate wheel in a separate credential-free environment, binds its SHA-256 into the signed predicate, drives public candidate report/recovery commands, and independently runs the required scenario registry and real cloud canary | split-install wheel run: one expected cloud-canary failure; clean candidate-venv diagnostic adds only the expected source-checker provenance failure; zero skips/errors/timeouts/no-op writes/tree changes/missing scenarios; protected release/workflow deployment remains |
| Protected mutation | Transaction commits use pinned parent descriptors, no-follow traversal, descriptor-relative replace/unlink, full blob preflight, and a released-harness symlink-swap injection; legacy generators are blocked before invocation when protected canonical policy is active | safe fail-closed path implemented; staged repair executor remains absent |
| PDD verification | `291 passed` for `tests/test_sync_core_*.py` with no skips; broad compatibility suite reached 1,145 pass/4 coverage-capture failures and all four focused regressions pass after the activation fast-path repair; unit snapshots no longer drift on unrelated human-owned changes | component green, E2E red |
| pdd_cloud boundary | Exact-tree path/Python/prompt/architecture scan reports zero forbidden vendored semantics at `677a9c88f`; the legacy finalizer declarations and implementation are removed and current consumer installs are exact-version pinned | implemented; final pin must target the protected reviewed release |
| pdd_cloud inventory | Protected registry/tombstone commit `39b78e487` retains 573 historical identities and authorizes only the retired finalizer; both transition and stable manifests report 572 managed = 572 expected, zero invalid, and zero unaccounted | profiles/evidence migration remains |
| Global certificate | Scan remains red for protected checker deployment, transactional staging, profile/evidence debt, and nightly history | correctly blocked |
| Adversarial review | xhigh round 9 returned `NOT APPROVED`; it confirmed exact-SHA candidate build attestation, protected release/nightly workflow, protected alias wiring, adapter completion, profile/evidence rollout, and seven real nights remain | no-follow commit and fail-closed unstaged mutation are implemented; release and rollout blockers remain |

No acceptance claim is valid until the signed certificate recomputes `ok: true`
for exact protected PDD and pdd_cloud SHAs and a verifier supplied with the
protected issuer, expected repository identities/SHAs, and current time accepts
it without candidate-controlled inputs.

### 2.2 Critical unblock sequence

The final certificate cannot be unblocked by weakening its predicate. Work must
proceed in this dependency order, with each exit check retained as evidence for
the next stage. The 2026-07-18 current PR gate above is a prerequisite to this
sequence and does not alter any of its ten steps.

The machine-readable source of truth for step status and exact evidence is
[`docs/global_sync_evidence_ledger.yaml`](global_sync_evidence_ledger.yaml).
This narrative summarizes that ledger; it does not override missing or red
machine evidence.

| Order | Unblock | Required exit evidence |
| --- | --- | --- |
| 1 | Split the current dirty implementation into reviewable foundation, transaction, runner/trust, command-routing, and rollout commits. Do not activate enforcement in these commits. | Each commit has focused tests; the branch is clean; source and built-wheel suites agree. |
| 2 | Publish the checker from a protected reviewed tag and pin its wheel digest in protected CI. The released checker, not candidate code, owns scenario definitions, lifecycle metrics, certificate predicate recomputation, and signing. Candidate generators and tests run only in credential-free children. | A candidate change that returns unconditional PASS, edits lifecycle scenarios, or prints environment variables still produces a red unsigned observation; the released checker artifact digest and workflow identity are present in the signed certificate. |
| 3 | Replace direct production writes with generate-to-staging followed by one durable transaction containing artifacts, shared metadata, evidence, report, and fingerprint. Use descriptor-relative no-follow commit operations and verify all WAL blobs before the first destination change. | Process death at every generation/journal/install phase recovers to the complete old or complete new state; immediate rerun writes zero files. |
| 4 | Make the pytest adapter compare protected expected node IDs with collected and executed node IDs, and bind every config-loaded plugin and executable support module. Add the remaining declared adapters before claiming cross-language coverage. | Removed parametrized cases, config-loaded local plugins, collection hooks, skips, xfails, deselection, and dirty support all fail closed. |
| 5 | Route runtime preprocessing, dependency discovery, change detection, and legacy operation selection through the canonical include graph, identity, classifier, and transaction APIs. | No production module independently parses includes, hashes fingerprints, classifies drift, or writes canonical metadata; compatibility modules contain orchestration only. |
| 6 | Land and release the PDD foundation. Run the released checker against clean exact-SHA PDD clones, then create protected verification profiles and trusted evidence for every expected managed unit. | PDD exact-SHA report has complete inventory, 100% profiles/evidence, and zero red semantic/baseline states or waivers. |
| 7 | Pin that release in pdd_cloud, remove `metadata_finalize.py` and all other vendored sync semantics, resolve the duplicate output conflict, then migrate profiles, fingerprints, and evidence by bounded subtree PRs. | Independent semantic ownership audit and exact-tree scan both report zero consumer-owned sync semantics; pdd_cloud has 100% profiles/evidence and no red units or waivers. |
| 8 | Enable the protected merge-group lifecycle lane using clean clones and the pinned checker. Run every required injected scenario, including the real pdd_cloud canary, without required skips. | One fresh signed scan certificate has `scan_ok: true`, lifecycle failures/skips/errors/timeouts zero, and both no-write counters zero. |
| 9 | Start the temporal gate only after steps 1-8 are stable. Store signed immutable nightly rows outside either candidate checkout and run complete scans even after ledger/cursor deletion. | Seven consecutive UTC-date certificates preserve repository identity/SHA lineage; normal nights are no-op and injected drift is detected, resolved or blocked, then rerun with zero writes. |
| 10 | Run the documented final command and a fresh Sol HIGH adversarial review. | Command exits 0; an independent verifier accepts the signed exact-SHA certificate; the review records the exact certificate and repository SHAs and returns `APPROVE`. |

Steps 1-7 are engineering work. Step 8 requires protected CI/release configuration.
Step 9 additionally requires seven elapsed nightly windows and therefore cannot
be replaced with locally fabricated timestamps. The current implementation is
at steps 1-4: released-wheel identity, exact pytest node collection proof, and
the checker-owned harness are implemented and built-wheel tested locally.
Protected release/workflow deployment, transactional generation-to-staging,
non-pytest adapters, and repository profile/evidence rollout are not complete.

## 3. Scope

### 3.1 In scope

- Prompt, transitive included-document, code, example, and test synchronization.
- Architecture and `.pddrc` identity/path consistency.
- Fingerprint and run-report trustworthiness.
- Manual edits, coding-agent edits, PDD command edits, CI auto-heal edits, and
  hotfix PRs.
- Nested projects, Git worktrees, duplicate leaf names, path-qualified modules,
  missing files, renames, and deletions.
- Python and every language currently supported by PDD path resolution.
- Human-owned tests and artifacts that PDD validates but must not overwrite.
- Source checkout and installed-wheel behavior.
- The PDD repository as the first dogfood target and pdd_cloud as the first large
  consumer rollout.

### 3.2 Out of scope

- A real-time background regeneration daemon. Commit, PR, merge, and nightly
  boundaries are sufficient.
- PRD synchronization. It needs a separate semantic model after the core artifact
  loop is trustworthy.
- Automatic acceptance of ambiguous conflicts.
- Proving arbitrary prose and arbitrary code are semantically equivalent with no
  declared contract or executable evidence. Such units must report `UNKNOWN`, not
  `IN_SYNC`.

## 4. Definitions and invariants

### 4.1 Three independent status dimensions

The implementation must stop using one `IN_SYNC` label for three different
claims.

| Dimension | Values | Meaning |
| --- | --- | --- |
| Inventory | `MANAGED`, `HUMAN_OWNED`, `REMOVED`, `INVALID` | Intrinsic unit/artifact ownership; waivers are a separate exception dimension |
| Baseline | `CURRENT`, `DRIFTED`, `UNBASELINED`, `CORRUPT` | Whether current bytes match a trustworthy fingerprint |
| Semantic | `VERIFIED`, `UNKNOWN`, `CONFLICT`, `FAILED` | Whether prompt-side intent and derived behavior have current evidence of agreement |

`IN_SYNC` is a derived convenience verdict and is legal only when:

```text
inventory == MANAGED
and baseline == CURRENT
and semantic == VERIFIED
and no required artifact is missing
and all required validation evidence is tied to the current artifact hashes
and every obligation in the unit's verification profile is trusted-verified
```

An explicit baseline reset produces `CURRENT + UNKNOWN`, not `IN_SYNC`.

### 4.2 Required invariants

1. **Complete inventory:** the candidate universe is the union of the base and head
   manifests, configured source/test roots, prompt declarations, architecture
   declarations, fingerprints, ownership records, and unmatched tracked artifacts.
   Every candidate is classified as managed, human-owned, removed, or invalid,
   with waiver state reported orthogonally. No unit disappears because its prompt,
   declaration, and metadata were deleted together.
2. **One identity:** every layer resolves the same stable repository-relative unit
   ID, checkout/config roots, artifact paths, and ownership.
3. **One classifier:** given the same snapshot and optional Git change set, every
   consumer emits the same baseline and semantic statuses.
4. **Transactional success:** a mutating command cannot report success unless its
   artifact writes, validation evidence, run report, and fingerprint commit as one
   successful state transition.
5. **No silent acceptance:** no unattended command changes a baseline merely to
   make drift disappear.
6. **No data loss:** a prompt-side and derived-side co-edit never auto-selects a
   winner or deletes ancestor metadata.
7. **No silent skip:** every ignored, waived, unbaselined, invalid, failed, or
   conflicted condition appears in human and JSON summaries, including gross
   inventory counts before waivers.
8. **Idempotency:** after a successful repair, the same command run again performs
   no writes and recommends no additional repair.
9. **Evidence freshness and trust:** tests, examples, surface checks, and run reports
   count only when a trusted validator recomputes them or verifies a trusted
   attestation bound to the complete input closure, manifest/config digest, runner
   command/config, tool versions, result, base SHA, and checked head/merge-group SHA.
   PR-authored status fields and evidence files cannot certify themselves.
10. **Boundary enforcement:** protected `main` accepts a managed unit only when it
    satisfies the complete `IN_SYNC` predicate. `DRIFTED`, `UNBASELINED`, `CORRUPT`,
    `UNKNOWN`, `CONFLICT`, `FAILED`, and `INVALID` block unless a trusted,
    snapshot-bound, reviewable, expiring waiver applies.

## 5. Target architecture

### 5.1 Package boundaries

Create a small sync core and migrate existing modules behind compatibility shims:

```text
pdd/sync_core/
  types.py              immutable IDs, snapshots, statuses, decisions
  identity.py           canonical project/unit/path/ownership resolution
  path_policy.py        protected read/write roots and no-follow validation
  includes.py           canonical include parser and dependency closure
  hashing.py            canonical artifact and composite prompt hashing
  fingerprint_store.py  schema migration, atomic read/write, locks
  classifier.py         pure drift and conflict classification
  planner.py            status -> allowed repair plans
  capabilities.py       command/agent/server mutation scopes and transaction policy
  transaction.py        artifact/fingerprint/evidence finalization
  ledger.py             durable changed-unit queue and acknowledgements
  reporting.py          stable human and JSON schema
```

Existing public APIs remain during migration:

- `sync_determine_operation` becomes a compatibility adapter that adds workflow
  progression and operation selection to the core classifier result.
- `operation_log.save_fingerprint` becomes a deprecated adapter around the
  transaction/store API and is eventually internal-only.
- `continuous_sync` becomes command composition and reporting, not a second unit
  resolver, hasher, or classifier.
- `ci_drift_heal`, `agentic_sync`, `update`, `change`, and global `sync` consume
  the same core snapshot and decision types.

### 5.2 Canonical unit identity

Use a typed candidate identity for every artifact and derive a `UnitId` only after
prompt-backed adoption. Do not use a flattened metadata filename:

```python
@dataclass(frozen=True)
class CandidateId:
    repository_id: str
    artifact_relpath: PurePosixPath
    role: str

@dataclass(frozen=True)
class UnitId:
    repository_id: str
    prompt_relpath: PurePosixPath
    language_id: str

SubjectId = UnitId | CandidateId

@dataclass(frozen=True)
class ResolvedUnit:
    unit_id: UnitId
    checkout_root: Path
    config_root: Path
    basename: str
    prompt_path: Path
    code_path: Path | None
    example_paths: tuple[Path, ...]
    test_paths: tuple[Path, ...]
    included_docs: tuple[Path, ...]
    dependencies: tuple[UnitId, ...]
    owned_artifacts: frozenset[str]
    validated_artifacts: frozenset[str]
    ownership_provenance: Mapping[str, str]
    config_path: Path | None
    architecture_path: Path | None
    manifest_digest: str
```

Resolution precedence is explicit and tested:

1. Read a stable UUID from the protected `.pdd/repository-id`, separately from the
   checkout/worktree root and nearest governing `.pddrc`. A new repository
   initializes it once in a reviewed setup commit. Fork PRs use the target base
   repository ID; remote rename/transfer does not change it. An independent fork
   requires an explicit protected rekey migration. Offline operation reads the
   file; a legacy repository without one may report using an ephemeral ID but may
   not write canonical v2 state until initialization.
2. Identify units by repository-relative POSIX prompt path plus stable language ID.
   Absolute paths never enter persistent identity; basename and language spellings
   are aliases, not identity.
3. Apply `.pddrc` path templates relative to the governing config directory.
4. Apply an exact architecture entry override only when it maps to the same prompt
   identity.
5. Reject ambiguous leaf aliases and duplicate prompt-to-artifact mappings.
6. Include normalized role-to-path mappings, `.pddrc`, architecture, ownership,
   graph declarations, and policy inputs in the manifest digest. A path-policy
   retarget is drift even when the old and new files have identical bytes.
7. Compare the base and head manifests. A rename requires an explicit identity
   migration; a removal requires a reviewed tombstone that accounts for every
   previously owned artifact and fingerprint.
8. Compile an in-memory `UnitManifest`; all downstream consumers use it rather
   than resolving paths again.

Promptless code/tests and other unmatched artifacts retain `CandidateId` and can
be reported, owned, waived, removed, or later adopted into a `UnitId`. Adoption is
an explicit protected mapping; it cannot happen by basename guess.

Reports, ledgers, waivers, tombstones, ownership transitions, and journals use a
discriminated `SubjectId`, never assume every candidate already has a `UnitId`.

The manifest is deterministic output, not another hand-maintained source of
truth. An optional committed inventory lock is only a generated assertion used to
detect unexplained additions/removals. Tests compare manifests across source
checkout, wheel installation, root invocation, nested invocation, and Git
worktrees. The migration must adapt or retire the existing `ResolvedSyncUnit`
resolver so it cannot remain a parallel identity implementation.

Repository-ID initialization, rekey, ownership transition, unit rename, adoption,
and removal are protected policy transitions evaluated against the base manifest.
Tests cover forks, renamed/transferred remotes, no-remotes/offline operation,
independent fork rekey, and legacy repositories.

The resolver also emits a protected `expected_managed` assertion derived from base
and historical prompt, architecture, fingerprint, ownership, and generation
provenance. It fixes the sync-capable denominator independently of current debt:

- A currently/previously generated or prompt-backed expected-managed subject cannot
  move to `HUMAN_OWNED` while non-`IN_SYNC`.
- Permanent decommissioning is a separate protected PR starting from a trusted
  `IN_SYNC` snapshot, contains no unrelated behavior change, accounts for every
  artifact through a tombstone, and records rationale/owner. It is reported as
  decommissioning, not drift burn-down.
- Activation and epic closure require zero managed-to-human transitions used to
  discharge debt. Reports show expected-managed total, current managed total,
  historical human-owned total, and all transitions.

#### Protected path policy

One protected-base `PathPolicy` governs every prompt, generated artifact, example,
test, architecture/config file, metadata file, runner config, evidence record,
staging file, journal, and shared resource. Include policy is one use of it, not a
separate trust boundary.

- Managed readable/writable paths are repository-relative and must resolve within
  the canonical checkout realpath. Managed path declarations using absolute paths,
  `..` escapes, unapproved symlinks, FIFOs, devices, sockets, or other special files
  are `INVALID`.
- A protected `RepositoryAlias` may represent an existing Git-tracked base-approved
  symlink such as `prompts -> pdd/prompts`. Its logical repository-relative path is
  preserved for identity while the manifest records the link blob/hash, canonical
  target path/identity, and alias-policy digest. The complete chain must remain
  inside the checkout, acyclic, non-dangling, and unchanged from protected base.
  Candidate alias additions/retargets cannot govern their own check.
- Transactions never write through or replace a symlink. For an approved alias,
  writes target the prevalidated canonical regular file through descriptor-relative
  operations while rechecking the protected alias chain. Link retarget, dangling or
  cyclic aliases, target replacement, and descriptor-time swaps fail closed.
- Protected external roots are read-only inputs only. PDD never finalizes managed
  artifacts, metadata, evidence, or journals outside the checkout.
- An explicit CLI output outside managed roots is allowed only as an unowned export:
  it is marked `SKIPPED_NO_FINALIZATION`, cannot update the unit fingerprint, and
  cannot contribute trusted semantic evidence.
- Resolution uses `lstat`/realpath checks for every existing component. Transaction
  commit revalidates with descriptor-relative operations (`openat`/`renameat` style),
  no-follow flags, inode/type preconditions, and parent directory descriptors so a
  symlink swap after planning becomes `CONFLICT`/failure rather than an overwrite.
- Capability-registry read/write scopes are constrained by `PathPolicy`; declaring a
  broad scope cannot widen protected roots.
- The policy digest is part of the manifest and trusted evidence. Candidate changes
  are proposals only and cannot govern the check evaluating that branch.

#### Language and format identity

Replace spelling/extension inference with a protected `LanguageSpec` registry. Each
row has a stable unique `language_id`, canonical display name, explicit aliases,
role-specific extensions/formats, text/binary hashing mode, and generator/runner
capabilities. Each language/role also references an `ArtifactModePolicy` defining
allowed artifact type, normalized Git mode (`100644`, `100755`, or protected alias
`120000`), and policy-relevant permission bits. `UnitId` and fingerprints persist
`language_id`; the registry/mode-policy digest is part of the manifest and evidence
closure.

- Every alias resolves to exactly one language ID in a declared context. Duplicate
  normalized aliases, conflicting role extensions, and ambiguous extension-only
  inference are `INVALID` until the registry is repaired.
- Extension collisions require explicit language/config identity; the resolver does
  not select the first row.
- Existing duplicate/ambiguous rows receive an explicit migration mapping before
  v2 identity becomes authoritative.
- Tests are generated from every protected registry row and every applicable output
  role in source and installed-wheel environments. Registry additions cannot merge
  without their generated conformance cases.

`UnitSnapshot` records content digest, artifact type, normalized Git mode, and
policy-relevant permission bits for every artifact. Mode-only changes are drift.
Platform-specific permission noise outside the protected policy is normalized, but
the executable bit and every declared security-relevant bit are authoritative.

### 5.3 Canonical dependency graph

The include parser used by preprocessing becomes the only parser. It must return
structured include records for:

- Bare `<include>path</include>`.
- Attributed body forms including `path`, `select`, and `query`.
- Self-closing `<include path="..." />`.
- `<include-many>` with comma and newline separation.
- Backtick include syntax where still supported.
- Transitive includes with cycle detection and a deterministic traversal order.

Path trust is defined before parsing content:

- The default readable boundary is the canonical realpath of the repository
  checkout, not the nearest nested config root. Nested `.pddrc` files may reference
  parent paths that remain inside that repository boundary.
- Resolve and normalize every path and symlink before the boundary check. Relative,
  `..`, absolute, and symlinked paths that escape the checkout are rejected.
- A protected-base external-root policy may allow a named external root. It is
  mounted read-only in the CI sandbox, assigned a stable external-root ID, and its
  exact content snapshot contributes to the baseline/evidence closure.
- Candidate branches cannot add or widen external roots for the check evaluating
  that branch. Local commands use the same protected policy and fail closed when
  it is unavailable.

The result is a typed directed multigraph. Every edge records its type, direction,
source authority, propagation policy, ownership effect, and hash contribution:

- `PROMPT_INCLUDE`: document/input -> prompt; reverse changes trigger regeneration.
- `UNIT_CONTRACT`: provider unit -> consumer unit; public-contract changes propagate.
- `TEST_VALIDATES`: test -> unit; it contributes evidence but not regeneration order.
- `RUNTIME_DEPENDENCY`: provider -> consumer; it informs affected validation and may
  have strongly connected components.
- `ARCHITECTURE_ASSERTION`: a declaration that must agree with authoritative prompt
  and config inputs; disagreement is `INVALID`, not an extra inferred edge.

Traversal is edge-policy-specific. Include cycles are errors, while legitimate
runtime dependency cycles are condensed into strongly connected components and
validated as a group. Graph declarations and resolved dependency snapshots are
hashed into the baseline and semantic evidence closure. Missing, ambiguous,
out-of-root, or policy-invalid edges are reportable failures rather than warnings.

All prompt expansion inputs are represented, including deterministic cached
results from supported web/shell/auto-deps inputs. An uncached or nondeterministic
external input makes semantic status `UNKNOWN` until a reviewed snapshot is bound
to the transaction.

### 5.4 Snapshot and classifier

The classifier is a pure function:

```python
def classify(
    unit: ResolvedUnit,
    baseline: FingerprintRecord | None,
    current: UnitSnapshot,
    evidence: ValidationEvidence | None,
    git_changes: GitChangeSet | None = None,
) -> SyncVerdict:
    ...
```

It performs no writes, LLM calls, subprocess calls, prompts, or logging side
effects. `git_changes` refines provenance and rename detection but never overrides
hash truth.

The minimum classification matrix is:

| Prompt/docs | Derived artifacts | Baseline result | Semantic result | Default action |
| --- | --- | --- | --- | --- |
| unchanged | unchanged | `CURRENT` | evidence-dependent | none or validate |
| changed | unchanged | `DRIFTED` | `UNKNOWN` | prompt-side repair (`sync`) |
| unchanged | changed | `DRIFTED` | `UNKNOWN` | derived-side repair (`update`/validate) |
| changed | changed | `DRIFTED` | `CONFLICT` | explicit resolution |
| any required file missing | any | `DRIFTED`/`CORRUPT` | `FAILED` | restore or regenerate, never stamp |
| no valid baseline | any | `UNBASELINED` | `UNKNOWN` | audited baseline or verified rebuild |

Test-only and example-only edits are derived-side changes, but ownership controls
whether PDD may rewrite them. Human-owned tests are validation inputs, never
generated outputs.

#### Verification profiles

Trusted execution proves that checks ran; it does not prove those checks cover the
prompt's complete intent. Every managed unit therefore has a typed
`VerificationProfile` with individually addressable obligations:

```python
@dataclass(frozen=True)
class VerificationObligation:
    obligation_id: str
    kind: str  # interface, requirement, story, example, test, policy, dependency
    validator_id: str
    validator_config_digest: str
    required: bool = True

@dataclass(frozen=True)
class VerificationProfile:
    unit_id: UnitId
    obligations: tuple[VerificationObligation, ...]
    required_requirement_ids: tuple[str, ...]
    profile_digest: str
    assurance: AssuranceLevel = AssuranceLevel.STANDARD_FRAMEWORK
```

`AssuranceLevel` is an ordered, digest-bound profile property:

- `standard_framework` is the compatibility default. It assumes the selected
  pytest, Jest, Vitest, or Playwright framework and its in-process hooks report
  honestly. The checker creates, owns, and bounds the FIFO/file-descriptor framework
  observation transport. It is candidate-visible under `standard_framework` and is
  not authenticated evidence against candidate code in the same address space and
  descriptor table.
- `isolated_black_box` is stronger. It requires candidate code to execute only as
  an external SUT behind a process boundary that cannot mutate checker state or its
  observation channel. No current in-process framework adapter satisfies this
  assurance.

Protected base/head reconciliation takes the stronger assurance level and records
an attempted downgrade as invalid. Assurance is included in `profile_digest`, so
evidence cannot be replayed across assurance levels. Until an external SUT adapter
is implemented, an in-process adapter selected by an `isolated_black_box` profile
returns a deterministic non-pass result and the unit remains semantic `UNKNOWN`;
it cannot issue a passing result for that obligation.

This boundary is fundamental rather than a missing FIFO, proxy, seccomp, or
cryptographic feature. Hostile code executing inside the test framework's process
can alter framework callbacks, memory, and inherited descriptors before the
checker observes them. Signing the resulting statement authenticates who signed
it and what was bound, but cannot retroactively make the in-process observation
Byzantine-resistant. The isolated-black-box follow-up therefore requires a truly
out-of-process adapter, not another in-process reporter transport.

The profile accounts for every structured prompt requirement/contract identifier,
declared interface, required story/example, PDD-owned and human-owned validation
test, policy/security check, and dependency-closure obligation. A completeness
validator reports unassigned requirements. Non-machine-verifiable requirements
need a protected human-review attestation bound to the same snapshot; they cannot
be silently omitted.

Profile and validator authority comes from protected-base policy and the trusted
checker release, not the candidate tree alone:

- Candidate additions form a conservative union with base obligations. Deleting
  an obligation, making it optional, remapping its validator, changing validator
  config, or changing an obligation-bearing test requires the designated protected
  profile/test owner approval.
- A candidate-modified validator implementation cannot validate its own change.
  The trusted released implementation remains authoritative until the two-release
  checker/validator promotion protocol completes.
- A changed validation test is provisional evidence. Trusted CI runs applicable
  unchanged/base obligations as well as candidate tests, and the changed test
  cannot be the sole proof of the behavior it was changed to accept. Protected
  owner review or another independent obligation is required.
- Profile completeness is evaluated against both base and candidate prompt/
  contract inputs, so deleting a requirement and its mapping together is detected.

Effective semantic `VERIFIED` requires trusted current evidence for every required
obligation in the protected profile. Interface-only checks, generated-old versus
generated-new comparison, partial profiles, missing validators, unstructured legacy
requirements, and locally authored evidence are safety signals only and leave the
overall unit `UNKNOWN`. A unit without a complete profile cannot enter the managed
sync guarantee: a historically human-owned candidate may remain human-owned, but an
expected-managed unit must be migrated or remain blocked.

Runner adapters normalize every expected and collected test to one terminal
outcome: `PASS`, `FAIL`, `ERROR`, `COLLECTION_ERROR`, `SKIP`, `XFAIL`, `XPASS`,
`DESELECTED`, `TIMEOUT`, `NOT_COLLECTED`, `QUARANTINED`, or `FLAKY`. Only `PASS`
may satisfy a required test obligation. Zero collected tests, collection errors,
and every other outcome leave the obligation unverified or failed. Diagnostic
retries preserve the first outcome and cannot turn a required failure into trusted
pass; an approved flaky/quarantine exception is a waiver, not `VERIFIED`.
`--skip-tests`, `--skip-verify`, filters, and deselection therefore cannot produce
overall `VERIFIED`.

### 5.5 Fingerprint schema

Introduce a versioned schema while reading the legacy format:

```json
{
  "schema_version": 2,
  "hash_algorithm_version": 2,
  "unit_id": {
    "repository_id": "018f3f5e-7b3c-7f12-a6d4-4b7fd7d8a921",
    "prompt_relpath": "pdd/prompts/widget_python.prompt",
    "language_id": "python"
  },
  "artifacts": {
    "prompt": {"path": "pdd/prompts/widget_python.prompt", "hash": "...", "git_mode": "100644"},
    "code": {"path": "pdd/widget.py", "hash": "...", "git_mode": "100644"},
    "examples": {"context/widget_example.py": {"hash": "...", "git_mode": "100755"}},
    "tests": {"tests/test_widget.py": {"hash": "...", "git_mode": "100644"}}
  },
  "include_deps": {"docs/widget.md": "..."},
  "manifest_digest": "...",
  "config_digest": "...",
  "ownership_digest": "...",
  "dependency_snapshot_digest": "...",
  "verification_profile_digest": "...",
  "provenance": {
    "kind": "generated|updated|resolved|baseline-reset",
    "command": "pdd sync widget",
    "transaction_id": "...",
    "git_commit": "..."
  },
  "claimed_semantic_status": "VERIFIED|UNKNOWN",
  "attestation_ref": "...",
  "timestamp": "...",
  "pdd_version": "..."
}
```

The tracked semantic field is an informational projection. A trusted checker
derives the effective semantic status by recomputing validation or verifying a
trusted DSSE/in-toto-style attestation. The attestation binds the complete input
closure, role-to-path mappings, manifest/config/ownership/graph digests, exact
runner commands and config files, validator and PDD versions, model/generator
identity where relevant, result summary, base SHA, and checked head or merge-group
SHA. Candidate-authored evidence without a trusted signature is `UNKNOWN`.

The fingerprint must not store null hashes for required existing artifacts.
Multi-file tests and examples are maps, not a lossy single representative hash.
Ancestor recovery stores a verified Git-object lookup strategy or durable
content-addressed snapshot sufficient for a three-way merge. PR 4 records the
choice in an ADR, including shallow-clone fetch behavior, retention, and secret
handling, and enables no conflict resolver until recovery works in CI.

### 5.6 Transaction protocol

`FingerprintTransaction` owns one resolved unit and participates in a durable
operation journal. Atomic rename of one fingerprint is not described as a
multi-file transaction.

1. Acquire all unit and shared-resource locks in deterministic global order.
   Shared files such as `architecture.json`, ownership policy, and graph snapshots
   have their own resource locks; nested calls inherit the owning transaction.
2. Capture compare-and-swap precondition hashes for every input and writable
   resource, including artifact type, normalized Git mode, and policy-relevant
   permission bits. Resolve paths once through protected `PathPolicy`; callers may
   not substitute another root later.
3. Persist and `fsync` a write-ahead journal entry containing participants,
   preconditions, durable rollback blobs, planned paths, and prepared output hashes.
4. Execute generators/tests in isolated staging locations. No owned destination is
   overwritten during preparation.
5. Validate outputs and create provisional run/evidence records tied to prepared
   hashes.
6. Recheck all preconditions. An external edit since planning changes the verdict
   to `CONFLICT`; it is never overwritten. Reopen destination parents through
   descriptor-relative no-follow operations and reject inode/type/mode/permission/
   symlink changes using `fstat`.
7. Mark the journal `COMMITTING`, then install artifacts and shared-file patches in
   deterministic order using same-directory temp files, flush/`fsync`, `os.replace`,
   and directory `fsync`. Set and verify the protected destination mode on staged
   files before install. Shared-file patches use compare-and-swap merge semantics.
8. Persist run reports and the fingerprint, then mark the journal `COMMITTED` and
   release resources.
9. At mutator preflight, or through explicit `pdd recover --transaction ID`,
   recovery scans incomplete journals. Based on the durable commit marker it
   deterministically completes the prepared commit or restores all participants
   from durable rollback blobs. Recovery itself is idempotent. Read-only commands
   never recover implicitly; they return `RECOVERY_REQUIRED` with the exact
   recovery command and leave all bytes unchanged.
10. Any failure raises a typed non-zero command error. Finalization failure is never
    downgraded to a warning.

Multi-unit commands maintain an aggregate journal with one state per participant.
Policy explicitly chooses all-or-nothing or independently committable units. In
the latter mode, a later failure reports `PARTIAL` with committed and pending unit
IDs; it never reports global success or loses the ability to resume. Resource-lock
ordering and aggregate recovery prevent deadlocks and shared-file lost updates.

Journal/rollback storage is operational state, never repository content:

- Store it under a Git-excluded per-repository state directory with directory mode
  `0700` and files `0600`; CI uses an ephemeral encrypted workspace.
- Apply bounded byte/count/age retention and clean committed/recovered journals.
  Retain unresolved journals until explicit recovery or protected quarantine.
- Secret-labeled artifacts require platform-backed encryption at rest or the
  transaction refuses to persist rollback content.
- Rollback records preserve artifact type and protected mode/permission metadata;
  recovery restores and verifies them, not only content bytes.
- Preflight available space before preparation. Quota/disk failures abort before
  destination writes and preserve the prior state.
- Artifact upload and debug-log collectors explicitly exclude journals, rollback
  blobs, and staged prompt/code content.
- Tests prove journals cannot be staged by normal Git commands, included in built
  packages, or uploaded by CI artifact patterns.

Dry-run and redirected-output modes explicitly record `SKIPPED_NO_FINALIZATION`
and cannot be mistaken for successful synchronized transitions.

### 5.7 Repair planner

The planner accepts a verdict and policy, then returns allowed actions. It never
changes classification to make a preferred operation possible.

| Verdict | Allowed unattended action | Interactive/reviewed action |
| --- | --- | --- |
| Prompt/doc-only drift | targeted `sync` if policy permits generation | review generated patch |
| Code-only drift | none by default; only a proven requirement-preserving three-way update under a complete profile | review and approve minimal prompt patch |
| Test/example-only drift | validate; update prompt only when contract changed | adopt or keep human-owned artifact |
| Conflict | none | prompt wins, code wins, or three-way merge |
| Unbaselined | none | verified rebuild or explicit baseline reset |
| Missing/corrupt artifact | restore/regenerate only when source is unambiguous | manual recovery |
| Validation failure | bounded repair with circuit breaker | manual fix |

`reconcile --heal` is deprecated because it currently means "accept current
hashes." Replacement commands are explicit:

- `pdd reconcile`: read-only status/report.
- `pdd reconcile --check`: read-only non-zero gate.
- `pdd baseline --accept-current UNIT --reason TEXT`: reviewed baseline reset,
  resulting in semantic `UNKNOWN`.
- `pdd resolve UNIT`: explicit conflict workflow.
- `pdd sync` / `pdd update`: semantic repair workflows.

Code-to-prompt repair is a three-way minimal patch using the last verified prompt
as ancestor. It must preserve every existing requirement/contract identifier and
all unrelated text, then satisfy every obligation in the complete verification
profile. If the prompt is unstructured, preservation cannot be proved, or any
obligation lacks trusted evidence, automation emits a review patch and leaves the
unit `UNKNOWN`; it does not finalize unattended.

## 6. Delivery workstreams and PR sequence

Each PR must be independently reviewable. Do not merge a 200-file epoch stamp in
the same PR as resolver, classifier, command, or policy changes.

### PR 0: Restore governance and pin strict expected failures

Issues: #1932, #1836, #1927-#1931

Tasks:

- Reopen #1932 or create a replacement tracking epic that links every workstream.
- Record PR #1954 as a partial milestone.
- Add this plan to the epic and make its exit gates the Definition of Done.
- Convert the existing issue #1932 tests into a durable acceptance lane.
- Add reproductions for the audit findings: incomplete inventory, semantic status
  after baseline reset, current/live classifier divergence, and missing artifact
  behavior.
- Put unresolved acceptance tests in a dedicated nonblocking lane with
  issue-linked `pytest.mark.xfail(strict=True)`. A fix that unexpectedly passes
  fails as XPASS until the marker is removed and the test moves to the required
  lane; ordinary required CI stays green while PR 0 lands.
- Keep PR #1969 blocked and split it along the PR boundaries below.
- Close or supersede PR #1937 unless it is completed as PR 4/5 below.

Exit gate:

- The epic is open, child dependencies are visible, and strict expected-failure
  tests reproduce each unresolved guarantee without changing production behavior.

### PR 1: Canonical unit manifest and ownership

Issues: #641, #884, #1931, #1903

Tasks:

- Add `CandidateId`, `UnitId`, `SubjectId`, `ResolvedUnit`, ownership types, and
  manifest diagnostics.
- Implement the resolution precedence in section 5.2.
- Build the candidate union from base/head manifests, configured source and test
  roots, prompts, architecture entries, fingerprints, ownership records, and
  tracked artifacts. Enumerate unmatched code/tests and whole-unit deletions even
  when no prompt or metadata remains at head.
- Represent hand-maintained code/tests and intentional orphans explicitly.
- Add explicit rename migrations and reviewed removal tombstones.
- Keep the inventory lock generated and non-authoritative; changing source inputs
  without regenerating it fails the assertion.
- Generate the protected expected-managed assertion from base/history provenance;
  prohibit debt-clearing ownership demotions.
- Port the useful architecture completeness work from PR #1969 without the epoch
  stamp.
- Exclude build-generated files such as `_version.py` by ownership/source rules,
  not environment-specific waivers.
- Add collision detection for flattened metadata names and duplicate leaves.
- Apply one protected `PathPolicy` to every managed read/write role and emit typed
  diagnostics for absolute paths, escapes, symlinks, and special files.
- Inventory current tracked in-repository symlink aliases in PDD and pdd_cloud and
  add protected `RepositoryAlias` records without changing logical unit identity.
- Replace ambiguous language spelling/extension inference with stable
  `LanguageSpec.language_id`, repair duplicate aliases, and bind the registry
  digest to the manifest.

Tests:

- Flat, path-qualified, nested `.pddrc`, worktree, duplicate leaf, architecture
  override, missing prompt, missing code, rename, and deletion.
- Every protected language registry row across every applicable output role,
  including extension collisions, duplicate aliases, source/wheel parity, and
  explicit disambiguation.
- Approved tracked aliases, candidate retarget, dangling/cycle, canonical target
  replacement, descriptor-time swap, and source/wheel identity parity.
- Source checkout and built/installed wheel produce identical manifests.
- PDD repository inventory count is deterministic and every exclusion has a
  structured reason.
- Base-to-head whole-unit deletion and config retarget to same-content paths are
  detected.
- An independent `git ls-files` plus base-tree partition accounts for every tracked
  path as managed artifact, validated artifact, configuration/policy, explicit
  exclusion, or unrelated human-owned path. Compare this partition to resolver
  output so resolver and generated lock cannot share an omission.

Exit gate:

- `managed + human_owned + removed + invalid == all discovered candidates`
  in all supported invocation environments, and the independent Git-tree partition
  has no unaccounted path; no silent omissions or debt-clearing ownership demotions.

### PR 2: Canonical includes, graph, and hashing

Issues: #881, #1807, #1930

Tasks:

- Extract/reuse the preprocessing include parser as a structured API.
- Replace include regexes in sync ordering, fingerprints, update scope guards,
  architecture validation, and CI detection.
- Build the typed deterministic multigraph with source attribution, edge-specific
  reverse propagation, and SCC policy.
- Make prompt composite hashing consume the graph result.
- Preserve stored include identities when preprocessing removes source tags.
- Add hash schema support for multiple tests/examples.
- Include manifest, config, ownership, graph declarations, dependency snapshots,
  and cached external expansion inputs in baseline/evidence closure.
- Include artifact type, normalized Git mode, and protected permission policy in
  snapshots, hashes/comparisons, baseline, and evidence closure.

Tests:

- Every supported include syntax, transitive closure, cycle, missing include,
  outside-root include, changed dependency, stripped tag, and deterministic order.
- Golden parity against current valid fingerprints and pdd_cloud include-bearing
  units.

Exit gate:

- Exactly one include parser and one composite prompt hash builder remain in
  production code. Edge types cannot be traversed without an explicit propagation
  policy.

### PR 3: Pure shared classifier and conformance matrix

Issues: #884, #1931, #1838

Tasks:

- Add snapshot, evidence, verification-profile, obligation, verdict, and stable
  report-schema types.
- Implement the pure classifier and full state matrix.
- Treat candidate-authored evidence as untrusted. Add an attestation-verifier
  boundary; only a trusted validator result can derive effective `VERIFIED`.
- Add profile completeness and effective-semantic-status evaluation. Partial or
  legacy-only safety checks cannot yield overall `VERIFIED`.
- Model missing/corrupt fingerprints and artifacts without fallback success.
- Make Git diff/rename data an explicit optional classifier input.
- Add a compatibility adapter for `sync_determine_operation`.
- Route read-only modes of sync, update, change, CI heal, agentic sync, and global
  scan to the classifier.
- Remove CI-only reclassification branches once parity tests pass.
- Inventory every inline bug-reference comment in `sync_determine_operation.py`;
  link a regression test or file a live issue for each.

Tests:

- Cross-product/property tests over artifact existence, hash changes, baseline
  validity, evidence freshness, ownership, and Git change provenance.
- Conformance test runs every consumer against the same fixture and compares the
  complete verdict, not only a classification string.
- Failure injection proves exceptions become typed `FAILED`, never skips.
- Forged evidence and manifest/config retargets cannot produce `VERIFIED` or
  `CURRENT`.

Exit gate:

- All read-only consumers return byte-identical normalized verdicts for the same
  input. `sync_determine_operation.py` contains no independent hash or drift
  classification logic.

### PR 4: Atomic fingerprint store and schema migration

Issues: #1926

Tasks:

- Add schema and hash-algorithm versions plus the v2 reader/writer.
- Persist artifact type/Git mode and mode-policy version for every role/path.
- Record an ADR for ancestor recovery and metadata-path migration before enabling
  v2-dependent conflict behavior.
- Add per-unit file locks and atomic replace with flush/fsync semantics.
- Reject null required hashes and identity/path mismatch.
- Preserve old fingerprints until a successful atomic replacement.
- Add ancestor reference/snapshot support required by conflict resolution.
- Use a collision-safe v2 metadata path. During migration, preserve legacy
  top-level fields or a generated v1 projection for old readers, but keep canonical
  v2 state in a path old writers cannot overwrite.
- Add a protected repository minimum-writer version policy. Trusted automation
  fails closed below it; new checkers detect and block legacy projection writes
  from direct old local binaries.
- Define forward migration and rollback. Do not make v2 authoritative until all
  trusted writers satisfy the minimum version.
- Reject mutable owner/repository slugs and absolute paths in v2 identity schema;
  require the protected repository UUID, stable language ID, and
  repository-relative POSIX paths.
- Make direct writes outside `fingerprint_store.py` fail a static architecture
  test.

Tests:

- Crash before write, partial temp write, replace failure, permission failure,
  concurrent writers, stale lock, nested call, wrong root, malformed JSON, legacy
  migration, old/new writer races, collision migration, rollback, disk exhaustion,
  and v2 UUID/path schema validation.

Exit gate:

- One internal fingerprint writer exists; failed persistence cannot corrupt or
  replace the prior valid fingerprint.

### PR 5: Transactional finalization for every mutator

Issues: #1926, #356, #1836

Tasks:

- Add `FingerprintTransaction`, durable per-operation write-ahead journals,
  aggregate multi-unit state, startup recovery, ordered shared-resource locking,
  compare-and-swap preconditions, and typed finalization failures.
- Route generate, example, auto-deps, update single/all, fix, sync, change,
  metadata sync, CI heal, test generation, architecture sync, server execution,
  agentic entry points, and every other registered mutator through it.
- Add a command capability registry covering every CLI, server, CI, and agentic
  entry point. Each record declares read paths, managed/shared write scopes,
  ownership effects, transaction mode, validation obligations, sandbox policy,
  and whether partial multi-unit commit is allowed.
- Derive the mutator invariant suite from the registry. Add a static/runtime write
  guard in tests so an unregistered entry point or an undeclared managed/shared
  write fails CI. Future commands cannot merge without a capability record.
- Remove or delegate every direct `save_fingerprint` call.
- Tie run reports and evidence to current input/output hashes.
- Prevent success summaries and zero exits when finalization fails.
- Ensure `pdd fix` regenerates/finalizes code when it changes a prompt.

Tests:

- Parametrized post-command invariant for every mutator.
- Registry completeness includes `pdd test`, `sync-architecture`, all command
  aliases, server routes/executors, CI scripts, and agentic subprocess launchers.
- Failure and process death at each transaction stage recover according to the
  durable commit marker without overwriting external edits.
- Mode-only precondition changes conflict; staged install and rollback preserve and
  verify protected executable/permission bits with descriptor `fstat`.
- Multi-unit runs expose committed/pending participants and resume or roll back
  according to their declared aggregate policy.
- Concurrent shared `architecture.json` updates cannot lose either valid change.
- Output-path escapes and symlink-swap races fail without modifying in-repository
  or external bytes; explicit out-of-root exports remain unfinalized.
- Journal tests cover restrictive permissions, disk/quota preflight, bounded
  retention, committed/recovered cleanup, encryption-required refusal, Git/package
  exclusion, and CI artifact/debug-log exclusion.
- Every successful command is a no-op on immediate second execution.

Exit gate:

- No mutating path can bypass transactional finalization, and the property test is
  required CI.

### PR 6: Honest reconcile, baseline, and repository inventory gate

Issues: #1927, #1836

Tasks:

- Make `pdd reconcile` read-only by default with stable human/JSON output.
- Add `--check`, module scoping, affected-only scoping, and strict exit semantics.
- Deprecate `--heal`; do not silently map it to a baseline reset.
- Add explicit `pdd baseline --accept-current --reason` and `--backfill` flows.
- Mark accepted/backfilled units semantic `UNKNOWN` until validation succeeds.
- Run the repository inventory/fingerprint check in nonblocking shadow mode. Do
  not port the 223-unit data baseline or activate a required gate in this PR.

Exit gate:

- A clean source checkout and installed wheel enumerate the same units and produce
  the same shadow report. Baseline reset cannot produce `IN_SYNC` without trusted
  evidence, and no check blocks before the audited baseline exists.

### PR 7: Explicit conflict resolution

Issues: #1929, #883

Tasks:

- Keep the merged protection that preserves fingerprints/run reports on co-edit.
- Persist a structured resolution plan and ancestor provenance.
- Implement `pdd resolve UNIT --prompt-wins`, `--code-wins`, and `--merge`.
- Show prompt-side and derived-side diffs from the last verified ancestor.
- Require explicit confirmation for destructive choices in interactive mode.
- Require a reason flag in non-interactive reviewed automation.
- Run normal validation and transactional finalization after resolution.
- Remove placeholder/stub strategies before command exposure.

Exit gate:

- Four-quadrant tests pass in every consumer; conflict E2E proves both edits and
  ancestor metadata survive unattended automation.

### PR 8: Semantic contract and self-repair

Issues: #1900, #1837, #1839, #928-class regressions

Tasks:

- Parse prompt-declared interfaces into a typed contract.
- Parse or assign stable identifiers to structured behavioral, security,
  operational, story, and policy requirements; build a complete
  `VerificationProfile` and report every unassigned requirement.
- Validate generated code against the prompt contract, not generated-old versus
  generated-new alone.
- Keep legacy surface comparison only when no prompt contract exists.
- Treat that legacy comparison as a safety guard only; it cannot produce overall
  semantic `VERIFIED`.
- Add bounded repair attempts with stable signatures and a real circuit breaker.
- Emit complete expected/actual diagnostics on final failure.
- Preserve unrelated declared symbols during incremental generation.
- Make code-to-prompt update a three-way minimal patch against the last verified
  prompt. Preserve all existing requirement/contract IDs and unrelated text.
  Unstructured or unprovable changes produce a review patch and remain `UNKNOWN`.
- Treat contract validation evidence as part of semantic `VERIFIED`.
- Migrate managed units to complete profiles. Units without complete profiles stay
  `UNKNOWN` and cannot enter enforcement as managed.

Exit gate:

- Additive declared changes pass; undeclared removals/signature changes repair or
  fail honestly; historical false-positive and dropped-feature fixtures pass. No
  incomplete profile or legacy-only comparison yields overall `VERIFIED`, and
  code-to-prompt updates preserve all unrelated requirements byte-for-byte.

### PR 9: Included-doc propagation and affected-unit repair

Issues: #890, #1930, #881

Tasks:

- Compute affected closures using edge-specific propagation rules from the typed
  graph. Do not topologically order test-validation edges as generation edges.
- Permit included-doc edits through update/change scope guards.
- Reject unrelated edits and cross-unit writes outside the plan.
- Re-sync every affected managed unit in topological order.
- Reject include cycles before mutation; condense allowed runtime dependency SCCs
  and validate them as groups.
- Finalize each unit transactionally and retain a durable multi-unit plan.

Exit gate:

- Historical scope-guard regressions #880/#987/#1025/#1054 are permanent E2E
  fixtures; second propagation run is a no-op.

### PR 10: Test ownership and runner alignment

Issues: #890, #1903, #1917

Tasks:

- Add explicit runner adapters (`pytest`, Jest, Vitest, and repository-declared
  adapters) with runner ID, working directory, collection command, execution
  command, config paths, and config digest. Support multiple disjoint runners.
- Prove collection through each runner's own collection mechanism; path inference
  alone is insufficient.
- Distinguish generated/PDD-owned tests from human-owned validation tests.
- Record ownership per artifact with provenance. Legacy tests default to
  human-owned unless an explicit reviewed adoption changes ownership.
- Adopt existing tests only through an explicit reviewed ownership transition.
- Never fork a shadow test outside the runner's collection path.
- Never overwrite human-owned tests.
- Let test churn open a review item/PR rather than corrupting or silently skipping
  validation. Bind evidence to the exact runner command, working directory,
  configuration digest, and collected test IDs.
- Require every test in `validated_artifacts`, regardless of ownership, to be
  collected and executed by a declared runner adapter or carry an exact temporary
  waiver. A runner-config change that drops or reroutes a validation test changes
  the manifest/profile digest and invalidates prior evidence.
- Emit normalized terminal outcomes for expected and collected IDs. Enforce
  pass-only obligation semantics, zero-test failure, fail-closed collection,
  skip/xfail/xpass/deselection/timeout handling, and non-overriding diagnostic
  retries.

Exit gate:

- Every PDD-owned and human-owned validation test is collected and executed by its
  declared real project runner. Human-owned tests remain byte-identical unless
  explicitly adopted, and no runner/config change can silently remove them from
  evidence. Every required test obligation is `PASS`; unresolved xfails, skips,
  deselections, quarantine, collection errors, timeouts, and flaky outcomes are 0.

### PR 11: Ledger and local boundary hooks

Issues: #1928

Tasks:

- Store a deduplicated durable ledger keyed by `SubjectId`, trigger, and current
  artifact hashes.
- Make editor/agent hooks map touched paths to units without LLM/network calls.
- Install, update, and uninstall Git hooks idempotently while preserving existing
  user hooks and honoring `core.hooksPath`/worktrees.
- Classify only commit-touched units under the default fast path.
- Default local policy annotates; optional strict policy blocks.
- Add ledger claim/ack semantics so successful CI/repair clears only entries it
  actually resolved.
- Treat the ledger as an advisory, reconstructable cache. Corruption, loss,
  expiration, rename, or absence can reduce targeting performance but can never
  suppress the full PR/merge/nightly scan. Rebuild it from Git diff plus current
  snapshots and update shared cursors with compare-and-swap.

Exit gate:

- Edit -> hook -> ledger -> targeted repair -> acknowledgement E2E passes in
  under the declared performance budget and leaves unrelated entries intact.

### PR 12: PR, merge, and nightly checks in shadow mode

Issues: #1928, #1836, #1464

Tasks:

- Add a nonblocking shadow PR check that classifies changed/affected units and
  merge-group synthetic commits. Enforcement activates only in PR 14.
- Load enforcement policy and waiver authority from the protected base branch or
  an external control plane, never from the candidate tree alone.
- Run the released/base trusted checker alongside candidate code when the PR
  modifies the classifier, policy loader, schemas, or validation adapters.
- Define the future blocker set now: baseline `DRIFTED`, `UNBASELINED`, `CORRUPT`;
  semantic `UNKNOWN`, `CONFLICT`, `FAILED`; inventory `INVALID`; and any manifest
  removal/retarget lacking a valid migration.
- Define structured waivers bound to subject/verdict/snapshot/manifest digests,
  issuance provenance, affected dependency-closure digest, owner, protected approver
  identity, reason, issue, creation time, and expiry.
- Keep waivers orthogonal to inventory. A managed unit with a waiver remains in
  gross managed and non-`IN_SYNC` counts; it is never reclassified as `WAIVED`.
- Treat ownership, adoption, repository-ID, rename, and removal changes as
  protected policy transitions loaded from the base and requiring CODEOWNERS
  approval.
- Treat verification-profile obligations/requiredness/mappings, validator
  implementations/config, and obligation-bearing test changes as protected
  transitions. Candidate changes cannot weaken the base obligation union or
  certify themselves.
- Re-run the strict check after any bot repair commit.
- Design checks for the final head SHA, current base SHA, and merge-group SHA, not
  an earlier successful head.
- Run a full read-only reconcile after merge and nightly.
- Nightly automation opens/updates a rolling repair PR; it never baseline-resets
  `main` automatically.
- Persist last-success cursors so failed nights do not create time-window gaps.
- Treat cursors as compare-and-swap advisory caches reconstructable from Git; a
  missing/corrupt cursor triggers a safe full scan.
- Define an untrusted-code boundary: classification is read-only; model and test
  execution run in an ephemeral sandbox without production secrets or push token,
  with CPU/time/output/filesystem/network limits. Repair produces a patch artifact.
  A separate narrow trusted applier checks allowed paths and head-SHA CAS before
  applying/pushing, then reclassifies the new head.
- Deploy the evidence trust plane before PR 13:
  - Protected-base/control-plane `AttestationTrustPolicy` loader and verifier.
  - Post-validation signer using dedicated workload identity and no candidate code.
  - Checker-owned bounded framework-observation transport for standard-framework
    adapters, plus an isolated external observation boundary before any
    isolated-black-box adapter is supported.
  - Transparency/audit record store and evidence cache invalidation service.
  - Threshold protected human-review attestation workflow for non-machine-verifiable
    obligations.
  - Rotation, revocation, expiry, replay rejection, outage, and compromise response.
- The signer does not sign sandbox-submitted JSON. It independently authenticates
  the trusted runner/workflow, fetches or recomputes observed hashes and profile/
  manifest/config/runner digests, verifies the check-run base/head/merge-group SHA
  and nonce, and signs only the resulting canonical statement.
- Run staging issuance and verification E2E for machine and threshold-human
  obligations, unknown signer, replay, signer outage, key/root rotation, revocation,
  cached-evidence invalidation, and compromised-signer recovery.

Exit gate:

- Shadow reports cover manual, agent, PDD, hotfix, base-movement, and merge-group
  channels with zero unexplained differences from expected enforcement. Sandbox,
  trusted-applier, stale-head, and policy-tamper tests pass; the evidence trust plane
  passes staging issuance/replay/outage/rotation/revocation/compromise E2E; merge is
  not blocked yet. PR 13 cannot start before this gate.

### PR 13: PDD dogfood baseline and burn-down

Tasks:

- Generate the canonical PDD inventory lock and ownership/waiver assertions. The
  lock is derived output, not an authoritative registry.
- Classify all units before creating a new baseline.
- Build complete verification profiles for every managed unit. Migrate structured
  requirements for every expected-managed unit. Historically human-owned artifacts
  remain separate; do not use ownership demotion or waivers to avoid profile work.
- Divide legacy units into verified, conflict, invalid, and accepted-unknown.
- Repair verified candidates through normal commands.
- Resolve conflicts with review.
- Baseline-reset only units whose current tree is explicitly accepted. Each such
  unit remains semantic `UNKNOWN` and must gain trusted validation evidence before
  enforcement. Expected-managed debt cannot be reclassified as human-owned.
- Commit the baseline in a data-only PR after all implementation PRs are green.
- Do not enable enforcement in the data PR.

Exit gate:

- PDD `main` reports complete inventory and every managed unit is full trusted
  `IN_SYNC`. Gross managed count is non-zero and fixed by the candidate union;
  managed waivers and semantic `UNKNOWN` units are zero. Human-owned/removed
  candidates and managed-to-human transitions are separately enumerated, with zero
  debt-clearing transitions. There are no second-run writes in source and wheel
  environments.

### PR 14: Activate protected enforcement

Tasks:

- Change the protected-base policy from `report` to `enforce` in a separately
  reviewed operational PR after PR 13's baseline and all shadow gates are green.
- Require the PR 0 issue-linked expected-failure count to be 0; all resolved tests
  have had strict xfail markers removed and moved to required lanes.
- Require CODEOWNERS/protected approval for checker policy, waiver authority,
  minimum-writer version, runner adapters, sandbox policy, repository identity,
  expected-managed/ownership/adoption, rename/removal, verification profiles,
  validator implementations/config, obligation-bearing validation tests,
  repository aliases, language registry, and attestation trust/issuer policy.
- Require both the trusted released/base checker and candidate checker during the
  checker transition window.
- Use the two-release checker promotion protocol in section 8.2; combine old/new
  verdicts conservatively so neither checker can downgrade the other's blocker.
- Gate the current base/head merge result or merge-group SHA and disable unaudited
  admin bypass for the sync check.
- Enable same-repository repair only through sandbox -> patch artifact -> trusted
  applier -> head-SHA CAS -> recheck. Fork repair remains non-mutating and blocked.
- Verify post-merge and nightly full scans cannot be narrowed by ledger/cursor loss.

Exit gate:

- Manual, agent, PDD, hotfix, base-movement, and merge-queue channels cannot land a
  managed non-`IN_SYNC` unit without a valid protected waiver. Policy-tamper and
  forged-evidence PRs are blocked by the trusted checker.

### PR 15: pdd_cloud migration and upstream reconciler retirement

Tasks:

- Pin a released PDD version containing PRs 1-14.
- Compare upstream results with pdd_cloud's vendored prompt reconciler in report
  mode across candidate IDs, unit identity, dependencies, affected closures,
  artifact paths, hashes, and verdicts; differences are failures to investigate,
  not values to average.
- Inventory all pdd_cloud units across nested `.pddrc` and architecture roots.
- Reclassify the historical 377/788 stale population into repair, conflict,
  invalid, waived, and accepted-unknown buckets.
- Burn down in bounded, reviewable PRs by project/subtree.
- Retire every vendored sync-semantic component only after parity is zero and the
  upstream command meets runner performance/reliability needs: repository/unit
  identity, candidate discovery, include parsing, dependency graph, reverse
  affected closure, path resolution, hashing, and classification. pdd_cloud may
  retain orchestration/scheduling only and consumes the upstream manifest, graph,
  closure, and verdict JSON contracts.
- Run one staging nightly, one same-repo repair PR, one manual hotfix PR, and one
  conflict canary before enabling enforcement broadly.
- Keep all repair/test/model execution inside the untrusted-code sandbox and use a
  separate narrow applier credential.
- Mirror the PDD sequence: shadow report, audited data-only baseline, then a
  separately protected enforcement activation. Accepted-unknown units must be
  trusted-verified before activation; ownership demotion and managed waivers are
  not baseline burn-down strategies.

Exit gate:

- pdd_cloud has complete candidate-union inventory, every managed unit trusted
  `IN_SYNC`, zero managed waivers and non-`IN_SYNC` managed states, no vendored
  identity/discovery/include/graph/closure/path/hash/classifier semantics, and
  consecutive full nightly no-op reports.

## 7. End-to-end validation program

### 7.1 Test levels

| Level | Purpose | Network/LLM |
| --- | --- | --- |
| Unit | Pure identity, include, hash, classifier, planner, schema | none |
| Component | Transaction failures, command adapters, ledger, hooks | none |
| Lifecycle fixture | Real Git repo and CLI subprocesses across all boundaries | none or fake model |
| Package | Built wheel in clean environment | none |
| Staging | Real CI bot, branch, check, repair PR, and selected LLM path | bounded |
| Consumer canary | Real pdd_cloud subtree and nightly runner | bounded |

Tests labeled E2E must cross at least one real process/repository boundary and
must exercise the live mutation path. Calling five reporting wrappers that all
invoke one helper is a conformance test, not lifecycle E2E.

### 7.2 Required lifecycle matrix

Each row runs through edit, Git commit, PR classification, repair or resolution,
transactional finalization, merge gate, post-merge check, and nightly no-op.

| Change source | Expected behavior |
| --- | --- |
| Included doc only | all affected units found and repaired in graph order |
| Prompt only | generated artifacts updated, contracts/tests current |
| Code only | prompt updated or PR blocked; no blind stamp |
| Example only | ownership-aware validation/update |
| Test only | real runner collects it; ownership preserved |
| Prompt + code | conflict, no unattended writes |
| Prompt + test | conflict when test is derived; ownership-aware otherwise |
| Code + validating test | changed test cannot solely certify changed code; protected profile/test policy applies |
| Prompt + code + test | conflict/resolution plus complete independent obligation evidence |
| Rename/move | identity preserved or explicit migration required |
| Required artifact deletion | failure/repair, never current |
| Chmod-only/executable-bit drift | baseline drift detected even when bytes match |
| Concurrent mode change during transaction | CAS/fstat blocks overwrite and preserves external mode |
| Crash recovery with executable artifact | content and protected mode restored/committed together |
| Missing fingerprint | unbaselined, explicit verified rebuild/baseline required |
| Corrupt fingerprint | corrupt failure, old bytes preserved |
| Interrupted mutation | rollback and non-zero exit |
| Process death after each journal phase | startup recovery completes or restores according to durable marker |
| Read-only check sees incomplete journal | reports `RECOVERY_REQUIRED`, exit 1, and performs no writes |
| Two concurrent syncs | one serialized result, no lost update |
| Concurrent shared architecture writes | both valid patches survive or one becomes a conflict |
| Nested `.pddrc` | correct project root and metadata location |
| Duplicate basename | path-qualified identity, no guessed target |
| Approved tracked prompt alias | logical identity stable; canonical target hashed and safely used |
| Candidate alias retarget/dangling/cycle | protected alias policy blocks without writes |
| Alias descriptor-time swap | no-follow canonical-target revalidation blocks commit |
| Every language/role registry case | source and wheel resolve the same stable language ID and paths |
| Ambiguous language alias/extension | inventory `INVALID`; no first-row inference |
| Whole-unit deletion | base manifest/tombstone check blocks silent disappearance |
| Config retarget to identical bytes | manifest drift detected despite equal content hashes |
| Managed-to-human demotion during debt | protected expected-managed policy blocks it |
| Required obligation deleted/remapped | base/candidate profile union remains blocking |
| Validator weakened with its tests | released validator cannot self-certify replacement |
| Human-owned test | validated but never overwritten |
| Multiple test runners | each owned test is collected by its declared adapter; no shadow test |
| Bot repair commit | final head SHA rechecked before merge |
| Stale bot head/rebase | compare-and-swap rejects push and recomputes verdict |
| Merge-group synthetic commit | trusted check binds result to merge-group and base SHAs |
| Forged fingerprint/evidence | trusted validator ignores it and reports `UNKNOWN`/failure |
| Unknown/replayed/expired attestation | trust policy rejects it; obligation remains unverified |
| Attestation key/root rotation | overlap accepts intended issuers only; retired key is rejected |
| Compromised signer revocation | cached evidence invalidated and obligations rerun before `VERIFIED` |
| PR weakens checker policy | protected-base checker and policy still enforce |
| Old/new writer race | canonical v2 state survives; mixed-version check fails closed |
| Shallow history ancestor lookup | bounded fetch recovers ancestor or resolution stops safely |
| Sandbox escape/resource abuse | no secrets/push token exposed; limits terminate the job |
| Nested config parent include within repo | allowed and hashed under repository boundary |
| Absolute/symlink include escape | blocked unless protected external-root policy applies |
| Protected external include | read-only mounted snapshot is bound to evidence |
| Absolute artifact output in config | managed resolution is `INVALID`; no external write |
| Artifact symlink-swap race | descriptor-relative revalidation blocks commit and preserves bytes |
| Artifact FIFO/device/socket path | path policy rejects before execution |
| WAL disk/quota/retention failure | no destination write; secure state retained or cleaned per policy |
| Required test skipped/xfail/deselected | obligation is not verified; gate fails after activation |
| Zero tests/collection error/timeout | normalized failure; retry cannot convert it to trusted pass |
| Failed nightly | next run resumes from last success without a window gap |

### 7.3 Historical regression fixtures

Keep minimal, checked-in reproductions for:

- Null/partial fingerprints and repeated heal loops (#437/#1305 class).
- Wrong subproject root (#1211/#1290 class).
- Rich include syntax missed by fingerprints (#881).
- Included-doc scope guard reverting legitimate edits
  (#880/#987/#1025/#1054).
- Public-surface false positive and silent feature loss (#1900/#928 class).
- Input-too-large or detector failure reported as no work (#1838).
- Test written outside the real runner path (#1903/pdd_cloud#3024).
- Prompt and code co-edit with preserved ancestor (#1929).
- Manual code hotfix followed by stale-prompt regeneration risk
  (pdd_cloud#2252/#2834 class).

### 7.4 Required CI lanes

1. Fast pure-core tests on every PR.
2. Classifier conformance matrix on every sync-related PR.
3. Mutator finalization property suite on every mutator-related PR.
4. Lifecycle fixture suite on every sync/CI/hook/identity change.
5. Built-wheel manifest and reconcile parity on every release candidate.
6. Full repository strict reconcile after unit tests. It is shadow-only before PR
   14 and required before a PR is mergeable after enforcement activation.
7. Staging canary before enabling a new repair policy in production.
8. At least one journal-recovery, forged-evidence, stale-head, and sandbox failure
   injection canary per release candidate.

Path filters may add fast-fail lanes, but the full suite remains part of normal CI;
path filters must never be the only protection against shared-core regressions.

Lifecycle tests use stable command/check semantics: exit `0` means the trusted
checked snapshot is clean or a requested repair committed successfully; exit `1`
means an unresolved/blocked/validation/transaction condition; exit `2` is reserved
for CLI usage/configuration errors. Every failure-injection row asserts the exact
exit code, pre-existing destination bytes, durable journal recovery state, complete
verdict, and the base/head/merge-group SHA recorded on the check run. A test cannot
pass by asserting only log text.

## 8. Rollout and migration controls

### 8.1 Feature flags

Use repository configuration with explicit defaults:

```yaml
sync:
  classifier_v2: report
  transaction_v2: off
  conflict_policy: block
  boundary_mode: report
  nightly_mode: report
  baseline_accept_requires_reason: true
```

The boundary state machine is `off -> report -> repair -> enforce`. `repair` means
the sandbox may propose a patch but the check remains nonblocking; `enforce` means
the final trusted verdict blocks and may also use the approved repair pipeline.
Rollback moves one state backward and never rewrites baselines. Classifier and
transaction flags have their own `off -> report -> enforce` transitions. Move one
state at a time after its exit gate; do not combine classifier, transaction,
baseline, repair, and enforcement activation.

### 8.2 Compatibility

- Read legacy fingerprints throughout one deprecation window.
- Introduce `schema_version` and `hash_algorithm_version` before v2-dependent
  behavior. Use a collision-safe canonical v2 path plus a generated legacy
  projection during the mixed-version window.
- Enforce a protected minimum writer version for trusted automation. Old direct
  local writers cannot overwrite canonical v2 state; any legacy projection change
  is detected and blocked by the new checker.
- Make v2 authoritative only after mixed-version source/wheel/rollback tests pass
  and all trusted writers meet the minimum.
- Keep existing CLI options with deprecation warnings where behavior is safe.
- Make unsafe `--heal` fail with actionable migration text before removal.
- Version the JSON report schema and provide a compatibility projection for CI
  consumers during migration.
- Package all runtime modules and schemas in the wheel; package tests verify it.
- Document forward migration, emergency rollback, and how canonical v2 state
  regenerates the legacy projection after rollback.

Checker/schema evolution uses a two-release promotion protocol:

1. **Compatibility release:** merge disabled, backward-compatible parsing and
   reporting support while the old trusted checker can still evaluate the tree.
   Publish and attest checker `N+1`.
2. **Trust transition:** update protected control-plane/base policy to trust both
   `N` and `N+1`. Run both on all candidate and merge-group snapshots; combine
   verdicts by the most conservative result. `UNSUPPORTED` is not success.
3. **Behavior activation:** in a later PR, activate the new schema/classification
   only after both trusted checkers understand the transition representation.
4. **Retirement:** after the compatibility window and rollback test, remove `N`
   from protected policy in another reviewed control change.

An emergency security checker upgrade uses a pre-authorized break-glass control
outside the candidate branch, requires two protected approvers, emits an immutable
audit record, and may only preserve or strengthen blockers. It cannot waive unit
drift or accept candidate-authored evidence.

### 8.3 Baseline policy

Baseline resets require:

- Exact unit scope.
- Human-readable reason.
- Actor and timestamp.
- Current Git commit or dirty-tree declaration.
- `semantic_status=UNKNOWN` unless validation runs in the same transaction.
- A baseline-reset unit cannot pass protected enforcement while `UNKNOWN` unless a
  valid waiver is bound to that exact subject snapshot and manifest digest.
- Review in a normal PR.

Repository-wide baseline reset is prohibited except for the one audited migration
PR per repository. That PR must contain only baseline/waiver data and its audit
report.

### 8.4 Waiver policy

Every waiver contains:

```json
{
  "subject": {"kind": "unit|candidate", "id": "..."},
  "status": "DRIFTED|UNBASELINED|CORRUPT|UNKNOWN|CONFLICT|FAILED|INVALID",
  "owner": "team-or-user",
  "approved_by": "protected-reviewer",
  "reason": "...",
  "issue": "https://...",
  "verdict_digest": "...",
  "snapshot_digest": "...",
  "manifest_digest": "...",
  "dependency_closure_digest": "...",
  "issued_from_base_sha": "...",
  "created_at": "...",
  "expires_at": "..."
}
```

Expired, malformed, overbroad, and stale waivers fail CI. A waiver suppresses the
merge block only for its exact bound snapshot/verdict. Policy and waiver authority
come from the protected base/control plane, and changes require protected approval.
Reports and nightly telemetry continue to show the condition.

`issued_from_base_sha` is audit provenance, not an equality condition that expires
on every unrelated merge. Validity is bound to the immutable subject snapshot,
manifest, verdict, and affected dependency closure. Unrelated base movement keeps
the waiver valid; a change in the unit or affected closure invalidates it. Both
cases have merge-group lifecycle tests.

Waivers never change intrinsic inventory status or reduce the gross managed
denominator. Reports show `managed_total`, `managed_in_sync`, `managed_waived`, and
each non-managed inventory bucket separately. Waivers are an incident mechanism,
not migration debt: epic closure and initial enforcement activation require
`managed_waived=0` in PDD and pdd_cloud.

### 8.5 Attestation trust policy

A protected-base/control-plane `AttestationTrustPolicy` defines which evidence can
be trusted. Its digest is part of every effective evidence decision. It specifies:

- Accepted issuer roots, keyless OIDC issuers/subjects or key IDs, algorithms, and
  threshold requirements for protected human-review attestations.
- Exact repository UUID, workflow identity/version, protected workflow source,
  environment, ref class, validator/checker release, and permitted claim values.
- Binding to a nonce/check-run ID, obligation/profile digest, complete input and
  dependency closure, runner/config digest, base/head/merge-group SHA, result, and
  issuance/expiry window to prevent cross-repository or cross-snapshot replay.
- Transparency/audit-log requirements and immutable links from the check result.
- Overlapping key/root rotation, revocation lists, maximum validity, and fail-closed
  behavior for unknown, expired, malformed, replayed, or revoked attestations.
- Compromise response: revoke the issuer/key/workflow identity, invalidate affected
  cached evidence, rotate through protected policy, and re-run obligations before
  any unit can return to `VERIFIED`.

Signing occurs only in the trusted post-validation service. Sandboxed candidate
code, model jobs, repair jobs, and test runners never receive signing keys/tokens.
Keyless claims are checked against the protected workflow and repository identity,
not merely a CI provider name.

## 9. Observability and operational ownership

### 9.1 Stable report fields

Every command and automation path emits:

- Report schema version and PDD version.
- Project root and manifest digest.
- Total candidates and every inventory bucket.
- Baseline and semantic status counts.
- Changed/affected artifacts and provenance.
- Recommended and attempted action.
- Transaction ID and finalization result.
- Validation/evidence digest.
- Waiver status.
- Cost, duration, and bounded-retry counts for repair paths.
- Explicit skipped/degraded reasons.

### 9.2 Metrics and service objectives

- Inventory coverage: 100% classified.
- Silent omissions: 0.
- Managed units on protected `main`: 100% satisfy the complete trusted `IN_SYNC`
  predicate at program completion. Gross managed, managed-in-sync, and
  managed-waived counts are reported separately; initial activation and epic
  closure require managed-waived and semantic `UNKNOWN` counts of 0.
- Drift dwell time: resolved or surfaced as blocking conflict by the next PR check;
  nightly is the fallback and must remain under 24 hours.
- Finalization success for successful mutators: 100%.
- Second-run writes after successful repair: 0.
- False-success incidents: 0.
- Automatic conflict winner selection: 0.
- Candidate-authored evidence accepted as trusted: 0.
- Repair jobs with production secrets or push credentials: 0.
- Hook changed-unit classification target: under 2 seconds for a five-file commit
  in the reference repository.
- Full 500-unit read-only reconcile target: recorded and enforced after a baseline
  benchmark establishes a realistic threshold.

### 9.3 Ownership

Assign one named owner before each workstream starts:

| Area | Required owner responsibility |
| --- | --- |
| Sync core | identity, graph, hashing, classifier API |
| Persistence | schema, lock, transaction, rollback |
| Repair | planner, sync/update/fix/resolve semantics |
| CI integration | hooks, ledger, PR/merge/nightly checks |
| Evidence trust service | policy loader, signer/verifier, nonce, transparency, human attestations, rotation/revocation |
| PDD dogfood | inventory and baseline burn-down |
| pdd_cloud rollout | consumer audit, canaries, vendored retirement |

The tracking epic records owner, PR, state, and exit-gate evidence for every row.

## 10. Failure handling and rollback

- Core classifier rollout starts in report mode and writes no metadata.
- Transaction rollout retains pre-state snapshots and can be disabled per command.
- CI enforcement can return to report mode without changing stored baselines.
- Durable journals are recovered before any new mutation; a corrupt journal stops
  mutation and preserves destination bytes for manual recovery.
- Bot repair never force-pushes and never edits a conflict.
- A failed post-merge/nightly run opens or updates an incident/repair PR; it does
  not stamp `main` green.
- Schema migration retains the prior file until atomic replacement succeeds.
- Any increase in false success, data loss, or unit omission is a stop-the-line
  rollback condition.
- Any consumer difference between vendored and upstream classification blocks
  vendored retirement until explained by an approved behavior change.
- Policy/waiver/checker changes in a candidate PR are evaluated by protected-base
  policy and a trusted released checker, so rollback cannot be authorized by the
  change under test.

## 11. Definition of Done

The global predicate described below is not currently achieved. In particular,
standard-framework observations do not satisfy a Byzantine-resistant
isolated-black-box claim, the external SUT adapter does not yet exist, and the
release/nightly evidence gates remain outstanding.

The global sync epic may close only when all conditions below hold with attached
commands, commit SHAs, and reports.

1. One canonical unit resolver, include parser, hash builder, classifier,
   verification-profile evaluator, fingerprint writer, and command capability
   registry remain in production code.
2. `sync_determine_operation.py` is a thin compatibility/workflow adapter and no
   longer owns drift classification or persistence.
3. The base/head candidate union includes configured roots, prompts, architecture,
   fingerprints, ownership, and unmatched tracked artifacts; every candidate is
   managed, human-owned, removed, or invalid in source and installed-wheel
   environments; waiver state is reported separately. An independent Git base/head
   tree partition has no unaccounted tracked path.
   Protected in-repository aliases preserve logical identity without permitting
   retarget/escape, and every language-registry row/output role passes exhaustive
   source/wheel conformance with no ambiguous mapping.
4. Every successful mutating command finalizes through a crash-durable journal,
   ordered shared-resource locks, and compare-and-swap preconditions, and is a
   no-op on immediate rerun.
5. `pdd reconcile` is read-only unless an explicit baseline command is invoked.
6. Baseline resets remain semantic `UNKNOWN` until current evidence verifies them.
7. Prompt/code co-edits cannot be auto-healed and retain recoverable ancestry.
8. Prompt, code, docs, examples, and tests follow the canonical affected graph and
   ownership model, and every managed read/write satisfies protected `PathPolicy`
   including descriptor-relative no-follow commit checks. Content, artifact type,
   normalized Git mode, and protected permission bits remain synchronized through
   classification, commit, rollback, recovery, Git, and source/wheel execution.
9. Declared runner adapters collect and execute every PDD-owned and human-owned
   validation test in `validated_artifacts`; human-owned tests are never
   overwritten without an explicit protected adoption transition.
   Every managed unit has a complete protected verification profile, and every
   required obligation has current trusted evidence; no validator/profile/test
   change certifies itself.
10. A trusted released/base checker and protected-base policy classify the current
    base/head result and merge-group SHA. Every managed unit must satisfy the full
    trusted `IN_SYNC` predicate; any temporary operational exception requires an
    active waiver bound to its verdict, snapshot, manifest, affected closure,
    issuance provenance, protected approver, and expiry.
    Trusted semantic evidence satisfies the protected attestation issuer/subject,
    replay, validity, rotation, revocation, and transparency policy.
11. Post-merge and nightly checks are read-only verifiers and converge to no-op.
12. The lifecycle matrix passes in fixture repos, built wheels, PDD staging, and a
    pdd_cloud canary. Unresolved issue-linked strict xfails, unapproved required-lane
    skips/xfails/deselections/quarantines, collection errors, timeouts, and flaky
    obligation outcomes are 0.
13. PDD and pdd_cloud `main` report complete candidate-union inventory, all managed
    units trusted `IN_SYNC`, `managed_waived=0`, and zero managed `DRIFTED`,
    `UNBASELINED`, `CORRUPT`, `UNKNOWN`, `CONFLICT`, `FAILED`, or `INVALID` states.
    Protected expected-managed totals have not been reduced through debt-clearing
    ownership transitions.
14. pdd_cloud no longer vendors sync identity, candidate discovery, include
    parsing, graph construction, affected closure, path resolution, hashing, or
    classification logic; it retains orchestration only.
15. Seven consecutive full nightly runs in both repositories are no-ops except for
    deliberately injected canary drift, which is detected and resolved as expected;
    ledger/cursor deletion during the window does not narrow the scan.
16. Issue #1932 child issues are closed only with links to the tests and production
    paths that satisfy their acceptance criteria.

## 12. Immediate next actions

1. Reopen/reframe issue #1932 and attach this document.
2. Mark PR #1954 as the reporting/conflict-preservation milestone.
3. Keep PR #1969 blocked; split inventory, implementation, data baseline, and CI
   enforcement into separate PRs.
4. Land PR 0 strict issue-linked expected failures in the nonblocking acceptance
   lane before changing the resolver again.
5. Implement PR 1 and PR 2 before any new repository-wide stamp.
6. Complete the shared classifier and transaction foundations before enabling
   auto-repair or merge enforcement.
7. Run boundary checks in shadow mode, land the audited data-only PDD baseline,
   then activate protected enforcement in a separate operational PR.
8. Maintain the pdd_cloud prompt-side reconciler in report/repair scope until the
   released upstream replacement passes parity and canary gates.
