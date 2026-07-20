# Global Sync Resolution Plan

Status: implementation in progress; acceptance gates remain red
Last updated: 2026-07-19
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

### Historical critical-path snapshot (2026-07-18)

This retained diagnostic snapshot is not a release prerequisite. The current
ledger-generation promotion and Gate 2 blocker are recorded in the 2026-07-19
live rebaseline below. Protected PDD profiles
demand only the `pytest` validator, so undemanded Vitest, Jest, and Playwright
work is frozen with PR #1995 and does not block gates 1-6. It does not authorize
a release, merge #1995, or claim global certification; the ten-step sequence
below remains controlling.

#### Authoritative execution snapshot

The following snapshot supersedes the historical attempt details retained below.
It distinguishes evidence collection from hosted acceptance and from merge or
release state.

| Verification boundary | Exact evidence | State |
| --- | --- | --- |
| Locally validated | PR #1995 Stage A correction [`d334266680881cbda59de4ecd4df967c92159fa7`](https://github.com/promptdriven/pdd/commit/d334266680881cbda59de4ecd4df967c92159fa7) is the two-commit fast-forward successor to reviewed diagnostic `4bba47d60e03093707962712334e7340734a84a4`. The strict production native compile failed on the base with `-Werror=unused-function` and passed after the test-only helper moved under `PDD_TEST_EXEC_PROBE`; the strict probe compile also passed. Four affected fixed-reason, authority, and wheel source-parity tests passed. The new Linux-only regression skipped locally and remains hosted-required. The prior Stage A composite passed 487 focused tests with 48 platform skips and 216 protected metadata/package/architecture tests. | bounded correction locally green; Linux execution hosted-required |
| Independently reviewed | Sol HIGH approved exact correction `d334266680881cbda59de4ecd4df967c92159fa7` with no findings after reviewing only commits `20401071697f8bdf5206d381142532e182b409eb` and `d334266680881cbda59de4ecd4df967c92159fa7`. Production sealing logic, fixed enums, N-API error behavior, probe behavior, and wheel/source parity are unchanged. Review evidence digest `6b0f634f49e7aacde102e1d20a1ff3dc8c4c0f67a2e1f74c6eeb0da14414c1d5` binds corrected native source `534d3afd44ceb4e578fc7ca2b6dea82d000a191104876efc65b54137f7196ace`, producer `c3e77f4fa3605c269dcc7c8299dca768c9e975d267cedf2af5422ab5d48164fc`, termination verifier `133d5be5c9035a7f45c96e47666280b59c1e34f088862a64c3d39dd613026ed1`, observation verifier `a9d097950c718edd0834e3c69bfaf948627e0498ab5de56858e9196525dba0d2`, Stage A verifier `31575aafcefa94d789fe412c225c024454c5463101bd334587674c7a789e9add`, Package verifier `b6e923061ea73ed46af4d03e497aa9ed4e538129f85b1c0eabc1bd47d45e177e`, Package provenance `12bc5a1950d9f2768ecb313cb32204e550a71799db4a747f700d2238921481d5`, and reviewed base `39776aa9bb027c638812a01b8dabbe03cab92f64`. | exact bounded correction approved |
| Hosted evidence collected | Exact-head [run 29658808029](https://github.com/promptdriven/pdd/actions/runs/29658808029) bound reviewed head `d334266680881cbda59de4ecd4df967c92159fa7`, reviewed base, review evidence, producer, verifiers, corrected native source, and pinned toolchains. Source [job 88117749946](https://github.com/promptdriven/pdd/actions/runs/29658808029/job/88117749946) verified artifact [`8433732767`](https://github.com/promptdriven/pdd/actions/runs/29658808029/artifacts/8433732767), Stage A digest `5972d8ae01213e069b886e16cfac65301a609c0aaa08e8844c7365fcd47a9000`. Package attempt 1 timed out all seven mandatory Playwright cases before Vitest, while the identical prior lane had passed; the same-SHA bounded rerun [job 88118943320](https://github.com/promptdriven/pdd/actions/runs/29658808029/job/88118943320) passed all seven real-browser cases and verified installed-wheel artifact [`8433907757`](https://github.com/promptdriven/pdd/actions/runs/29658808029/artifacts/8433907757), Stage A digest `894a56e3333012fec433507235309c8a60b641a8a25556ea9e066ff6bb743bb6`. Both fail-closed verifiers accepted `PDD_VITEST_SEAL_DESCRIPTOR_TABLE_OPEN` at `reporter-authority-seal` in the `vitest-coordinator`, with matching progress frames, no result frame, zero cgroup event deltas, and `cause_red_status: pending`. The wheel artifact binds package attestation `be7e0711f93a54c60dc9b8dfc98c00de14bce1e8e4f541d62649fd7355bd044c`, wheel `be1c1379608f7390dbd2be3cb1cacbf482446942fb7d84d58fa785e9eae6d717`, and installed runner `c3e77f4fa3605c269dcc7c8299dca768c9e975d267cedf2af5422ab5d48164fc`. CodeQL, Story Regression, Public CLI Regression, and Repo Bloat Docker E2E passed. Unit and Package remain intentionally red after verifier acceptance because the candidate test still fails. | Stage A reconciled; one cause-specific RED is permitted |
| Artifact predicates | Both hosted observation verifiers accepted their exact-lane artifacts. Independent replay of the downloaded bytes, after restoring archive-normalized mode `0600` and protected parent mode `0700`, reproduced both accepts and both exact termination-verifier rejections. Both traces are identical through `reporter-addon-load-succeeded`, `reporter-authority-seal-start`, `reporter-authority-seal-failed`, `coordinator-explicit-exit`, and `coordinator-exit`; supervisor exit is `0` and no result frame exists. | Stage A0 closed; evidence is explicitly non-causal |
| Diagnostic disposition | Freeze remote PR #1995 at `d334266680881cbda59de4ecd4df967c92159fa7`; do not push or merge another diagnostic correction. Local native correction branch head `6ee03883aa39bf1a4eb822bfc259c9c23f92b80a` and GREEN-transition head `6c02fb5ff80c64956ff90792e7873fda56aa2de0` are preserved as unpushed evidence only. Sol found one native coverage gap, then the correction added cleanup and close-precedence coverage but remained Linux-unhosted. Sol found two blocking defects in the separate GREEN transition: four obsolete Stage A tests still fail and push runs can check out the stale reviewed PR SHA. These findings will not be corrected on #1995 because no protected PDD profile demands Vitest. | frozen diagnostic evidence; not on gates 1-6 critical path |
| Merged to protected `main` | Docs-gate [PR #2213](https://github.com/promptdriven/pdd/pull/2213) and ownership prerequisite [PR #2216](https://github.com/promptdriven/pdd/pull/2216) remain historical evidence; #2216 merged as [`c712cbb7e08c157757a238cb8e49d65a9a3a2239`](https://github.com/promptdriven/pdd/commit/c712cbb7e08c157757a238cb8e49d65a9a3a2239) and preauthorized only the four exact Gate 1 paths. Gate 1 [PR #2214](https://github.com/promptdriven/pdd/pull/2214) reviewed exact head [`6301d6c613199604702c2c3242fc8b837960d586`](https://github.com/promptdriven/pdd/commit/6301d6c613199604702c2c3242fc8b837960d586), passed [Unit run 29674097485](https://github.com/promptdriven/pdd/actions/runs/29674097485) ([job 88158086892](https://github.com/promptdriven/pdd/actions/runs/29674097485/job/88158086892)), [Package job 88158086891](https://github.com/promptdriven/pdd/actions/runs/29674097485/job/88158086891), [CodeQL run 29674096680](https://github.com/promptdriven/pdd/actions/runs/29674096680), [heal run 29674097086](https://github.com/promptdriven/pdd/actions/runs/29674097086), and [auto-heal 88158092713](https://github.com/promptdriven/pdd/runs/88158092713), then merged as [`63bf4dd789d65a9cf4b08f5b39886d0cdda5e0ee`](https://github.com/promptdriven/pdd/commit/63bf4dd789d65a9cf4b08f5b39886d0cdda5e0ee). The immutable profile evidence source remains `2cacc91f90759ff45f1ad976da3b773e1a5f07a5`; its registry is unchanged at digest `56ea5d189034c9d85e91c86348689eb18c4c34fa67406258f78f0ae3330eaeb6`, as required by `git diff --quiet 2cacc91f..63bf4dd -- .pdd/verification-profiles.json`. Neither source nor live main is an ancestor of diagnostic head `d334266680881cbda59de4ecd4df967c92159fa7`; #1995 remains frozen and is not a release vehicle. | Gate 1 evidence hosted-green and merged; global gates remain 0/10, with no checker release or certificate |
| Released checker | No protected reviewed checker release or pinned wheel digest exists. | pending |
| Globally certified | No protected merge-group certificate or seven-night streak exists. | pending |

#### Ordered unblock from current evidence

1. Stage A0 is closed on exact reviewed head `08cc80e0ab752414eb1527a1652181ef9b4e2679`:
   both hosted observation verifiers accepted and both termination verifiers
   rejected the artifacts as cause proof. The overall Unit and Package failures
   are the preserved candidate baseline and do not close Stage A.
2. A separately reviewed Stage A diagnostic now reports a trusted native
   fixed-enum reason for `sealResultAuthority` failure. Do not parse
   `error.message`, infer cause from exit `0`, or treat the broad authority-seal
   boundary as the behavioral fix. The trusted native operation has multiple
   fail-closed paths, so the reason must distinguish at least argument/identity,
   procfs seal, descriptor-table open/read/inspection/close, descriptor
   `CLOEXEC` set/verification, alias-not-found, and response failures. This is
   locally complete on `4bba47d60e03093707962712334e7340734a84a4` but has no
   hosted Stage A artifact.
3. Exact-head run `29658808029` closed Stage A in both protected lanes on
   `d334266680881cbda59de4ecd4df967c92159fa7`. Both verifiers accepted
   `PDD_VITEST_SEAL_DESCRIPTOR_TABLE_OPEN` at `reporter-authority-seal` in the
   `vitest-coordinator`, with no result frame and matching bound evidence. The
   same-SHA Package rerun passed all seven mandatory real-browser cases before
   producing the installed-wheel Stage A artifact.
4. Freeze #1995 at remote head `d334266680881cbda59de4ecd4df967c92159fa7`.
   Preserve the local unpushed correction branches and Sol findings as evidence,
   but do not integrate, push, host, or merge them. No protected PDD profile
   demands Vitest, Jest, or Playwright. pdd_cloud has no protected verification
   profile registry yet, so its future adapter demand is unknown and must be
   generated at migration time rather than assumed.
5. Gate 1 PR #2214 merged its reviewed adapter-demand artifact and extraction
   manifest as `63bf4dd789d65a9cf4b08f5b39886d0cdda5e0ee`. Its former
   ledger-generator/drift-check blocker is superseded by #2219's protected-main
   merge. The canonical next blocker is
   `gate2-standalone-checker-package-boundary`: under 24 hours, open the
   standalone non-`pdd` checker extraction manifest/package-boundary PR; OCI and
   protected pin wiring follow strictly. Any early certificate is explicitly
   narrower and cannot satisfy the final global predicate until all managed
   units and both repositories meet the gate-10 denominator.

#### Historical attempt ledger

The table below is retained for evidence lineage. Where it conflicts with the
authoritative execution snapshot above, the snapshot above controls.

| Verification boundary | Exact evidence | State |
| --- | --- | --- |
| Locally validated | PR #2164 exact reviewed head `5f6d747aa75a0629f33d0900489a613a3f1e2b8d` passed its affected suites. PR #1995 exact head [`07d3d7d71d1dd308984d349d6751da9378579cf1`](https://github.com/promptdriven/pdd/commit/07d3d7d71d1dd308984d349d6751da9378579cf1) contains protected base `0e22fe9f4`. Terra reported 305 affected passes and 36 platform skips for the protected Package authority correction; post-main integration verifier/package/tamper tests passed 44. YAML, 45 embedded shell scripts, bash syntax, pycompile, pylint, and diff checks passed. | local evidence green for both diagnostic lanes |
| Independently reviewed | Sol approved exact head `07d3d7d71`, producer digest `146919c7c1c2bbd09c9d0577723638b41591f09c301a7467d0ab5bb96fc2394b`, termination verifier `e371cd4d12a6b4d64ea3488d773054b2dfc51320db892e7019d1f20db393d1f2`, Package verifier `b6e923061ea73ed46af4d03e497aa9ed4e538129f85b1c0eabc1bd47d45e177e`, Package provenance `36f27b84f21b62b80dd5f2ad826e2fde395d986a5eec35936f9462335faa8ff1`, protected base `0e22fe9f4`, and verdict `NO_BEHAVIORAL_FIX`. | exact-composite approved |
| Hosted green | #2164 exact-head [run 29622818907](https://github.com/promptdriven/pdd/actions/runs/29622818907) passed all required checks. On #1995 prior head `daa67f2044`, [run 29635743590](https://github.com/promptdriven/pdd/actions/runs/29635743590) had green CodeQL, Story/Public CLI regressions, and Docker E2E, but Unit failed in silent preflight; Package passed all seven installed-wheel Playwright variants, then reproduced the installed-wheel Vitest exit with untrusted diagnostic `340afd630c05209f62419c312abe3aeb7464262e3c5d8367e8d28fec22428471`. On exact head `84b19758f`, [Unit job 88061484993](https://github.com/promptdriven/pdd/actions/runs/29637193871/job/88061484993) uploaded checksummed failure artifact `aec9faa5a2c27cfdaddfb0b82135493d7cafb594728ac22a897a738da0f8cbee`: predicate `runner-provisioner-version-count`, expected 1, actual 0, command exit 0, decoded observation `version=20260707.563`, full-output digest `1e40203d955c084de9ec279dbe867aa074eb9697c4549b763eb753e048536840`. On exact head `07d3d7d71`, [run 29639041827 attempt 1](https://github.com/promptdriven/pdd/actions/runs/29639041827/attempts/1) failed both lanes at `review-evidence-decode` because the protected base64 variable was missing one trailing padding character; the corrected value decodes to reviewed digest `c8ad0ae8e96806928d971e710be64bb5648fe7ed96fc5235a0e31561e5cff39c`. [Attempt 2](https://github.com/promptdriven/pdd/actions/runs/29639041827/attempts/2) passed provenance, all pre-Vitest Unit sandbox/transport checks, the Package wheel attestation, and all seven installed-wheel Playwright variants. Both source and wheel candidates then returned `COLLECTION_ERROR: Vitest reporter produced no result` without an eligible fixed-enum cause artifact. Source preflight PASS digest is `e9b33d7c02f55a9361ba74a1fd908d948bd60c5d6e288926e6822a8aa6d014c7`; wheel attestation digest is `52726db19e9ec485e8be54406c8629a0433f40739842409a57df667086be07a5`, binding wheel `41b528e5ebad9b25818d7cc89036ebaa4b3542401d7e0524792b4e051053cadd` to the reviewed runner. CodeQL, Story, Public CLI, and Docker E2E passed; Unit, Package, heal, and auto-heal remain red. | #1995 Stage A red at one shared unclassified coordinator exit |
| Merged to protected `main` | #2164 merged with ancestry preserved at [`d91b07a9002be895556b38c5bafff18a420b256e`](https://github.com/promptdriven/pdd/commit/d91b07a9002be895556b38c5bafff18a420b256e). At that historical point, #1995 head `07d3d7d71` lacked a later main ancestor. This attempt is superseded; no further #1995 integration cycle is authorized. | archived negative evidence; non-operative |
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

This entire sequence is archival and non-operative. It records the superseded
diagnostic process and does not authorize a push, hosted rerun, merge, release,
or new evidence stage. Its stale head and base identifiers are superseded by the
authoritative execution snapshot.

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
3. **Superseded planned gate:** the historical plan would have fetched and
   resolved live `origin/main`, integrated it into #1995, and obtained fresh
   exact-composite review before adding Stage A0. Exact-head attempt 2 proved
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
7. The superseded process would have required all hosted checks on one exact
   reviewed SHA. That process is frozen and no #1995 merge is authorized.
8. The superseded process expected a #1995 merge before checker release. That
   dependency is revoked; release-required deltas must come from fresh live-main
   PRs with complete net-diff review.

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

For #2164, the complete first half of this historical predicate is true. For
#1995, hosted Stage A evidence was later reconciled on frozen remote head
`d334266680881cbda59de4ecd4df967c92159fa7`. The historical merge predicate
remains false and is permanently non-operative: #1995 will not be pushed again,
merged, released, or used to block gates 1-6. Its evidence remains diagnostic
history only.

#### Archived pinned Vitest cause-evidence gate

This section preserves the old three-stage contract for evidence lineage. It is
non-operative and authorizes no future #1995 work. Stage A0 observed the hosted
path, Stage A collected a fixed-enum cause, and the unpushed Stage B correction
was frozen. The protected workflow historically pinned these identities:

```yaml
failure_baseline_sha: b09b6bef2c8c4bee762965be463527cd0b050154
protected_base_sha: 39776aa9bb027c638812a01b8dabbe03cab92f64
diagnostic_head_sha: $PDD_REVIEWED_DIAGNOSTIC_HEAD_SHA
trigger_head_sha: $PDD_TRIGGER_PR_HEAD_SHA
checkout_head_sha: $PDD_REVIEWED_DIAGNOSTIC_HEAD_SHA
reviewed_head_sha: $PDD_REVIEWED_DIAGNOSTIC_HEAD_SHA
review_evidence_sha256: $PDD_REVIEW_EVIDENCE_SHA256
producer_sha256: $PDD_REVIEWED_PRODUCER_SHA256
termination_verifier_sha256: $PDD_REVIEWED_VERIFIER_SHA256
observation_verifier_sha256: $PDD_REVIEWED_OBSERVATION_VERIFIER_SHA256
stage_a_verifier_sha256: $PDD_REVIEWED_STAGE_A_VERIFIER_SHA256
native_addon_sha256: $PDD_REVIEWED_NATIVE_ADDON_SHA256
package_verifier_sha256: $PDD_REVIEWED_PACKAGE_VERIFIER_SHA256
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

Stage A first proves the pinned preflight and then runs the same intentional
failing node in both lanes. Its producer is eligible only when the authenticated
transport contains one known native `sealResultAuthority` enum immediately before
`reporter-authority-seal-failed`; supervisor exit zero and the broad seal boundary
remain insufficient. A missing Stage A artifact, a nonzero verifier result, or an
unexpected candidate status leaves Stage A pending. Neither lane may convert the
intentional candidate exit `1` into a pass or claim a cause-specific RED.
The existing preflight records remain canonical mode-0600 artifacts with SHA-256
sidecars: `vitest-preflight-v1` records a failed stable predicate and
`vitest-preflight-pass-v1` records the exact reviewed/toolchain bindings. Both are
uploaded with `if: always()` and neither is a substitute for a native Stage A
artifact.

The following common predicate is evaluated against the checked-out reviewed
head before either lane executes. It binds the Stage A verifier and native-addon
bytes in addition to the existing producer, Stage A0, and Package identities:

##### Source lane

```bash
set -euo pipefail
umask 077
failure_baseline=b09b6bef2c8c4bee762965be463527cd0b050154
protected_base=39776aa9bb027c638812a01b8dabbe03cab92f64
diagnostic_head="$(git rev-parse HEAD)"
test "$diagnostic_head" = "$PDD_TRIGGER_PR_HEAD_SHA"
test "$diagnostic_head" = "$PDD_REVIEWED_DIAGNOSTIC_HEAD_SHA"
git merge-base --is-ancestor "$failure_baseline" "$diagnostic_head"
git merge-base --is-ancestor "$protected_base" "$diagnostic_head"
producer_sha256="$(sha256sum pdd/sync_core/runner.py | cut -d' ' -f1)"
termination_verifier_sha256="$(sha256sum scripts/verify_vitest_termination_evidence.py | cut -d' ' -f1)"
observation_verifier_sha256="$(sha256sum scripts/verify_vitest_no_result_observation.py | cut -d' ' -f1)"
stage_a_verifier_sha256="$(sha256sum scripts/verify_vitest_stage_a_evidence.py | cut -d' ' -f1)"
native_addon_sha256="$(sha256sum pdd/sync_core/native/vitest_fd_cloexec.c | cut -d' ' -f1)"
package_verifier_sha256="$(sha256sum scripts/verify_vitest_package_attestation.py | cut -d' ' -f1)"
package_provenance_sha256="$(sha256sum scripts/verify_vitest_package_provenance.sh | cut -d' ' -f1)"
test "$producer_sha256" = "$PDD_REVIEWED_PRODUCER_SHA256"
test "$termination_verifier_sha256" = "$PDD_REVIEWED_VERIFIER_SHA256"
test "$observation_verifier_sha256" = "$PDD_REVIEWED_OBSERVATION_VERIFIER_SHA256"
test "$stage_a_verifier_sha256" = "$PDD_REVIEWED_STAGE_A_VERIFIER_SHA256"
test "$native_addon_sha256" = "$PDD_REVIEWED_NATIVE_ADDON_SHA256"
test "$package_verifier_sha256" = "$PDD_REVIEWED_PACKAGE_VERIFIER_SHA256"
test "$package_provenance_sha256" = "$PDD_REVIEWED_PACKAGE_PROVENANCE_SHA256"
test "$(sha256sum "$PDD_REVIEW_EVIDENCE_PATH" | awk '{print $1}')" = \
  "$PDD_REVIEW_EVIDENCE_SHA256"
jq -e \
  --arg baseline "$failure_baseline" \
  --arg protected "$protected_base" \
  --arg head "$diagnostic_head" \
  --arg producer "$producer_sha256" \
  --arg termination_verifier "$termination_verifier_sha256" \
  --arg observation_verifier "$observation_verifier_sha256" \
  --arg stage_a_verifier "$stage_a_verifier_sha256" \
  --arg native_addon "$native_addon_sha256" \
  --arg package_verifier "$package_verifier_sha256" \
  --arg package_provenance "$package_provenance_sha256" \
  '(.schema == "vitest-diagnostic-review-v1") and
   (.verdict == "APPROVE") and
   (.behavioral_verdict == "NO_BEHAVIORAL_FIX") and
   (.failure_baseline_sha == $baseline) and
   (.protected_base_sha == $protected) and
   (.diagnostic_head_sha == $head) and
   (.producer_sha256 == $producer) and
   (.verifier_sha256 == $termination_verifier) and
   (.observation_verifier_sha256 == $observation_verifier) and
   (.stage_a_verifier_sha256 == $stage_a_verifier) and
   (.native_addon_sha256 == $native_addon) and
   (.package_verifier_sha256 == $package_verifier) and
   (.package_provenance_sha256 == $package_provenance)' \
  "$PDD_REVIEW_EVIDENCE_PATH"
stage_a_directory="$RUNNER_TEMP/pdd-vitest-stage-a-evidence"
stage_a_artifact="$stage_a_directory/vitest-source-stage-a-native-seal-v1.json"
mkdir -p "$stage_a_directory"
chmod 700 "$stage_a_directory"
export PDD_VITEST_STAGE_A_OUTPUT="$stage_a_artifact"
export PDD_VITEST_STAGE_A_FAILURE_BASELINE_SHA="$failure_baseline"
export PDD_VITEST_STAGE_A_PROTECTED_BASE_SHA="$protected_base"
export PDD_VITEST_STAGE_A_TRIGGER_HEAD_SHA="$PDD_TRIGGER_PR_HEAD_SHA"
export PDD_VITEST_STAGE_A_CHECKOUT_HEAD_SHA="$diagnostic_head"
export PDD_VITEST_STAGE_A_REVIEWED_HEAD_SHA="$diagnostic_head"
export PDD_VITEST_STAGE_A_REVIEW_EVIDENCE_SHA256="$PDD_REVIEW_EVIDENCE_SHA256"
export PDD_VITEST_STAGE_A_PRODUCER_SHA256="$producer_sha256"
export PDD_VITEST_STAGE_A_TERMINATION_VERIFIER_SHA256="$termination_verifier_sha256"
export PDD_VITEST_STAGE_A_OBSERVATION_VERIFIER_SHA256="$observation_verifier_sha256"
export PDD_VITEST_STAGE_A_VERIFIER_SHA256="$stage_a_verifier_sha256"
export PDD_VITEST_STAGE_A_NATIVE_ADDON_SHA256="$native_addon_sha256"
export PDD_VITEST_STAGE_A_PACKAGE_VERIFIER_SHA256="$package_verifier_sha256"
export PDD_VITEST_STAGE_A_PACKAGE_PROVENANCE_SHA256="$package_provenance_sha256"
export PDD_VITEST_STAGE_A_RUNNER_IMAGE="$PDD_MEASURED_RUNNER_IMAGE"
export PDD_VITEST_STAGE_A_RUNNER_PROVISIONER="$PDD_MEASURED_RUNNER_PROVISIONER"
export PDD_VITEST_STAGE_A_PYTHON_VERSION="$PDD_MEASURED_PYTHON_VERSION"
export PDD_VITEST_STAGE_A_NODE_VERSION="$PDD_MEASURED_NODE_VERSION"
export PDD_VITEST_STAGE_A_PACKAGE_SHA256="$PDD_MEASURED_VITEST_PACKAGE_SHA256"
export PDD_VITEST_STAGE_A_LOCK_SHA256="$PDD_MEASURED_VITEST_LOCK_SHA256"
export PDD_VITEST_STAGE_A_TEST_NODE="$PDD_VITEST_TEST_NODE"
export PDD_VITEST_STAGE_A_LANE=source
export PDD_VITEST_STAGE_A_RUNNER_ORIGIN=source-checkout
unset PDD_VITEST_STAGE_A_PACKAGE_ATTESTATION_SHA256
unset PDD_VITEST_STAGE_A_WHEEL_SHA256
unset PDD_VITEST_STAGE_A_INSTALLED_RUNNER_SHA256
set +e
pytest -q tests/test_sync_core_runner_vitest.py::test_real_vitest_runs_copied_entrypoint_without_candidate_result_access --timeout=180
test_status=$?
set -e
test "$test_status" -eq 1
test -f "$stage_a_artifact"
test -f "$stage_a_artifact.sha256"
stage_a_artifact_sha256="$(sha256sum "$stage_a_artifact" | awk '{print $1}')"
test "$stage_a_artifact_sha256" = "$(tr -d '\n' < "$stage_a_artifact.sha256")"
test "$(stat -c '%a' "$stage_a_directory")" = 700
test "$(stat -c '%a' "$stage_a_artifact")" = 600
test "$(stat -c '%a' "$stage_a_artifact.sha256")" = 600
test "$(wc -c < "$stage_a_artifact.sha256")" -eq 65
python scripts/verify_vitest_stage_a_evidence.py \
  --evidence "$stage_a_artifact" \
  --evidence-sha256 "$stage_a_artifact_sha256" \
  --review-evidence "$PDD_REVIEW_EVIDENCE_PATH" \
  --review-evidence-sha256 "$PDD_REVIEW_EVIDENCE_SHA256" \
  --repository "$GITHUB_WORKSPACE" \
  --failure-baseline-sha "$failure_baseline" \
  --protected-base-sha "$protected_base" \
  --trigger-head-sha "$PDD_TRIGGER_PR_HEAD_SHA" \
  --checkout-head-sha "$diagnostic_head" \
  --reviewed-head-sha "$diagnostic_head" \
  --producer-sha256 "$producer_sha256" \
  --termination-verifier-sha256 "$termination_verifier_sha256" \
  --observation-verifier-sha256 "$observation_verifier_sha256" \
  --stage-a-verifier-sha256 "$stage_a_verifier_sha256" \
  --native-addon-sha256 "$native_addon_sha256" \
  --package-verifier-sha256 "$package_verifier_sha256" \
  --package-provenance-sha256 "$package_provenance_sha256" \
  --runner-image "$PDD_VITEST_STAGE_A_RUNNER_IMAGE" \
  --runner-provisioner "$PDD_VITEST_STAGE_A_RUNNER_PROVISIONER" \
  --python "$PDD_VITEST_STAGE_A_PYTHON_VERSION" \
  --node "$PDD_VITEST_STAGE_A_NODE_VERSION" \
  --vitest-package-sha256 "$PDD_VITEST_STAGE_A_PACKAGE_SHA256" \
  --vitest-lock-sha256 "$PDD_VITEST_STAGE_A_LOCK_SHA256" \
  --test-node "$PDD_VITEST_STAGE_A_TEST_NODE" \
  --lane source
exit "$test_status"
```

##### Installed-wheel lane

```bash
set -euo pipefail
umask 077
failure_baseline=b09b6bef2c8c4bee762965be463527cd0b050154
protected_base=39776aa9bb027c638812a01b8dabbe03cab92f64
diagnostic_head="$(git rev-parse HEAD)"
test "$diagnostic_head" = "$PDD_TRIGGER_PR_HEAD_SHA"
test "$diagnostic_head" = "$PDD_REVIEWED_DIAGNOSTIC_HEAD_SHA"
git merge-base --is-ancestor "$failure_baseline" "$diagnostic_head"
git merge-base --is-ancestor "$protected_base" "$diagnostic_head"
producer_sha256="$(sha256sum pdd/sync_core/runner.py | cut -d' ' -f1)"
termination_verifier_sha256="$(sha256sum scripts/verify_vitest_termination_evidence.py | cut -d' ' -f1)"
observation_verifier_sha256="$(sha256sum scripts/verify_vitest_no_result_observation.py | cut -d' ' -f1)"
stage_a_verifier_sha256="$(sha256sum scripts/verify_vitest_stage_a_evidence.py | cut -d' ' -f1)"
native_addon_sha256="$(sha256sum pdd/sync_core/native/vitest_fd_cloexec.c | cut -d' ' -f1)"
package_verifier_sha256="$(sha256sum scripts/verify_vitest_package_attestation.py | cut -d' ' -f1)"
package_provenance_sha256="$(sha256sum scripts/verify_vitest_package_provenance.sh | cut -d' ' -f1)"
test "$producer_sha256" = "$PDD_REVIEWED_PRODUCER_SHA256"
test "$termination_verifier_sha256" = "$PDD_REVIEWED_VERIFIER_SHA256"
test "$observation_verifier_sha256" = "$PDD_REVIEWED_OBSERVATION_VERIFIER_SHA256"
test "$stage_a_verifier_sha256" = "$PDD_REVIEWED_STAGE_A_VERIFIER_SHA256"
test "$native_addon_sha256" = "$PDD_REVIEWED_NATIVE_ADDON_SHA256"
test "$package_verifier_sha256" = "$PDD_REVIEWED_PACKAGE_VERIFIER_SHA256"
test "$package_provenance_sha256" = "$PDD_REVIEWED_PACKAGE_PROVENANCE_SHA256"
test "$(sha256sum "$PDD_WHEEL_REVIEW_EVIDENCE_PATH" | awk '{print $1}')" = \
  "$PDD_REVIEW_EVIDENCE_SHA256"
jq -e \
  --arg baseline "$failure_baseline" \
  --arg protected "$protected_base" \
  --arg head "$diagnostic_head" \
  --arg producer "$producer_sha256" \
  --arg termination_verifier "$termination_verifier_sha256" \
  --arg observation_verifier "$observation_verifier_sha256" \
  --arg stage_a_verifier "$stage_a_verifier_sha256" \
  --arg native_addon "$native_addon_sha256" \
  --arg package_verifier "$package_verifier_sha256" \
  --arg package_provenance "$package_provenance_sha256" \
  '(.schema == "vitest-diagnostic-review-v1") and
   (.verdict == "APPROVE") and
   (.behavioral_verdict == "NO_BEHAVIORAL_FIX") and
   (.failure_baseline_sha == $baseline) and
   (.protected_base_sha == $protected) and
   (.diagnostic_head_sha == $head) and
   (.producer_sha256 == $producer) and
   (.verifier_sha256 == $termination_verifier) and
   (.observation_verifier_sha256 == $observation_verifier) and
   (.stage_a_verifier_sha256 == $stage_a_verifier) and
   (.native_addon_sha256 == $native_addon) and
   (.package_verifier_sha256 == $package_verifier) and
   (.package_provenance_sha256 == $package_provenance)' \
  "$PDD_WHEEL_REVIEW_EVIDENCE_PATH"
test "$(sha256sum scripts/verify_vitest_package_attestation.py | awk '{print $1}')" = \
  "$package_verifier_sha256"
python scripts/verify_vitest_package_attestation.py verify \
  --attestation "$PDD_WHEEL_ATTESTATION_PATH" \
  --attestation-sha256 "$PDD_WHEEL_ATTESTATION_SHA256" \
  --wheel "$PDD_WHEEL_PATH" \
  --installed-python "$RUNNER_TEMP/pdd-wheel-smoke/bin/python" \
  --repository "$GITHUB_WORKSPACE" \
  --diagnostic-head-sha "$diagnostic_head" \
  --producer-sha256 "$producer_sha256"
installed_runner_sha256="$(python - "$PDD_WHEEL_ATTESTATION_PATH" <<'PY'
import json
import sys
print(json.load(open(sys.argv[1], encoding="ascii"))["installed_runner_sha256"])
PY
)"
wheel_sha256="$(sha256sum "$PDD_WHEEL_PATH" | awk '{print $1}')"
stage_a_directory="$RUNNER_TEMP/pdd-vitest-wheel-termination-evidence"
stage_a_artifact="$stage_a_directory/vitest-wheel-stage-a-native-seal-v1.json"
mkdir -p "$stage_a_directory"
chmod 700 "$stage_a_directory"
export PDD_VITEST_STAGE_A_OUTPUT="$stage_a_artifact"
export PDD_VITEST_STAGE_A_FAILURE_BASELINE_SHA="$failure_baseline"
export PDD_VITEST_STAGE_A_PROTECTED_BASE_SHA="$protected_base"
export PDD_VITEST_STAGE_A_TRIGGER_HEAD_SHA="$PDD_TRIGGER_PR_HEAD_SHA"
export PDD_VITEST_STAGE_A_CHECKOUT_HEAD_SHA="$diagnostic_head"
export PDD_VITEST_STAGE_A_REVIEWED_HEAD_SHA="$diagnostic_head"
export PDD_VITEST_STAGE_A_REVIEW_EVIDENCE_SHA256="$PDD_REVIEW_EVIDENCE_SHA256"
export PDD_VITEST_STAGE_A_PRODUCER_SHA256="$producer_sha256"
export PDD_VITEST_STAGE_A_TERMINATION_VERIFIER_SHA256="$termination_verifier_sha256"
export PDD_VITEST_STAGE_A_OBSERVATION_VERIFIER_SHA256="$observation_verifier_sha256"
export PDD_VITEST_STAGE_A_VERIFIER_SHA256="$stage_a_verifier_sha256"
export PDD_VITEST_STAGE_A_NATIVE_ADDON_SHA256="$native_addon_sha256"
export PDD_VITEST_STAGE_A_PACKAGE_VERIFIER_SHA256="$package_verifier_sha256"
export PDD_VITEST_STAGE_A_PACKAGE_PROVENANCE_SHA256="$package_provenance_sha256"
export PDD_VITEST_STAGE_A_RUNNER_IMAGE="$PDD_WHEEL_MEASURED_RUNNER_IMAGE"
export PDD_VITEST_STAGE_A_RUNNER_PROVISIONER="$PDD_WHEEL_MEASURED_RUNNER_PROVISIONER"
export PDD_VITEST_STAGE_A_PYTHON_VERSION="$PDD_WHEEL_MEASURED_PYTHON_VERSION"
export PDD_VITEST_STAGE_A_NODE_VERSION="$PDD_WHEEL_MEASURED_NODE_VERSION"
export PDD_VITEST_STAGE_A_PACKAGE_SHA256="$PDD_WHEEL_MEASURED_VITEST_PACKAGE_SHA256"
export PDD_VITEST_STAGE_A_LOCK_SHA256="$PDD_WHEEL_MEASURED_VITEST_LOCK_SHA256"
export PDD_VITEST_STAGE_A_TEST_NODE="$PDD_VITEST_TEST_NODE"
export PDD_VITEST_STAGE_A_LANE=installed-wheel
export PDD_VITEST_STAGE_A_RUNNER_ORIGIN=installed-wheel
export PDD_VITEST_STAGE_A_PACKAGE_ATTESTATION_SHA256="$PDD_WHEEL_ATTESTATION_SHA256"
export PDD_VITEST_STAGE_A_WHEEL_SHA256="$wheel_sha256"
export PDD_VITEST_STAGE_A_INSTALLED_RUNNER_SHA256="$installed_runner_sha256"
export PDD_REQUIRE_INSTALLED_WHEEL=1
smoke_dir="$(mktemp -d)"
cp tests/test_sync_core_runner_vitest.py "$smoke_dir/"
cd "$smoke_dir"
set +e
"$RUNNER_TEMP/pdd-wheel-smoke/bin/pytest" -q \
  test_sync_core_runner_vitest.py::test_real_vitest_runs_copied_entrypoint_without_candidate_result_access \
  --timeout=120
test_status=$?
set -e
test "$test_status" -eq 1
test -f "$stage_a_artifact"
test -f "$stage_a_artifact.sha256"
stage_a_artifact_sha256="$(sha256sum "$stage_a_artifact" | awk '{print $1}')"
test "$stage_a_artifact_sha256" = "$(tr -d '\n' < "$stage_a_artifact.sha256")"
test "$(stat -c '%a' "$stage_a_directory")" = 700
test "$(stat -c '%a' "$stage_a_artifact")" = 600
test "$(stat -c '%a' "$stage_a_artifact.sha256")" = 600
test "$(wc -c < "$stage_a_artifact.sha256")" -eq 65
python "$GITHUB_WORKSPACE/scripts/verify_vitest_stage_a_evidence.py" \
  --evidence "$stage_a_artifact" \
  --evidence-sha256 "$stage_a_artifact_sha256" \
  --review-evidence "$PDD_WHEEL_REVIEW_EVIDENCE_PATH" \
  --review-evidence-sha256 "$PDD_REVIEW_EVIDENCE_SHA256" \
  --repository "$GITHUB_WORKSPACE" \
  --failure-baseline-sha "$failure_baseline" \
  --protected-base-sha "$protected_base" \
  --trigger-head-sha "$PDD_TRIGGER_PR_HEAD_SHA" \
  --checkout-head-sha "$diagnostic_head" \
  --reviewed-head-sha "$diagnostic_head" \
  --producer-sha256 "$producer_sha256" \
  --termination-verifier-sha256 "$termination_verifier_sha256" \
  --observation-verifier-sha256 "$observation_verifier_sha256" \
  --stage-a-verifier-sha256 "$stage_a_verifier_sha256" \
  --native-addon-sha256 "$native_addon_sha256" \
  --package-verifier-sha256 "$package_verifier_sha256" \
  --package-provenance-sha256 "$package_provenance_sha256" \
  --runner-image "$PDD_VITEST_STAGE_A_RUNNER_IMAGE" \
  --runner-provisioner "$PDD_VITEST_STAGE_A_RUNNER_PROVISIONER" \
  --python "$PDD_VITEST_STAGE_A_PYTHON_VERSION" \
  --node "$PDD_VITEST_STAGE_A_NODE_VERSION" \
  --vitest-package-sha256 "$PDD_VITEST_STAGE_A_PACKAGE_SHA256" \
  --vitest-lock-sha256 "$PDD_VITEST_STAGE_A_LOCK_SHA256" \
  --test-node "$PDD_VITEST_STAGE_A_TEST_NODE" \
  --lane installed-wheel \
  --package-attestation "$PDD_WHEEL_ATTESTATION_PATH" \
  --package-attestation-sha256 "$PDD_WHEEL_ATTESTATION_SHA256" \
  --wheel-sha256 "$wheel_sha256" \
  --installed-runner-sha256 "$installed_runner_sha256"
exit "$test_status"
```

Each accepted Stage A artifact is canonical `vitest-stage-a-native-seal-v1`,
stored outside the candidate checkout in a mode-0700 parent with mode-0600
artifact and SHA-256 sidecar. The source form has `lane: source` and
`runner_origin: source-checkout` and forbids all wheel fields. The installed-wheel
form has `lane: installed-wheel`, `runner_origin: installed-wheel`, and binds the
canonical Package-attestation digest, wheel digest, and installed-runner digest.
Both forms bind `stage_a_verifier_sha256`, `native_addon_sha256`, exact head/base/
toolchain values, an ordered native-seal trace, all three cgroup deltas, and
`cause_red_status: pending`. The Stage A verifier is the acceptance predicate for
this artifact. The termination verifier remains an explicit rejection predicate
for the distinct Stage A0 observation only; it does not accept or substitute for
native Stage A evidence.

The diagnostic head must be an exact reviewed, evidence-only descendant of
`failure_baseline_sha`; its review evidence binds the permitted diff, producer,
termination, observation, Stage A verifier, native-addon, and both Package
authority digests with the `NO_BEHAVIORAL_FIX` verdict. The protected workflow
hashes the Package provenance script before executing it and uploads both lane
artifacts and sidecars with `if: always()`. Stage B starts only after both native
Stage A verifiers accept authentic source and installed-wheel artifacts. It adds a
distinct RED bound to the observed fixed-enum cause, proves that RED fails before
the fix, and then requires the RED plus source and installed-wheel hosted Vitest
checks to pass on one exact reviewed correction head. No behavioral fix,
rerun-as-pass, or PR merge is allowed before these ordered predicates are true.

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
the next stage. Frozen #1995 diagnostics are not a prerequisite to this sequence
and do not alter any of its ten steps.

The machine-readable source of truth for step status and exact evidence is the
reviewed metadata source
[`docs/global_sync_evidence_ledger_source.yaml`](global_sync_evidence_ledger_source.yaml),
rendered verbatim to
[`docs/global_sync_evidence_ledger.yaml`](global_sync_evidence_ledger.yaml).
This narrative summarizes that ledger; it does not override missing or red
machine evidence. Source rows are claims, not trust anchors: the protected
drift command uses `--verify-remote` to match hosted/merge promotions to GitHub
PR, check, and merge metadata. Every referenced bundle also carries a typed,
exact subject: its ledger-generation or numbered-gate identity, only the named
lifecycle states, a canonical SHA-256 of that record's required predicate, and
the record's repository, reviewed-head, and merge claims. The renderer
recomputes that subject for every reference, so a bundle cannot be replayed
across gates, predicates, or lifecycle states. It never infers an accepted
evidence state from this prose or local results; reviewed source rows must
retain exact SHA and hosted-artifact values.

<!-- global-sync-ledger-source: global_sync_evidence_ledger_source.yaml -->

#### 2026-07-19 live rebaseline and recommendation disposition

Progress is reported by closed evidence gates, never by commit count or local
test volume. The live scoreboard is `0/10` passed and the qualifying nightly
streak is `0/7`. PR #1995 remains an unstable diagnostic branch at remote head
`d334266680881cbda59de4ecd4df967c92159fa7`, with 48 changed files,
39,468 additions, and 5,130 deletions. Exact-head run `29658808029` reconciled
source and installed-wheel Stage A evidence on `d334266680881cbda59de4ecd4df967c92159fa7`.
Those artifacts are not green merge evidence. The remote branch and all unpushed
corrections are frozen as diagnostic evidence and are not on the gates 1-6
critical path.

#### 2026-07-19 Gate 2 architecture rebaseline

Protected `main` is now [`35e903cb5ed103980affbdf2a64ef7a80a66ca4a`](https://github.com/promptdriven/pdd/commit/35e903cb5ed103980affbdf2a64ef7a80a66ca4a). [PR #2223](https://github.com/promptdriven/pdd/pull/2223) reviewed head [`0ca5eb173a31c2ed2b46d7db0feeb88c62645907`](https://github.com/promptdriven/pdd/commit/0ca5eb173a31c2ed2b46d7db0feeb88c62645907) merged as [`9c1dc6f2fb1b621ed5320f407f5ae6a2c5299214`](https://github.com/promptdriven/pdd/commit/9c1dc6f2fb1b621ed5320f407f5ae6a2c5299214), and [PR #2224](https://github.com/promptdriven/pdd/pull/2224) reviewed head [`862f725d9d9f41b5509dbbcba61d7789f49ad74b`](https://github.com/promptdriven/pdd/commit/862f725d9d9f41b5509dbbcba61d7789f49ad74b) merged as that protected head. Both had 12 green checks; #2223 adds only the released-checker evidence wrapper and #2224 only preauthorizes the absent target-lock path. Neither releases nor pins a checker.

[PR #2225](https://github.com/promptdriven/pdd/pull/2225), closed unmerged, is diagnostic evidence only and cannot advance Gate 2. Attempt 1, head `09015bcc79c00575262e8c23d9b14693ae8be80f`, ended in a build-version failure at [job 88224039194](https://github.com/promptdriven/pdd/actions/runs/29698754085/job/88224039194). Attempt 2, head `d060da1cc1d6c81abf0c42cf5df69ac81d79a75e`, ended in a read-only build-source failure at [job 88224395133](https://github.com/promptdriven/pdd/actions/runs/29698879393/job/88224395133). Attempt 3, closed head [`0bae19c2fb9575d8b8edccaeee3c5d9420e00e9f`](https://github.com/promptdriven/pdd/commit/0bae19c2fb9575d8b8edccaeee3c5d9420e00e9f), built `pdd-cli 0.0.0` and resolved the Python closure, then candidate-owned `runpy` imported eager `pdd.__init__` → `update_main.py` → GitPython without a `git` executable at [job 88224752678](https://github.com/promptdriven/pdd/actions/runs/29699017734/job/88224752678). No artifact upload or target lock completed. `GIT_PYTHON_REFRESH=quiet` is rejected.

Gate 2 is therefore ordered as: (1) a fresh separately released standalone checker under a non-`pdd` top-level package, with checker-only dependencies, strict lock/RECORD validation, and an exact `z3_solver-4.16.0.0-py3-none-manylinux_2_27_x86_64.whl` tag regression; (2) a sealed checker OCI runtime with Git/system closure, pinned base, Debian snapshot/InRelease, exact package and final-image digests, and signed provenance binding the exact released checker wheel digest and exact checker dependency-lock digest as well as Dockerfile/source SHA, image, SBOM, and dpkg inventory. Before launch, protected verification proves installed checker files and `RECORD` equivalent to the pinned wheel. Runtime execution uses only the verified absolute protected interpreter and installed entrypoint with `-I -S`, never a module resolved from candidate checkout or CWD. Signed evidence carries wheel, lock, image, SBOM/dpkg inventory, interpreter, and entrypoint identities. The runtime also has network-none/read-only root and candidate mounts, a sanitized environment, and a clean exact-SHA clone smoke; then (3) protected release and pin wiring for the checker wheel, OCI attestation, expectations, workflow, wheelhouse, scenarios, PATH, and verifier inputs. Candidates that unconditionally pass, print environment values, or edit scenarios remain red and unsigned. Non-goals are a `pdd/__init__` refactor, OCI/release/certificates in layer 1, checker semantic or candidate-policy changes in layer 2, and certificate promotion in layer 3. All new execution-binding predicates remain pending; no hosted-green, merged, released, deployed, or certified Gate 2 evidence exists.

The deterministic ledger generator is now merged as [PR #2219](https://github.com/promptdriven/pdd/pull/2219): Sol HIGH approved exact reviewed head [`06d976de23f6da45c9078fdd1a8f89dbf1aecd2c`](https://github.com/promptdriven/pdd/commit/06d976de23f6da45c9078fdd1a8f89dbf1aecd2c) after full-net review and same-reviewer finding verification; all 12 hosted checks were green, including Unit workflow [29680411144](https://github.com/promptdriven/pdd/actions/runs/29680411144), heal [29680410549](https://github.com/promptdriven/pdd/actions/runs/29680410549), CodeQL [29680409993](https://github.com/promptdriven/pdd/actions/runs/29680409993), and auto-heal [88175432245](https://github.com/promptdriven/pdd/runs/88175432245). Its protected ledger-drift step passed and it squash-merged at [`fb344f1c66e807dc51cac0f5363e5484cc487de9`](https://github.com/promptdriven/pdd/commit/fb344f1c66e807dc51cac0f5363e5484cc487de9) on 2026-07-19T09:34:05Z. The local record is 55 ledger tests passed, pylint 10/10, live `--check --verify-remote` passed, source/generated bytes equal, and architecture and protected-ownership checks passed. Only `implemented`, `hosted_green`, and `merged` are promoted by the `github-pr-checks` bundle; local and independent-review states remain in progress, and release, deployment, certification, Gate 2, and either certificate remain pending.

Ownership prerequisite [PR #2220](https://github.com/promptdriven/pdd/pull/2220) is supporting evidence only: reviewed head [`1c2abbdb495f9364614fe95fb8670b55275d2f70`](https://github.com/promptdriven/pdd/commit/1c2abbdb495f9364614fe95fb8670b55275d2f70) passed all 12 hosted checks and squash-merged as [`67c118bd2f469d780987f93e9b8edf663dd40b4b`](https://github.com/promptdriven/pdd/commit/67c118bd2f469d780987f93e9b8edf663dd40b4b) on 2026-07-19T08:19:35Z. It is not a promotion state or gate pass.

Protected PDD `main` at
`35e903cb5ed103980affbdf2a64ef7a80a66ca4a` contains 468 expected managed
units and 468 profiles. The immutable profile-evidence source is
`2cacc91f90759ff45f1ad976da3b773e1a5f07a5`; its registry is profile-equivalent
to live main (`git diff --quiet 2cacc91f..35e903cb -- .pdd/verification-profiles.json`)
at digest `56ea5d189034c9d85e91c86348689eb18c4c34fa67406258f78f0ae3330eaeb6`.
Only one profile has a required machine-test obligation;
467 are human-attestation-only, so protected machine-obligation profile coverage
is `1/468` (`0.213675%`). The PR #1995 candidate contains 472 expected units and
profiles, but still only one machine-obligation profile and 471 human-only
profiles (`1/472`, `0.211864%`). These figures prove only profile configuration.
No protected artifact establishes machine-verified unit count or current machine-
evidence coverage for either exact SHA; both remain unknown. Profile presence and
trusted human attestation must not be reported as machine verification.
Diagnostic head `d334266680881cbda59de4ecd4df967c92159fa7` contains reviewed
base `39776aa9bb027c638812a01b8dabbe03cab92f64` but not current protected
`main`; live-main ancestry remains a separate red gate.

The recommendations are adopted with these corrections:

| Recommendation | Disposition | Controlling correction |
| --- | --- | --- |
| Stronger non-human predicate | Adopt | Global certification requires every expected managed unit to have current machine verification; human-only units must be zero. Narrower claims must name their excluded denominator. |
| Generated evidence ledger with separate lifecycle states | Adopt with correction | PR #2219's generator and protected drift check are merged; lifecycle/evidence states remain separately reported as `implemented`, `local_green`, `independently_reviewed`, `hosted_green`, `merged`, `released`, `deployed`, and `certified`, and Gate 2 is next. |
| Freeze PR #1995 diagnostics | Adopt | Run the reviewed fixed-enum diagnostic once, permit one cause-specific RED and one bounded correction, then stop adding observability. A failure to close both hosted lanes triggers adapter-architecture reconsideration. |
| Stop growing #1995 as a release monolith | Adopt | Complete the single bounded #1995 diagnostic cycle, then freeze its head and preserve it as immutable evidence. Extract the minimum fix/prerequisite stack onto fresh live-main PRs and completely review each release PR's net diff. A full #1995 review may validate diagnostic evidence but does not convert it into the release vehicle. |
| Profile-derived adapter demand | Adopt | Generate PDD and pdd_cloud adapter demand from protected profiles. Only demanded adapters block the first certificate; demanded Playwright coverage requires a real browser execution. |
| Three independent workstreams | Adopt with dependency constraint | A, B, and C may proceed concurrently only with disjoint production files. Release, hosted, migration, and certification gates remain dependency ordered. |
| Early protected vertical slice | Adopt | Immediately after checker release, gate broad migration on one fixture, one PDD unit, and one real pdd_cloud unit covering edits, death, stale evidence, tampering, recovery, exact-SHA signatures, and zero-write reruns. |
| Canonical mutator routing and static enforcement | Adopt | Production code must use canonical identity/include/classifier/transaction/fingerprint APIs; a protected static ownership test rejects independent implementations and direct canonical metadata writes. |
| Nonqualifying shadow nightlies | Adopt | Start shadows immediately for infrastructure debugging. They never increment the official streak, which starts only after steps 1-8 pass. |
| Evidence-based progress format | Adopt | Every update reports gates, machine profile coverage, released digest, lifecycle rows, cloud canary, qualifying nights, and one blocker. |

The 2026-07-18 execution ratification fixes the immediate sequencing:

- Carry the exact local PDD-only adapter-demand matrix and three-way extraction
  manifest into the guarded gate-1 PR first. Protected PDD profiles demand only
  `pytest`. A combined matrix is deferred until pdd_cloud has a protected
  verification-profile registry; its future demand is not inferred.
- Classify every possible #1995 extraction as an already-merged prerequisite,
  a release-required delta, or excluded diagnostic work. Already-protected
  foundation code is not re-extracted. Fresh-main release PRs should target
  roughly 2,000 net lines when module boundaries permit, but complete review and
  coherent ownership are the controlling predicates.
- Freeze #1995 and every unpushed correction branch. Preserve before pruning;
  do not discard branches or worktrees without a clean-state and ownership audit.
- Gate tooling required by the delivery program is exempt from the ban on new
  diagnostic layers. No new #1995 verifier, artifact schema, or observability
  stage is permitted.
- Define the ledger generator schema before moving attempt history out of this
  plan. The future design separates generated current state from append-only
  historical evidence; an arbitrary line count cannot remove evidence.
- The three-working-day and same-day-deliverable rules are governance discipline,
  not certificate predicates. Every gate initializes `last_state_change` at this
  ratified baseline and updates it only on an evidence-backed state transition.

For the full global claim, the certificate predicate is non-negotiable:
`machine_verified_units == expected_managed_units`, machine verification-profile
coverage and current trusted machine-evidence coverage are both 100%,
`human_attestation_only_units == 0`,
`unaccounted_tracked_paths == 0`, and `waivers == 0`. Human review may add
evidence but cannot be the only satisfying evidence for a protected managed unit.
If an obligation cannot be machine verified, the certificate must name the
excluded units and denominator and make a narrower claim; it must not call that
result globally certified.

The deterministic ledger generator named in the YAML and its protected drift
check are merged and green. They render the canonical ledger from an explicit
versioned YAML source and fail closed on duplicate keys, malformed schema/state
rows, or byte drift. The canonical blocker
`gate2-standalone-checker-package-boundary` requires the standalone non-`pdd`
checker extraction manifest/package-boundary PR as the under-24-hour
deliverable; the sealed OCI and protected pin wiring follow strictly. This
deliverable is intentionally smaller than the whole release and does not
authorize a release or certificate claim. The named
`extraction_manifest_verifier` is planned future evidence only; it is not
implemented and does not prove gate 1.

PR #1995 is frozen at remote head
`d334266680881cbda59de4ecd4df967c92159fa7`. Its hosted Stage A artifacts and
unpushed correction branches are diagnostic evidence only. No further correction,
hosted run, merge, or release extraction may be pushed to that PR. Release changes
are extracted onto fresh live-main PRs and receive complete net-diff review.

| Order | Unblock | Required exit evidence |
| --- | --- | --- |
| 1 | Rebaseline against protected live main. Inventory already-merged prerequisites, release-required deltas, and excluded diagnostic work in `docs/global_sync_extraction_manifest.md`; deliver the standalone non-`pdd` checker package boundary before OCI and protected pin wiring. | The manifest accounts for the frozen #1995 net diff and #2225 diagnostic attempts without treating either as a release vehicle, identifies already-protected foundations without re-extracting them, excludes diagnostic workflow/bootstrap work, and maps every release-required delta to a bounded fresh-main PR with complete net-diff review. |
| 2 | Extract a standalone non-`pdd` checker distribution with checker-only dependencies, strict lock/RECORD validation, and corrected compatible-wheel tag handling; then seal it in a separately pinned Git-capable OCI runtime and wire protected release/pin expectations. #2225 is diagnostic evidence only, never the release vehicle. | All three layers have their distinct lifecycle evidence: released checker wheel digest; protected OCI digest, provenance, SBOM, and dpkg inventory; and protected workflow/expectation pins. Candidate-controlled checker, scenario, PATH, wheelhouse, expectation, or verifier inputs remain impossible, while unconditional-PASS, env-printing, and scenario-edit candidates are red and unsigned. |
| 3 | Replace direct production writes with generate-to-staging followed by one durable transaction containing artifacts, shared metadata, evidence, report, and fingerprint. Use descriptor-relative no-follow commit operations and verify all WAL blobs before the first destination change. Before broad migration, run the protected vertical slice from clean clones and built wheels against one fixture, one PDD unit, and one real pdd_cloud unit. | Process death at every generation/journal/install phase recovers to the complete old or complete new state; prompt/include/code/test edits, stale evidence, and candidate tampering are detected; signed evidence binds exact SHAs; immediate rerun writes zero files. |
| 4 | Carry the exact local PDD-only adapter-demand matrix into the guarded gate-1 PR. Make the pytest adapter compare protected expected node IDs with collected and executed node IDs and bind every config-loaded plugin and executable support module. Defer a combined PDD/pdd_cloud matrix until pdd_cloud has a protected profile registry. Implement every actually demanded adapter before claiming coverage; defer undemanded universal adapters. | The PDD matrix accounts for all 468 protected profiles, reports demanded validators exactly `{pytest}`, and has no unknown adapter. Removed parametrized cases, config-loaded local plugins, collection hooks, skips, xfails, deselection, and dirty support fail closed. The later combined matrix accounts for every protected pdd_cloud profile and requires real-browser execution only if a protected profile demands Playwright. |
| 5 | Route every production mutator, runtime preprocessor, dependency discoverer, change detector, legacy operation selector, and fingerprint writer through the canonical include graph, identity, classifier, staging transaction, and fingerprint APIs. | A protected static enforcement test reports zero independent include parsers, fingerprint hashers, drift classifiers, or canonical metadata writers; compatibility modules contain orchestration only. |
| 6 | Land and release the PDD foundation. Run the released checker against clean exact-SHA PDD clones, then create protected machine-verification profiles and trusted evidence for every expected managed unit. Human review may supplement but cannot solely satisfy a managed unit. | PDD exact-SHA report has complete inventory, `machine_verified_units == expected_managed_units`, 100% machine profile/evidence coverage, `human_attestation_only_units == 0`, zero unaccounted tracked paths, red states, or waivers. |
| 7 | Pin that release in pdd_cloud, remove `metadata_finalize.py` and all other vendored sync semantics, resolve the duplicate output conflict, then migrate machine profiles, fingerprints, and evidence by bounded subtree PRs. A unit that cannot be machine verified must be excluded from a clearly narrower claim, never silently accepted via human-only evidence. | Independent semantic ownership audit and exact-tree scan report zero consumer-owned sync semantics; pdd_cloud has `machine_verified_units == expected_managed_units`, 100% machine profile/evidence coverage, zero human-attestation-only managed units, unaccounted paths, red units, or waivers. |
| 8 | Enable the protected merge-group lifecycle lane using clean clones and the pinned checker. Run every required injected scenario, including the real pdd_cloud canary, without required skips. | One fresh signed scan certificate has `scan_ok: true`, lifecycle failures/skips/errors/timeouts zero, and both no-write counters zero. |
| 9 | Start the temporal gate only after steps 1-8 are stable. Store signed immutable nightly rows outside either candidate checkout and run complete scans even after ledger/cursor deletion. | Seven consecutive UTC-date certificates preserve repository identity/SHA lineage; normal nights are no-op and injected drift is detected, resolved or blocked, then rerun with zero writes. |
| 10 | Run the documented final command and a fresh Sol HIGH adversarial review. | Command exits 0; an independent verifier accepts the signed exact-SHA certificate and proves the full non-human predicate above; the review records the exact certificate and repository SHAs and returns `APPROVE`. |

Steps 1-7 are engineering work. Step 8 requires protected CI/release configuration.
Step 9 additionally requires seven elapsed nightly windows and therefore cannot
be replaced with locally fabricated timestamps. The current implementation is
at steps 1-4: released-wheel identity, exact pytest node collection proof, and
the checker-owned harness are implemented and built-wheel tested locally.
Protected release/workflow deployment, transactional generation-to-staging,
non-pytest adapters, and repository profile/evidence rollout are not complete.

Up to three implementation workstreams may run concurrently when their write
sets are disjoint:

- **A, checker release:** preserve frozen #1995 diagnostics, classify its net
  diff, extract only release-required pytest checker deltas from live main, and
  publish the protected checker digest.
- **B, transaction:** implement generation-to-staging, durable recovery, and
  zero-write reruns without touching A's adapter/release files.
- **C, certification data:** build the PDD demand matrix and ledger generator,
  then build PDD/pdd_cloud inventories, machine profiles, and evidence without
  touching A or B production modules. Once profile generation exists and before
  gate 5 completes, partition all 467 current human-only PDD units into:
  obligations derivable from existing tests, units requiring new tests, and
  candidates for protected expected-managed narrowing with named exclusions.
  Surface that partition for a human scoping decision before gate 6 begins.

Local work may overlap in time, but B cannot close protected/released evidence
before A, and C cannot claim trusted current coverage before the released checker
and vertical slice pass.

Start nonqualifying shadow nightlies immediately to exercise release lookup,
signer identity, immutable storage, lifecycle orchestration, and canary plumbing.
Every row must be marked `qualifying: false` and excluded from streak counters.
The first qualifying UTC row is permitted only after steps 1-8 pass.

Every progress update uses this exact scoreboard:

```text
gates passed/10: N/10
machine profile coverage: obligation-profiles/expected (percent), human-only=N
machine verified units: verified/expected | unknown
current machine-evidence coverage: percent | unknown
released checker digest: sha256:<digest> | pending
protected lifecycle rows: passed/required
pdd_cloud canary: pass | fail | pending
qualifying nights/7: N/7
single next blocker: <one evidence gate>
gate last_state_change: 1=YYYY-MM-DD ... 10=YYYY-MM-DD
same-day deliverable: <one concrete artifact or PR>
```

The profile denominator in each update is the exact protected target SHA. A
candidate denominator may be reported separately but must never replace protected
state until that candidate merges and becomes the protected target.

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
- Give every expected-managed unit at least one machine-verifiable obligation and
  current trusted machine evidence. Human attestations may supplement that evidence
  but cannot solely satisfy a managed unit.
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
  `IN_SYNC`. `machine_verified_units == expected_managed_units`, machine profile
  and current machine-evidence coverage are 100%, and
  `human_attestation_only_units == 0`. Gross managed count is non-zero and fixed by
  the candidate union; unaccounted tracked paths, managed waivers, and semantic
  `UNKNOWN` units are zero. Human-owned/removed candidates and managed-to-human
  transitions are separately enumerated, with zero debt-clearing transitions.
  There are no second-run writes in source and wheel environments.

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

## 11. Certificate milestones and Definition of Done

At an exact protected merge-group SHA, a released independent checker installed
from a digest-pinned wheel into a clean environment and run against clean clones
must produce a signed Sync Certificate. Both the primary and separately released
reference verifiers must accept it using only protected expectations, trusted
issuer material, current time, and expected repository identities and SHAs. No
candidate-controlled input may reach either verifier.

There are two certificate classes:

- **Certificate A (Sync Integrity)** is the release milestone. It proves that the
  sync machinery detects every violation it is shown, recovers from every injected
  crash, survives real merge traffic, and accounts for every unit honestly.
- **Certificate B (Global Sync)** is the terminal goal. It requires Certificate A
  for both repositories plus 100% machine-verified content coverage.

Milestone order is `A{pdd} -> A{pdd,pdd_cloud} -> B{pdd,pdd_cloud}`. Certificate A
is intermediate evidence toward, and does not by itself satisfy, gates 6 or 10.
The global predicate is not currently achieved: the external out-of-process SUT
adapter, release evidence, and nightly evidence remain outstanding.

### 11.1 Unit tiers and temporal definitions

Every managed unit is in exactly one tier, and every certificate publishes each
tier count:

- `machine_verified`: every required obligation passes under the released runner;
  evidence binds the unit's current artifact hashes in its input closure; and each
  test-kind obligation's bound coverage report attributes at least 60% line
  coverage to the unit's code artifact. A schema, build, or static validator with
  no coverage semantics must be listed as coverage-exempt in the protected
  validator registry and consume the artifact bytes by hash. Import-only and
  existence-only checks never qualify.
- `machine_checked`: obligations pass and bind current hashes, without coverage
  binding.
- `human_attested`: a protected human attestation binds the current snapshot.
- `excluded_with_reason`: a closed reason enum, issue link, and expiry are present.
  This is the only tier in which an active waiver may exist, and every waiver and
  expiry is enumerated in the certificate.

A `void night` is a nightly run whose failure is classified outside the sealed
check boundary by named preflight predicates, such as runner provisioning,
checkout, or toolchain installation, and has a checksummed failure artifact. It
neither advances nor resets the streak. A failure inside a sealed check is a
check-failure night.

An `organic merge` is a protected-branch merge during the streak window that was
not authored by the certification tooling. An `anchor` is an append-only store
outside both candidate repositories that holds nightly rows and certificates;
verifiers check its hash-chain continuity and timestamps.

### 11.2 Certificate A: Sync Integrity

The following predicate is evaluated independently for the repository set being
certified:

```text
ledger_generated_and_drift_checked == true
checker_wheel_digest == protected_expectations.checker_digest
verifier_wheel_digest == protected_expectations.verifier_digest
reference_verifier_accepts == true
nightly_rows_anchored == true

unaccounted_tracked_paths == 0
every_candidate_classified == true
expected_managed_units >= protected_expectations.managed_floor
denominator_reductions_without_tombstone_ref == 0

every_managed_unit_in_exactly_one_tier == true
machine_verified_pct >= protected_expectations.floor_pct
machine_verified_pct >= previous_certificate.machine_verified_pct
waivers_outside_excluded_tier == 0

boundary_mode == enforce
mutators_outside_canonical_apis_detected == 0

required_lifecycle_rows_passed == 18 of 18
seeded_mutation_batch_injected_per_night >= 25
seeded_mutation_batch_detected == seeded_mutation_batch_injected
post_repair_rerun_writes == 0
post_recovery_rerun_writes == 0
post_merge_tree_changes == 0

qualifying_consecutive_utc_nights == 7
organic_merges_during_streak >= 5
check_failure_nights == 0
void_nights_in_window <= 2
```

The separately released reference verifier must share no code with
`pdd.sync_core`, and the certificate schema must be documented. The boundary mode
and all predicates are evaluated at the exact protected merge-group SHA. Seeded
mutation runs publish their seed in the certificate.

The `floor_pct` starts at the measured `machine_verified_pct` of the first
Certificate A. It may only increase through protected-expectations PRs as gate-6
coverage work lands. The previous-certificate comparison is a non-regression
ratchet. A void night requires the named preflight classification and checksummed
failure artifact; a third void night invalidates the current window.

### 11.3 Certificate B: Global Sync

Certificate B retains this plan's Definition of Done unchanged in intent and adds
the terminal machine-coverage predicate:

```text
certificate_A_holds_for == {pdd, pdd_cloud}
evidence_gates_passed == 10 of 10
machine_verified_pct == 100
human_attested_units == 0
excluded_with_reason_units == 0
current_machine_evidence_coverage == 100
pdd_cloud_vendored_sync_semantics == 0
real_pdd_cloud_canary == PASS
```

The global sync epic may close only when all conditions below hold with attached
commands, exact commit SHAs, reports, anchored nightly rows, and both verifier
results.

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

### 11.4 Injection and verification contract

All injections run in ephemeral clones or sandboxes; protected branches never
receive injected faults. The matrix includes:

- Prompt, include, code, test, and simultaneous edits.
- Missing, corrupt, renamed, deleted, chmod-only, and retargeted artifacts.
- Process death at every transaction phase, recovery to a complete old or new
  state, and a zero-write rerun.
- Concurrent sync and external-write races, including symlink swaps at commit.
- Forged, stale, replayed, and revoked evidence, plus a vacuous-obligation case in
  which an import-only test must not yield `machine_verified`.
- Candidate tampering and merge-group base movement.
- Source and installed-wheel execution; real-browser execution only when a
  protected profile demands it.
- A seeded randomized mutation batch whose seed is published in the certificate.

The release assertions are:

```bash
pdd sync certify \
  --certificate-class integrity \
  --repos pdd \
  --merge-group "$PROTECTED_MERGE_GROUP_SHA" \
  --full-inventory \
  --run-lifecycle-matrix \
  --run-seeded-mutation-batch \
  --require-nightly-streak 7 \
  --require-organic-merges 5 \
  --nightly-anchor "$PROTECTED_ANCHOR_URI" \
  --output sync-integrity-certificate.json

python -m pdd.sync_core.certificate_verifier \
  --certificate sync-integrity-certificate.json \
  --expectations "$PROTECTED_EXPECTATIONS"

pdd-sync-reference-verifier \
  --certificate sync-integrity-certificate.json \
  --expectations "$PROTECTED_EXPECTATIONS"
```

All three commands must exit 0. Repeat the same Certificate A sequence with
`--repos pdd,pdd_cloud`. Certificate B uses the two-phase sequence below rather
than repeating the three commands directly:

1. Produce an immutable `--certificate-class global` candidate payload carrying
   completed evidence for gates 1-9.
2. Run the primary and reference verifiers and persist their signed results.
3. Bind the Sol HIGH adversarial review to the exact payload digest and repository
   SHAs.
4. Run a separately released, digest-pinned `pdd-sync-certificate-finalizer`. It
   binds the payload, both verifier-result digests, and review digest; signs a
   detached gate-10 evaluation; and cannot read candidate-controlled input.
5. Run both verifiers again against the unchanged payload plus detached evaluation.
   Each must validate the protected finalizer wheel digest and signer identity,
   evaluation signature, all bound phase-one digests, and the final 10/10 result.

The canonical exact command sequence and required output predicates are
`steps[9].validation_commands` and `steps[9].required_predicate` in
`docs/global_sync_evidence_ledger.yaml`; this narrative cannot authorize a shorter
Certificate B path.

Any unclassified unit, unpinned denominator reduction, missing, stale, or forged
evidence, undetected injected violation, vacuous obligation qualifying as
`machine_verified`, check-failure night, third void night, ratchet regression,
active waiver outside the excluded tier, unexpected write, candidate-sourced
verifier input, unpinned finalizer, altered phase-one result, or invalid closure
envelope must produce a nonzero exit.

Every certificate carries this claim verbatim:

> This certificate proves the sync system's integrity: complete honest inventory,
> active enforcement, transactional recovery, evidence trust at standard_framework
> assurance, 100% detection of injected violation classes, and stability under
> real merge traffic. For machine_verified units it proves obligations executed
> and passed against current artifact hashes with bound coverage. It does not claim
> obligations exhaust prompt intent. The claim is "synchronized and honestly
> accounted", not "semantically equivalent".

Gate 10's adversarial review evaluates Certificate A at its release milestone and
Certificate B at epic close. Certificate B, not Certificate A, closes the epic.
Certificate A review binds its exact certificate digest and repository SHAs but
does not mark gate 10 complete.

Gate 10 closes in two non-recursive phases. Phase 1 produces an immutable
Certificate B candidate payload after gates 1-9, runs both released verifiers, and
binds the adversarial review to that exact payload digest and repository SHAs.
Only after those three approvals does a protected, independently released and
digest-pinned finalizer count gate 10 and emit a detached signed evaluation showing
10/10. The finalizer binds the candidate payload, both verifier-result digests, and
adversarial-review digest; its signer identity is protected expectation. Both
verifiers then validate the unchanged payload and detached evaluation, including
the finalizer identity, evaluation signature, and every phase-one digest. Thus
`evidence_gates_passed == 10 of 10` is an evaluator result, not a self-assertion in
the payload being reviewed.

For both certificate classes, the verifier invocation binds protected digests for
expectations, trusted issuer material, and anchor configuration, plus a trusted
time source and protected expected repository identities and SHAs. The verifier
predicate requires `candidate_controlled_verifier_inputs == 0`.

## 12. Immediate next actions

1. Preserve #2213 and #2216 as historical prerequisite evidence. Gate 1 PR
   [#2214](https://github.com/promptdriven/pdd/pull/2214) was reviewed at
   `6301d6c613199604702c2c3242fc8b837960d586`, passed Unit run
   [29674097485](https://github.com/promptdriven/pdd/actions/runs/29674097485)
   (job [88158086892](https://github.com/promptdriven/pdd/actions/runs/29674097485/job/88158086892)),
   Package job [88158086891](https://github.com/promptdriven/pdd/actions/runs/29674097485/job/88158086891),
   [CodeQL run 29674096680](https://github.com/promptdriven/pdd/actions/runs/29674096680),
   [heal run 29674097086](https://github.com/promptdriven/pdd/actions/runs/29674097086),
   and [auto-heal 88158092713](https://github.com/promptdriven/pdd/runs/88158092713),
   then merged as `63bf4dd789d65a9cf4b08f5b39886d0cdda5e0ee`. This advances
   Machine promotion records only Gate 1 `implemented`, `hosted_green`, and
   `merged`: local and independent-review narrative evidence remains
   in-progress until a distinct protected verifier can prove those dimensions.
   The global score remains `0/10` and no release or certificate is claimed.
2. Treat #2223 and #2224 as merged prerequisites only, and preserve closed,
   unmerged #2225 as diagnostic evidence that cannot advance Gate 2. The single
   canonical blocker is `gate2-standalone-checker-package-boundary`; its
   same-day deliverable, bounded to under 24 hours, is the standalone checker
   extraction manifest/package-boundary PR: a non-`pdd` top-level package with
   checker-only dependencies, strict lock/RECORD salvage, and the exact z3
   compatible-wheel regression. It does not release, containerize, or certify.
3. Only after that boundary is released may the sealed Git-capable OCI runtime
   and protected checker/OCI/workflow expectation pins be pursued. Certificate A
   and Certificate B intent is unchanged; neither is claimed by these layers.
4. Before gate 5 completes, generate the 467-unit gate-6 coverage partition and
   obtain the required human scoping decision.
