# Global Sync M0 Scope and Sample Evidence

Status: **RED — evidence only. No migration, promotion, denominator reduction,
or production metadata mutation is authorized.**

Date: 2026-07-24 (America/Los_Angeles)

This report records a reproducible, read-only M0 sample run against these exact
inputs:

| Input | Commit |
| --- | --- |
| PDD base | `315f03def92d160024190c57d2bed525ab976e38` |
| pdd_cloud provenance input | `09f9d3fea71c4c0ed6655f2acd5e95b14a32c3c8` |

The committed verifier is
`scripts/verify_global_sync_m0_samples.py`. Its deterministic result is
[`global_sync_m0_sample_results.json`](global_sync_m0_sample_results.json);
the host-dependent timings and RSS measurements are in
[`global_sync_m0_sample_metrics.json`](global_sync_m0_sample_metrics.json).
The pdd_cloud input is resolved by the verifier for provenance; this M0 sample
does not mutate or promote either repository.

## Exact recorded artifacts

The checked-in artifacts are byte-for-byte copies of the successful recorded
run:

| Artifact | SHA-256 |
| --- | --- |
| `docs/global_sync_m0_sample_results.json` | `6b8e06aab1cec387c418cb5566ca62d846391e2c972362e7e3fe4dd82a64f52f` |
| `docs/global_sync_m0_sample_metrics.json` | `1c489a5bada0bf02df630a832ec3be728ee4308e55d52de6b0d93a657cbf0454` |

The primary result is deterministic for the fixed source inputs. Metrics are
intentionally separate because elapsed time and peak RSS are host-dependent;
their recorded checksum identifies this particular execution, not a timing
threshold or a success criterion.

The result inventory records 469 profiles and 469 managed units. Of the
profiles, 465 are human-attestation-only; the conservative classification is
220 derivable, 26 missing-tests, and 219 ownership-or-scope. These counts
preserve the current denominator. They do not establish semantic test coverage
or authorize a coverage waiver.

The explicit default remains to retain all 469 expected-managed units. The 219
ownership-or-scope units require a protected ownership, validator, or future
decommission decision; absence of that decision does not reduce the
denominator.

## Reproduction and validation

The following command creates clean detached source checkouts, runs the
committed verifier, validates the resulting structure, prints checksums, and
proves that the two source checkouts remain unchanged. It intentionally writes
the two artifacts into the documentation checkout from which it is invoked.

```bash
set -eu
base_sha=315f03def92d160024190c57d2bed525ab976e38
cloud_sha=09f9d3fea71c4c0ed6655f2acd5e95b14a32c3c8
source_root="$(mktemp -d /tmp/pdd-global-sync-m0.XXXXXX)"
artifact_root="$(pwd)"
trap 'rm -rf "$source_root"' EXIT

git clone --quiet https://github.com/promptdriven/pdd.git "$source_root/pdd"
git -C "$source_root/pdd" checkout --quiet --detach "$base_sha"
git clone --quiet https://github.com/promptdriven/pdd_cloud.git "$source_root/pdd_cloud"
git -C "$source_root/pdd_cloud" checkout --quiet --detach "$cloud_sha"

env -u VIRTUAL_ENV -u PYTHONHOME -u PYTHONPATH -u PDD_PATH \
  PDD_NO_AUTO_UPDATE=1 /opt/homebrew/Caskroom/miniforge/base/envs/pdd/bin/python \
  "$source_root/pdd/scripts/verify_global_sync_m0_samples.py" \
  --root "$source_root/pdd" \
  --base-sha "$base_sha" \
  --closure-limit 20 \
  --pdd-cloud-root "$source_root/pdd_cloud" \
  --pdd-cloud-sha "$cloud_sha" \
  --output "$artifact_root/docs/global_sync_m0_sample_results.json" \
  --metrics-output "$artifact_root/docs/global_sync_m0_sample_metrics.json"

jq -e '
  .base_sha == "315f03def92d160024190c57d2bed525ab976e38" and
  .pdd_cloud_sha == "09f9d3fea71c4c0ed6655f2acd5e95b14a32c3c8" and
  (.cases | length) == 10 and
  (.closure.requested == 20 and .closure.completed == 20)
' "$artifact_root/docs/global_sync_m0_sample_results.json"
jq -e '
  .base_sha == "315f03def92d160024190c57d2bed525ab976e38" and
  .deterministic_report_bytes == 8586
' "$artifact_root/docs/global_sync_m0_sample_metrics.json"
shasum -a 256 \
  "$artifact_root/docs/global_sync_m0_sample_results.json" \
  "$artifact_root/docs/global_sync_m0_sample_metrics.json"
git -C "$source_root/pdd" diff --exit-code
test -z "$(git -C "$source_root/pdd" status --porcelain)"
git -C "$source_root/pdd_cloud" diff --exit-code
test -z "$(git -C "$source_root/pdd_cloud" status --porcelain)"
```

The verifier creates a separate temporary shared clone for candidates. It
commits each profile and ownership candidate inside that temporary clone so
the public APIs can inspect the candidate commit. It also writes and reads the
fingerprint candidate there. The verifier deletes that clone before returning;
the detached PDD and pdd_cloud source checkouts above are not modified. The
working documentation checkout receives only the two requested evidence files.

The older legacy `pdd sync --dry-run` zero-discovery experiment is historical
negative CLI evidence and is superseded for M0 candidate validation by this
committed verifier. It is not a migration result and is not used below.

## Candidate outcomes

All ten outcomes below are direct fields from
`global_sync_m0_sample_results.json`. “Rejected” is the required fail-closed
result for the eight profile candidates and the ownership candidate. The one
accepted fingerprint is accepted only for public-API serialization and
round-trip under semantic `UNKNOWN`; it is not trusted evidence.

| ID | Kind | Sample path | Public-API outcome |
| --- | --- | --- | --- |
| `01-profile` | profile | `pdd/prompts/commands/checkup_python.prompt` | `rejected-by-public-profile-api` |
| `02-profile` | profile | `pdd/prompts/sync_main_python.prompt` | `rejected-by-public-profile-api` |
| `03-profile` | profile | `pdd/prompts/core/cli_python.prompt` | `rejected-by-public-profile-api` |
| `04-profile` | profile | `pdd/prompts/sync_orchestration_python.prompt` | `rejected-by-public-profile-api` |
| `05-profile` | profile | `pdd/prompts/Makefile_makefile.prompt` | `rejected-by-public-profile-api` |
| `06-profile` | profile | `pdd/prompts/auto_deps_main_python.prompt` | `rejected-by-public-profile-api` |
| `07-profile` | profile | `pdd/prompts/ci_detect_changed_modules_python.prompt` | `rejected-by-public-profile-api` |
| `08-profile` | profile | `pdd/prompts/frontend/components/DependencyViewer_typescriptreact.prompt` | `rejected-by-public-profile-api` |
| `09-ownership` | ownership | `.pdd/sync-ownership.json` | `rejected-by-public-manifest-api:ManifestError` |
| `10-fingerprint` | fingerprint | `pdd/prompts/_keyring_timeout_python.prompt` | `accepted-by-public-fingerprint-api-semantic-unknown` |

The profile candidates are intentionally rejected by
`load_verification_profiles`; the ownership candidate is intentionally
rejected by `build_unit_manifest` with `ManifestError`. Neither rejection
is a migration success. The fingerprint candidate round-trips through
`FingerprintStore`, but its semantic status is `UNKNOWN`, so it is neither
attested nor a promotion signal.

The result artifact also records the binary patch size and SHA-256 for every
candidate. Those patch bytes are transient verifier evidence, not checked-in
production metadata.

## Twenty-closure sample and measurements

The closure run requested 20 valid unit snapshots and completed all 20. It
continued past 40 invalid closures, which the result artifact records
individually. Those invalid entries include required includes that are absent
and unapproved managed symlinks; they are data/closure findings, not evidence
that a candidate passed.

| Measurement | Recorded value |
| --- | ---: |
| Inventory elapsed time | 25.497711 s |
| Inventory peak RSS | 320,733,184 B |
| Inventory subprocess calls | 1,086 |
| Closure elapsed time | 2.323471 s |
| Closure peak RSS | 320,733,184 B |
| Closure subprocess calls | 120 |
| Deterministic report size | 8,586 B |

The verifier measures elapsed time with `time.perf_counter()`, RSS with
`resource.getrusage(RUSAGE_SELF).ru_maxrss`, and subprocess calls by counting
normal `subprocess.run` calls. These figures describe one uncached,
read-only run; they do not establish a performance service-level objective.

## Historical fixed-source classification benchmarks

The following benchmark evidence predates the committed M0 sample verifier and
is retained as supplemental, historical evidence. It was measured from a
disposable detached PDD checkout at
`d8423f5fcc1b22583f8262b994cf3f154a128b8b`, with
`2c1b5adacc164e62f62a18a12043285b88bebb26`
(`fix(sync): support package-local report module identities`) cherry-picked
locally. The resulting temporary commit was recorded as `4a4b7eb17`. The
temporary checkout was not production state. The new verifier's
315f03def inventory and closure measurements supplement these results; they do
not claim to reproduce the full canonical classification or module-filter
benchmark.

| Historical case | Result | Time | Peak RSS | Subprocess calls | Report size |
| --- | --- | ---: | ---: | ---: | ---: |
| Full canonical inventory/classification (`build_canonical_report`) | completed, exit 0: 469 units; 469 complete profiles; no profile/manifest mismatch | 42.371 s | 317,390,848 B | 2,028 | 118,200 B |
| Representative package-local module filter (`commands/checkup`) | completed, exit 0: one selected `pdd/prompts/commands/checkup_python.prompt`; package-local module identity works | 22.910 s | 310,329,344 B | 1,092 | 961 B |

The historical full report was red because the external attestation replay
ledger was not configured, not because of a loader crash or denominator gap.
It recorded 206 drifted, 262 unbaselined, 263 unknown, 205 failed, one
conflict, zero corrupt, and zero trusted/current evidence, with `ok=false`.
The module filter was run from the temporary checkout with
`VIRTUAL_ENV`, `PYTHONHOME`, `PYTHONPATH`, and `PDD_PATH` unset;
provenance identified `pdd.sync_core.reporting` from the fixed source and
showed that `_module_identity` accepted both `prompts` and `pdd/prompts`.
These are historical recorded observations, not a claimed execution of the
new verifier.

## pdd_cloud canary selection

The selected M1 canary is
`extensions/github_pdd_app/prompts/Dockerfile_webhook_Dockerfile.prompt`.
At `09f9d3fea71c4c0ed6655f2acd5e95b14a32c3c8`, its closure includes the
sibling `src/webhook_app_Python.prompt`; the extension has `.pddrc`,
`architecture.json`, the generated `Dockerfile.webhook`, metadata file
`.pdd/meta/Dockerfile_webhook_dockerfile.json`, `requirements.txt`, and
`src/webhook_app.py`. Its architecture entry maps the prompt to
`Dockerfile.webhook` and declares the webhook dependency. This crosses a
Dockerfile artifact, a Python runtime dependency, architecture ownership, and
deployment-facing configuration without selecting the whole consumer
repository.

No consumer mutation is authorized. At that SHA, the detached consumer
checkout has no discoverable `.pdd/verification-profiles.json`,
`.pdd/expected-managed.json`, or repository-id entry; its `.pdd` state is
not the protected canonical profile, ownership, and evidence surface required
by M1. The PDD sampling evidence does not authorize changes to the consumer's
prompt, Dockerfile, metadata, or upstream interface.

## Historical release and access inventory

This inventory is retained from the prior scope report. It is limited to the
recorded observations below, does not inspect secret values, and was not rerun
by the committed M0 sample verifier.

| Capability | Observation | Milestone effect |
| --- | --- | --- |
| Package index | `python -m pip index versions pdd-cli` reached PyPI; latest listed `0.0.308`, installed `0.0.305.dev253` | Read access works; publish authority was not tested |
| Release workflow | `.github/workflows/release.yml` uses protected `pypi-test-publish` and `pypi-publish` environments, PyPI trusted publishing, and attestations | Protected publish is external; no mutation authorized |
| OCI registry / local engine | `docker version` failed: `command not found: docker` | OCI build, push, and deployment dependent milestones blocked locally |
| Protected environment | GitHub CLI authenticated to `github.com`; PDD branch-protection query returned 200 and shows `auto-heal` required with admins enforced. pdd_cloud's branch-protection endpoint returned 403 with the repository-plan limitation message | PDD control is observable; pdd_cloud protection cannot be audited through this endpoint |
| Staging cloud context | `gcloud config configurations list` reported an active account configured to staging project `prompt-driven-development-stg` | Configuration only; no `gcloud` action, deployment, or credential inspection performed |
| Signer | Only non-secret PDD runtime configuration names were present (`PDD_DETERMINISTIC_PIPELINE`, Playwright limits); no signer command or key environment name was present | Protected attestation signing unavailable locally |
| Anchor | No local `.pdd` filename matching anchor, trust, signer, key, attestation, or certificate was found by the recorded search | Trusted anchor must be supplied by protected CI or a reviewed external control plane |
| pdd_cloud | `git ls-remote` and clean clone at `09f9d3fea71c4c0ed6655f2acd5e95b14a32c3c8` succeeded | Read access works; no consumer mutation attempted |

Credential discovery listed variable names only and did not read or print
their values. The GitHub CLI output was redacted before inspection. Missing
package publishing, OCI, signer, and trust-anchor credentials block their
dependent milestones; they do not block local M1 engineering.

## Exit statement

M0 remains red. The evidence establishes only that the committed verifier can
reproduce the recorded partition, exercise ten candidate paths through public
APIs, fail closed on unauthorized profile and ownership changes, round-trip one
`UNKNOWN` fingerprint, and obtain twenty valid closures while recording invalid
ones. It does not authorize migration success, metadata promotion, consumer
mutation, trusted verification, or a denominator reduction.

Integrity checks for this documentation change:

```bash
jq -e . docs/global_sync_m0_sample_results.json
jq -e . docs/global_sync_m0_sample_metrics.json
shasum -a 256 docs/global_sync_m0_sample_results.json docs/global_sync_m0_sample_metrics.json
git diff --check
```
