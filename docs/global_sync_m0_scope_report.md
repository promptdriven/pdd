# Global Sync M0 Scope and Scale Report

Status: **RED — evidence only; no denominator reduction and no production
metadata mutation are authorized.**

Date: 2026-07-24 (America/Los_Angeles)

PDD protected head: `abd9726bddbdb04e9889fbf14f751cb126d7cf23`
pdd_cloud protected head: `09f9d3fea71c4c0ed6655f2acd5e95b14a32c3c8`

This report implements the non-production sampling requested by section 3.4
of `docs/global_sync_resolution_plan.md`.  Commands used the PDD Conda Python
at `/opt/homebrew/Caskroom/miniforge/base/envs/pdd/bin/python` and disposable,
clean, detached clones for every PDD or pdd_cloud checkout that was inspected
or exercised. No sample clone was committed, and no tracked production file
was changed.

## Evidence summary

`git fetch origin main && git rev-parse origin/main` returned the PDD SHA above.
`git ls-remote https://github.com/promptdriven/pdd_cloud.git refs/heads/main`
returned the pdd_cloud SHA above. The two clean-clone `git status --porcelain`
checks were empty before sampling. The PDD sample clone finished with
`git diff --exit-code` status 0 and zero status lines.

The registry and current canonical inventory disagree with stale historical
counts:

| Current protected input | Count | Interpretation |
| --- | ---: | --- |
| `.pdd/verification-profiles.json` profiles | 468 | Registry entries at this SHA |
| Human-attestation-only profiles | 465 | Current human-only population |
| Machine-obligation profiles | 3 | The remaining registry profiles |
| Expected managed units from `build_unit_manifest` | 469 | Current denominator; it is one greater than the profile registry |
| Managed units from `build_unit_manifest` | 469 | No unaccounted paths or manifest invalid reasons |

The older `docs/global_sync_pdd_adapter_demand.json` value of 467 human-only
profiles is not current-state evidence for this SHA. This report does not edit
that historical evidence.

## 1. Human-attestation-only partition

The 465 profiles were partitioned by a deliberately conservative, reproducible
path rule. For a profile prompt `pdd/prompts/<relative>/<stem>_<language>.prompt`:

1. **Derivable from existing tests** means that either
   `tests/<relative>/test_<stem>.py` or `tests/test_<stem>.py` exists.
2. **Genuinely missing tests** means `language_id == python`,
   `pdd/<relative>/<stem>.py` exists, and neither test path exists.
3. **Ownership/scope decision** is the remainder. This includes non-Python
   generated artifacts and Python prompts whose output/test ownership cannot be
   established by that mechanical rule.

This is an inventory classification, not a claim that a matching filename
proves semantic coverage.

| Partition | Count | Examples | Estimated next effort |
| --- | ---: | --- | --- |
| Derivable obligations | 220 | `agentic_architecture_python`, `agentic_bug_python`, `sync_main_python` | 2–4 engineer-weeks to bind existing tests to requirements and review false matches |
| Genuinely missing tests | 26 | `_keyring_timeout_python`, `checkup_file_selection_python`, `commands/contracts_python` | 2–3 engineer-weeks to write and stabilize tests |
| Ownership/scope decision | 219 | `Makefile_makefile`, `agentic_arch_step10_completeness_LLM`, frontend TypeScript/TSX prompts | one product/ownership decision first; then 4–10 engineer-weeks depending on which non-code artifacts remain expected-managed |
| Total | 465 | all current human-only profiles | — |

Language distribution in the human-only set was Python 234, LLM 160,
TypeScript React 51, TypeScript 7, CSV 3, Bash 2, and one each of Makefile,
prompt, Fish, Zsh, JSON, reStructuredText, TOML, and log. The two Python
partitions total 246 because 12 Python units fall in the scope-decision
remainder (their ownership cannot be established from the rule above).

Recommended default: preserve all **469** expected-managed units. Do not
reduce the denominator based on filename heuristics or this sample. The only
requested human decision is whether the 219 scope-decision units should receive
machine validators, explicit protected human ownership, or a future protected
decommission record. Silence means no denominator reduction, as required by
the plan.

## 2. Disposable migration samples

One fresh clone was created and detached at the PDD protected SHA:

```bash
sample_root=$(mktemp -d /tmp/pdd-m0-samples.XXXXXX)
git clone --quiet https://github.com/promptdriven/pdd.git "$sample_root/pdd"
git -C "$sample_root/pdd" checkout --quiet --detach \
  abd9726bddbdb04e9889fbf14f751cb126d7cf23
```

The first attempted interface (kept as negative evidence) was:

```bash
PDD_NO_AUTO_UPDATE=1 /opt/homebrew/Caskroom/miniforge/base/envs/pdd/bin/python \
  -m pdd sync '<sample path>' --dry-run --json --skip-verify
```

Each invocation returned exit code 0 but emitted the same unusable result:
`ok=false`, `summary.total=0`, `summary.failures=0`, and `units=[]`. It wrote
no patch or staged output. This is **not a pass**: a zero exit from a dry run
that discovered zero units cannot validate a migration. The final clone check
was `git diff --exit-code` = 0 and `git status --porcelain | wc -l` = 0.

| # | Required stressor | Sample path | Outcome |
| ---: | --- | --- | --- |
| 1 | Nested config | `examples/template_example/prompts/main_python.prompt` | no discovered unit; no patch |
| 2 | Include closure | `pdd/prompts/sync_main_python.prompt` | no discovered unit; no patch |
| 3 | Duplicate basename | `pdd/prompts/core/cli_python.prompt` (`cli` also exists outside `core`) | no discovered unit; no patch |
| 4 | Human-owned test | `tests/test_sync_core_adapter_demand_verifier.py` | no discovered unit; no patch |
| 5 | Multi-file example/test | `pdd/prompts/sync_orchestration_python.prompt` | no discovered unit; no patch |
| 6 | Executable artifact | `pdd/prompts/Makefile_makefile.prompt` | no discovered unit; no patch |
| 7 | Architecture override | `pdd/prompts/agentic_architecture_python.prompt` | no discovered unit; no patch |
| 8 | Runtime dependency | `pdd/prompts/auto_deps_main_python.prompt` | no discovered unit; no patch |
| 9 | Historically problematic unit | `pdd/prompts/ci_detect_changed_modules_python.prompt` | no discovered unit; no patch |
| 10 | Cross-language output branch | `pdd/prompts/frontend/components/DependencyViewer_typescriptreact.prompt` | no discovered unit; no patch |

The ninth sample was selected because its prompt has been part of reviewed
global-sync transition history; `sync_main_python` also has historical
include/reverse-include fixes. The tenth prevents the sample from silently
being Python-only.

This negative result is not the M0 migration sample. It establishes only that
the legacy artifact-sync CLI is not the profile/inventory migration interface.

### Candidate profile, ownership, and fingerprint patches

The remediation sample used a new disposable, exact-SHA shared clone and a
custom ephemeral Python script. The script did **not** invoke an LLM, use a
remote mutation, or write the PDD worktree. It constructed one candidate test
obligation per row against the profile's existing requirement IDs, wrote each
individual unified diff under the ephemeral clone root, then committed the
combined candidate only inside that disposable clone. The generated patch
paths are under
`/var/folders/5z/6xlxcqg50c1f8wjr3fkx6pyw0000gn/T/pdd-m0-profile-batch.voj27cko/patches/`.
They are evidence artifacts, not production metadata.

| # | Candidate patch | SHA-256 | Bytes | Schema / manifest / canonical outcome |
| ---: | --- | --- | ---: | --- |
| 1 | `01-nested-config.profile.patch` | `6b461b746806efdac89a2b5ac45378289f35f720a00e41c092c9f2e890dbe2aa` | 1,035 | obligation schema accepted; profile is not a current manifest profile |
| 2 | `02-include-closure.profile.patch` | `252859041e746df66c63ffe8ba726d98672c1d6cd30f0ea26e8584a0e2d1d032` | 795 | obligation schema accepted; candidate canonical-profile result not promotable |
| 3 | `03-duplicate-basename.profile.patch` | `0b31a38abc0166e2485a1fa9dfec6e1fcf26ca71ac75663c1702504048e98dc6` | 820 | obligation schema accepted; canonical path remains explicit (`core/cli`) |
| 4 | `04-human-owned-test.profile.patch` | `41c2891c3071f4819d53bca77c86a8e78004e3ce73eaa13ea7f19d1ff1cfe8b6` | 875 | obligation schema accepted; ownership candidate separately rejected |
| 5 | `05-multi-file-example-test.profile.patch` | `0f371da9c798614328ac57848f087ee34c4842011db916b44dfaf2b3f4a5d71f` | 822 | obligation schema accepted; candidate canonical-profile result not promotable |
| 6 | `06-executable-artifact.profile.patch` | `3224cccaeac08f0e60980be373719345c6c625fd2c909283ee052ac945a4e250` | 821 | obligation schema accepted; test/artifact binding remains a scope decision |
| 7 | `07-architecture-override.profile.patch` | `ba961e299df6464e3fbe1cf32907ed209874df148803608580c39d12f80e6164` | 826 | obligation schema accepted; candidate canonical-profile result not promotable |
| 8 | `08-runtime-dependency.profile.patch` | `178a481e43929d335729ca56be30ebc1402676f1602d84fd58d8b102abf416c0` | 810 | obligation schema accepted; closure is separately invalid (`context/utils.py`) |
| 9 | `09-historical-problem.profile.patch` | `21f1fb51541cba8e45d236f29e1c18f9045132c4e9585fc259bba776b88c5baa` | 832 | obligation schema accepted; candidate canonical-profile result not promotable |
| 10 | `10-typescript-output.profile.patch` | `8bafaec90fb4eeb53ef98396ac99be433ca09d5a7516ba85c1febe3c3d29cb8e` | 881 | obligation schema accepted; cross-language policy remains a scope decision |

Exact validation commands and outcomes:

```bash
# all ten generated obligations parsed through the existing profile parser
python -c 'from pdd.sync_core.verification import _obligation; ...'
# schema_obligations_valid=10

# combined ownership candidate, detached exact-SHA clone
build_unit_manifest(root, base_ref=BASE, head_ref=CANDIDATE)
# ManifestError: protected ownership rule has duplicate pattern:
# tests/test_sync_core_adapter_demand_verifier.py

# profile-only candidate, detached exact-SHA clone
build_unit_manifest(...); load_verification_profiles(...)
# manifest completed; the loader terminated the local process with no result
# before the 300-second alarm or a JSON result could be emitted.
```

The ownership result is fail-closed and is the expected evidence that a
candidate cannot self-grant a duplicate protected ownership rule. The profile
parser accepted all ten obligation structures, but the full candidate loader
did not produce a pass/fail result in this environment; this is recorded as
**inconclusive and not a pass**, not as an authorization to merge the patches.
The profile and ownership candidate clones ended clean after their local
candidate commit. The fingerprint clone intentionally retained its untracked
candidate until read-back validation; it was never copied into production. The
production worktree remained unchanged except for this report.

One actual v2 fingerprint metadata candidate was also generated with the
existing `FingerprintStore` for the human-only
`pdd/prompts/_keyring_timeout_python.prompt`, then read back successfully:

| Artifact | Patch path | Patch SHA-256 | Bytes | Validation |
| --- | --- | --- | ---: | --- |
| Canonical v2 fingerprint | `/tmp/m0-keyring-fingerprint.patch` | `37cf3b5a588468850baa250f3d904c22f4832d6a2bb76e2f239a28ea290d5e0a` | 2,331 | `FingerprintStore.load(unit).valid == True`; semantic status remains `UNKNOWN`, with no attestation |

The underlying candidate metadata path was
`.pdd/meta/v2/fc823821c0be971fea8b0b008edf974494498716768ab30b0f365a659f0ceaa9.json`
with SHA-256 `0bf9d0074bddf2c1979d8dcb9ae240e8615a75d74d95e10baa5e5cdb144c2ddd`.
It was untracked in the disposable clone and never copied into production.
This validates metadata serialization and read-back, not trusted verification
or a denominator reduction.

M0 does **not** depend on Track A's M1 staging artifact-repair executor. The
remaining M0 sample blockers are narrower: the profile loader's abnormal
no-result behavior, the fail-closed ownership rejection, invalid include
closures, and the profile/manifest denominator mismatch.

## 3. Read-only scale benchmarks

All timings use `time.perf_counter()`, and peak RSS is
`resource.getrusage(RUSAGE_SELF).ru_maxrss` (bytes on this macOS host).
`subprocess.run` was monkey-patched only to count calls; the measured code
still executed its normal subprocesses. JSON report size is the compact,
sorted byte length of the in-memory payload described in the command.

| Case | Result | Time | Peak RSS | Subprocess calls | Report size |
| --- | --- | ---: | ---: | ---: | ---: |
| Full read-only inventory (`build_unit_manifest`) | completed: 469 managed/expected, 3,114 candidates, zero invalid/unaccounted | 5.194 s | 316,440,576 B | 16 | 151 B summary |
| Full canonical inventory/classification (`build_canonical_report`, then an equivalent alarm-bounded direct classifier) | **not completed**. A fresh clean-clone direct run was bounded with `signal.alarm(300)`, but the process ended with no result JSON/stdout/stderr before the alarm; the original foreground attempt likewise ended after 28–30 s | incomplete; no trustworthy completed time | not captured before abnormal exit | not captured before abnormal exit | none |
| First alphabetical 20-unit closure | **failed** | incomplete | not captured | not captured | none |
| Retried 20-unit affected closure | completed for 20 snapshots after recording six invalid candidates | 25.392 s | 331,677,696 B | 1,138 | 3,260 B |

The exact failed first-closure exception was:

```text
SnapshotError: cannot build unit snapshot: required include is missing: path/to/file.txt
```

The successful retry selected Python units with a mechanically matching tracked
test, continued past bad candidates, and recorded these six failures before it
found 20 valid closures:

- `agentic_architecture_orchestrator_python`: required include missing `pdd/`.`
- `agentic_change_orchestrator_python`: required include missing `pdd/`.`
- `agentic_split_orchestrator_python`: required include missing `pdd/`.`
- `agentic_sync_python`: invalid wildcard `**_): return []`
- `agentic_sync_runner_python`: invalid wildcard `**_): return []`
- `agentic_update_python`: required include missing `pdd/prompts/docs/source.md`

Thus the 20 successful snapshots demonstrate a measurable closure cost, but do
not clear the invalid include set or make the full classification benchmark
green. The full inventory result alone must not be represented as a full
classification pass. A 20-unit closure requiring 1,138 subprocesses (56.9 per
successful snapshot, including complete inventory/profile construction) is not
a practical default budget for a per-change fast path. It needs cached Git
tree/blob reads or an explicit high-cost full-scan lane before M1/M4 rollout.

The bounded full-run command was:

```bash
nohup /opt/homebrew/Caskroom/miniforge/base/envs/pdd/bin/python \
  /tmp/m0_full_benchmark.py <clean-exact-sha-clone> <result.json> &
```

The script installed a 300-second `SIGALRM`, measured `resource` peak RSS and
`subprocess.run`, and writes a partial JSON result in its timeout handler. Its
child ended without producing `result.json`, stdout, or stderr. That abnormal
termination is a benchmark failure requiring diagnosis; it is not evidence of
either completion or acceptable performance.

## 4. pdd_cloud canary selection

The real selected canary is:

```text
extensions/github_pdd_app/prompts/Dockerfile_webhook_Dockerfile.prompt
```

At `09f9d3f…`, its real closure includes the sibling
`src/webhook_app_Python.prompt`; the extension has `.pddrc`, `architecture.json`,
the generated `Dockerfile.webhook`, a metadata file
`.pdd/meta/Dockerfile_webhook_dockerfile.json`, `requirements.txt`, and
`src/webhook_app.py`. Its architecture entry maps the prompt to
`Dockerfile.webhook` and declares the webhook dependency. This is a useful M1
canary because it crosses a Dockerfile artifact, a Python runtime dependency,
architecture ownership, and deployment-facing configuration without selecting
the whole consumer repository.

No mutation is authorized yet. The detached consumer checkout has no
`.pdd/verification-profiles.json`, `.pdd/expected-managed.json`, or
repository-id entry discoverable at this SHA; its `.pdd` state is not the
protected canonical profile/ownership/evidence surface required by M1. The PDD
profile/inventory samples above do not authorize a consumer mutation. Altering
the consumer's prompt, Dockerfile, metadata, or upstream interface before
consumer controls and M1 implementation are reviewed would create unvalidated
production state.

## 5. Release and access inventory (no secret values inspected)

| Capability | Observation | Milestone effect |
| --- | --- | --- |
| Package index | `python -m pip index versions pdd-cli` reached PyPI; latest listed `0.0.308`, installed `0.0.305.dev253` | Read access works; publish authority was not tested |
| Release workflow | `.github/workflows/release.yml` uses protected `pypi-test-publish` and `pypi-publish` environments, PyPI trusted publishing, and attestations | Protected publish is external; no mutation authorized |
| OCI registry / local engine | `docker version` failed: `command not found: docker` | OCI build/push/deployment dependent milestones blocked locally |
| Protected environment | GitHub CLI authenticated to `github.com`; PDD branch-protection query returned 200 and shows `auto-heal` required / admins enforced. pdd_cloud's branch-protection endpoint returned 403 with the repository-plan limitation message | PDD control is observable; pdd_cloud protection cannot be audited through this endpoint |
| Staging cloud context | `gcloud config configurations list`; active account is configured to staging project `prompt-driven-development-stg` | Configuration only; no `gcloud` action, deployment, or credential inspection performed |
| Signer | Only non-secret PDD runtime configuration names were present (`PDD_DETERMINISTIC_PIPELINE`, Playwright limits); no signer command/key env name was present | Protected attestation signing unavailable locally |
| Anchor | No local `.pdd` filename matching anchor/trust/signer/key/attestation/certificate was found by the recorded search | Trusted anchor must be supplied by protected CI or a reviewed external control plane |
| pdd_cloud | `git ls-remote` and clean clone at `09f9d3f…` succeeded | Read access works; no consumer mutation attempted |

Credential discovery intentionally listed variable names only and did not read
or print their values. The GitHub CLI output was redacted before inspection.
Missing package publishing, OCI, signer, and trust-anchor credentials block
only their dependent milestones; they do not block local M1 engineering.

## Exit criteria and integrity checks

M0 early-scope/scale is not promotable. Its genuine blockers are the
profile-loader abnormal no-result behavior, ownership policy rejection for the
human-owned-test candidate, invalid include closures, incomplete full canonical
classification benchmarking, and the 469-unit manifest versus 468-profile
registry mismatch. The legacy `pdd sync` zero-unit runs are retained as failed
interface evidence, not blockers on an M1 repair executor. The recommended M0
action is to diagnose the canonical loader/benchmark, reconcile profile and
manifest inventory through the protected policy process, and retain the current
denominator; do not hide the gap through a coverage waiver or denominator
reduction.

Report integrity was checked with:

```bash
git diff --check
git diff -- docs/global_sync_m0_scope_report.md
```
