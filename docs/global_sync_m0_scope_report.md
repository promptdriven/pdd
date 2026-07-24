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

For every row below, the exact attempted interface was:

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

The closest current canonical mutation command is also deliberately
non-repairing:

```bash
python -m pdd reconcile --help
# --heal: Deprecated; blind fingerprint acceptance is disabled.
```

`python -m pdd validate --help` accepts only a module plus protected base/head
and validators; it exposes no generate-to-staging patch option. Therefore no
current command can safely generate and validate the requested migration
patches. M0 remains red until a staging repair executor can create an explicit
patch/plan, validate its closure, and prove a zero-write rerun. No hand-edited
profile patch was substituted for that missing product interface.

## 3. Read-only scale benchmarks

All timings use `time.perf_counter()`, and peak RSS is
`resource.getrusage(RUSAGE_SELF).ru_maxrss` (bytes on this macOS host).
`subprocess.run` was monkey-patched only to count calls; the measured code
still executed its normal subprocesses. JSON report size is the compact,
sorted byte length of the in-memory payload described in the command.

| Case | Result | Time | Peak RSS | Subprocess calls | Report size |
| --- | --- | ---: | ---: | ---: | ---: |
| Full read-only inventory (`build_unit_manifest`) | completed: 469 managed/expected, 3,114 candidates, zero invalid/unaccounted | 5.194 s | 316,440,576 B | 16 | 151 B summary |
| Full canonical inventory/classification (`build_canonical_report`) | **not completed** before the local execution harness ended the 28–30 s attempt; no report emitted | >28 s, incomplete | not captured | not captured | none |
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
classification pass.

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
side also lacks the staging patch executor demonstrated above. Altering the
consumer's prompt, Dockerfile, metadata, or upstream interface before those
boundaries exist would create unvalidated production state.

## 5. Release and access inventory (no secret values inspected)

| Capability | Observation | Milestone effect |
| --- | --- | --- |
| Package index | `python -m pip index versions pdd-cli` reached PyPI; latest listed `0.0.308`, installed `0.0.305.dev253` | Read access works; publish authority was not tested |
| Release workflow | `.github/workflows/release.yml` uses protected `pypi-test-publish` and `pypi-publish` environments, PyPI trusted publishing, and attestations | Protected publish is external; no mutation authorized |
| OCI registry / local engine | `docker version` failed: `command not found: docker` | OCI build/push/deployment dependent milestones blocked locally |
| Protected environment | GitHub CLI authenticated to `github.com`; reported scopes include `repo` and `workflow` | Read/push capability may exist; branch protection/environment administration was not exercised |
| Signer | Only non-secret PDD runtime configuration names were present (`PDD_DETERMINISTIC_PIPELINE`, Playwright limits); no signer command/key env name was present | Protected attestation signing unavailable locally |
| Anchor | No local `.pdd` filename matching anchor/trust/signer/key/attestation/certificate was found by the recorded search | Trusted anchor must be supplied by protected CI or a reviewed external control plane |
| pdd_cloud | `git ls-remote` and clean clone at `09f9d3f…` succeeded | Read access works; no consumer mutation attempted |

Credential discovery intentionally listed variable names only and did not read
or print their values. The GitHub CLI output was redacted before inspection.
Missing package publishing, OCI, signer, and trust-anchor credentials block
only their dependent milestones; they do not block local M1 engineering.

## Exit criteria and integrity checks

M0 early-scope/scale is not promotable. Its blockers are: no migration patch
executor/validator, zero-unit legacy dry runs for all ten samples, invalid
include closures, incomplete full canonical classification benchmark, a
469-unit manifest versus 468-profile registry mismatch, and missing consumer
canonical controls. The recommended M0 action is to keep this work red and
build the command-contract and staging-repair interfaces; do not hide the gap
through a coverage waiver or denominator reduction.

Report integrity was checked with:

```bash
git diff --check
git diff -- docs/global_sync_m0_scope_report.md
```
