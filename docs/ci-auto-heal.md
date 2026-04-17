# CI Auto-Heal

## Overview

Automatically detects prompt/code/example drift in PDD modules and runs `pdd update` (for stale prompts) and `pdd sync` (for stale examples) to fix it. Pushes a `chore: auto-heal …` commit back to the triggering branch.

Runs on Google Cloud Build against the `prompt-driven-development-stg` project, authenticated as the `pdd-auto-heal-gltanaka` GitHub App so it can push to `gltanaka/pdd` without a PAT.

## Files

| Path | Role |
|---|---|
| `cloudbuild-auto-heal.yaml` | Build pipeline: loop-guard → mint-token → fetch-history → detect-modules → heal |
| `scripts/ci_detect_changed_modules.py` | Standalone module-basename extractor (reads `git diff`, returns comma-separated list) |
| `scripts/mint_github_app_token.py` | Mints installation tokens via RS256 JWT; uses `cryptography` directly (no pyjwt) |
| `pdd/ci_drift_heal.py` | Orchestrator the `heal` step invokes: classifies drift, runs pdd subprocesses, commits and pushes |
| `.github/workflows/auto-heal-drift.yml` | **Disabled** (`if: false`). Kept as the rollback path — see below |

## GCB triggers (project: `prompt-driven-development-stg`)

| Name | Event | Build config |
|---|---|---|
| `pdd-auto-heal-pr` | Pull request → `main` | `cloudbuild-auto-heal.yaml` |
| `pdd-auto-heal-push` | Push → `main` | `cloudbuild-auto-heal.yaml` |

Both pass `_GITHUB_APP_ID=3404088` as a substitution. The push trigger additionally passes `_HEAD_BRANCH=main`.

## Auth

| Layer | Mechanism |
|---|---|
| LLM calls | Vertex AI via ADC on the `cloud-build-triggers@` service account (already has `roles/aiplatform.user`) |
| GitHub push | GitHub App installation token, minted per build from the PEM in Secret Manager (`auto-heal-github-app-pem`) |

The App is installed only on `gltanaka/pdd` with `Contents: RW`, `Pull requests: RW`, `Metadata: R`. Tokens are 1-hour TTL.

## Inter-step state (`/ci-state` volume)

The pipeline shares four files between steps: `skip` (loop-guard flag), `github_token`, `modules.txt`, and `diff_base.txt`. They live on a Cloud Build `ci-state` volume mounted at `/ci-state` on every step:

```yaml
volumes:
  - name: ci-state
    path: /ci-state
```

Critical: these files **must not** live under `/workspace` because `/workspace` is the repo working directory. The heal step's `pdd.ci_drift_heal.commit_and_push()` runs `git add -A`; anything under `/workspace` gets staged into the auto-heal commit. Earlier versions of this pipeline wrote `/workspace/github_token` and **leaked four `ghs_*` installation tokens** to PR commit history (#1213). Volume mount eliminates the class entirely — the files literally cannot be staged.

Defense in depth: `.gitignore` (added in #1211) lists `github_token`, `modules.txt`, `diff_base.txt`. If anyone ever moves them back under `/workspace`, gitignore catches it before the commit.

## Budget and runtime caps

| Cap | Where | Default |
|---|---|---|
| LLM spend per build | `_PDD_BUDGET_CAP` substitution on the yaml | `5.00` USD |
| Per-subprocess wall time (`pdd sync`/`pdd update`) | `_run_pdd_command` in `ci_drift_heal.py` | 1200s |
| Total build wall time | `timeout:` in the yaml | 1800s (30 min) |

## Loop prevention

Single in-build check (GCB has no trigger-level commit-message filter):

```bash
MSG=$(git log -1 --pretty=%s)
if printf '%s' "$MSG" | grep -qE '^(\[skip ci\] )?chore: auto-heal'; then
  touch /ci-state/skip  # every downstream step checks this
fi
```

Push-to-main heal commits are also prefixed `[skip ci]` so that `pdd-ci` and any other push-triggered builds also skip them.

## Emergency disable

Either works. Prefer the first for fast rollback without a commit:

```bash
# Option A: pause both triggers (instant, no commit)
gcloud builds triggers describe pdd-auto-heal-pr --project=prompt-driven-development-stg \
  --format='value(id)' | xargs -I{} gcloud alpha builds triggers update {} --disabled \
  --project=prompt-driven-development-stg
# (repeat for pdd-auto-heal-push)

# Option B: commit-based disable (survives config regeneration)
# Change substitutions._PDD_BUDGET_CAP in cloudbuild-auto-heal.yaml to '0' — heal
# will detect drift but the budget guard stops all heals. Merge via PR.
```

## Rollback to GH Actions

The old workflow is still in-tree, gated by `if: false`. To re-enable:

```yaml
# .github/workflows/auto-heal-drift.yml
jobs:
  auto-heal:
    ...
    if: >-                             # <— replace `if: false` with this
      github.event_name == 'pull_request' ||
      (github.event_name == 'push' && !startsWith(github.event.head_commit.message, 'chore: auto-heal'))
```

Also pause or delete the GCB triggers so both don't run concurrently. Billing must be paid on the GH account before the old workflow actually runs.

## Rotating the GitHub App PEM

Triggers for rotation: PEM was leaked, suspected exposure, or scheduled hygiene.

```bash
# 1. Generate a new private key at:
#    https://github.com/settings/apps/pdd-auto-heal-gltanaka → Generate a private key
#    (keeps old key valid until you delete it on GitHub — gives you a window
#    to roll forward in Secret Manager before any in-flight build breaks)

# 2. Upload as a new secret version (becomes "latest"; yaml reads versions/latest)
gcloud secrets versions add auto-heal-github-app-pem \
  --data-file=/path/to/new-key.pem \
  --project=prompt-driven-development-stg

# 3. Verify a build mints a token via the new key (open a no-op PR or wait for one).
#    Cannot manually fire a PR trigger; use a real PR or the push trigger:
gh pr create ...   # or wait for any PR that touches PDD-managed paths

# 4. Once confirmed working, delete the OLD key in the App settings page.
#    This invalidates any in-flight installation tokens minted from the old key.

# 5. Disable the old Secret Manager version (hygiene; not strictly required since
#    yaml uses versions/latest):
gcloud secrets versions disable <old-version-number> \
  --secret=auto-heal-github-app-pem \
  --project=prompt-driven-development-stg
```

Already-issued installation tokens (`ghs_*`, 1h TTL) are NOT retroactively revoked when you delete the key. They expire on TTL, but new JWTs cannot be signed against the deleted key, so the App can't mint new tokens against the old key after step 4.

## Reading failures

```bash
# Recent auto-heal builds only
gcloud builds list --project=prompt-driven-development-stg \
  --filter="buildTriggerId=1938d59c-d67e-4aa6-a05b-8f55e9ddf122 OR buildTriggerId=ea9c2b0a-816c-4a19-b66b-e2be1b16e210" \
  --limit=10 --format='table(id,substitutions.BRANCH_NAME,status,createTime)'

# Build log for a specific ID
gcloud builds log <build-id> --project=prompt-driven-development-stg
```

Common failure modes seen during migration:
- **`git diff` exit 128** → shallow checkout; the `fetch-history` step should deepen first. If it failed, check that the `mint-token` step succeeded (it has to run before `fetch-history` so the authed deep fetch has credentials).
- **Heal subprocess timeout** → `pdd sync`'s `summarize_directory` routes to Claude Opus via Vertex and can exceed 10 min on large repos. The 1200s timeout covers it; raise further if you hit it.
- **`git push` fails with "no upstream branch"** → the heal step must set `push.default=current` before invoking `ci_drift_heal`.
- **`mint-token` step fails with `401 A JSON web token could not be decoded`** → the App private key on GitHub has been deleted but Secret Manager still serves the matching PEM, OR vice versa. Re-run the rotation flow above; ensure the latest Secret Manager version corresponds to a private key that still exists on the App's settings page.
- **Auto-heal commit contains `github_token` / `modules.txt` / `diff_base.txt`** → someone moved the state files back under `/workspace/` in the yaml. Check `cloudbuild-auto-heal.yaml` — every step that uses inter-step state must declare the `ci-state` volume and reference `/ci-state/<file>` only. See "Inter-step state" section above.

## Related

- [Public PR Testing](./PUBLIC_PR_TESTING.md) — Testing public PRs against private codebase
- Migration PRs: [#1193](https://github.com/gltanaka/pdd/pull/1193) scaffolding, [#1195](https://github.com/gltanaka/pdd/pull/1195) PR detection + authed fetch, [#1196](https://github.com/gltanaka/pdd/pull/1196) gate old workflow + raise timeout, [#1201](https://github.com/gltanaka/pdd/pull/1201) `push.default=current`, [#1211](https://github.com/gltanaka/pdd/pull/1211) `.gitignore` defense for state files, [#1216](https://github.com/gltanaka/pdd/pull/1216) `/ci-state` volume (root-cause fix for [#1213](https://github.com/gltanaka/pdd/issues/1213) token leaks)
