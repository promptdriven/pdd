# PDD CLI Release Process

This is the canonical maintainer runbook for a PDD CLI release, including
post-publication release-video recovery. Use
[`pr-loop-process.md`](../runbooks/pr-loop-process.md) for every code fix found
during the release. Keep operational recovery separate from a fix PR: recovery
must not bypass its review, test, merge, or deployment gates.

The package release and release video have different terminal states. A video
failure after package publication does not make the PyPI release unpublished,
and it must not be "fixed" by publishing the package again.

## Safety record before mutations

Before any command that creates cloud work, pushes a tag, approves publication,
edits a GitHub Release, publishes a video, or posts to Discord, write this in the
operator session and retain it with the release evidence:

```text
Target: <repository/project/service/account/resource and environment>
Rollback path: <exact prior state or compensating action>
Risk: <cost, irreversible publication, duplicate-post, or user impact>
```

In other words, state the **target, rollback path, and risk** before the
mutation. Stop if the target identity cannot be proven. Package versions and a
published tag are immutable; their "rollback" is a follow-up release, not tag
reuse or deletion. A YouTube or Discord publication may be externally visible
and may require manual removal. Never print tokens or webhook URLs in the
record.

## 1. Derive the candidate

Work from a clean dedicated release worktree while fixes remain on their own PR
branches. Fetch tags and derive the candidate; never copy a version number from
an issue or hard-code the next version in this runbook:

```bash
git fetch origin main --tags --prune
LATEST_TAG=$(git tag --list --merged origin/main --sort=-v:refname 'v*' \
  | grep -E '^v[0-9]+\.[0-9]+\.[0-9]+$' | head -1)
BUMP=${BUMP:-patch}
NEXT_VERSION=$(python - "$LATEST_TAG" "$BUMP" <<'PY'
import sys

version = [int(part) for part in sys.argv[1].removeprefix("v").split(".")]
index = {"major": 0, "minor": 1, "patch": 2}[sys.argv[2]]
version[index] += 1
for position in range(index + 1, 3):
    version[position] = 0
print(".".join(map(str, version)))
PY
)
RELEASE_TAG="v${NEXT_VERSION}"
RELEASE_GIT_SHA=$(git rev-parse origin/main)
printf 'candidate=%s sha=%s previous=%s\n' \
  "$RELEASE_TAG" "$RELEASE_GIT_SHA" "$LATEST_TAG"
```

Confirm the candidate tag does not exist locally, on origin, on PyPI, or as a
GitHub Release. Record the intended bump and the source SHA. Inspect commits,
merged PRs, open release blockers, and the latest release before proceeding.

Release-video uses PDS `0.1.11`. Local targets default to:

```bash
npx -y @promptdriven/pds@0.1.11 --timeout 120s
```

The release workflow defaults `PDS_CLI_PACKAGE` to the same version. If the
repository variable overrides it, verify that it is not older:

```bash
gh variable get PDS_CLI_PACKAGE --repo promptdriven/pdd || true
make check-release-video-config-local
```

An empty variable means the workflow default applies. Changing a repository
variable is a production-affecting mutation and needs its own safety record.

## 2. Cloud test

Record the staging Cloud Batch target, how to cancel the job or restore the
prior image, and the compute/image risk. Then run the candidate source through
the real cloud boundary:

```bash
make cloud-test
```

Use `make cloud-test-quick` only when the dependency-image hash proves a rebuild
is unnecessary. Save the Batch job/build identifiers, source SHA, image digest,
test counts, result artifact URI, and final status. A failed or incomplete job
is a release blocker. Fix failures via the PR loop; do not patch only the
release worktree or silently exclude a test.

## 3. PR, review, and merge

For every release-blocking change:

1. Inspect the issue, sibling bugs, and prior related commits/PRs.
2. Add and push a failing test commit before the fix when practical.
3. Implement in a dedicated worktree, run focused and broader relevant tests,
   lint/static checks, an end-to-end boundary check, and `git diff --check`.
4. Open a non-draft PR, post TDD and investigation evidence, obtain independent
   adversarial review, and resolve findings.
5. Merge only the reviewed exact head with required hosted checks green.

Follow [`pr-loop-process.md`](../runbooks/pr-loop-process.md) for the complete
commands and evidence format. After all release PRs merge, rerun cloud test on
the final candidate SHA if any merged change could affect its result.

## 4. Release from clean `main`

Create a fresh or cleaned `main` worktree; do not release from a PR branch:

```bash
git fetch origin main --tags --prune
git switch main
git pull --ff-only origin main
make check-release-remote
make check-release-branch
make check-release-clean
make check-release-video-config-local
```

Re-derive `RELEASE_TAG` and `RELEASE_GIT_SHA` after the pull and confirm they
match the tested candidate. Before the release mutation, record:

- Target: `promptdriven/pdd`, the derived tag, PyPI project `pdd`, the
  `pypi-publish` GitHub environment, the production PDS endpoint, and the
  configured YouTube account.
- Rollback: do not reuse/delete a published tag or PyPI version; correct defects
  with a new version. Before publication, retain the same tag/SHA and resume the
  idempotent workflow. A video can be recovered or explicitly skipped later.
- Risk: irreversible public package publication, supply-chain identity,
  production PDS cost, unlisted YouTube publication, and duplicate messaging.

Only then run the maintainer entrypoint:

```bash
make release-local BUMP="$BUMP"
```

The target derives the next tag, pushes it, and invokes local release-video.
The tag push also starts `.github/workflows/release.yml`; its best-effort video
path can overlap the local attempt. Treat the persisted request provenance,
idempotency key, and run handle as authority. Do not start an unlabelled second
attempt because one surface is still running.

If `HEAD` already has the intended tag at the same SHA, `make release-local`
uses the recovery path. If it differs, stop. Never move a release tag.

## 5. Approve and verify package publication

The tag workflow builds and checks the artifacts, then waits at the protected
`pypi-publish` production environment. Before approving, re-check the target
tag/SHA, cloud-test evidence, artifact attestations, and safety record. Approval
is the production publication gate. Reject it if any identity differs.

After approval, require all of the following before package closeout:

```bash
gh run list --repo promptdriven/pdd --workflow release.yml \
  --limit 20 --json databaseId,headSha,status,conclusion,url
gh release view "$RELEASE_TAG" --repo promptdriven/pdd \
  --json tagName,targetCommitish,publishedAt,url,body
python -m pip index versions pdd
```

- The workflow run is successful and its `headSha` is `RELEASE_GIT_SHA`.
- PyPI shows the exact derived version and its artifacts/attestations.
- The GitHub Release exists at the same tag and contains real release notes,
  not an authentication, quota, or tool diagnostic.

Record URLs and immutable identifiers. Do not rerun package publication merely
because release notes or video work remains.

## 6. Create, audit, and distribute the release video

The configured PDS CLI must report at least `0.1.11` in preflight. Local Claude
script generation uses `RELEASE_VIDEO_CLAUDE_MODEL` (default
`claude-opus-4-8`); `RELEASE_VIDEO_PDS_CLAUDE_MODEL` controls non-vision PDS
stages. Empty local model values are treated as unset.

Normal release-video publication is production-affecting. State the PDS
project/endpoint, request provenance, YouTube account/privacy, rollback, and
paid-generation/publication risk before invoking it. When resuming an existing
release, use the already-derived identifiers:

```bash
make release-video \
  RELEASE_TAG="$RELEASE_TAG" \
  RELEASE_GIT_SHA="$RELEASE_GIT_SHA"
```

PDS must retain one attributable chain from request through distribution:

1. Script and release notes pass local validation before paid work.
2. The persisted PDS project, request hash, provenance, attempt, parent
   `agent_run_*`, and child jobs describe the current attempt.
3. The stitched video generation/hash is immutable.
4. The promoted audit generation/hash is immutable and its aggregate counts
   pass the distribution gate. Never substitute a later mutable audit path.
5. Distribution package and dry-run receipts bind the same video and audit.
6. The publish receipt binds the YouTube video ID and requested privacy.

Preserve `.pdd/release-videos/<tag>/` and the workflow recovery artifact. Do not
rename a failed aggregate to `final-audit`; store attempts as
`historical/intermediate-<attempt>` and reserve authoritative final status for
the manifest described below.

### Status and safe recovery

Inspect the persisted sidecar first, then refresh its authoritative status:

```bash
make release-video-status RELEASE_TAG="$RELEASE_TAG"
make release-video-status \
  RELEASE_TAG="$RELEASE_TAG" \
  RELEASE_VIDEO_STATUS_QUERY=1
```

Read parent `agent_run_*` state together with child job IDs, `failedStage`,
terminal state, retryability, request hash, and distribution gate. Old rows and
prior-attempt prose are historical; they cannot override the current run.

- **Active/timeout:** wait and query the saved run. A timeout with an active run
  handle is pending, not permission to create another run.
- **Local Claude failure before PDS:** fix the local model/auth environment and
  reuse a valid generated script if present. This is not a PDS publish failure.
- **Metadata conflict:** inspect status first. Use
  `RELEASE_VIDEO_METADATA_CONFLICT=use-existing` only when PDS says existing
  metadata is authoritative. `replace` is destructive and is allowed only with
  `RELEASE_VIDEO_FORCE_REGENERATE=1`, a new labelled attempt, and a safety
  record.
- **Provider quota/capacity:** do not loop paid calls. Follow the current-run
  terminal hint: wait, choose an approved provider/model, or open/update the GVS
  provider issue before a labelled retry.
- **Audit failure:** keep the package release, block video distribution, and
  open/update the GVS audit issue with immutable evidence. Never weaken the
  audit to obtain a URL.
- **Incomplete/slow status planning:** retain the run handle and retry status;
  update the GVS status issue if the bounded status path fails. Do not infer
  success from a partial artifact list.

Keep `RELEASE_VIDEO_METADATA_CONFLICT` unset for ordinary exact retries. If PDS
explicitly recommends the raw recovery shape
`--metadata-conflict replace --force-regenerate`, use the wrapper equivalent
`RELEASE_VIDEO_METADATA_CONFLICT=replace` with
`RELEASE_VIDEO_FORCE_REGENERATE=1` so the original artifacts and run metadata
remain in the release directory.

For an authorized recovery that must reuse exact inputs:

```bash
make release-video \
  RELEASE_TAG="$RELEASE_TAG" \
  RELEASE_GIT_SHA="$RELEASE_GIT_SHA" \
  RELEASE_VIDEO_PROJECT_ID=<project-id> \
  RELEASE_VIDEO_SCRIPT_PATH=".pdd/release-videos/$RELEASE_TAG/release_video_script.md" \
  RELEASE_VIDEO_RELEASE_NOTES_PATH=".pdd/release-videos/$RELEASE_TAG/release_notes.md"
```

Exact retries reuse the original idempotency key and provenance. Set
`RELEASE_VIDEO_ATTEMPT_ID=<timestamp-or-label>` only after proving the previous
run cannot be resumed. Never use both an attempt ID and a full idempotency key.

## Warnings versus blockers

A warning label is not authority to publish. Use the current immutable audit
and distribution decision:

- Informational transport/status warnings with a successful authoritative gate,
  complete receipts, and unchanged hashes can be recorded as non-blocking.
- Any failed audit gate (including a policy that promotes a `content_warn` to a
  blocker), provider limit that prevents required work, missing/mismatched
  generation or receipt, unknown terminal state, failed distribution dry-run,
  or unverifiable live resource is blocking.
- Video blockers do not invalidate an already successful package release. They
  do block video backfill and final video-success closeout.

Do not downgrade a blocker based only on an error string or the existence of a
rendered file.

## 7. Verify the live YouTube resource

A returned URL is not sufficient. Open the canonical live resource using the
authenticated YouTube account or supported API and bind the observation to the
publish receipt. Verify:

- **title** exactly names the derived release tag and has no diagnostic text;
- **channel** is the approved PDD release channel;
- **privacy** is the requested value (normally `unlisted`);
- **captions** are present/processed as required, or their receipt records an
  explicit approved state;
- **thumbnail** is present and bound to the intended uploaded asset/receipt;
- the video is playable and its ID matches the distribution publish receipt.

Record the observation timestamp and receipt IDs. If any check fails, the video
success path remains blocked even when the URL resolves.

## 8. Complete Discord and release closeout

First inspect the GitHub Release body and the normal release workflow. If its
Discord announcement already included the verified YouTube URL, record Discord
as complete and **do not** send a follow-up.

If the verified video arrived after the main announcement, state the target
release/webhook, rollback (release-body edit plus manual Discord deletion when
available), and duplicate/ambiguous-delivery risk. Then use the protected
**Backfill release video Discord post** workflow, or its local equivalent:

```bash
DISCORD_WEBHOOK_URL=<webhook> make release-video-discord-backfill \
  RELEASE_TAG="$RELEASE_TAG" \
  RELEASE_VIDEO_YOUTUBE_URL="https://youtu.be/<video-id>"
```

Discord marker semantics are:

- `pdd-release-video-discord-backfill-pending`: delivery may have happened but
  completion is not proven. Inspect Discord; do not rerun blindly.
- `pdd-release-video-discord-backfill`: the matching follow-up and release-body
  update completed. Repeating the same backfill is a no-op.
- A definite 4xx delivery rejection removes the pending marker; correct the
  cause before retrying. A timeout/5xx is ambiguous and keeps it.
- For stale pre-marker releases, inspect Discord manually before removing any
  stale marker or doing a single controlled backfill.

### Explicit no-video skip

After repeated terminal blockers, an operator may choose a documented no-video
terminal state. State the GitHub Release target, release-body rollback, and
public-record risk, then run:

```bash
make release-video-skip \
  RELEASE_TAG="$RELEASE_TAG" \
  RELEASE_VIDEO_SKIP_REASON="<specific upstream blocker and issue URL>"
```

This writes `pdd-release-video-skipped` to the GitHub Release and sends no
Discord message. Mark Discord follow-up explicitly unnecessary. A later real
video may supersede the skip through the normal verified backfill path.

## Terminal decision tree

1. Package workflow not published: stay at the protected approval/build gate.
   Resume the same tag only for the unchanged SHA/artifacts; if a code fix is
   required, ship it under a newly derived version without moving the old tag.
2. Package published, video local preflight failed: preserve the package and
   fix/reuse the script without invoking package release.
3. PDS run active or timed out with a handle: query that run and wait.
4. Metadata conflict: select `use-existing`, or an explicitly destructive new
   attempt, only from authoritative PDS guidance.
5. Provider quota/capacity: wait/switch under policy or track upstream; do not
   retry in a paid loop.
6. Audit/distribution gate failed: block publish and update the GVS issue with
   immutable evidence.
7. Publish receipt and YouTube URL exist: perform all live-resource checks.
8. Live checks pass: update the GitHub Release, send Discord only if the main
   announcement lacked the URL, and finalize evidence.
9. Safe video recovery is abandoned: record `pdd-release-video-skipped`, or
   leave an active release-level recovery issue; never imply full completion.

Recovery must never create or push another package tag for the same release,
must never republish to PyPI, and must never weaken, bypass, or relabel a failed audit.
Do not delete/re-push a published tag to retrigger automation.

## Authoritative final evidence

Maintain exactly one authoritative `final-evidence.json` for the release.
Automation is tracked in #2041; until then, construct it from authoritative
receipts, validate it, attach it to the release-level closure issue, and store
its SHA-256. Never include secrets. Earlier snapshots must be labelled
`historical/intermediate` and must not use "final" in their path.

The manifest must bind these fields (use `null` plus a reason only for the skip
or active-recovery terminal branch):

Core contract fields are `releaseTag`, `releaseGitSha`, `pypiUrl`,
`githubReleaseUrl`, `cloudTest`, `pdsProjectId`, `requestHash`, `attemptId`,
`agentRunId`, `stitchedGeneration`, `stitchedSha256`,
`promotedAuditGeneration`, `promotedAuditSha256`,
`distributionPackageReceipt`, `distributionDryRunReceipt`,
`distributionPublishReceipt`, `youtubeVideoId`, `youtubeTitle`,
`youtubeChannel`, `youtubePrivacy`, `captionReceipt`, `thumbnailReceipt`,
`discordMarker`, `discordWorkflowRunUrl`, and `closureIssueUrl`. The schema also
retains the supporting provenance and receipt fields needed to validate them.

```json
{
  "releaseTag": "<derived tag>",
  "releaseGitSha": "<40-char SHA>",
  "previousReleaseTag": "<derived previous tag>",
  "pypiUrl": "<exact version URL>",
  "pypiArtifactSha256": ["<hash>"],
  "githubReleaseUrl": "<URL>",
  "releaseWorkflowRunUrl": "<URL>",
  "cloudTest": {
    "sourceSha": "<SHA>",
    "buildId": "<ID>",
    "batchJobId": "<ID>",
    "imageDigest": "<digest>",
    "resultUri": "<URI>",
    "passed": 0,
    "failed": 0
  },
  "pdsProjectId": "<ID>",
  "requestHash": "<hash>",
  "requestProvenance": "<local or github-actions>",
  "attemptId": "<label>",
  "agentRunId": "agent_run_<ID>",
  "childJobIds": ["<ID>"],
  "stitchedGeneration": "<generation>",
  "stitchedSha256": "<hash>",
  "auditJobId": "<ID>",
  "promotionAttemptId": "<ID>",
  "promotionFingerprint": "<hash>",
  "promotedAuditGeneration": "<generation>",
  "promotedAuditSha256": "<hash>",
  "promotedAuditCounts": {"total": 0, "passed": 0, "warned": 0, "failed": 0},
  "distributionPackageReceipt": "<immutable ID/hash>",
  "distributionDryRunReceipt": "<immutable ID/hash>",
  "distributionPublishReceipt": "<immutable ID/hash>",
  "youtubeVideoId": "<ID>",
  "youtubeUrl": "<canonical URL>",
  "youtubeTitle": "<observed title>",
  "youtubeChannel": "<observed channel ID/name>",
  "youtubePrivacy": "<observed privacy>",
  "captionReceipt": "<receipt or approved state>",
  "thumbnailReceipt": "<receipt or approved state>",
  "liveVerifiedAt": "<RFC3339 timestamp>",
  "discordMarker": "<completed marker, unnecessary, skipped, or pending>",
  "discordWorkflowRunUrl": "<URL or null with reason>",
  "closureIssueUrl": "<URL>",
  "terminalState": "<video-published | video-skipped | recovery-active>",
  "videoTerminalReason": "<null or issue-bound skip/recovery reason>"
}
```

Final closeout is one of exactly three honest branches:

- verified video, GitHub Release updated, and Discord posted or proven already
  covered by the main announcement;
- explicit skip recorded and Discord marked unnecessary; or
- package released with a release-level recovery issue still open.

Post a concise closure comment containing the manifest hash/location, test and
workflow URLs, live verification result, terminal branch, unresolved risks, and
follow-up issue links.

## Issue routing

- File in **PDD**: local environment/script validation, Make targets,
  idempotency/provenance wrapper behavior, release workflow, PyPI/GitHub
  Release, Discord marker/backfill behavior, or runbook/manifest automation.
- File in **Generative-Video-Studio (GVS)**: PDS run planning/status, provider
  quota/capacity, paid-generation replay, render/stitch closure, immutable audit
  promotion, storage receipts, distribution package/publish, or YouTube receipt
  integrity.

Search first. Augment an existing issue with release tag, current run IDs,
immutable hashes/receipts, redacted signatures, and workflow URLs; otherwise
create a narrowly scoped issue. Code changes in either repository follow that
repository's PR-loop runbook.
