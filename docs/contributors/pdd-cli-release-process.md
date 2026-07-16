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
PYPI_PROJECT="$(python -c 'import tomllib; print(tomllib.load(open("pyproject.toml", "rb"))["project"]["name"])')"
printf 'candidate=%s sha=%s previous=%s distribution=%s\n' \
  "$RELEASE_TAG" "$RELEASE_GIT_SHA" "$LATEST_TAG" "$PYPI_PROJECT"
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

- Target: `promptdriven/pdd`, the derived tag, PyPI project `pdd-cli`, the
  `pypi-publish` GitHub environment, the production PDS endpoint, and the
  configured YouTube account.
- Rollback: do not reuse/delete a published tag or PyPI version; correct defects
  with a new version. Before publication, retain the same tag/SHA and resume the
  idempotent workflow. A video can be recovered or explicitly skipped later.
- Risk: irreversible public package publication, supply-chain identity,
  production PDS cost, unlisted YouTube publication, and duplicate messaging.

Only then run the maintainer entrypoint:

```bash
RELEASE_VIDEO=0 make release-local BUMP="$BUMP"
```

The target derives and pushes the next tag. `RELEASE_VIDEO=0` disables the
Makefile's local create path, including its recursive `release-video` call. The
tag-triggered `.github/workflows/release.yml` job is the sole normal creation
authority: it uses `github-actions` provenance after package publication. This
prevents local and CI from creating distinct requests for the same release.
General automation to make this authority/state machine explicit is tracked in
#2044; until it ships, the environment override is mandatory.

Do not use `make release-local` as a same-tag recovery command. Once the tag is
on origin, use the state-specific recovery below.

### pdd_cloud attested-release boundary

The public Makefile advertises
`PDD_CLOUD_RELEASE_ATTESTATION_CONTRACT_VERSION := 2`. A pdd_cloud caller must
pass the version, a full lowercase `PDD_CLOUD_VALIDATED_SHA`, a unique
`PDD_CLOUD_RELEASE_LEASE_OWNER`, and the reviewed
`PDD_CLOUD_RELEASE_LEASE_REF=refs/pdd-cloud/release-lease` as GNU Make
command-line assignments. Ambient values are not the contract. The cloud
wrapper starts the public Make process with GNU Make control variables removed,
and the SOPS runner removes `MAKEFILES`, `MAKEFLAGS`, `GNUMAKEFLAGS`, `MFLAGS`,
`MAKEOVERRIDES`, and related Make controls from both ambient and decrypted
environment data. After SOPS it passes the four reviewed values again as
explicit GNU Make command-line assignments, preserving their `command line`
provenance in the recursive Make process.

`release-attestation-contract.txt` binds the security-critical public
Makefile, `scripts/release_attestation.py`, and `scripts/sops_release_env.py`
to SHA-256 values. The cloud wrapper pins the manifest's own SHA-256 and reads
both the manifest and every listed file directly from the attested Git object;
a version marker by itself is not a release contract. When any listed file is
intentionally changed, regenerate its SHA-256 entry from the exact staged
content, update the cloud pin in the companion PR, and review/push both changes
together. Do not add the manifest to its own file list: its cloud-side pin is
what avoids a self-referential hash.

After SOPS/video preflights, the release target refetches `origin/main`, checks
both it and local `HEAD` against the attested SHA, and acquires a unique-owner,
server-visible remote lease. Cleanup deletes the lease only with the exact
owner object's `--force-with-lease` value, so a stale owner cannot delete a
successor's lease. If a successful lease push cannot be read back, it attempts
that same exact owner-safe remote deletion before removing local state. A
competing attested release cannot get past that lease.

Git cannot atomically assert that an unchanged `main` still has an expected SHA
while also creating a tag: it omits a no-op `main` refspec, so that is not a
server compare-and-swap. Until a server-side atomic compare-and-swap policy is
available, the attested path deliberately refuses the tag push after the final
check and lease. This is fail-closed; it does not turn the timing window into a
claimed guarantee. Existing remote same-tag recovery remains safe because it
does not create or publish a tag. A direct standalone `make release-local`
without all attestation inputs keeps its historical behavior, but explicitly
does **not** carry the pdd_cloud guarantee.

### Recovering a durable pdd_cloud release lease

SIGINT and SIGTERM trigger owner-safe lease cleanup. The helper installs a
lease lifecycle owner before the create-only push and defers further SIGINT or
SIGTERM until normal exact cleanup has finished, so there is no acquisition
return/assignment cleanup gap. Each attempt also records an independent
cryptographic claim in its annotated tag; exact OID equality alone is never
accepted as proof that a same-owner attempt owns a lease. A power loss, SIGKILL, or
an ambiguous transport outcome cannot be cleaned up by the interrupted process.
There is deliberately **no automatic TTL**: a clock-based expiry could delete a
live release that is paused in a network or approval step. Treat an extant
lease as active until the release owner is known to be gone and the release
attempt is known not to be publishing anything.

Only a maintainer with the normal production Git authorization may perform this
manual recovery. First coordinate with the owner, verify no release job or
operator is active, and run the read-only inspection from a clean canonical
`promptdriven/pdd` clone with `origin` pointing to production:

```bash
LEASE_REF=refs/pdd-cloud/release-lease
python scripts/release_attestation.py inspect-lease --lease-ref "$LEASE_REF"
```

The command prints the exact remote `lease_oid`, the owner, target `sha`, and
the annotated tag's `created_epoch` metadata. Record all four values in
the incident. Choose and record a `STALE_BEFORE_EPOCH` at or later than the
inspected creation time, and only after the owner has been confirmed dead;
this is an explicit human decision, not a lease timeout. Copy the inspected
values exactly into the recovery command:

Both manual commands reject any noncanonical or ambiguous fetch or push
`origin` before reading or mutating the lease.

```bash
LEASE_OID='copied-exact-40-hex-lease-oid'
LEASE_OWNER='copied-exact-owner'
LEASE_SHA='copied-exact-40-hex-target-sha'
STALE_BEFORE_EPOCH='copied-reviewed-epoch'
python scripts/release_attestation.py recover-stale-lease \
  --lease-ref "$LEASE_REF" \
  --lease-oid "$LEASE_OID" \
  --expected-owner "$LEASE_OWNER" \
  --expected-sha "$LEASE_SHA" \
  --stale-before-epoch "$STALE_BEFORE_EPOCH"
python scripts/release_attestation.py inspect-lease --lease-ref "$LEASE_REF"
```

Recovery refetches the lease and rejects changed, malformed, owner-mismatched,
target-mismatched, or newer metadata. It deletes only when the current remote
OID still equals `LEASE_OID`, using `--force-with-lease`; a stale recovery can
therefore never delete a successor lease. A failed or unreadable post-push
readback is an ambiguous failure—stop, retain the incident record, inspect
again, and do not retry based on an assumed deletion. Do not use raw `git push
origin :refs/pdd-cloud/release-lease`, force-push the ref, or recover solely
because a local process stopped. SIGKILL recovery follows this same manual
procedure.

## 5. Approve and verify package publication

The protected `pypi-publish` environment is attached to the entire
`publish-pypi` job. Its approval therefore occurs before checkout, build, Twine
verification, and publication. Approval authorizes those steps from the exact
tag SHA; it does not approve a prebuilt wheel.

**Before approval**, verify the remote tag/SHA, final cloud-test evidence,
workflow file and event identity, reviewed source, intended distribution name,
and safety record. Wheel hashes and attestations do not exist yet. Reject the
job if any available identity differs.

**After publication**, verify the built artifact hashes, PyPI attestations,
public version, workflow result, and GitHub Release. Approval alone is not
publication evidence.

After approval, require all of the following before package closeout:

```bash
gh run list --repo promptdriven/pdd --workflow release.yml \
  --limit 20 --json databaseId,headSha,status,conclusion,url
gh release view "$RELEASE_TAG" --repo promptdriven/pdd \
  --json tagName,targetCommitish,publishedAt,url,body
python -m pip index versions "$PYPI_PROJECT"
PYPI_VERSION_URL="https://pypi.org/project/${PYPI_PROJECT}/${NEXT_VERSION}/"
PYPI_JSON_URL="https://pypi.org/pypi/${PYPI_PROJECT}/${NEXT_VERSION}/json"
printf '%s\n' "$PYPI_VERSION_URL"
curl -fsS "$PYPI_JSON_URL" | python -c '
import json, sys
payload = json.load(sys.stdin)
assert payload["info"]["name"] == "pdd-cli"
assert payload["info"]["version"] == sys.argv[1]
assert payload["urls"] and all(item["digests"]["sha256"] for item in payload["urls"])
' "$NEXT_VERSION"

TAG_REFS=$(git ls-remote origin \
  "refs/tags/$RELEASE_TAG" "refs/tags/$RELEASE_TAG^{}")
DIRECT_TAG_SHA=$(printf '%s\n' "$TAG_REFS" \
  | awk '$2 !~ /\^\{\}$/ {print $1; exit}')
PEELED_TAG_SHA=$(printf '%s\n' "$TAG_REFS" \
  | awk '$2 ~ /\^\{\}$/ {print $1; exit}')
if [ -n "$PEELED_TAG_SHA" ]; then
  REMOTE_TAG_SHA="$PEELED_TAG_SHA"
else
  REMOTE_TAG_SHA="$DIRECT_TAG_SHA"
fi
test -n "$REMOTE_TAG_SHA"
test "$REMOTE_TAG_SHA" = "$RELEASE_GIT_SHA"
```

- The workflow run is successful and its `headSha` is `RELEASE_GIT_SHA`.
- PyPI shows the exact derived version and its artifacts/attestations.
- The GitHub Release exists at the same tag and contains real release notes,
  not an authentication, quota, or tool diagnostic.
- The exact version page at `$PYPI_VERSION_URL` identifies distribution
  `pdd-cli` and the recorded files/hashes/attestations.
- The remote tag's peeled commit equals `RELEASE_GIT_SHA`; do not use
  `targetCommitish` (often `main`) as tag-object proof.

Record URLs and immutable identifiers. Do not rerun package publication merely
because release notes or video work remains.

### Same-tag package workflow recovery

First verify PyPI and the GitHub Release to distinguish an unpublished failure
from an ambiguous response after publication. `skip-existing` limits duplicate
file upload after an ambiguous PyPI response; it is not proof that a rerun is
safe or that publication did not occur.

Locate the existing production tag-push run and prove its SHA:

```bash
RUN_ID=$(gh run list --repo promptdriven/pdd --workflow release.yml \
  --event push --branch "$RELEASE_TAG" --limit 20 \
  --json databaseId,headSha,event,headBranch,status,conclusion \
  --jq ".[] | select(.headSha == \"$RELEASE_GIT_SHA\" and .event == \"push\") | .databaseId" \
  | head -1)
test -n "$RUN_ID" || {
  echo "no matching production tag-push run exists; open an automation incident" >&2
  exit 1
}
gh run view "$RUN_ID" --repo promptdriven/pdd --json jobs,status,conclusion,url
```

Rerun only when the job/step evidence proves package publication did not
complete **and the video step did not start**. The unchanged tag/SHA then keeps
the tag-triggered workflow as the first and sole video authority:

```bash
gh run rerun "$RUN_ID" --repo promptdriven/pdd
```

The protected environment requires approval again. If the prior video step
started, do not rerun the whole workflow: use PDS status/recovery and the
release/Discord reconciliation paths. If no matching production tag-push run
exists, stop and open an automation incident; `workflow_dispatch` targets
TestPyPI and is not production recovery.

If PyPI is proven complete but the GitHub Release is missing, state a new
target/rollback/risk record, verify PyPI first, then create the release once:

```bash
gh release view "$RELEASE_TAG" --repo promptdriven/pdd >/dev/null 2>&1 \
  || gh release create "$RELEASE_TAG" --repo promptdriven/pdd \
       --generate-notes --verify-tag --target "$RELEASE_GIT_SHA"
```

This reconciliation is not permission to rerun PyPI or video work.

## 6. Create, audit, and distribute the release video

The configured PDS CLI must report at least `0.1.11` in preflight. Local Claude
script generation uses `RELEASE_VIDEO_CLAUDE_MODEL` (default
`claude-opus-4-8`); `RELEASE_VIDEO_PDS_CLAUDE_MODEL` controls non-vision PDS
stages. Empty local model values are treated as unset.

Normal release-video publication is production-affecting. The sole normal
creation authority is the tag-triggered `.github/workflows/release.yml` job;
section 4 disables local creation. Its retained safety record must name the PDS
project/endpoint, `github-actions` provenance, YouTube account/privacy,
rollback, and paid-generation/publication risk. Monitor that exact workflow and
download its `release-video-<tag>` recovery artifact. Do not invoke a second
create from the operator shell.

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
run cannot be resumed. A manual create is exceptional and permitted only when
authoritative status proves that no attempt was started by the normal authority
and the safety record explicitly transfers creation authority to the operator.
Never use both an attempt ID and a full idempotency key.

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
Discord message. It fails before editing the release when a video URL or exact,
pending, stale, or mismatched backfill marker already exists. Mark Discord
follow-up explicitly unnecessary. Reciprocally, the backfill command refuses to
backfill while a matching skip record remains, so either direction stays
monotonic while the full state machine in #2044 is pending.

To supersede a skip, first state the release-body target, saved-body rollback,
and ambiguous Discord risk. Save the current body, remove only the exact
tag-bound skip text/marker with the shared parser, inspect the diff, and edit the
release once:

```bash
BEFORE=$(mktemp)
AFTER=$(mktemp)
gh release view "$RELEASE_TAG" --repo promptdriven/pdd --json body --jq .body \
  >"$BEFORE"
python - "$RELEASE_TAG" "$BEFORE" "$AFTER" <<'PY'
import pathlib
import sys
from scripts.backfill_release_video_discord import remove_release_video_skip_records

tag, before, after = sys.argv[1:]
body = pathlib.Path(before).read_text(encoding="utf8")
reconciled = remove_release_video_skip_records(body, tag)
if reconciled == body:
    raise SystemExit("matching skip record not found; refusing broad edit")
pathlib.Path(after).write_text(reconciled, encoding="utf8")
PY
diff -u "$BEFORE" "$AFTER"
gh release edit "$RELEASE_TAG" --repo promptdriven/pdd --notes-file "$AFTER"
```

Read the body back and verify the edited release body contains neither the skip
text nor marker for the tag. Only then run the verified
`release-video-discord-backfill` command. If delivery becomes ambiguous, follow
the pending-marker rules; do not restore a skip that could contradict a sent
Discord post. Atomic skip supersession automation remains follow-up work.
The broader duplicate-create, same-tag, and skip-reconciliation state machine is
tracked in #2044; this runbook's current path stays fail-closed and manual.

This controlled supersession is allowed only before `final-evidence.json`
exists. An immutable skipped final cannot be replaced by a second final under
the current one-final contract; keep that release skipped and track any future
publication design in #2044. Before final issuance, verify reconciliation and
then backfill:

```bash
READBACK=$(mktemp)
gh release view "$RELEASE_TAG" --repo promptdriven/pdd --json body --jq .body \
  >"$READBACK"
python - "$RELEASE_TAG" "$READBACK" <<'PY'
import pathlib
import sys
from scripts.backfill_release_video_discord import remove_release_video_skip_records

tag, readback = sys.argv[1:]
body = pathlib.Path(readback).read_text(encoding="utf8")
if remove_release_video_skip_records(body, tag) != body:
    raise SystemExit("skip reconciliation did not persist; refusing backfill")
PY
DISCORD_WEBHOOK_URL=<webhook> make release-video-discord-backfill \
  RELEASE_TAG="$RELEASE_TAG" \
  RELEASE_VIDEO_YOUTUBE_URL="https://youtu.be/<verified-video-id>"
```

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
9. Safe video recovery is abandoned: record `pdd-release-video-skipped` and
   produce terminal evidence.
10. Recovery remains active: write a recovery checkpoint and keep the release
    issue open; active recovery is not final closeout.

Recovery must never create or push another package tag for the same release,
must never republish to PyPI, and must never weaken, bypass, or relabel a failed audit.
Do not delete/re-push a published tag to retrigger automation.

## Authoritative final evidence

Maintain exactly one authoritative `final-evidence.json` only after the video is
terminally published or skipped. Automation is tracked in #2041; until then,
construct it from authoritative receipts, validate it, attach it to the
release-level closure issue, and store its SHA-256. Never include secrets.
Earlier snapshots must be labelled `historical/intermediate` and must not use
"final" in their path.

Active recovery uses `recovery-checkpoint-<sequence>.json`, never a final
manifest. Each immutable checkpoint includes `schemaVersion`, `sequence`,
`previousCheckpointSha256` (null only for the first), observed state, present
receipts, and explicit per-field absence reasons. A later checkpoint links to
the previous hash; success or skip then produces the sole final manifest.

The manifest must bind these fields. A published manifest has no missing
evidence. A skipped manifest uses `null` only for unavailable video fields and
adds a `missingEvidenceReasons` entry for every null field; one aggregate reason
cannot stand in for field-level provenance.

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
  "schemaVersion": 1,
  "releaseTag": "<derived tag>",
  "releaseGitSha": "<40-char SHA>",
  "previousReleaseTag": "<derived previous tag>",
  "pypiUrl": "https://pypi.org/project/pdd-cli/<version>/",
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
  "discordMarker": "<completed marker, unnecessary, or skipped>",
  "discordWorkflowRunUrl": "<URL or null with reason>",
  "closureIssueUrl": "<URL>",
  "terminalState": "video-published | video-skipped",
  "missingEvidenceReasons": {
    "<null field>": "<issue-bound reason; allowed only for video-skipped>"
  },
  "videoTerminalReason": "<null for published; issue-bound reason for skipped>"
}
```

Final closeout is one of exactly two terminal branches:

- verified video, GitHub Release updated, and Discord posted or proven already
  covered by the main announcement;
- explicit skip recorded and Discord marked unnecessary.

A package release with an open release-video recovery issue is an operational
checkpoint, not final closeout and not `final-evidence.json`.

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
