# PDD CLI Release Process

## Release-Video PDS CLI

Local release-video targets default to:

```bash
npx -y @promptdriven/pds@0.1.7 --timeout 120s
```

That avoids silently picking up an older globally installed `pds` binary and
keeps the PDS wait path bounded before recovery/status metadata is needed. Run
the local preflight before a release to print the redacted PDS command and the
resolved CLI version:

```bash
make check-release-video-config
```

Release-video creation sends `--claude-model glm-5.2` to PDS by default for
non-vision pipeline stages such as specs and compositions. Override with
`RELEASE_VIDEO_PDS_CLAUDE_MODEL=<model>` only when intentionally changing the
downstream PDS model; the local script-generation `CLAUDE_MODEL` remains a
separate setting.

The release workflow also installs `@promptdriven/pds@0.1.7` by default when
`PDS_CLI_PACKAGE` is unset and runs the same preflight before creating the
video. If the GitHub repo variable is pinned below `0.1.7`, update it outside
the PR:

```bash
gh variable set PDS_CLI_PACKAGE --repo promptdriven/pdd --body '@promptdriven/pds@0.1.7'
```

## Release-Video Metadata Recovery

When PDS create times out but prints an active run handle, or when PDS reports
an existing-project conflict with an active run, the wrapper exits successfully
with a pending `pds_response.json`. It prints the project/run/status plus the
exact status and Discord backfill commands. Do not rerun package publishing,
tag creation, or PyPI upload for this recovery path; wait for the PDS run and
backfill the release-video announcement after YouTube is available.

Keep `RELEASE_VIDEO_METADATA_CONFLICT` unset for ordinary retries so the PDS
idempotency key still matches the original create request. Set
`RELEASE_VIDEO_METADATA_CONFLICT=use-existing` only when PDS explicitly reports
that preserving existing project metadata is the recovery mode. Use
`RELEASE_VIDEO_METADATA_CONFLICT=replace` only with
`RELEASE_VIDEO_FORCE_REGENERATE=1`, because replacement is destructive.

When PDS reports a recoverable project metadata mismatch such as
`release_video_existing_project_metadata_mismatch`, inspect the existing run
state first:

```bash
make release-video-status RELEASE_TAG=<tag> RELEASE_VIDEO_STATUS_QUERY=1
```

PDS may recommend a direct command shaped like:

```bash
pds release-video create --metadata-conflict replace --force-regenerate
```

Use the PDD wrapper for release recovery so the generated script, idempotency
key, and PDS run metadata stay under `.pdd/release-videos/<tag>/`:

```bash
make release-video \
  RELEASE_TAG=<tag> \
  RELEASE_GIT_SHA=<release-sha> \
  RELEASE_VIDEO_PROJECT_ID=<project-id> \
  RELEASE_VIDEO_SCRIPT_PATH=.pdd/release-videos/<tag>/release_video_script.md \
  RELEASE_VIDEO_METADATA_CONFLICT=replace \
  RELEASE_VIDEO_FORCE_REGENERATE=1 \
  RELEASE_VIDEO_ATTEMPT_ID=<timestamp-or-label>
```

Use `RELEASE_VIDEO_METADATA_CONFLICT=use-existing` when the PDS remediation
requires preserving the existing project metadata.
