# PDD CLI Release Process

## Release-Video PDS CLI

Local release-video targets default to:

```bash
npx -y @promptdriven/pds@0.1.6 --timeout 120s
```

That avoids silently picking up an older globally installed `pds` binary and
keeps the PDS wait path bounded before recovery/status metadata is needed. Run
the local preflight before a release to print the redacted PDS command and the
resolved CLI version:

```bash
make check-release-video-config
```

The release workflow also installs `@promptdriven/pds@0.1.6` by default when
`PDS_CLI_PACKAGE` is unset and runs the same preflight before creating the
video. If the GitHub repo variable is pinned below `0.1.6`, update it outside
the PR:

```bash
gh variable set PDS_CLI_PACKAGE --repo promptdriven/pdd --body '@promptdriven/pds@0.1.6'
```

## Release-Video Metadata Recovery

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
requires preserving the existing project metadata. Use
`RELEASE_VIDEO_METADATA_CONFLICT=replace` only with
`RELEASE_VIDEO_FORCE_REGENERATE=1`, because replacement is destructive.
