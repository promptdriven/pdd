# Notice a newer pdd release

As a person using pdd, I want the next command after a release to tell me the exact update command, so that I do not keep using an old install unknowingly.

## Acceptance criteria

1. When I run an older pdd after a release, I see one stderr line naming the new version, my installed version and the exact GitHub update command; stdout and the command exit status stay intact.
2. Equal or older releases, malformed release data and an unavailable release service do not produce a reminder or prevent my command.
3. CI and internal PATH version probes skip the release lookup and reminder.
4. A stable release replaces an installed prerelease with the same version numbers; version numbers compare numerically and build metadata does not make an equal release newer.
5. pdd never installs an update automatically, including during a workflow or in CI; a release lookup has a one-second deadline and a 65536-byte response limit.

## Rules to check

Only a strictly newer valid release produces a reminder. CI and internal PATH probes make zero release reads. Version components compare numerically, with a stable release newer than a prerelease with the same numbers.

```pdd-boundary
prompts/cli/release-notice.prompt.md
```

The Runtime scenarios check the release decision through its injected release read. Native executable tests check stderr, stdout, exit status, CI, workflow command dispatch, transport failure and bounds. No automatic installer is part of this Story.
