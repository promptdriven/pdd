# Read the interpreter build

As a PDD user, I want a detailed version command, so that I can report which local CLI and interpreter build I use.

## Acceptance criteria

1. `pdd -V` behaves exactly like `pdd --version`: stdout contains only the installed package version and a newline; existing local diagnostics stay unchanged, with no interpreter or token read.
2. `pdd -VV` prints the installed package version, the interpreter's full reported build identifier and its exact supported interface, test and app-map format IDs, then exits with code 0.
3. When existing GitHub sign-in, interpreter access or usable build metadata is unavailable, `pdd -VV` prints the local version and "PDD interpreter: unknown", then exits with code 0 without asking for sign-in.
4. `pdd -VV` uses at most one metadata GET with a ten-second limit, sends no source, starts no model or prompt job and prints no credential, raw server message or control character.
5. Invalid version syntax exits with code 2 before token reads, network access or other command effects.

## Proposed output to review

Ordinary `--version` and `-V` keep the current version-only stdout and local
stderr diagnostics. Detailed output labels the local version as "PDD CLI" and
prints the full interpreter build. Its three format lines preserve received ID
order. Missing or unsafe format lists read "unknown"; an empty list reads "none".
Unavailable build metadata gives only the local line and the unknown line.
Detailed version does not run local PATH or stale-skill diagnostics.

## What must not change

Other commands, help behavior, origin validation, account choice and version
metadata failures keep their current behavior. This change adds no historical
artifact, provenance, checkout recovery or model-version reporting.

## Rules to check

Use only existing noninteractive GitHub credentials. A missing token must prevent
the metadata request. A redirect, HTTP failure, malformed response or unsafe build
must never become a known build. No retries, uploads, state writes or job creation
are permitted. The actual command makes zero AI calls; PDD checks of its prompts
are separate model activity. Native tests must verify process/fetch wiring,
timeouts, aborts, redirects and absence of jobs; faked ports prove decisions only.

The boundary includes the CLI entry and every Runtime call target. Address,
PATH and skill implementations are native callback dependencies, represented by
resources rather than excluded executable prompt calls.

```pdd-boundary
prompts/cli/pdd-cli.prompt.md
prompts/cli/interpreter-version.prompt.md
```
