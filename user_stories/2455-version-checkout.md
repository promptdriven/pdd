# Distinguish checkout builds in `pdd --version`

As a tester using a local checkout or GitHub branch, I can identify that build in `pdd --version` and distinguish it from the release with its branch and commit.

## Acceptance criteria

1. Running `pdd --version` from the approved checkout or branch build prints the package version with a `-dev.<branch>.<sha>` suffix, such as `0.1.9-dev.feature-2455-bd781e7d.5a45a2c8b`, followed by one newline and no package-name prefix.
2. Running `pdd --version` from the published release continues to print only the release version, such as `0.1.9`, followed by one newline.

## Rules to check

- The branch and commit identify the exact checkout build; the approved branch encoding and SHA length remain to be decided before implementation.
- PATH diagnostics and stale-skill diagnostics stay on stderr and do not change the version-only stdout contract.
