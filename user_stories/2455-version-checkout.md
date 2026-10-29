# Distinguish checkout builds in `pdd --version`

As a tester using a local checkout or GitHub branch, I can identify that build in `pdd --version` and distinguish it from the release with its branch and commit.

## Acceptance criteria

1. Running `pdd --version` from a checkout or branch build runs `git symbolic-ref --short HEAD`, replaces every `/` in that branch with `-` while leaving letters, digits, `.`, `_` and `-` unchanged, takes the first 9 hexadecimal characters from `git rev-parse HEAD`, and prints the package version followed by exactly `-dev.<encoded-branch>.<sha9>` (for example `0.1.9-dev.feature-2455-bd781e7d.5a45a2c8b`), one newline, and no package-name prefix.
2. Running `pdd --version` from the published release continues to print only the release version, such as `0.1.9`, followed by one newline.

## Documentation deliverable

Repository usage documentation explains how to test a fix before release. It shows `npm install -g .` for a local checkout, `npm install -g github:promptdriven/pdd#BRANCH` for a GitHub branch, and `pdd --version` after either install. It shows the matching skills branch command `npx skills add promptdriven/pdd#BRANCH -g -a codex -a claude-code -y`, then shows restoring the release with the release branch in both commands. The documentation records the planner's evidence that local and branch npm installs already work and explicitly closes the obsolete managed `~/.pdd` installer scope.

## Rules to check

- The checkout suffix is deterministic: `git symbolic-ref --short HEAD` supplies the branch, every `/` becomes `-`, letters, digits, `.`, `_` and `-` remain unchanged, and `git rev-parse HEAD` supplies the first 9 hexadecimal characters. The format is exactly `-dev.<encoded-branch>.<sha9>`.
- PATH diagnostics and stale-skill diagnostics stay on stderr and do not change the version-only stdout contract.
- The documentation commands reflect existing npm behavior; they do not define a new installer or managed state.
