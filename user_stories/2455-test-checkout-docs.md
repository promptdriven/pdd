# Document testing a checkout fix before release

As a tester, I can follow concise repository instructions to install a local or branch checkout, install the matching branch skills, verify the development version, and restore the release afterward.

## Acceptance criteria

1. The instructions show `npm install -g .` for a local checkout and `npm install -g github:promptdriven/pdd#BRANCH` for a GitHub branch, followed by checking `pdd --version`.
2. The instructions show `npx skills add promptdriven/pdd#BRANCH -g -a codex -a claude-code -y` for testing the matching skills branch.
3. The instructions show restoring the release with the release branch in both the npm install and `npx skills add` commands, and state that a separate managed `~/.pdd` development installer is out of scope.

## Rules to check

- The documented commands reflect the planner's evidence that local and branch npm installs already work.
- Documentation must not claim that checkout testing requires a new installer or managed state.
