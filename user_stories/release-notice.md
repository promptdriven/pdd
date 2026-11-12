# See a newer pdd release

As a pdd user, I want to know when a newer release is available so I can update my installation.

## Acceptance criteria

1. When pdd 0.1.28 checks and the latest release is v0.2.0, it prints `pdd 0.1.28: update available (0.2.0). Run: npm install -g github:promptdriven/pdd` on stderr.
2. When the latest release is v0.1.28 or older, or the release check fails, pdd prints no update notice.
3. In CI, pdd makes no release check and prints no update notice.
4. pdd never starts an update automatically, including during a workflow command.

## Command coverage

The next ordinary non-CI `pdd test STORY` that contacts the interpreter shows the same one-line update notice as `pdd --version` when a newer release exists. The notice keeps stdout and the command's exit status unchanged, uses no token for the public release lookup, and checks for a release at most once even when the command sends several interpreter requests. A failed release lookup never stops the interpreter request.

Local help, completion, workflow list and view, and `pdd test` local modes, local cached results and early refusals keep their existing behavior without a release lookup. Native executable tests cover command dispatch; the Runtime scenarios below cover the release decision helper.
