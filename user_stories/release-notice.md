# See a newer pdd release

As a pdd user, I want to know when a newer release is available so I can update my installation.

## Acceptance criteria

1. When pdd 0.1.28 checks and the latest release is v0.2.0, it prints `pdd 0.1.28: update available (0.2.0). Run: npm install -g github:promptdriven/pdd` on stderr.
2. When the latest release is v0.1.28 or older, or the release check fails, pdd prints no update notice.
3. In CI, pdd makes no release check and prints no update notice.
4. pdd never starts an update automatically, including during a workflow command.
