# Open a pull request from a symlinked repository path

As a workflow user, I want a run started from a repository reached through a folder symlink to prepare its pull request without a false body-file rejection, so that the checkout alias and run folder name do not affect publication.

## Acceptance criteria

1. Preparing a pull request from a repository path reached through a folder symlink succeeds and returns the prepared intent with its marker; preparation does not read, write or validate a PR body file.

## Rules to check

- The repository path may be a symlink alias for its physical directory, regardless of the alias or run folder name.
- Body text is supplied by the caller at publication; `gh pr create` receives it through `--body-file -` on stdin.
- Clean-worktree, committed-topic-branch and same-GitHub-origin safety checks remain in force.
