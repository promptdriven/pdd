# Open a pull request from a symlinked repository path

As a workflow user, I want a run started from a repository reached through a folder symlink to open its pull request, so that the repository's physical location does not cause a false unsafe-body rejection.

## Acceptance criteria

1. Preparing a pull request from a repository path reached through a symlink succeeds and returns the prepared pull-request intent; a body file whose physical parent is inside the repository remains accepted, while a body file outside the repository remains refused as unsafe.

## Rules to check

- The repository path may be a symlink alias for its physical directory.
- Body-path safety is evaluated on physical paths: an in-repository body is accepted, and an outside body is refused before writing.
