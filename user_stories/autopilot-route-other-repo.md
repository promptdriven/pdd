# Flag work filed in the wrong repository

As a repository maintainer, I want core Autopilot to flag work that names a different repository before trying to claim it, so that I can route it without wasting a work slot.

## Acceptance criteria

1. Autopilot selects `promptdriven/prompt-runtime` for an issue titled `[prompt-runtime] Fix duplicate retries` and marks it `pdd:elsewhere` instead of claiming it.
2. A file explicitly targeted in `promptdriven/runtime-client` or a service explicitly targeted in `promptdriven/pdd_cloud` gets the same treatment for its own repository.
3. Mentioning another repository for context, or explicitly targeting both the current and another repository, does not trigger routing.

## What must not change

- GitHub routing notes name the destination, but a maintainer still decides where to move the issue.
