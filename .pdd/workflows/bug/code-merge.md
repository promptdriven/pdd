# Leave merge to the normal process

Let the person review the current diff and evidence. Follow the repository's existing checks and merge authority. Revised behavior needs relevant tests and current review. Do not merge, enable automatic merge or claim publication solely because this recipe reached its last step.

The local runner observes the exact recorded PR and its head on resume. It advances only after a real merge, never merges on the person's behalf, and stops before a new effect when resumed without a decision. After a separate prompt PR merges, implementation must preserve the accepted prompt revision and start its code branch from a base containing that merged revision; do not silently rewrite the base or existing work.
