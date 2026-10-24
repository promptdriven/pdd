# Leave merge to the normal process

Follow the repository's existing checks and authority for the current revision. A person decides whether to merge. Do not merge or enable automatic merge just because the recipe is complete. If feedback changes behavior, rerun the affected checks and show the new diff.

The local runner observes the exact recorded PR and its head on resume. It advances only after a real merge, never merges on the person's behalf, and stops before a new effect when resumed without a decision. After a separate prompt PR merges, implementation must preserve the accepted prompt revision and start its code branch from a base containing that merged revision; do not silently rewrite the base or existing work.
