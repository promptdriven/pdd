# Prepare and review the Code PR

The `publish-code-pr` stage publishes a Code PR with the implementation, focused tests, applicable vector replay, formal evidence if any, and limitations. Link the accepted Story and current prompt revision.

The person reviews the diff and evidence for the current PR revision. The linked wait stage remains paused until the person merges it. If the revision changes, recheck what the change invalidated and request a current review. Keep missing evidence visible; do not turn it into a pass.
