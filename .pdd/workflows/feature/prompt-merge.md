# Follow the agreed prompt review route

If the person chose a separate prompt PR and requires its merge before implementation, follow that repository process and use the accepted revision. Otherwise continue under the agreed scope in the current change. No automated wait or merge gate runs here.

Keep requested revisions and unresolved decisions visible. Do not infer that a PR merged, change repository protection rules or enable automatic merge.

The local runner observes the exact recorded PR and its head on resume. It advances only after a real merge, never merges on the person's behalf, and stops before a new effect when resumed without a decision. After a separate prompt PR merges, implementation must preserve the accepted prompt revision and start its code branch from a base containing that merged revision; do not silently rewrite the base or existing work.
