# Wait for the Prompt PR merge

The `wait-for-merge: pr1` stage holds the workflow until the person merges the current Prompt PR. Code work starts only after that merge is confirmed and uses the prompt revision that landed. If the prompt PR is revised, the person reviews the current revision before merging.
