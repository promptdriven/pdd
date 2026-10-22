# Prepare the Prompt PR

If the prompt changed, the `publish-prompt-pr` stage publishes a Prompt PR with the approved prompt, Story, authored expectations, and current check evidence. The person reviews and merges the current revision before code work begins; the linked wait stage holds the workflow until then.

If the prompt was already correct, record that conclusion and skip this PR. Do not edit a correct prompt merely to create a separate review stage.
