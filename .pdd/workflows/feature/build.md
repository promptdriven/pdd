# Implement the approved behavior

Start from the repository's current reviewed base and implement only the approved Story. Use the prompt as the behavior source. When the Prompt PR was needed, use the revision that the person reviewed and merged.

For each changed behavior, add or update a meaningful test through the public code boundary. Keep the test's expected result independent from the implementation. Do not include runtime source or internal schemas in the public change.
