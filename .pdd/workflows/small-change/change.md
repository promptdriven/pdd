# Make the change

Change only the agreed scope. A small change can proceed without creating prompts or adopting prompt space. If an existing prompt is the source of the behavior being corrected, update it before changing code and keep both changes in the same PR.

Add focused tests for changed behavior through the public code boundary. Keep expected results independent from the implementation. Do not add new dependencies or unrelated prompt rewrites for a contained fix.
