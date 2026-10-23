# Bug workflow

Use this recipe when an observed behavior violates an existing expectation. Reproduce the report first, then correct the owning prompt when its contract is wrong or incomplete. Check the prompt and optionally Try it before the person's approval. If the prompt changes, the Prompt PR is reviewed and merged before code work. Then replay accepted vectors, run tests and applicable formal checks, and send the Code PR for person review and merge.

1. [Reproduce the bug](reproduce.md)
2. [Write the corrected prompt and Story](prompt-story.md)
3. [Check the prompt and examples](check.md)
4. [Try the behavior, when useful](try.md)
5. [Get the person's approval](approve.md): approval: story
6. [Publish the Prompt PR, when prompts changed](prompt-pr.md): publish-prompt-pr
7. [Wait for the Prompt PR merge](prompt-merge.md): wait-for-merge: pr1
8. [Implement the fix](build.md)
9. [Replay vectors and run checks](verify.md)
10. [Publish the Code PR](code-pr.md): publish-code-pr
11. [Wait for the Code PR merge](code-merge.md): wait-for-merge: pr2

If the existing prompt already states the correct behavior, record why a prompt edit is unnecessary and proceed without a Prompt PR. Do not invent a prompt defect to force a prompt change.
