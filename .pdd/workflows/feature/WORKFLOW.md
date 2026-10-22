# Feature workflow

Use this recipe for a new behavior that needs both a prompt contract and a code change. Follow the linked steps in order. Skip a visual only when the feature has no visible interface, and skip Try when it is not useful or the installed release does not support it.

1. [Understand the request](understand.md)
2. [Choose a visual direction](visual.md)
3. [Write the prompt and Story](prompt-story.md)
4. [Check the prompt](check.md)
5. [Try the behavior, when useful](try.md)
6. [Get the person's approval](approve.md): approval: story
7. [Publish the Prompt PR](prompt-pr.md): publish-prompt-pr
8. [Wait for the Prompt PR merge](prompt-merge.md): wait-for-merge: pr1
9. [Implement the approved behavior](build.md)
10. [Run vectors, tests, and applicable formal checks](verify.md)
11. [Publish the Code PR](code-pr.md): publish-code-pr
12. [Wait for the Code PR merge](code-merge.md): wait-for-merge: pr2

If no prompt change is needed, record that in the Story and skip the Prompt PR. Do not implement against a prompt revision that is still awaiting review.
