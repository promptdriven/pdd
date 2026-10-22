# Feature workflow

Use this recipe for a new behavior that needs both a prompt contract and a code change. Follow the linked steps in order. Skip a visual only when the feature has no visible interface, and skip Try when it is not useful or the installed release does not support it.

1. [Understand the request](understand.md)
2. [Choose a visual direction](visual.md)
3. [Write the prompt and Story](prompt-story.md)
4. [Check the prompt](check.md)
5. [Try the behavior, when useful](try.md)
6. [Get the person's approval](approve.md)
7. [Prepare the Prompt PR](prompt-pr.md)
8. [Implement the approved behavior](build.md)
9. [Run vectors, tests, and applicable formal checks](verify.md)
10. [Prepare and review the Code PR](code-pr.md)
11. [Person merges the reviewed revision](merge.md)

If no prompt change is needed, record that in the Story and skip the Prompt PR. Do not implement against a prompt revision that is still awaiting review.
