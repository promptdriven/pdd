# Keep the cause found during reproduction

As a person fixing bugs, I want the cause and evidenced relations recorded in a fixed form, so that other issues with the same cause or class do not get separate local fixes.

## Acceptance criteria

1. A reproduced bug records the file, function, flaw, class and explicit relations with exact evidence quotes; no discovered relations is recorded as an empty list.
2. A quote absent from the named issue or code is refused before any GitHub link is written.
3. Only explicitly selected relations write links: needs can block the current issue, same class can put it under an existing Class parent, and duplicate can mark the duplicate; shared cause alone creates no dependency.

## Rules to check

- Check all quotes before any write; their presence does not prove the relation true.
- Refuse self, closed and repeated target issues and unsafe source paths.
- Keep the same Cause and Relations lines in the saved reproduce record and PR 1; legacy runs without a cause still work.
- Never infer ordering, create a class parent, close an issue or change its labels.

```pdd-boundary
prompts/cli/workflow-bug-cause.prompt.md
```
