# Stop a Try with its Story path

As a developer who tries a Story in the Simulator, I can stop an open Try with the Story path that started it, so that I can close my session without switching to the Story basename.

## Acceptance criteria

1. `pdd simulate --stop user_stories/fakes/tester-panel.md` prints `The Try link for "I can control test events while I try Pocket" is stopped.`, exits with code 0 and saves the open Try list as empty.
2. When `tester-panel` is open, `pdd simulate --stop user_stories/fakes/other.md` prints `No open Try for "user_stories/fakes/other.md". Open Try links: tester-panel.` to stderr, exits with code 2 and saves nothing.

## Rules to check

- `--stop [STORY]` matches an open Try record by Story name, Story path (normalized relative to the repository root, or by `<story>.md` in a `user_stories` folder when an older saved record has no `storyPath`), test path or test file name. Forbidden: refusing a Story path that `pdd simulate <story-path>` accepts when that Story's Try is open. Native test: `test/runtime-try.test.mjs` stops an open Try by Story name, repository-relative Story path, subdirectory-relative Story path and a legacy record without `storyPath`.
- When `--stop` finds no matching open Try, it never sends `DELETE /v1/try/<id>` to the interpreter. Forbidden: calling `DELETE` on exit 2. Native test: `test/runtime-try.test.mjs` checks that `--stop` with an unknown Story path makes 0 `DELETE` requests and keeps the saved Try record.
