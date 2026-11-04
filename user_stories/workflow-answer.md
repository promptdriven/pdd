# Answer a workflow question

As someone who answers a workflow question from a phone, I can send an answer with `pdd workflow answer`, so that the run log records an answer instead of a change request.

## Acceptance criteria

1. When run #2576 waits in the `story` chat for "Which date format?", `pdd workflow answer 2576 "ISO"` sends "The person answers your question: ISO Go on with the step." to the `story` chat, saves round 1 in the #2576 run log with text "ISO" and `answer` set to `true`, clears the open question, sets the #2576 run state to "running", prints "Sent your answer to the story chat of #2576. The agent goes on with the step." and exits with code 0.
2. When run #2576 has no open question, `pdd workflow answer 2576 "ISO"` prints "No question is open for promptdriven/pdd#2576." to stderr, exits with code 1, sends 0 chat messages and saves nothing.
3. With no open question left on run #2576, `pdd workflow changes 2576 "Use ISO dates"` sends "The person asks for changes: Use ISO dates\nRevise in this chat, run done again for the step you changed, then show the result and ask again." to the `story` chat, saves round 2 in the #2576 run log with text "Use ISO dates" and no `answer` flag, prints "Sent your change request to the story chat of #2576." and exits with code 0.

## Rules to check

- `pdd workflow answer ISSUE TEXT` is listed in `docs/cli.md` and `--help`, and dispatches through `src/pdd-cli.mjs` to `answerRun`. Native test: `test/docs-commands.test.mjs` and `test/workflow-runner.test.mjs` verify help, CLI dispatch and `answerRun`.
- When a question is open, `pdd workflow changes ISSUE TEXT` still sends the text as an answer and records `answer: true`. Native test: `test/workflow-runner.test.mjs` runs `changeRun` while a question is open and checks the chat message and run log.
