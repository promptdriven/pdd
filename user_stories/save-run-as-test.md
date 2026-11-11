# Keep a command as a test

As a person running a prompt program, I want to keep its last run as a test of a Story only after I confirm that the answer is right, so that a wrong answer does not become a passing test.

## Acceptance criteria

1. `pdd run --save-last finish-task` shows the last confirmed run's input, data before and output, then asks "Is this answer right? [y/N]".
2. Answering y adds that input and observed output as one new step of the existing Story test, which can be selected by `pdd test finish-task`.
3. Answering N, an empty answer or any answer other than y writes nothing and explains how to write the right expected value by hand.
4. Without terminal input and output, saving writes nothing and says that a person must answer in a terminal.
5. After saving, the message names the test file and actual step, asks me to review the data before it, and gives `pdd test finish-task`.
6. An unknown run, changed prompt, missing starting data or starting data incompatible with the Story continuation cannot become a saved passing test.

## Rules to check

The [Try doors prompt](../prompts/cli/try-doors.prompt.md) owns correctness confirmation and safe append. The [runtime client](../prompts/cli/runtime-client.prompt.md) owns the shared engine's Story-free recording and selection at save time. Standalone command execution is separate work (#2739); native tests exercise its existing shared runDoorCall boundary without a Story, then the save command and pdd test selection. Controlled owner responses prove local capture and replay submission, not hosted execution.

Only a terminal's single y permits retaining a case. Editor handoff alone never approves an expected value. Keep the original test's starting world and preceding steps; incompatible data stays pending for manual repair.

Native vectors cover all criteria, including confirmation before editor handoff and no stdin consumption in headless mode. The Runtime scenario selects the actual runSaveLast entry; its current prompt has no Runtime interface for private session storage and terminal interaction, so no interpreter coverage is claimed for this boundary.
