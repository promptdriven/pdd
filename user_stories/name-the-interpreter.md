# Name the interpreter

I can read "PDD interpreter" in the help and messages that pdd writes, so I know which hosted service checks and runs my prompts.

## Acceptance criteria

1. `pdd --help` calls the hosted service the "PDD interpreter", never says "PDD runtime" or "runtime call", prints nothing to stderr and exits with code 0.
2. `pdd test --help` says that it checks Stories on the PDD interpreter with my gh login, never says "PDD runtime" and exits with code 0.
3. `pdd lint --help` says that it runs the PDD interpreter lint with 0 AI calls, never says "PDD runtime" and exits with code 0.
4. `pdd simulate --help` says that it opens the PDD Simulator on the PDD interpreter, never says "PDD runtime" and exits with code 0.
5. `pdd product --help` says that the product commands make no interpreter calls, never says "runtime" and exits with code 0.
6. `pdd approve --help` still says "runtime interface", the name of the block in a prompt file, prints nothing to stderr and exits with code 0.

## What must not change

Commands, options, exit codes and stdout bytes stay the same. Only the words for the hosted service change.

These machine-read words keep "runtime": the schema ids `prompt-runtime.*`, the default host, `PDD_RUNTIME_URL`, the folder `~/.pdd/runtime`, the block label `Runtime interface` in a prompt file and the detection of the server text "The runtime opens soon.". The summary line is `Prompt tests (story): ...` ([Read the Prompt tests line](prompt-tests-line.md)); pdd still reads the older `Runtime check (story): ...` lines. A server text that pdd prints as it got it, such as "The runtime is busy. Try again later.", stays as the server sent it.

## Rules to check

Every line that pdd writes itself for a person calls the hosted service "the PDD interpreter", or "the interpreter" after the first mention. This includes help, errors, progress lines, status lines, PR text and the Try guide text. Forbidden: "PDD runtime" or "the runtime" for the service in such a line, for example "Your GitHub login sam is not on the PDD runtime invite list yet." or "Checking 3 files (29 KB) on the PDD runtime (lint, 0 AI calls)…".

A machine-read word from the list above must not change. Forbidden: a changed schema id, host, setting name or folder; a prompt block that pdd no longer finds; an older `Runtime check` line that the PR and status readers no longer read; or a gate answer "The runtime opens soon." that pdd no longer detects. A message that tells me to add or fix the block keeps the words "Runtime interface", because I must find them in the file.

The test file checks the help lines. The error, progress and status lines need an interpreter answer, so the code area checks them with Node tests.
