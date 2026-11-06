# Run tests inside a workflow chat

I can run `npm test` inside a workflow chat and get the same test result as outside the chat, without tests reading the chat's live session or waiting for input I did not provide.

## Acceptance criteria

1. Running the same tests with the same test outcomes inside and outside a workflow chat gives the same exit status and output.
2. A test never reads the live Herdr session or the agent session of the shell that runs it.
3. A test never waits on input that it does not supply.
4. A failed test keeps its nonzero exit status and useful failure output.

## Rules to check

The child test process receives no environment variable whose name starts with `HERDR_` or equals `PDD_AGENT_SESSION`. It does not inherit the caller's stdin, stdout or stderr. Its stdin is ignored, and its stdout and stderr are captured. Any child that receives one of those session markers or caller streams is forbidden.

## Native verification boundary

The prompt test checks the injected launch arguments and fixed program replies. It does not create a real Node child, inspect OS socket ownership or prove termination. Verify those effects with native tests in the code step. The issue's hang and its cause remain unproved by the current reproduction.
