# Read a check result

I can tell what lint or a check did, and why it did not pass.

## Acceptance criteria

1. Every result has one public state: waiting, sent, passed, failed, refused, partial or not run. Each result except passed has a reason code. Text, JSON, saved batches and PR evidence use the same result.
2. Local lint reports partial with reason local-only. It checks SVG layout only. It exits 0, but it cannot provide a full lint pass to a gate, workflow or Autopilot.
3. A Sent progress line appears only after the check has reached the server and admission is confirmed.
4. For a new check, the --timeout clock starts after the free lint. An explicit timeout names --timeout and reports timeout-flag. A server or default deadline reports deadline.
5. A saved result can be read without sending the same check again. A partial lint cannot admit a paid check. A caller that cannot run a broken test can use not run with reason broken-test; this change does not skip tests.

## Native verification

Run `node --test test/named-check-states.test.mjs`. It loads the controlled result cases from `test/fixtures/named-check-states/results.json`. It uses the repo's Harbor fixture, fake Runtime HTTP server, fake clock and fake authentication. It also runs the real CLI process for local lint. No hosted interpreter or paid call is needed.

## Rules to check

Only passed can supply a full pass. Every other public state has a nonempty reason code. A check cannot print Sent before admission and dispatch.
