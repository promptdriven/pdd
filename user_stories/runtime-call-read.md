# Read an interrupted command

I can read a command's final result using the recovery command pdd printed when it stopped.

## Acceptance criteria

1. Reading a call ID shows its final output, error output, program exit code and known AI usage without running the command again.
2. A running call stays pending and prints its exact read command.
3. An interrupted command that may have run prints its exact read command.
4. Reading one call never shows another call's result.

## Rules to check

The owner ledger is authoritative. A read sends no operation again and does not claim to release held calls or restart execution. A successful receipt can contain a nonzero program exit code. Existing batch reads continue to work.

Verification: `node --test test/runtime-call-read.test.mjs` exercises authenticated owner receipts and interruption with a fake service; it makes no model calls.
