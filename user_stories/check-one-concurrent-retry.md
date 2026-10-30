# Recover a held check from two terminals

I can retry a saved check batch in two terminals without paying twice or losing a job's results.

## Acceptance criteria

1. When two retries recover the same held check, only one new check is sent. Both commands can show its passed result with four AI calls, and the saved batch keeps that request ID and its receipt.
2. A batch read that overlaps a retry cannot erase the new request ID or its result. Reading a UUID keeps its existing raw-receipt-only behavior.
3. A busy batch never blocks a different batch. Waiting is bounded and interruptible; a command that cannot acquire ownership sends nothing and leaves the saved batch and summary unchanged.
4. Ownership is released after success, a refusal, an exception or interruption. A dead owner's abandoned lock can be recovered, while a live or uncertain owner cannot be displaced merely because time passed.
