# Recover a held check from two terminals

I can retry a saved check batch in two terminals without paying twice or losing a job's results.

## Acceptance criteria

1. When two retries recover the same held check, only one new check is sent. The owning command shows its passed result with four AI calls; a competing command sends nothing, exits 2 and says to wait, then read this batch. The saved batch keeps every sent request ID and receipt.
2. A batch read that overlaps a retry cannot erase the new request ID or its result. Reading a UUID keeps its existing raw-receipt-only behavior.
3. A busy batch never blocks a different batch. A command that cannot acquire ownership immediately sends nothing and leaves the saved batch and summary unchanged.
4. Ownership is released after success, a refusal, an exception or interruption. A dead owner on the same host can be recovered with one warning, while a live, foreign-host or uncertain owner cannot be displaced merely because time passed.
