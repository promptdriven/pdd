# Keep an uncertain run link

I can see which run needs repair when GitHub cannot verify its saved issue.

## Acceptance criteria

1. Status marks phone-1 unverified after a 503 reply for issue 81, and keeps server-1 and barista-1 ready.
2. Starting phone-1 after that reply fails without creating an issue or starting work, and keeps the saved hint.
