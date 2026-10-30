# Try my server with my screens

I can try my phone, server and barista together when my server has no screen.

## Acceptance criteria

1. With phone, server and barista selected, I see only the phone and barista screens, and each tap still includes the server's background work.
2. My server's starting data is included even though the server has no screen, and trying it leaves my project files unchanged.
3. If I select only the server, Try explains that no screen is available.

## Verification scope

The Runtime scenario checks the joined product and the server-only refusal code. Ordinary Node tests replay the complete cases from `test/native/product-server-without-screen.json`, including the explanation that no screen is available; Runtime error checks cannot inspect error messages.
