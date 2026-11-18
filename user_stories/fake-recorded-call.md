# Replay saved lookup replies

As a developer who runs Story checks, I want to replay my saved lookup cases against native code, so that I can check the same answers without another AI call.

## Acceptance criteria

1. The first lookup of book-7 calls the supplied service once and returns Available from the first saved reply.
2. The second lookup of book-7 calls the supplied service once and returns Reserved from the second saved reply.

## What must not change

- The existing fixed-answer service example and its original Story cases keep their behavior.

## Rules to check

- Replay uses the original saved replies and checks. Forbidden: changing an expected value, omitting a check, or treating an unrun step as passed.
- A missing saved reply never starts a live command, service or model. Forbidden: silent live fallback.
- Whole numbers keep their exact value during native transport and comparison. Forbidden: rounding a large integer into a passing result.
- Fixture counters advance in step order, while call counts restart for each step. Forbidden: reusing the first reply for the second lookup.
