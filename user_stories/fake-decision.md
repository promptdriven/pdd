# decision

As a developer testing a lookup decision module, I want to verify pure reply handling and service-backed lookups deterministically, so that no live network call is needed.

## Acceptance criteria

1. A supplied unavailable reply shows Unavailable without a request; looking up book-7 requests it once and shows Available for an available reply.
