# service

As a developer testing a service client wrapper, I want lookups to forward exact IDs to an injected callback deterministically, so that forwarding is verified without live network access.

## Acceptance criteria

1. Looking up book-7 forwards that exact ID once and returns Available from the supplied reply.
