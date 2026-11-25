---
kind: native-only
reason: Thin native-only worker adapter wiring vault storage and audit ports
---

# Native worker adapter

Thin native-only adapter implemented in `src/worker.mjs` that wires the vault and audit adapters.

## Port bindings

- Bind `vault.read`, `vault.write`, and `audit.append` to the isolated worker runtime.

## Boundary and runtime contract

- Persist vault entries in transactional SQLite storage with atomic compare-and-set updates and isolated process credentials over loopback HTTP.

## Error mapping

- Map missing keys to HTTP `404` (`not_found`), invalid inputs to HTTP `400` (`invalid_request`), and storage failures to HTTP `503` (`persistence_unavailable`).

## Real-host verification cases

1. Execute concurrent `vault.write` calls against a live SQLite database and verify monotonic version numbering with zero lost updates.

## Dependencies

- [Vault service](vault.prompt.md)
