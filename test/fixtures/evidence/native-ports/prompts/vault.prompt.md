# Vault service

Stores and audits versioned secret entries for authorized workers.

## Ports

- `vault.read`: read a stored entry by key and return `{ found, value }`.
- `vault.write`: write a versioned entry by key and return `{ saved, version }`.
- `audit.append`: append an immutable audit event and return `{ ref }`.

## Dependencies

None.
