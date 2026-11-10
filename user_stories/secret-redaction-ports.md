# Redact remembered, environment and streamed secrets through Runtime ports

I can register secrets in memory, collect known secrets from environment entries, redact secrets across stream chunks via an emission port, and sanitize diagnostic strings.

```pdd-boundary
prompts/cli/secret-redaction.prompt.md
```

## Acceptance criteria

1. Remembering secrets stores deduplicated values and combines them with secret-named environment entries in `knownSecretValues`.
2. Streaming redaction holds back undecided secret prefixes across chunk boundaries, emits `[redacted]` once the secret completes, and flushes remaining safe text on `end`.
3. Scalar `redactSecrets` replaces remembered values and token patterns with `[redacted]`.
4. Invalid inputs or writing to a closed stream fail with `empty-secret-values`, `invalid-secret-env`, `invalid-stream-secrets`, `stream-closed` and `invalid-redact-target`.
