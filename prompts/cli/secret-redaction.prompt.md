# Shared secret redaction

Own `src/secret-redaction.mjs`. Export `redactSecrets(value, secrets = [])`,
returning a string safe for diagnostic evidence. Replace exact nonempty supplied
secret strings with `[redacted]`. Reuse the agent guide's existing string
sanitizer: remove URL user/password and secret query values; redact PEM private
keys (including unterminated blocks), GitHub `gh[pousr]_` and `github_pat_`
tokens, OpenAI `sk-` tokens, Basic/Bearer credentials, and case-insensitive
colon/equal pairs for token, password, secret, api_key, authorization, cookie
and credential. Also cover bare `key`, Google `AIza` API keys and `ya29.` access
tokens. Pairs accept quoted or unquoted values. Redact an entire Authorization
header value, including schemes other than Basic/Bearer. Remove control bytes
except tab, CR and LF. Preserve ordinary diagnostic text. Redaction precedes
storage and truncation; callers with streams must supply complete logical text
or suppress incomplete oversized values, never sanitize chunks independently.

## Dependencies

- Native JavaScript strings, regular expressions and URL parsing.
