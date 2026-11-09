# Shared secret redaction

Own `src/secret-redaction.mjs`. Export `redactSecrets(value, secrets = [])`,
returning a diagnostic string. Exact value redaction is complete for every
nonempty secret value known to the process. Collect values from environment
names containing TOKEN, SECRET, PASSWORD, PASSWD, CREDENTIAL, AUTHORIZATION or
COOKIE, names ending in _KEY, and API key names (including GH_TOKEN,
GITHUB_TOKEN and OPENAI_API_KEY). Include explicit caller secrets and gh and
agent credentials read by pdd. Remember these credentials only in memory;
never save the value inventory or include it in child command arguments.
Export `rememberSecrets(...values)` to register read credentials and
`knownSecretValues(env = process.env, secrets = [])` to obtain the deduplicated
inventory, including process environment values and explicit invocation values.
Replace exact values with `[redacted]` before pattern matching or truncation.

Export `redactingValues(emit, secrets)` with write(text) and end() methods.
It redacts exact values on each independent string stream, using a bounded
overlap window derived from the longest known value. Transport chunks and line
breaks do not end that window. A value containing line breaks is matched as
supplied, without normalization. Scan before discarding oversized lines. Do not
emit an undecided prefix of a known value. At EOF redact complete matches and
release safe remaining text. Call emit(text, original) with strings: text is
safe output and original is the consumed input for internal byte accounting.
Original can contain a secret; never store or forward it. A caller can use
lossless byte strings when it encodes secret values the same way. Preserve
ordinary text and recover after a match.

Pattern redaction is a best-effort extra layer for unknown values, not a
complete guarantee. Reuse the agent guide's string sanitizer: remove URL
user/password and secret query values; redact PEM private keys (including
unterminated blocks), GitHub `gh[pousr]_` and `github_pat_` tokens, OpenAI `sk-`
tokens, Basic/Bearer credentials, and case-insensitive colon/equal pairs for
key, token, password, secret, api_key, authorization, cookie and credential.
Also cover Google `AIza` API keys and `ya29.` access tokens. Pairs accept quoted
or unquoted values. Redact an entire Authorization header value, including
other schemes. Basic/Bearer whitespace includes line breaks; bounded stream
recognition must retain a pending scheme across whitespace and omitted lines,
then suppress its credential through the next whitespace or EOF. Remove control
bytes except tab, CR and LF. Unknown encodings, unrecognized formats and
arbitrary positional values may evade patterns. Exact matching does not cover
transformed, encoded or altered copies of a known value. Callers must pass
newly learned values before emitting output that can contain them.

## Dependencies

- Native JavaScript strings, regular expressions and URL parsing.
