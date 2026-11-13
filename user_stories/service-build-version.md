# Read the interpreter and service builds

As a PDD user, I want `pdd -VV` to show the hosted service revision alongside the interpreter engine revision when reported, so that I can tell which server deployment answered.

## Acceptance criteria

1. When `/v1/version` reports engine revision "0123456789abcdef0123456789abcdef01234567" and service revision "fedcba0987654321fedcba0987654321fedcba09", `pdd -VV` prints "PDD CLI: 0.1.29", "PDD interpreter: 0123456789abcdef0123456789abcdef01234567", "PDD service: fedcba0987654321fedcba0987654321fedcba09" and the supported format lines, exiting with code 0.
2. When `/v1/version` includes `service_sha` as "unknown" or a value that is not 40 hexadecimal digits, `pdd -VV` prints "PDD service: unknown" without printing raw server text, exiting with code 0.
3. When `/v1/version` omits `service_sha`, `pdd -VV` omits the "PDD service:" line and keeps its existing output, exiting with code 0.

## What must not change

- `pdd -V`, `pdd --version`, missing-token fallback, origin validation, ten-second GET limit and format-list validation stay unchanged.

## Rules to check

- Only an exact 40-character hexadecimal `service_sha` is printed in lowercase; any other present `service_sha` value prints `unknown`, preventing control characters or arbitrary server prose from reaching terminal output.

```pdd-boundary
prompts/cli/interpreter-version.prompt.md
```
