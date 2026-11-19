# Exact calculator command

`src/calc.mjs` implements the local `pdd calc` command for exact arbitrary-precision arithmetic so prompt authors and agents can compute numeric expected values without floating-point drift, shell `bc` bugs, or ad-hoc scratch scripts.

## Public API

This module is pure and declares no external ports or resources.

- `evaluateCalcExpression(expression)` — evaluates one arithmetic expression string using exact arbitrary-precision rational arithmetic and returns its canonical string representation. Throws a `SyntaxError` with `code = "scenario-derivation-invalid"` and a short single-line message when the expression is blank, malformed, divides by zero, or exceeds a resource limit.
- `runCalc({ expression } = {})` — evaluates `{ expression }` directly via `evaluateCalcExpression` and returns `{ exit_code, stdout, stderr }`:
  - When `expression` is missing, not a string, or blank after trimming, returns `{ exit_code: 2, stdout: "", stderr: "pdd calc: missing expression\n" }`.
  - On success, returns `{ exit_code: 0, stdout: "<result>\n", stderr: "" }`.
  - On error, collapses any whitespace runs in the error message to single spaces (falling back to `"invalid expression"` when empty) and returns `{ exit_code: 2, stdout: "", stderr: "pdd calc: <reason>\n" }`.

## Expression language

- **Numbers:** unsigned decimal integer or fractional literals with optional scientific exponent (`e` or `E`, optional `+`/`-`, integer exponent with `|exp| <= 10,000`), parsed as exact rationals (for example `4000`, `0.1`, `1e-3`, `2.5E+2`).
- **Grouping & whitespace:** ASCII whitespace is ignored between tokens; parentheses `(` `)` group subexpressions.
- **Operators (highest to lowest precedence):**
  1. Unary `+` and `-`.
  2. Left-associative `*`, `/`, `div`, `mod` (`div` and `mod` are case-sensitive lowercase keyword operators).
  3. Left-associative `+` and `-`.
- **Integer quotient & remainder (`div`, `mod`):**
  - `a div b` is the exact integer quotient truncated toward zero (`trunc(a / b)`): `-7 div 2` is `-3`, `7 div -2` is `-3`, `-7 div -2` is `3`.
  - `a mod b` is the matching remainder `a - (a div b) * b`: `-7 mod 2` is `-1`, `7 mod -2` is `1`, `-7 mod -2` is `-1`.
- **Built-in functions (case-sensitive lowercase names):**
  - `min(x, ...)` and `max(x, ...)` take one or more arguments and return the exact minimum or maximum.
  - `floor(x)` returns the greatest integer `<= x`.
  - `ceil(x)` returns the least integer `>= x`.
  - `trunc(x)` returns the integer part toward zero.
  - `round_half_up(x)` rounds to the nearest integer with half-integer ties rounded away from zero (`round_half_up(2.5)` is `3`, `round_half_up(-2.5)` is `-3`).
  - `round_half_even(x)` rounds to the nearest integer with half-integer ties rounded to the nearest even integer (`round_half_even(2.5)` is `2`, `round_half_even(3.5)` is `4`, `round_half_even(-2.5)` is `-2`).
- **Disallowed constructs:** no variables, assignments, strings, boolean or bitwise operators, loops, arbitrary identifiers, or side effects. Unknown functions, wrong argument counts, trailing tokens, unbalanced parentheses, and division or modulo by zero are refused.

## Canonical output format

Every valid result is reduced to lowest terms `p / q` with `q > 0`, `gcd(|p|, q) = 1`, and zero normalized to `0 / 1`:

| Condition | Format | Examples |
| --- | --- | --- |
| `q == 1` | Exact decimal integer with no leading zeros or `+` sign | `0`, `3784`, `-3` |
| `q` has only prime factors `2` and `5`, and exact decimal has `<= 10,000` fractional digits | Terminating decimal with no trailing fractional zeros | `0.3`, `-1.25` |
| Any other reduced rational | Reduced fraction `p/q` with positive denominator (never silently rounded) | `1/3`, `-2/3` |

## Domain decisions

- **Exact rational arithmetic:** All operations use exact arbitrary-precision rationals rather than IEEE-754 floating point, so `0.1 + 0.2` prints `0.3` and `4000 - floor(4000 * 540 / 10000)` prints `3784`.
- **Shared evaluator semantics:** Native code delegates `evaluateCalcExpression` to `evaluateDerivation` re-exported from `@promptdriven/runtime-client` via `src/runtime-seam.mjs` so `pdd calc` and scenario check `derivation` verification use one single source of truth.
- **Resource budgets:** Reject expressions longer than `10,000` characters, nesting depth greater than `128`, exponents with `|exp| > 10,000`, intermediate or final reduced numerator/denominator exceeding `10,001` decimal digits (`>= 10^10001`), or canonical output longer than `20,004` characters.
- **Exit and stream separation:** Valid calculations always exit `0` with `<result>\n` on `stdout` and empty `stderr`. Any missing, invalid, divide-by-zero, or over-budget input exits `2` with empty `stdout` and one `pdd calc: <reason>\n` line on `stderr`.
- **Zero side effects:** `pdd calc` declares no external ports and performs no file reads or writes, no network or interpreter calls, no credential lookups, and no subprocess execution. The CLI dispatcher writes any non-empty `stdout` or `stderr` returned by `runCalc` to the terminal streams.

## Dependencies

None.
