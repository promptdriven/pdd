# Exact calculator command

As a prompt author writing numeric test cases, I want a local exact calculator command so that I can compute pricing, rounding, and remainder expectations offline without floating-point drift or ad-hoc scratch scripts.

## Acceptance criteria

1. Running `pdd calc "4000 - floor(4000 * 540 / 10000)"` prints "3784" and running `pdd calc "0.1 + 0.2"` prints "0.3", each to stdout with empty stderr and exit code 0.
2. Running `pdd calc "-7 div 2"` prints "-3" and running `pdd calc "-7 mod 2"` prints "-1", using truncation toward zero with empty stderr and exit code 0.
3. Running `pdd calc "1 / 3"` prints "1/3" and running `pdd calc "-4 / 6"` prints "-2/3", printing nonterminating quotients as reduced fractions with a positive denominator, empty stderr and exit code 0.
4. Running `pdd calc` on "round_half_up(2.5)", "round_half_up(-2.5)", "round_half_even(2.5)", "round_half_even(3.5)", and "max(ceil(1.2), trunc(-2.9), min(10, 5))" prints "3", "-3", "2", "4", and "5" respectively, with empty stderr and exit code 0.
5. Running `pdd calc` on a blank expression, division by zero ("1 / 0"), or an unknown function ("foo(1)") prints nothing to stdout, writes one "pdd calc:" error line to stderr, and exits with code 2.

## Rules to check

- Never silently round or approximate a nonterminating quotient into a decimal.
- Never print anything to stdout when an expression fails, and never print anything to stderr when an expression succeeds.

```pdd-boundary
prompts/cli/calc.prompt.md
```
