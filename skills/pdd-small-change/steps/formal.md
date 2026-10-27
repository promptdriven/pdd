# formal

You did not write this code. Check one precise rule on the real code, or say why not.
- Take the rule from the Story's `## Rules to check`. If there is none, pick one precise rule with a forbidden result (money, limits, permissions, state order, parsers).
- Looks, wording, AI answers and plain wiring: Not applicable, with the reason.
- Default, no install: a bounded check. Write `<story>.formal.test.*` in the repo's test runner: call the real code for every input in a small stated range and compare with an oracle from the Story.
- Only if the range is too big to loop and the rule is arithmetic or logic: use Z3 or CrossHair in a temp venv. Replay each counterexample and 2 witnesses on the real code.
- Control: the planted mistake from verify must fail this check. If it does not, the result is Not run: the check cannot see the mistake.
- Result: Proved (bounded), Proved (solver), Failed + counterexample, Not run + reason, or Not applicable + reason. Advisory: it covers only the rule and the bounds.
- Append `## Formal check` to verify.md: result, rule, method and bounds, the command and its real output, the control, and what is not covered.
- Commit the formal test as a normal test. Never commit raw logs.
