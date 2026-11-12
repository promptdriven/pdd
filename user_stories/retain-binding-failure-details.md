# Keep saved binding failure details

As a person using Autopilot, I want saved failure details to reach the waiting run, so that a missing binding gets the right repair hold.

## Acceptance criteria

1. Reading a saved check or lint result keeps each test's detailed refusal, compatibility and binding repair evidence, with its original values and order.
2. A generic short reason does not hide a saved binding refusal or a matching missing-binding finding when Autopilot chooses its repair hold.
3. Passing and older results keep their existing meaning. Absent, malformed, unrelated or mismatched details do not create a binding finding. Person questions and explicit blockers keep their existing priority.
4. Reading the saved results changes no file and starts no test, service request, repair or workflow action.

## Rules to check

Keep detailed evidence with its own test. Do not replace its short result reason,
invent absent evidence, or classify a missing binding from unrelated or
mismatched details. A person question or explicit blocker must not be replaced
by a binding hold.

## Verification boundary

The owning prompt's partial Runtime interface exposes native evidence assessment,
but not the saved-result reader. These criteria require native checks of the
real reader and the normal Autopilot tick. The independent draft cases are in
`test/fixtures/retained-binding-evidence-cases.json`; they are not a hosted
Runtime scenario or a passing result. The original reported edge replay remains
outside this smaller saved-evidence repair.
