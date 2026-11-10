# I add the first starting value to an empty shared world

As a test author, I want to add an explicit starting value to an empty shared world so that my scenario remains valid JSON.

## Acceptance criteria

1. A first starting value added to an empty shared world produces valid JSON and preserves false, null and the empty string as explicit values.
2. Adding the first key to a nested empty object also keeps valid JSON, including when the key is `__proto__` or `constructor`.
3. The surrounding scenario and the seed reference snapshot remain unchanged.

## Rules to check

For each key `x`, `__proto__`, and `constructor` and each value false, null, and the empty string, adding the key to an empty object must place an own member with that exact value inside the braces. The expanded text must parse as JSON; emitting a member outside the braces, dropping it or changing its value is forbidden. The same rule applies to an empty nested object. New members of an empty object use compact separators. The input seed and surrounding scenario bytes are preserved, and the reference snapshot remains the original seed.

Runtime check: expandSource with supplied file replies; native tests must also check own properties and unchanged prototypes.
