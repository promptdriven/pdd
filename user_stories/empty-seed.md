# I add a first value to an empty starting world

As a person starting a journey, I can add a first value to an empty shared world and receive valid JSON containing that explicit value.

## Acceptance criteria

1. Adding a first key to an empty seed produces valid JSON with that own key and its exact false, null or empty-string value.
2. Keys `__proto__` and `constructor` remain ordinary own data, and the seed and surrounding scenario bytes stay unchanged.

## Rules to check

An object's final key may be added. For an empty object, new members use compact separators; retain the seed's surrounding whitespace and the scenario's bytes outside the expanded reference. Never change object prototypes or the authored seed.
