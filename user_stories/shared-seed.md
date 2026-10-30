# I start tests from a shared world

## Acceptance criteria

1. A shared world can replace an array value, add an object key and preserve 0, false and null.
2. Starting another scenario from the same seed leaves the shared world unchanged.
3. Overlapping overrides apply in written order, including replacement of the whole world.
4. An override with a missing parent or array index is refused.
5. Literal step inputs and expected values containing reference-like keys stay literal.

## Rules to check

Only an initial_world root can load a seed. Clone before applying set pointers; never rewrite the seed file or expected results. Pointer escapes use ~0 and ~1. Parent traversal must exist; an object final key may be added, an array index must exist. Native tests must prove local validation and uploaded seed bytes agree without changing original scenario paths.

Runtime check: expandSource bound with supplied file replies; host-file isolation and native capture require native verification.
