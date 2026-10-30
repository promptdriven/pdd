# I check real shared-contract layouts locally

## Acceptance criteria

1. I can keep existing Key tables and use exact nested Path ownership with complete writer labels and optional schema links.
2. I see unrelated JSON skipped once while declared invalid schemas and real copy drift still fail.
3. I can read the same local check facts as JSON without changing files or contacting a service.
4. I keep schema-map validation and copy eligibility while incidental legacy copies cannot hide drift.

## Rules to check

A Key table retains top-level seed coverage. A Path table compares exact declared
paths only: parent and child may have different writer labels. A writer label is
the complete nonblank cell, even with commas. Schema links are optional; only
explicit links require value validation. Declared invalid schemas fail with 4;
non-schema files skip, while genuinely unproved value predicates remain 5.
Implicit wrapper leaves validate but cannot authorize copy agreement. The original
object-copy size thresholds remain unchanged. JSON and text have the same facts;
JSON alone or with sync is syntax exit 2. No runtime, model, auth, slot, history or
source write occurs during a valid local check.

Runtime check: Not run: this Story uses native CLI/Git/filesystem cases, with
no Runtime entry claimed. Native replay follows the reviewed source oracle.
