# I declare runtime writers and see uncovered seed data

## Acceptance criteria

1. I can distinguish a runtime writer from initial-only seed data and resource descriptions in my world table.
2. I see two runtime writers rejected while repeated actors and hyphenated names keep their meaning.
3. I see one warning naming present seed branches with no declaration, without inheriting writers or inventing schemas.
4. I get the same counts, diagnostics and separate warnings in text and JSON without a service call or source change.

## Rules to check

The [world writer and seed rules](../prompts/cli/contracts.prompt.md#world-keys-and-their-seed-values)
own this behavior. Exact normalized seed labels identify initial-only data; a
path with only blank Writer claims is still invalid. A comma qualifier describes the preceding writer,
including its inner punctuation; a later comma can introduce a second actor.
Separate actors with commas, case-insensitive standalone `and`, `/`, `&` or `;`. Hyphenated names
stay whole, identical runtime actors coalesce, and two different actors fail.
Initial-only and runtime claims may agree on one exact path without inventing a
runtime writer for initialization. With initialization provenance and no runtime
actor, one warning names each unique exact declared path, including absent and
symbolic paths; duplicates coalesce. A runtime actor on that path suppresses it.

Coverage warnings stop at a declared concrete value. Descendant-only namespaces
expose their closest uncovered branches. This is advisory coverage, never writer
inheritance or schema inference. For this warning only, `<name>` matches one
existing decoded seed segment, including an empty key. Embedded placeholders
retain literal segment pieces, and repeated names match independently. Matching
never expands ownership or seed schema validation. A scalar or empty prefix
before a required descendant still warns. Absent values add nothing;
empty containers, null, false, zero and escaped own keys remain present. Schema
warnings stay separate and use "1 world key" for one unchecked declaration.
Every native case observes both text and JSON, exact warning paths and kinds,
unchanged bytes/modes, and zero runtime/model/authentication/slot/history/write
calls. No live product behavior is claimed.

Runtime check: Not run: synthetic native CLI/Git/filesystem cases in
`test/shared-contracts/local-contract-writers.json`; no Runtime entry or service.
