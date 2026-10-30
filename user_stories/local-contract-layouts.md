# I check real shared-contract layouts locally

## Acceptance criteria

1. I can keep existing Key tables and use exact nested Path ownership with one writer per path and optional schema links.
2. I see unrelated JSON skipped once while declared invalid schemas and real copy drift still fail.
3. I can read the same local check facts as JSON without changing files or contacting a service.
4. I keep schema-map validation and copy eligibility while incidental legacy copies cannot hide drift.

## Rules to check

Key and Path cells beginning with `/` are exact JSON Pointers. Bare Keys retain
top-level identity and namespace declarations cover their root seed container
without assigning parent ownership. Writer lists follow the
[writer rules](../prompts/cli/contracts.prompt.md#world-keys-and-their-seed-values):
initialization labels are not runtime writers, comma qualifiers describe the
preceding writer, and repeated actors coalesce. Missing seed declarations warn
without assigning an ancestor's writer to a child. Optional
schemas can be inferred from one declared record identity named or linked in a
row; unresolved or ambiguous inference warns without a refusal. Primitive JSON
metadata never suppresses a recognized schema member. Annotation/resource/
simulation and seed values are not mined as schemas. Implicit member leaves
validate without gaining copy authority. Existing copy thresholds remain.
Warnings report unchecked declarations and disagreeing declared records without
changing a successful exit. JSON and text carry the same facts; no runtime,
model, authentication, slot, history or source write occurs. JSON alone or with
sync remains syntax exit 2.

Runtime check: Not run: this Story uses native CLI/Git/filesystem cases, with
no Runtime entry claimed. Native replay follows the reviewed source oracle.
