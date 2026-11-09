# Authored files view

Own `src/project-files.mjs`. Export `inspectProjectFiles(root)` and
`runProjectFiles({cwd=process.cwd(),json=false}, ports={})`.
A person can see which prompts, Stories and tests PDD reads and why it refuses
a file, without changing files, signing in or calling the interpreter.

Use the required shared reader for discovery, prompt parsing, contract expansion,
call closure, schema checks and scenario preflight. Inspect all eligible
Git-visible prompts, including prompts with no interface. Use default all-Story
fixture-project exclusions, with the same workspace limits. Report each bad
prompt or test separately and continue inspecting independent files. Reference
or source failures retain their code and reason; never print source contents.
Pair tests with Stories by the shared name rule, never by trusting story_path.
Pair prompts with tests through step entry_path, declared entry_paths and
transitive interface call targets. Keep paths sorted and unique. Do not guess
an interface kind; this task does not add or validate kind metadata.

`inspectProjectFiles` returns exactly this top-level JSON shape:
- `schema_version`: `pdd.files.v1`.
- `prompts`: path-sorted rows with `path`, `has_interface` (true for exactly one recognized
  block, false for none/multiple, null when a source/reference failure stops reading), `stories` and `tests` (sorted path arrays), `references` (the resolver's
  provenance rows), and `refusals` (the shared prompt hash/status and parse/schema
  problems, without duplicates).
- `stories`: path-sorted rows with `path`, `title` (string or null), and `tests`
  (all matching test paths, empty when untested).
- `tests`: path-sorted rows with `path`, `files` (all conflict members), `stories`
  (name-rule owners), `prompts` (entry/call closure paths), and `refusals` from
  shared scenario preflight. A source/reference failure is a refusal for that
  test and does not hide other tests.
- `orphans`: shared discovery rows `{path,line}` for test-folder JSON files with
  no Story. Do not parse these unrelated JSON files.
- `refusals`: deduplicated problems from prompt and test rows, each with `path`
  (the affected file), `code`, `section`, `message`, and any shared `hint`.
- `warnings`: shared discovery and preflight warnings, including untested Stories
  and excluded fixture projects.

A caught source/reference failure uses its code (or `source-unreadable` when
absent), section `source`, its safe message and the affected path. Sort global
refusals by path, code, section, then message. No timestamp or absolute repository
path belongs in this JSON. An empty repository returns empty arrays.

Resolve cwd's Git root with a read-only Git command. Outside Git, write one
finite stderr diagnostic and return 2. A root discovery/configuration failure
writes its reason to stderr and returns its exit code (default 4). Otherwise
print JSON plus newline with --json, or a text list of every prompt, Story, test,
orphan, refusal reason and warning. Text states whether a prompt has a Runtime
interface. Inspection returns 0 even when listed files have refusals; this is
an inventory, not a pass verdict. Use injected stdout/stderr ports for output.

## Dependencies

- [Shared authored-file reader](runtime-preflight.prompt.md): required generation,
  verification and testing context for all parsing, pairing and refusal rules.

<details><summary>Runtime interface</summary>

```json
{
  "kind": "native-only",
  "status": "draft",
  "prose_sha256": "86a632c0f370c0b637e8d9465443b5fe40fdab9bda8e55723fe98c14a6930f3d",
  "reason": "Native Git-visible source inspection and the strict reader need native evidence first. Native evidence owners: test/cli.test.mjs."
}
```
</details>
