# Local shared-contract commands

Own `src/contracts.mjs`. Module function
`runContracts({words,options,cwd}, {env,stdout,stderr})` returns an exit code.
`words: []` lists contracts; `words: ['sync']` previews migration;
`options['--write'] === true` applies it. Syntax belongs to the command catalog.
With no words, `options['--check'] === true` checks the local plan contracts.
These routes read working files and private local Check history. They never
authenticate, reserve a runtime slot, upload, lint remotely or call a model.

Find the Git root as preflight does. Read Git-visible Markdown/JSON files under
`contracts/`, prompts and discovered scenarios using preflight's safe-file rules.
Do not follow symlinks or secret paths, including during writes. Use the
contract-reference module's catalog, expansion, comparison and migration APIs;
this command owns orchestration and presentation, not another resolver.

## Check the plan locally

`pdd contracts --check` checks working contracts and their current prompt/scenario
uses without needing a prompt, Story, test or previous Check. It does not read
Check history. It writes nothing, including hashes, expectations and approvals.
Plain listing and sync retain their advisory behavior below. `--check` cannot be
combined with sync or `--write`.

```mermaid
flowchart TD
    R[Read safe local contracts and uses] --> V{Definite contract problem?}
    V -->|Yes| F[Report locations; exit 4]
    V -->|No| U{All required validation available?}
    U -->|No| N[Report unavailable locations; exit 5]
    U -->|Yes| P[Report checked counts; exit 0]
```

Check all independent available records, references, copy comparisons and world
values. Diagnostics name the file, canonical record or world key, and field JSON
Pointer (or the table column). A broken reference also retains its consumer and
requested target. Do not call a catalog warning a successful check: unresolved,
invalid, ambiguous or cyclic selected records are problems. A definite problem
wins over validation uncertainty; absent a definite problem, incomplete evidence
is unavailable, never a pass. Syntax/no-repository and native I/O retain their
own exits. Print a truthful checked-record/world-value count on success, including
zero when there is nothing to validate.

### Schema roles and copy authorities

Separate validation from authority to prevent an old incidental copy from hiding
real drift. Seed worlds and resolved `$seed` targets remain data; never search
business values, annotations or simulation/resource declarations for schemas.

Validate Markdown `###` JSON records, root JSON schemas, explicit `$contract`
and world-table Schema selections, and recognized JSON members independently.
Use preflight's `schemaKeywordNames()` vocabulary, including forbidden structural
keywords, to recognize schema nodes. Any direct vocabulary keyword except the
annotation/value-only keys below marks schema intent. Thus `type`, `properties`, `required`,
`additionalProperties`, `items`, `oneOf`, reference or composition keyword marks
schema intent even when its value is invalid: `{"type":"objekt"}` and
`{"$ref":"x"}` must be checked. Expand before validating. Descend through
object-map containers to find members without requiring their siblings to be
schemas; primitive metadata and empty unselected branches do not suppress a
recognized sibling. Once recognized, a schema's children belong to validation,
not independent discovery.

Annotation/value-only objects (`enum`, `const`, `default`, `examples`, `title`,
`description`, `format`) are data unless explicitly selected. Never mine their
payloads, resources, simulation declarations or seed data for schemas. Thus a
selected integer leaf with unrelated business `enum`/`default` values containing
schema-looking keys and broken references still validates just the selected leaf.
An explicit empty selection is checked and invalid; unselected empty data skips.
Skip files with no recognized or selected schema using one sorted named line:
`Skipped N files that are not schemas: <comma-separated paths>`.
A mixed file with a recognized member is not skipped whole. Misspelled-only
schema keys with no recognized structural marker remain named skips.

Copy authorities are only Markdown records, root JSON schemas and explicitly
selected `$contract`, Schema or uniquely inferred row targets. Implicit wrapper
leaves may validate but
cannot become copy authorities. Thus `contracts/legacy.json` containing an old
schema under `copy` cannot hide drift against a declared Markdown record.
Filter the catalog records supplied to `compareCopies`; preserve ordinary
listing/sync's catalog and advisory comparison behavior. Keep its existing
object-copy eligibility and near-copy thresholds unchanged. Deduplicate repeated
drift differences by consumer, schema source pointer, canonical target and
field/difference while retaining independent locations. Ambiguous declared
candidates leave agreement unavailable. Exact copies pass; near copies differ.

Independently warn once per unordered pair of valid declared object records with
the same property-name set but differing shapes, including one- and two-property
records. Use the reference owner's `schemaValuesEqual` on expanded parsed trees;
canonical identities distinguish records. Do not impose inline-copy eligibility
thresholds on this advisory or compare invalid schemas as though valid. A warning
must neither hide genuine consumer drift nor introduce a refusal.

Use `expandSource` with the existing safe file port for selected schemas and
applicable prompt/scenario references, including transitive uses; reuse
`catalogRecords` for canonical identities and expansion. Do not duplicate the
reference resolver, codec or comparison rules.

Validate expanded schemas and present world values through preflight's module
function `validateContract({schema_json,value_json?})`, retaining exact JSON text.
It owns the supported subset and concrete value evidence. Standalone component
schemas may have array or primitive roots; do not impose resource-interface
object-root rules on them. Map its problems to exit 4 and `unproved` to exit 5.
Never round numbers, coerce data, reserialize authored source or change own keys
to obtain a verdict. A numeric or pattern predicate that cannot be established
by the canonical validator remains unavailable with its field and reason.

### World keys and their seed values

`contracts/world.md` and `contracts/seed-world.json` are optional together. If
exactly one exists, checking the world is incomplete (exit 4, naming the missing
partner). The seed must expand to an object by the reference owner's seed rules.
Read the first actual contiguous Markdown table outside fences with `Key` or
`Path` and `Writer` columns; unrelated tables and prose are not declarations.
`Schema` is optional, including a blank cell.

Under either Key or Path, a leading `/` means an exact JSON Pointer, plain or
backticked. Decode `~1` as `/` and `~0` as `~`; reject malformed escapes rather
than guessing a slash-containing literal key. A bare Key names one exact top-level
own seed key, represented by its escaped pointer. A Path must begin with `/`.
Separately backticked paths enumerated in one cell declare separate paths; commas
inside backticks are literal. Key tables retain top-level seed coverage: a root
key is covered by its exact declaration or a declaration beneath its namespace
(for example `/kv/shop` covers the seed container `kv`). This does not give any
writer ownership of undeclared parents or siblings. An uncovered extra top-level
seed key is a problem. Path tables require no top-level seed coverage. Parent
and child ownership remain independent. Symbolic paths such as
`/hosts/<machine_id>` declare ownership without wildcard matching or guessed
concrete seed values.

Split Writer cells on commas, standalone word `and`, and `/`. Trim actors and
coalesce identical actor claims for the same exact key/path. Zero or more than
one unique actor is a Writer problem. Duplicate rows with the same actor coalesce;
different actors for the same exact path fail. There are no prose or test-data
exceptions. Missing key/path is a problem. Distinct explicit schema mappings for
the same key/path are problems; blanks supply no conflicting mapping. Do not
require product parts.

A nonblank Schema cell takes precedence. Otherwise find known declared records
designated in the row by a schema link, an inline-code span whose complete content is an exact
record identifier, or a whole plain Key or What it holds cell exactly equal to
a record name. Links and code spans may occur in Key, Path, What it holds or
other descriptive cells; Writer and Readers actor labels never designate schemas.
Ordinary prose words and the terminal component of a world path do not designate
records: neither "Run events: work resumed" nor `/wire/work` selects `work`.
Known records include valid recognized JSON members as well as Markdown and
root schemas. Naming or linking one such member uniquely
selects that member as an authority; this does not promote its unselected siblings
or every implicit member globally. Resolve links relative to world.md and use canonical
record identities: repeated mentions of one identity coalesce. Exactly one
identity selects that record. No candidate or multiple distinct identities leave
this declaration without a schema. Unknown or unresolved non-Schema row links
are inference candidates only, not new reference errors. Never guess plural
aliases, array wrappers, templates or schemas from a value's shape. Explicit
Schema and `$contract` resolution errors retain their existing definite errors.
Count unique declared keys/paths without a unique schema, including absent and
symbolic declarations, and emit one honest warning:
`N world keys have no schema; their seed values were not checked`.
Retain sorted key/path names in JSON. This advisory alone does not change exit 0.

A nonblank Schema cell is one plain/backticked repository-root target resolved
by the reference owner. Validate it even when its key/path is absent in the seed.
Schema validation diagnostics name the canonical target file and record;
resolution/selection failures retain their consumer and Schema column.
For present concrete paths whose explicit or inferred schemas are valid, validate the corresponding
seed value using exact pointer segments, without coercion or guessed templates.
Do not attempt redundant value validation under a known-invalid schema.
Absent values require no seed value check. Preserve null, false, zero and empty
containers as present values. These checks establish declared ownership and
shape, not actual runtime writes.

### Machine-readable check results

`--json` is accepted only with `--check`; other combinations exit 2. Emit one
JSON object on stdout with `exit_code`, `checked_records`, `checked_world_values`,
`skipped_files`, `diagnostics` and `warnings`, with no text summary mixed into stdout.
Count each canonical schema validation attempted once, including invalid verdicts,
and each attempted present value validation. Expansion failures do not count as
completed schema validations. Skipped files are sorted.
Each diagnostic has `file`, `record`, `field`, `kind` (`problem` or `unavailable`)
and a finite `message`. Include `source_pointer` and `target` only when actually
available. Sort by file, record, field, kind, source_pointer and target, then
message. Text and JSON carry the same counts, diagnostics and exit result.
Warnings are separate from problem/unavailable diagnostics and never change the
exit code. Missing-schema warnings have `kind: "world-schema-missing"`,
`file: "contracts/world.md"`, sorted `world_keys` and the summary `message`.
Declared-record warnings have `kind: "declared-record-disagreement"`, sorted
`records` (two canonical IDs) and a nonempty `message`. Sort warnings by kind,
then file/record identities. Text prints the same advisory facts once.
Native I/O and syntax retain their existing exit semantics.

## Listing and freshness

`pdd contracts` lists every catalog record's canonical target and owner file,
its current prompt/test users, and their Stories. Supply current used targets to
the catalog, including seeds and leaf schemas. Include transitive uses; ignore
literal business/expected values. Show unused records with no users. Report
catalog warnings without inventing a record or a user. Skip or warn for an
oversized catalog/discovery-only document before reading its contents; it cannot
abort independent listing, preview or selected good work. Report any affected
record/use or footprint evidence as unavailable rather than complete. Required
selected source retains preflight's bounded safe-read refusals.

Use `readContractHistory` from the runtime client for the most recent actual
Check baseline for each Story. Compare canonical target snapshots, including
removed targets, against that Story's current uses. Say `changed since the last
check` with the affected record identities and `stale: needs a new check` with
the affected Stories. A changed common record affects all its users. Another
record in the same file and another Story in the same batch do not become stale
merely because they shared a file or batch. Other source changes retain ordinary
source freshness behavior. Each Story's current effective footprint is independent
of which other tests were selected: checking one file, all tests for that Story,
or a multi-Story batch must produce the same footprint for unchanged Story
inputs. Account for all discovered tests belonging to that Story and their own
closures, without adding another Story's files. Preflight's
[unavailable-footprint rule](runtime-preflight.prompt.md#source-capture) applies:
report an incomplete current footprint as unavailable with its cause, never as
current or as a selected-source refusal merely because an unselected sibling is
broken. A baseline records a check, not necessarily a pass;
never display a failed result as passing.

With no actual Check baseline or a legacy baseline lacking reference provenance,
show `not checked` or `baseline unavailable`, respectively. Do not invent an old
value or a change. Lint, Try and file previews never advance these baselines.
Current user discovery reflects working files even without history. Unreadable
history is reported as unavailable, never treated as proof of freshness.

## Preview and write

`pdd contracts sync` prints proposed paths, schema locations, canonical targets
and constraint differences. It writes nothing. Ambiguous candidates warn and
skip while independent proposals remain available. Exact copies may migrate as
well as near copies; differing near copies explicitly adopt the canonical shape.

`pdd contracts sync --write` explicitly authorizes applying these proposals.
Before each write require the same safe destination and exact previewed `before`
bytes; a concurrent edit refuses that file without overwriting it. Write the
complete planned bytes into a new exclusive temporary regular file in the safe
destination directory, then atomically rename it into place. Recheck destination
identity, safe ancestors and exact `before` bytes immediately before replacement;
a concurrent content/identity change or symlink refuses without overwriting it
or its target. Failed preparation or replacement leaves the original complete
and removes only this operation's temporary file. Readers see the complete
original or complete replacement, never a truncated/intermediate file. Preserve
unrelated files, prose and unmatched schemas. Write only planned `after` bytes;
report changed paths and skipped/failed paths. Use the planner's draft transition
for edited approved interfaces; never approve, fill hashes or change expectations.
A repeated write with unchanged inputs performs no writes.

Exit 0 for completed listing/preview/write, including advice and ambiguity;
2 for invalid syntax or no repository; 4 for an unsafe/missing required consumer,
reference or refused write; 5 for unavailable local I/O. Keep a finite cause on
stderr; every nonempty output line ends with one newline. No history or source
write happens while merely listing or previewing.
For `--check`, exit 0 only for complete successful validation; 4 for definite
schema, reference, drift, mapping, writer or seed problems; 5 for unavailable
local validation or I/O; 2 for invalid syntax or no repository.

## Dependencies

- [References](contract-refs.prompt.md): required generation and verification
  context for record, expansion, comparison and migration rules; its native
  module functions `parseJsonValue`, `stringifyJsonValue`, `jsonNumberText` and
  `jsonValuesEqual` supply lossless read-only JSON inspection when determining
  roles and passing selected values to validation, without a second codec;
  its `schemaValuesEqual` supplies existing schema-comparison semantics for
  declared-record disagreement, without copy-candidate eligibility thresholds.
- [Preflight](runtime-preflight.prompt.md): required generation and verification
  context for Git discovery and safe native reads; native module functions
  `schemaKeywordNames` and `validateContract` supply role vocabulary and the
  supported-schema/concrete-value verdicts.
- [Runtime client](runtime-client.prompt.md#shared-contract-check-history):
  required generation and verification context for the local history API only.

The native discovery/history/write effects are not bound by the expansion
Runtime entry. Supplied blob replies do not prove host-file or history safety.
