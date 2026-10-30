# Shared contract references

Own `src/contract-refs.mjs`: resolve shared schema records and starting worlds,
retain their provenance, and compare inline schemas with the catalog. Callers
supply UTF-8 source and synchronous file ports. This module has no filesystem,
network, history or approval effects. Existing source without an applicable
reference returns byte for byte unchanged.

Module function `expandSource({path,text,format}, files)` returns
`{text,references}`. `path` is the original repository-relative consumer;
`format` is `prompt`, `scenario` or `json-schema`. The native and Runtime entry
use this same function and port, without an alternate checking API. Native
failures throw an Error with the declared code and a diagnostic message.

## Where references have meaning

For `prompt`, expand only schema roots in Runtime interface entries
(`input_schema`, `result_schema`) and resources' operations
(`arguments_schema`, `result_schema`). For `json-schema`, the whole JSON value
is a schema root. Descend into schema `properties` values, `items` and `oneOf`
variants. Do not traverse literal annotations (`default`, `examples`, `enum`,
`const`), ordinary prose, business inputs or expected values. A scenario expands
only an `initial_world` root containing `$seed`; literal step inputs, checks,
simulation and other fields remain values even if they contain `$contract`.
A real `$ref` is left alone for the existing schema validator to refuse.

A schema reference is an object with string `$contract` and, optionally, string
`title` and `description`. Expand the target recursively, then apply those local
annotations in place of its annotations. Other siblings give `contract-invalid`:
never discard, merge or silently override a local constraint. A selected schema
record must be a JSON object; final engine schema acceptance belongs to preflight.

## Target identity and reading

References use repository-root paths, including nested references; never resolve
them relative to a consumer. Accept POSIX paths without absolute/home/scheme,
backslash, NUL, empty, `.` or `..` components. Apply the safe adapter's secret-name
and ancestor checks before reading; unsafe paths give `contract-unsafe`.

`files.stat({path})` returns `{exists,is_symlink,size}` (UTF-8 byte size);
`files.read({path})` returns `{content}`. Stat before read; a missing file gives
`contract-missing`, a symlink gives `contract-unsafe`. The caller supplies a safe
adapter that also rejects hidden unsafe ancestors and nonregular files. Port
failures retain the consumer and target in a finite diagnostic. A target whose
stat size exceeds 10,485,760 bytes is refused before read with `contract-invalid`
and a finite too-big diagnostic naming consumer and target. Enforce that same
existing source-byte limit during recursive expansion, before a branch, clone,
provenance snapshot or text replacement can materialize an oversized value. The
final UTF-8 effective source and each expanded record/world must fit; equality
with the limit is allowed here. Stop with `contract-invalid`, never a partial
result, a native allocation failure or an unbounded expansion. Preflight still
owns the aggregate selected-file and tar limits.

Account for size once per expanded reference result, including its local
annotations or seed overrides, while retaining early bounded expansion before
oversized intermediates. Ordinary schema nodes after a reference do not trigger
repeated full-subtree size walks. A deeply nested fitting schema remains eligible;
its depth alone must not multiply full-size accounting. Cached targets, exact
numbers, key order and errors retain their existing meaning; this adds no timing
threshold or input restriction.

<details>
<summary>Record selection, pointers and cycles</summary>

Markdown targets are `contracts/x.md#heading`: a level-three heading owns text
until the next level-one/two/three heading outside fenced blocks. Retain literal
trailing hashes in a title, so `### C#` names `C#`. Remove an optional ATX closing
run of hashes only when separated from title text by whitespace: `### C# ###`
also names `C#`. Its record is
exactly one fenced `json` block. No JSON block means a descriptive section: ignore
it in the catalog, but selecting it gives `contract-missing`. Multiple JSON blocks
or invalid JSON give `contract-invalid`. Unrelated descriptive sections do not
invalidate a selected record. Support backtick and tilde fences.

Accept the literal heading or its conventional fragment: lowercase the title,
remove punctuation except hyphen/underscore and letters/digits, replace whitespace
with hyphens. Resolve against the union of literal and fragment matches; multiple
headings matching either spelling give `contract-ambiguous`, even if one is a
literal match. Canonical identity uses the literal heading, e.g.
`contracts/relay.md#sign_in_start input`. Do not invent suffixes for duplicates.

JSON targets are `contracts/x.json#` for the whole document or
`contracts/x.json#/pointer`. Decode JSON Pointer tokens `~1` as `/` and `~0` as `~`;
reject other tilde escapes. The empty pointer means root. Object traversal uses
own keys only; array tokens are canonical nonnegative decimal indices (0 or a
nonzero digit followed by digits), strictly within existing bounds. Missing
members give `contract-missing`; malformed pointers give `contract-invalid`.
Do not percent-decode headings or pointer tokens.

Expand nested references and fail with `contract-cycle` when a canonical target
is already on the active expansion chain. Repeated independent uses are allowed.
Errors name the originating consumer, requested target and failing chain; missing
headings name the requested heading. Never return a partial expansion as success.

</details>

## Shared starting worlds

`initial_world` may be exactly `{"$seed":"contracts/seed-world.json"}` plus an
optional `set` object mapping JSON Pointers to replacement values. The seed path
has no fragment and its JSON must be an object. Its canonical document-root target
identity is always `path#`, as for a JSON-root `$contract` target. Use that identity
in `references` and cycle chains for every seed, including nested/transitive seeds.
Resolve a nested root `$seed` by the same rules, with cycle detection; ordinary
nested world values stay literal.
Clone the seed and every replacement; never mutate files, supplied data or another
scenario's world. Preserve absent, null, false, 0 and empty containers distinctly.

Each set pointer traverses existing own members only. An object's final key may be added;
an array's final index must already exist (no append or `-`). The root pointer
replaces the entire world, which must remain an object. Apply set entries in their
written order: a parent/root replacement may precede a child override; a later
parent replacement wins over earlier children. Disjoint overrides commute.
Invalid world shape, siblings, missing parents,
array bounds or set pointers give `seed-invalid`. A missing seed file still gives
`contract-missing`; seed cycles give `contract-cycle`.

## Effective bytes and provenance

Expansion, provenance, cataloging and sync preserve JSON number values and their
exact number tokens, including `9007199254740993`; never round, coerce to strings
or reject otherwise valid JSON because of numeric representation. This adds no
numeric acceptance gate; engine schema acceptance remains preflight's concern.
Outside applicable schema/world slots, literal business inputs, annotations and
expected values retain their exact bytes.
Preserve every own JSON key, including `__proto__` and `constructor`, as ordinary
data during selection, cloning and writes; never change object prototypes.

Replace only applicable reference value subtrees. Keep every surrounding byte,
including JSON whitespace, newlines, key order, literal number tokens and the
rest of a Runtime interface fence. Insert selected records in their authored key
order and layout, applying nested substitutions locally. In particular,
`reasoning` before `answer` stays in that order, as do numeric-looking own keys.
Local annotations replace existing annotation values without moving their keys;
append absent annotations in their written consumer order. Expanded seeds retain
the selected world's layout and key order while replacements affect only their
value subtrees; append a new object key after existing keys. Preserve literal
replacement key order and apply overlapping overrides in written order. New
members use the containing object's existing whitespace/separator layout, or
compact separators for an empty object. No applicable references means no
reserialization.
Do not expand schemas into authored source during ordinary reads.

Each reference has `consumer` (original input path), `source_pointer` (the authored
schema slot or `/initial_world`), `target` (canonical identity), `kind`
(`contract` or `seed`) and `value_json` (compact JSON of that target after nested
expansion, before this consumer's annotations or set). Recursively sort object
keys only; preserve array element order at every length, including 11 or more,
and leave number tokens and literal values unchanged.
Include transitive targets under the originating source pointer. Deduplicate by
consumer/pointer/target/kind and sort by those fields. This is a content snapshot,
not an approval hash or a pin that prevents changes. A no-reference result has
`references: []`.

## Catalog and copy proposals

### Shared native lossless JSON bindings

Expose the existing lossless codec through these module functions for native
consumers, including preflight. These are not additional Runtime entries:

- `parseJsonValue(text)` takes a JSON text string and returns an opaque lossless
  JSON tree. Invalid JSON throws `SyntaxError`; a non-string argument throws
  `TypeError`. Reuse the existing parser, including exact numeric tokens, own
  keys and parsed container layout; do not parse through rounded numeric values.
- `stringifyJsonValue(value)` returns JSON text for a parsed tree or subvalue
  through the existing codec. Preserve exact number tokens, own-key order and
  retained unchanged parsed container layout. This returns the selected JSON
  value, not whitespace outside it or an enclosing source file.
- `jsonNumberText(value)` returns the original JSON number token string for a
  numeric node, or `null` for a nonnumeric node. Callers must not inspect private
  brands or assume a numeric node is an ordinary JavaScript number.
- `jsonValuesEqual(a,b)` returns Boolean general JSON value equality using the
  existing value identity: object key order is immaterial, arrays retain order,
  and numeric tokens compare by exact mathematical value. Thus `1`, `1.0` and
  `1e0` are equal; `9007199254740993` and `9007199254740992` differ. This is literal
  equality for enum, const and uniqueItems, not schema-copy comparison: it never
  ignores annotations or reorders required/enum arrays in a supplied value.

The domain of codec/equality/accessor values is trees and subvalues returned by
`parseJsonValue`; native consumers may traverse own object keys and array items
but must consume them read-only. These bindings promise no editing API or new
write behavior. Reuse the current parser, renderer and general value identity;
do not duplicate their implementations or expose their private representation.

Module function `catalogRecords(sources, targets = [])` takes `{path,text}` files
from `contracts/` and canonical used-target strings, returning `{records,warnings}`.
Each record is
`{path,target,value_json}`. Enumerate Markdown records, each JSON document's root
object (including a shared world), and nested JSON object nodes that have object
`properties`. Also include the supplied used JSON Pointer targets, so a referenced
leaf schema appears in the catalog. JSON identities use escaped JSON Pointers. Ignore
descriptive Markdown sections; a world is never an inline-schema copy candidate.
Resolve nested references against the supplied source set before recording
value_json. Within one expansion or catalog operation, read and parse each JSON
contract file once, regardless of how many records, pointers or consumers use it.
Reuse that parsed document without mutating it; selections, nested expansions and
seed overrides remain independent. Catalog work must not reparse a complete file
for every discovered record. Warn about invalid or ambiguous records without
choosing an arbitrary record.

Module function `compareCopies(sources, records)` takes prompt sources and catalog
records, returning `{matches,warnings}`. A match is
`{path,source_pointer,target,kind,differences}`, where `kind` is `exact` or `near`
and differences are plain field/constraint descriptions. Inspect the same schema
positions as expansion, skipping existing references. Compare object schemas with
object `properties` only. Skip inline objects with fewer than three properties,
including empty and one-field no-input schemas. A semantically equal record with
three properties can be an exact candidate. A differing candidate is eligible
only when the canonical record has at least four properties and the field sets
are identical or their symmetric difference has exactly one field. Thus a
four-field canonical record may match a three-, four- or five-field copy; a
differing three-field canonical record never creates a near proposal.
Semantic equality ignores object key order and local title/description. Treat
schema-keyword `required` lists and `enum` alternatives as order-free with the
same elements and multiplicities; this does not erase duplicate values in an
invalid schema. Preserve required membership, enum values and every other nested
constraint. Order inside
an enum alternative that is itself an array remains significant. Arrays in
`default`, `examples`, `const` and other literal data also retain order; names
`required` or `enum` inside those literal values do not turn them into keywords.
For this comparison, JSON number tokens are equal
exactly when they represent the same mathematical value: `1`, `1.0` and `1e0`
are equal, as are `0`, `-0`, `0.0` and `0e0`. Distinct exact values, including
`9007199254740993` and `9007199254740992`, must compare different even when binary
rounding would collapse them. A differing candidate is drift, including changed
nested types with the same field set; an equal candidate needs no drift warning.
Prefer a unique exact candidate; otherwise require exactly one candidate. Multiple
candidates produce advice and no selected match.

Module function `planSync(sources, matches)` returns `{edits,warnings}`; an edit is
`{path,before,after}`. Replace selected exact/near inline schemas by `$contract`
objects, retaining their local title/description. Near conversion deliberately
adopts the canonical record's constraints: make those differences visible in the
preview. Never rewrite an ambiguous/unmatched schema, existing reference, ordinary
prose or expected value. Only copied schema value subtrees and the
`approved` to `draft` status value may change; all other interface bytes and
unmatched files stay exact. Insert `$contract` first, followed by retained local
annotations in their original written order, using the replaced object's layout.
An edited approved interface becomes draft,
never approved. No prompt prose changes or approval hash changes are authorized.
A second plan after applying the edits has no further edits.

## Dependencies

The caller supplies complete source text and the actual `files` port.
Preflight owns safe native reads; the contract command owns discovery and writes;
the runtime client owns saved Check provenance and freshness judgments.

<details><summary>Runtime interface</summary>

```json
{
  "status": "draft", "prose_sha256": "4ccf86b2b020563b8aedf6322cd1a53564b5c54c88e76e4ffbc8cd61659ff5d0",
  "entries": [{
    "operation": "expandSource",
    "input_schema": {
      "type": "object",
      "properties": {
        "path": {"type": "string"}, "text": {"type": "string"},
        "format": {"type": "string", "enum": ["prompt", "scenario", "json-schema"]}
      },
      "required": ["path", "text", "format"], "additionalProperties": false
    },
    "result_schema": {
      "type": "object",
      "properties": {
        "text": {"type": "string"},
        "references": {"type": "array", "items": {
          "type": "object",
          "properties": {
            "consumer": {"type": "string"}, "source_pointer": {"type": "string"},
            "target": {"type": "string"}, "kind": {"type": "string", "enum": ["contract", "seed"]},
            "value_json": {"type": "string"}
          },
          "required": ["consumer", "source_pointer", "target", "kind", "value_json"],
          "additionalProperties": false
        }}
      },
      "required": ["text", "references"], "additionalProperties": false
    },
    "errors": ["contract-invalid", "contract-missing", "contract-ambiguous", "contract-cycle",
               "contract-unsafe", "seed-invalid"]
  }],
  "calls": [],
  "resources": [{
    "name": "files", "kind": "blob", "access": "read",
    "operations": [{
      "name": "stat", "access": "read",
      "arguments_schema": {
        "type": "object", "properties": {"path": {"type": "string"}},
        "required": ["path"], "additionalProperties": false
      },
      "result_schema": {
        "type": "object", "properties": {
          "exists": {"type": "boolean"}, "is_symlink": {"type": "boolean"},
          "size": {"type": "integer", "minimum": 0}
        },
        "required": ["exists", "is_symlink", "size"], "additionalProperties": false
      }
    }, {
      "name": "read", "access": "read",
      "arguments_schema": {
        "type": "object", "properties": {"path": {"type": "string"}},
        "required": ["path"], "additionalProperties": false
      },
      "result_schema": {
        "type": "object", "properties": {"content": {"type": "string"}},
        "required": ["content"], "additionalProperties": false
      }
    }]
  }],
  "limits": {"max_steps": 24, "max_model_calls": 8}, "conventions": []
}
```
</details>
