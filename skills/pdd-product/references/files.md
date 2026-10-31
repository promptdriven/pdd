# Product files

Keep these files in the person's repo. Use Markdown tables with these headings
and columns; keep IDs stable and separate comma lists with commas.

## Map: product/map.md

Start with `# Product name: map`, `Sentence: "the person's sentence"` and
`Size: small|medium|large (N CORE Stories, M parts)`.

| Heading | Columns |
|---|---|
| Parts | Part, Folder, What it is |
| Stories | Id, Part, Story, Tag |
| Journeys | Id, Journey, Stories |
| Questions | Id, Question, Recommendation, Example, Answer |

A part names its prompt folder, such as `phone` and `prompts/phone`. Stories use
stable IDs such as P01, the person's words, and CORE or LATER. A journey names
its constituent Story IDs. Leave unanswered questions blank; never supply the
person's answer. Give each question a recommended choice and concrete example.

## Plan: product/plan.md

Use `# Product name: plan`. The small path needs no separate plan.

| Heading | Columns |
|---|---|
| Boundaries | From, To, What crosses, Contract |
| Runs | Run, Part, Slice, Stories, Needs |

State what never crosses a boundary. A Run is a stable name such as phone-1;
Part names one map part, or `all` for journeys. Slice is a label such as 1.
Stories and Needs are comma lists. Needs names `plan PR` or earlier runs; empty
means no needs. `plan PR` is satisfied when the plan file is on the base branch;
a planned run is done when its implementation PR is merged. Commands read local
base refs, which may be stale, and do not prove a person's approval. Large plans
describe the journey of each slice.

## Planned-run identity

The issue for a planned run carries `<!-- pdd-product: run=RUN -->`, with RUN
replaced by its exact plan run ID. This marker is case-sensitive; phone-1 and
phone-10 are different. Issue writers put the marker on its own line; lookup
still recognizes the exact comment within an issue body. More than one
distinct planned-run marker does not identify one run. The workflow runner may
retain one unambiguous marker in its private run record and carry it into that
run's PR descriptions, once on its own line. The marker identifies the planned run within its
repository; a reference in a comment or unrelated prose is not PR ownership.

## Contracts

`contracts/*.md` starts with a title and an Owner line naming the plan run.
Each record has a `### record_name` heading and a fenced `json` schema. Schema
objects name properties, required fields and additionalProperties explicitly.
`contracts/world.md` has a key table: Key, What it holds, Writer, Readers, How it
is written, with an optional Schema column. Accept Key or Path with Writer.
A Key is an exact top-level seed key; a Path is an exact nested declaration,
including separately backticked path lists. Follow the
[writer rules](../../../prompts/cli/contracts.prompt.md#world-keys-and-their-seed-values)
for actor lists, initialization labels and comma qualifiers. Parent and child
paths have independent ownership; two runtime actors for one exact path conflict. Prefer explicit
repository-root Schema targets for new plans, for example
`contracts/world.md#orders`; existing tables may omit or leave them blank.
Only declared schemas validate corresponding present seed values. Symbolic paths
without schemas declare ownership only, without inferred template matching.
Do not infer schema links from names or prose. Identical repeated declarations coalesce;
conflicting runtime writers or explicit schemas for the same exact path are errors.
A declared key may be absent initially. Present seed branches without declarations
warn once with their exact paths under either heading; coverage of a declared
container does not assign its writer to child paths. State shared refusal and update rules.
Put shared starting data in `contracts/seed-world.json`.

For example, phone → server crosses order_in and order_view under
`contracts/phone-server.md`. Server → barista crosses ticket and ticket_done
under `contracts/server-barista.md`. The phone never talks to the barista screen.
