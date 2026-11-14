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

Use `# Product name: plan`. A small map with exactly one part needs no separate plan.

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
is written. Each key has one writer. State shared refusal and update rules.
Put shared starting data in `contracts/seed-world.json`.

For example, phone → server crosses order_in and order_view under
`contracts/phone-server.md`. Server → barista crosses ticket and ticket_done
under `contracts/server-barista.md`. The phone never talks to the barista screen.

## Whole-product exploration

Declare background work in the plan before drafting the parts:

```markdown
## After every tap
1. prompts/server/server.prompt.md#forward_tickets
2. prompts/barista/board.prompt.md#refresh
```

Each numbered item is a repository-relative prompt path followed by `#OPERATION`.
The operations must accept `{}`. After an executable tap handler and its existing
`after` steps, these operations run in order against the same shared world; later
operations see earlier writes. Gap handlers do not run the chain. A tap allows
at most eight `after` steps and forty total model calls, including internal calls
and destination rendering; setup refuses an unprovable or excessive call bound.

From the product checkout, surface `pdd simulate --product` during prompt-space
review, before generating code or merging part implementation PRs. Use
`pdd simulate --product --journey J1` to choose one existing journey scenario,
or `pdd simulate STORY --product`; `--parts phone,server` selects a subset.
Draft the Story and its test in the product checkout first: the command uses an
existing scenario and does not invent a seed Story. A subset must include every
explicit navigation destination.

Each active feature run with the exact planned-run marker supplies only its
part's declared Folder, `app/maps/PART.json` and referenced `views/` assets.
Screenless parts need no map. Contracts, the plan, journey scenarios and unrelated
files stay in the product checkout. Parts without active drafts use that checkout.
The overlay is read-only: source, worktrees, approvals and run prerequisites do
not change. This preview is distinct from a journey run waiting for merged code.

Complete missing draft inputs before trying again. When two active runs supply
the same part, end the stale run or resolve the plan association. Give each part
its own view paths and nonoverlapping prompt folder; ownership conflicts name the
parts and paths instead of silently selecting bytes. Use `--new` to reload an
existing Simulator after changing drafts.
