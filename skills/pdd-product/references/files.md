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
| Rules to check (optional) | Id, Owner, Rule, Verified By |

A part names its prompt folder, such as `phone` and `prompts/phone`, and states
whether it faces a person or runs headless (only user-facing parts get `.ui.svg`
screens and `app/maps/<part>.json`; backend servers, routers and daemons get `0`
screens). Stories use stable IDs such as P01, plain customer words (`As a <person>,
I want <goal>, so that <reason>`), and CORE or LATER. Never write component-actor Stories
(`"I want the router/connector to..."`), cross-part plumbing duplicates (`1` user
goal = `1` Story), or standalone Stories for edge cases and internal safety rules
(put those in module prompts and `## Rules to check`). Under `## Rules to check`,
use the structured table (`Id`, `Owner`, `Rule`, `Verified By`) where `Owner`
names one or more map parts or `all` / `*` / `shared` (plain bullet lists also
parse as cross-cutting rules). `pdd product start` copies every rule owned by a
run's primary part, declared secondary shared surfaces, or `all` / `*` / `shared`
into the generated feature issue. A journey names its
constituent Story IDs. Leave unanswered questions blank; never supply the person's
answer. Give each question a recommended choice and concrete example.

## Plan: product/plan.md

Use `# Product name: plan`. An optional `Through: prompt-pr|code` line before the
first `## ` heading sets the rollout's default completion target (`code` when
omitted). A small map with exactly one part needs no separate plan.

| Heading | Columns |
|---|---|
| Boundaries | From, To, What crosses, Contract |
| Runs | Run, Part, Slice, Stories, Needs, Shared surfaces (optional) |

State what never crosses a boundary. Name cross-part boundary operations in
`What crosses` (or an optional `Operations` column) using dotted `<part>/<prompt>.<op>`
or `<prompt>.<op>` tokens so `pdd lint --local` and `pdd product status` can
warn when a declared operation has no consumer prompt outside its defining prompt.
Under a separate `## Prompts` heading (not
inside `## Boundaries` or `## Runs`), list each part's `.prompt.md` files (in a
table or bullet list) and state how each part starts and connects in
real execution, naming both its checkable domain/screen prompt(s) (faked over
injected `<port>.<op>` ports in `pdd test`, never linking `kind: native-only`
adapters under their `## Dependencies`) and each `kind: native-only` boundary
specification prompt that depends on those domain prompts for real HTTP/HTTPS
routes, auth/cookies/crypto, SQLite or external databases, CLI/OS/sandbox/TTY
processes and browser DOM/network clients (RUNBOOK §21; `0` Runtime AI calls in
`pdd test`, verified by non-mocked real-host native tests in `code` PR 2) so
Story checks run cleanly and finished runs form a runnable product.
When `## Prompts` lists `.prompt.md` paths, `pdd lint --local` and `pdd product status`
warn on declared prompts missing on disk or extra `.prompt.md` files under tracked
part folders. A Run is a stable name such
as phone-1; Part names one primary map part (or `all` for journeys). When a run
must also update shared entrypoints such as `cli`, list secondary parts in the
optional `Shared surfaces` (or `Updates` / `Also updates`) column, after a comma
in `Part` (`ledger, cli`), or on a `Shared surfaces (RUN): cli` line inside
`## Runs`; `pdd product start` includes those shared-surface folders, contracts,
prompts and owned rules in the feature issue. Slice is a label such
as 1. Stories and Needs are comma lists. Needs names `plan PR` or earlier runs;
empty means no needs. `plan PR` is satisfied when the plan file is on the base
branch; a planned run is done when its implementation PR is merged, or when its
prompt PR (or implementation PR) is merged for a Prompt-Space rollout (`Through:
prompt-pr` in `product/plan.md` or `--through prompt-pr`). Commands read
local base refs, which may be stale, and do not prove a person's approval. Large
plans describe the journey of each slice.

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

## Native-only prompt contract

Every `kind: native-only` boundary prompt is a complete executable specification,
not a short stub or uninstantiated dependency-injection shell. Include YAML
frontmatter (`kind: native-only` and a concrete `reason`), `## Dependencies`
linking the checkable domain prompt(s) it wires (never the reverse), and three
required contract elements:

1. **Boundary & runtime contract:** Concrete storage/DDL schemas (declarative
   fenced `sql`, `ddl`, `openapi`, `yaml`, `json`, `protobuf`, or `graphql`
   blocks are exempt from prompt code-fence length limits), transaction/locking
   or concurrency model, HTTP/wire routes, CLI/OS/process/sandbox/TTY boundaries,
   and auth/crypto primitives as applicable, plus exact `<port>.<op>` bindings
   matching ports declared by linked checkable prompts (`native-only-unknown-port`).
2. **Error mapping & failure behavior:** How driver, transport, OS, permission,
   sandbox, timeout, lock, and malformed-input failures map to observable exit
   codes, HTTP/wire statuses, rollbacks, or domain error shapes (fail closed).
3. **Real-host / native verification cases:** Concrete executable, non-mocked
   verification checks naming real binary, OS kernel, database driver, local
   server, or subprocess smoke probes (such as `--live-local` or real-driver
   integration tests, never mocked-only unit shells). Cover applicable real-host
   classes: nested OS sandbox child execution, host `/dev/tty` UID/permission
   ownership, multi-turn Turn 1 → Turn 2 real CLI state containment, and
   full-size realistic payloads exceeding `4 KiB` without lossy preview truncation.
