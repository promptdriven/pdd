# Multi-part product roadmaps and contracts

Use this reference in `product` mode when planning or coordinating a multi-part application across independent modules and shared contracts.

## 1. Sizing and workflow

- Size by architecture boundaries, not fixed Story counts:
  - **Single cohesive part:** write `product/map.md` only and deliver via normal `feature` mode.
  - **Multiple decoupled parts:** define parts, shared contracts (`contracts/*.md`), and planned runs in `product/plan.md`.
  - **Broad cross-part rollouts:** define vertical slices where Slice 1 is one thin end-to-end journey through the parts.
- Parts share **contracts**, not internal code. Feature tests fake sibling parts strictly through those contracts. Contract changes go through a plan PR.
- Inspect and advance planned runs with `pdd product status`, `pdd product next`, and `pdd product start <run>`.

## 2. `product/map.md`

Start with `# <Product name>: map`, `Sentence: "<the person's sentence>"`, and `Size: small|medium|large (N CORE Stories, M parts)`.

| Heading | Columns |
|---|---|
| `## Parts` | `Part`, `Folder`, `What it is` |
| `## Stories` | `Id`, `Part`, `Story`, `Tag` (`CORE` or `LATER`) |
| `## Journeys` | `Id`, `Journey`, `Stories` |
| `## Questions` | `Id`, `Question`, `Recommendation`, `Example`, `Answer` |
| `## Rules to check` *(optional)* | `Id`, `Owner`, `Rule`, `Verified By` |

- State whether each part faces a person or runs headless (only user-facing parts get screens/UI; backend servers, routers, and daemons stay screenless).
- Write Stories in plain customer words (`As a <person>, I want <goal>, so that <reason>`). Never write component-actor Stories (`"I want the router to..."`) or duplicate plumbing Stories (`1` user goal = `1` Story).
- Leave unanswered questions blank with a clear recommendation and concrete example; never invent the person's answer.

## 3. `product/plan.md`

Start with `# <Product name>: plan` (optional `Through: prompt-pr|code` before the first `## ` heading).

| Heading | Columns |
|---|---|
| `## Boundaries` | `From`, `To`, `What crosses`, `Contract` |
| `## Runs` | `Run`, `Part`, `Slice`, `Stories`, `Needs`, `Shared surfaces` *(optional)* |
| `## Prompts` | List each part's checkable `.prompt.md` files and `kind: native-only` boundary specs, plus how parts start and wire together |

- Name cross-part boundary operations in `What crosses` using dotted `<part>/<prompt>.<op>` or `<prompt>.<op>` tokens so `pdd lint` and `pdd product status` catch unwired operations.
- Planned-run issues carry `<!-- pdd-product: run=RUN -->` on its own line (case-sensitive).
- **Whole-product integration & wiring contracts:** Do not stop at siloed per-part modules or per-part KV stores. Specify in `product/plan.md` and `kind: native-only` integration prompts:
  1. **Shared persistence schema:** unified relational schema, foreign keys, and migration ownership (never disconnected per-part ad-hoc KV databases).
  2. **Transport & auth perimeter:** real HTTP/RPC authentication middleware, session/revocation enforcement, CSRF/`Origin` validation, and server-side clocks (never trusting forged auth decisions or caller-supplied timestamps).
  3. **CLI-to-server wiring & Day-0 bootstrap:** real client-to-server transport (`--api-url` / HTTP calls, not pre-seeded local files) and a Day-0 startup/bootstrap command.
  4. **Unmocked end-to-end journey recipe:** prove cross-part integration on the integrated branch with at least one unmocked end-to-end journey recipe in `pdd.json` `verify.paths`.

## 4. Shared contracts (`contracts/*.md`)

- Each `contracts/*.md` starts with a title and an `Owner` line naming the plan run.
- Each record has a `### record_name` heading and a fenced `json` schema (`properties`, `required`, `"additionalProperties": false`).
- `contracts/world.md` defines a key table (`Key`, `What it holds`, `Writer`, `Readers`, `How it is written`). Each key has one writer. Put shared seed data in `contracts/seed-world.json`.
- Reference schemas with `{"$contract": "contracts/records.json#/defs/order"}` and seed worlds with `{"$seed": "contracts/seed.json", "set": {...}}`.

## 5. `kind: native-only` boundary prompt contract

Every `kind: native-only` adapter prompt is a complete executable specification (not a thin stub). Include YAML frontmatter (`kind: native-only`, `reason`), `## Dependencies` linking the checkable domain prompt(s) it wires (never the reverse), and:

1. **Boundary & runtime contract:** concrete DDL/SQL/HTTP/wire schemas (declarative `sql`/`ddl`/`openapi`/`yaml`/`json`/`protobuf`/`graphql` blocks are exempt from fence-length limits), locking/concurrency rules, CLI/OS/TTY boundaries, and exact `<port>.<op>` bindings matching linked checkable prompts.
2. **Error mapping & failure behavior:** how driver, transport, permission, sandbox, timeout, and malformed-input failures map fail-closed to observable exit codes, HTTP statuses, or domain errors.
3. **Real-host verification cases:** concrete non-mocked probes exercising real binaries, database drivers, local servers, OS sandboxes, `/dev/tty`, multi-turn CLI state, and payloads `> 4 KiB`.
