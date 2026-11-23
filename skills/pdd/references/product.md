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
- **Completion target (`Through:`):** By default, each planned run delivers one implementation PR (`Through: code`). Set `Through: prompt-pr` (or pass `--through prompt-pr`) only when a multi-part product explicitly stages prompt-only PRs ahead of implementation PRs.
- **Whole-product integration & wiring contracts (where applicable to the product's architecture):** Do not stop at siloed per-part modules or disconnected stubs. Specify in `product/plan.md` and `kind: native-only` integration prompts:
  1. **Shared persistence:** unified storage/schema and migration ownership when parts share state (avoid disconnected per-part ad-hoc stores).
  2. **Transport & auth perimeter:** real authentication/authorization, session/revocation enforcement, CSRF/`Origin` validation, and server-side clocks for networked APIs or services.
  3. **Client-to-server wiring & Day-0 bootstrap:** real client-to-server transport and a documented startup/bootstrap command when parts communicate across processes.
  4. **Unmocked end-to-end journey recipe:** prove cross-part integration on the integrated branch with at least one unmocked cross-part journey recipe in `pdd.json` `verify.paths` (executed by `pdd prove`).

## 4. Shared contracts (`contracts/*.md`)

- Each `contracts/*.md` starts with a title and an `Owner` line naming the plan run.
- Each record has a `### record_name` heading and a fenced `json` schema (`properties`, `required`, `"additionalProperties": false`).
- `contracts/world.md` defines a key table (`Key`, `What it holds`, `Writer`, `Readers`, `How it is written`). Each key has one writer. Put shared seed data in `contracts/seed-world.json`.
- Reference schemas with `{"$contract": "contracts/records.json#/defs/order"}` and seed worlds with `{"$seed": "contracts/seed.json", "set": {...}}`.

## 5. `kind: native-only` boundary specs

Follow [prompting.md §3](prompting.md#3-dependency-declarations-and-kind-native-only) for `kind: native-only` frontmatter, dependency inversion, boundary contracts, error mapping, and real-host verification cases.
