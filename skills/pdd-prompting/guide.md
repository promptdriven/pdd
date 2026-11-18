# Prompting guide

Each production module has one canonical `.prompt.md` (including independently generated frontend children). It states **what the module must do and why**, with explicit ownership, domain decisions, public operations and consequential failure edges.

**Preservation sets the boundary; abstraction chooses the expression.** Keep required observations and reasons. State domain rules, leaving algorithms, private helpers and internal data structures free within the [preservation promise](#preservation).

## Contract content and ownership

A contract states its preservation promise across three owners (small modules may combine them):

| Owner | Required meaning | Placement |
|---|---|---|
| Domain decisions | Purpose, responsibility, inputs, outcomes, guards, precedence, technical invariants (symlinks, `.GIT` casing, V1/V2 schema rules, bounds) and why rules exist | `## Domain decisions` near the top; audited in PR 2's formal check without ratcheting `user_stories/*.md` |
| Public contract | Exact operation names, signatures, defaults, bindings, units and input/output/error shapes | Beside a small rule, or in one named interface/contract section |
| Consequential operations | Evaluation order, port effects and surviving state when a guard or dependency fails | Beside the affected rule, or in one compact boundary table |

Make every observable input and output key, field or tuple position, unit and error shape explicit:

- When a prompt links a shared `$contract` schema, that schema is the single owner of the field, type and requiredness inventory; prose states domain rules, invariants, ordering and nonobvious semantics instead of repeating property tables.
- Without a shared `$contract` schema, name every input/output field and group repeated shapes once so lazy interface synthesis derives exact strict schemas without guessing.
- Retain public binding kinds (module function, method, CLI entry), observable metadata and public identifier values within the selected promise.
- Distinguish optional absence from malformed required values, early refusal from partial state mutation, and comparison values from returned/stored values. Group aliases compactly (canonical spelling, accepted aliases, unknown-value behavior). Never minify JSON onto one line.
- Keep module policy in the owning prompt. Never duplicate the same business rule across two prompts; link the canonical owner instead.

## Representations of consequential behavior

Use Mermaid (`flowchart TD`) when branching or state transitions clarify precedence; prefer prose or a compact table for a single rule, lookup or short sequence. Define predicates once, label yes/no branches and terminal outcomes, and keep failure commits beside their guards.

### Synthetic example: a small contract with one compatibility boundary

A fictional exhibition owns caption approval and permits one correction. A supplied caption has `caption_id` and Boolean `accurate` and `fits` fields. **Ready** means `accurate AND fits`. Initially `revision_used` is `false`. Review returns `{outcome, caption_id}` where `outcome` is `approved`, `declined` or `pending`.

```mermaid
flowchart TD
    R{Ready?} -->|Yes| A([approved])
    R -->|No| U{Revision used?}
    U -->|Yes| D([declined])
    U -->|No| P([pending])
```

Accept a replacement only while `pending`; otherwise raise `ValueError("correction unavailable")` without state change. An accepted replacement sets `revision_used` to `true` and becomes current before review:

| Commit | If assignment raises before storing |
|---|---|
| Set `revision_used` true | Current caption and flag remain unchanged; skip replacement |
| Store replacement caption | `revision_used` stays true; previous caption stays current |

## Dependency declarations and port direction

Use one explicit `## Dependencies` section as the loading declaration, linking canonical dependency prompts or shared contracts with relative Markdown links (plus `#fragment` when only one section applies). Navigation links outside `## Dependencies` are not loaded automatically. Required context must be transitively reachable without missing files, broken fragments or required-context cycles.

Inject outside effects (databases, filesystem, HTTP/network, clocks, randomness, generated IDs, child processes) via explicit operation inputs or named `<port>.<op>` operations in prose so `pdd test` fakes them deterministically rather than deriving randomness from ad-hoc state counters in prose (RUNBOOK §21):

- **Dependency direction for `kind: native-only` boundary adapters:** Checkable domain, CLI flow and screen prompts must depend on shared contracts or checkable peers over injected `<port>.<op>` interfaces — **never** list a `kind: native-only` adapter prompt under `## Dependencies` of a checkable prompt (including Story `entry_path` prompts). Invert the dependency so the thin `kind: native-only` adapter depends on the checkable domain prompt.

## SVG appearance content for frontend modules

Every user-facing frontend module links minimal representative `.ui.svg` mockups (`views/<state>[--<variant>]__<layout-mode>.ui.svg`) using Markdown image syntax (`![Alt text](relative/path.ui.svg)`) under `## Appearance`. Backend servers, routers, CLIs and daemons carry no `.ui.svg` screens.

- **Single source of truth:** SVG owns visual layout, visible labels, spatial order and stable intent-based `id`s (`viewBox`, `<title>`, `<desc>`; mark unowned surroundings `data-context-only="true"` or class `context-only`; exclude scripts, event handlers, framework classes, external fonts/assets and base64 blobs). Prose owns behavior, responsive rules, keyboard/click flows, accessibility/focus order and dynamic data authority.
- **Fidelity and purpose:** Declare whether each view is **illustrative** or a **comparison reference** for a named state, and state fidelity once (**Relational**, **Measured** at a reference viewport with comparator/tolerances, or **Exact**).
- **Stylesheets and fast authoring lint:** HTML operation screens (`"source": "operation"`, `"format": "html"`) list CSS files under `"stylesheets"` in `app-map.json` and name matching CSS classes in the screen prompt. During authoring, verify `.ui.svg` and `app-map.json` alignment with `pdd lint --local` (`<150ms`, zero browser/AI calls); render `.ui.svg` to PNG only when a person explicitly requests PNG previews.

<a id="preservation"></a>
<details>
<summary><strong>Required reference — preservation and numerical meaning</strong></summary>

### Preservation promise and evidence

Policy comes from authorized requirements and accepted consumer or shared contracts. Distinguish obligations, source observations, authorized changes and unresolved conflicts.

- **Behavioral refinement** preserves named behavior and essential interfaces while stating permitted variation. **Drop-in replacement** additionally preserves invocation forms, representation, identity and observable side-effect ordering. With source alone and no selected mode, default to provisional behavioral refinement: retain public declarations, exports, error categories and consequential observed behavior (including visible failures on unsupported inputs unless an authorized boundary excludes them).
- Missing, `null`, empty, `0` and `false` may differ; preserve domains, units, defaults, ties, duplicates, ordering, mutability and serialization. Mark genuine evidence gaps explicitly rather than inventing narrower rules.
- For financial or evidence modules, preserve publication time, source identity, metric definitions, units, rounding and nonfinite/overflow behavior. Exact machine compatibility additionally preserves accumulation order and representation; authorized approximations state metric, bound, units and scope without loosening eligibility or rejection boundaries. Label synthetic examples as synthetic.

</details>

## Story scope and scenario evidence

Choose the proof boundary before touching `user_stories/` (see `story-guide.md` for Story structure and `<= 35`-line / `<= 6`-criteria bounds):

- **`0` Stories + `"No Story: <reason>"` PR line:** Internal refactors, `kind: native-only` adapters, or changes already covered by an existing Story over an injected port.
- **Edit existing Story vs `1` Story per cohesive standalone user loop:** Modify the existing Story when changing an existing user slice; write `1` Story per new standalone user loop (ask before `> 3`), give steps self-contained starting states by default so `pdd test` runs them in parallel, and assert `1` observable check per material claim in its Short JSON scenario.
- **Technical invariants stay in `.prompt.md`:** Put symlink, `.GIT` casing, V1/V2 schema, and boundary invariants in `.prompt.md` `## Domain decisions` (verified by PR 2 native/formal checks), never in `user_stories/*.md`. Test suites, fixtures, CI configs, manifests and docs never get `.prompt.md` owners.

## Prompt format and native-only declarations

A behavior prompt is plain Markdown: purpose, `## Domain decisions`, public operations, failure edges and `## Dependencies` (no embedded `Runtime interface` block). Owned code files carry `Generated from <path>.prompt.md` near line 1 (or line 2 after `#!`; commentless files use `pdd-bindings.json`).

Use YAML frontmatter at the very top of the file **only** when a prompt owns pure physical/OS plumbing with `0` Runtime Stories:

```yaml
---
kind: native-only
reason: <the native effect that bound ports cannot fake>
---
```

`reason` must name the concrete physical effect bound ports cannot fake (`fsync`, live sockets, OS signals, subprocess TTYs, crypto primitives). `pdd approve` records prompt approval in the local journal without editing the prompt file.
