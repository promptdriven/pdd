# Prompting guide

Each owned production module has one canonical `.prompt.md` stating **what the module must do and why**: ownership, domain decisions, public operations, and consequential failure edges.

State domain rules clearly while leaving private helpers, internal data structures, and algorithms free within the required observable behavior.

## 1. Contract content and ownership

A module prompt covers three parts (small modules may combine them):

| Part | Required meaning | Placement |
|---|---|---|
| Domain decisions | Purpose, inputs, outcomes, guards, precedence, technical invariants (symlinks, `.GIT` casing, schema rules, bounds) and why rules exist | `## Domain decisions` near the top |
| Public contract | Exact operation names, signatures, defaults, bindings, units, and input/output/error shapes | Beside the rule or in one named contract section |
| Consequential operations | Evaluation order, port effects, and surviving state when a guard or dependency fails | Beside the affected rule or in a compact table |

Make every observable input and output field, unit, and error shape explicit:

- When linking a shared `$contract` schema, that schema owns field types and requiredness; prose states domain rules, invariants, ordering, and nonobvious semantics.
- Without a shared `$contract` schema, name every input/output field and type (never write bare untyped `"object"` — list concrete properties or explicitly say `"open object"`). Avoid polymorphic write-port payloads; split distinct shapes into separate `<port>.<op>` operations or a tagged envelope.
- Distinguish missing vs `null` vs empty vs `0` vs `false`, early refusal vs partial state mutation, and comparison values vs stored values. Never minify JSON onto one line.
- Keep one business rule in one owning prompt; link the canonical owner instead of duplicating prose.
- Use a compact Markdown table or `flowchart TD` Mermaid diagram when branching or state transitions clarify precedence. Keep prompts crisp (`40–120` lines typical, `<= 500` lines max, `<= 15` lines per code fence).

## 2. 100% Truth Rule, top-of-file headers, and Hybrid Brownfield PRs

- **100% Truth Rule:** A `.prompt.md` owns **100%** of its code file — never write half-prompts and never force whole-repo rewrites. Either adopt one small clean module, extract a clean pure decision core into a new PDD file (*Functional Core, Imperative Shell*), or make a plain code fix with a failing-first regression test.
- **Top-of-file (first 4 KiB) header standard:** Place the explicit ownership header inside the first 4 KiB of every owned code file, after any shebang (`#!`), `'use client'`/`'use server'`, `<?php`/`<?xml`, Python PEP 263 encoding, `//go:build`, Astro `---`, or SPDX license line — **followed by a blank line** (prevents `go doc` capture and keeps import sorters from pushing it past 4 KiB):
  - JS/TS/Go/Rust/C/Java: `// Prompt: prompts/<name>.prompt.md`
  - Python/Shell/Ruby/YAML: `# Prompt: prompts/<name>.prompt.md`
  - HTML/Markdown/XML: `<!-- Prompt: prompts/<name>.prompt.md -->`
  - MDX/JSX: `{/* Prompt: prompts/<name>.prompt.md */}`
  - Commentless files (e.g. JSON): bind in root `pdd-bindings.json`.
  - Legacy `Generated from <path>.prompt.md` headers remain readable for compatibility.
  - Only explicit headers and `pdd-bindings.json` confer ownership; opening-sentence prose mentions and filename matches are advisory hints only.
- **Hybrid Brownfield PR lane:** Brownfield PRs may combine newly extracted or prompt-owned PDD modules (strict prompt-first 100% Truth) with small surgical edits to unowned legacy wiring, routes, ORM adapters, or migrations verified natively (Red→Green TDD on bugs, native tests, `pdd lint --diff`, and `pdd prove`).
- **Never own non-product files:** Test suites (`test/`, `tests/`, `*.test.*`), fixtures, CI configs, manifests, and docs never get `.prompt.md` owners.

## 3. Dependency declarations and `kind: native-only`

- List required peer prompts and shared contracts under `## Dependencies` using relative Markdown links (plus `#fragment` when only one section applies). Navigation links outside `## Dependencies` are not loaded automatically.
- Inject outside effects (DB, filesystem, HTTP, clock, RNG, IDs, child processes) via explicit inputs or `<port>.<op>` operations ([ports-and-cli.md](ports-and-cli.md)).
- **Dependency direction:** Checkable domain, CLI, and screen prompts depend only on shared contracts or checkable peers — **never** list a `kind: native-only` adapter under `## Dependencies` of a checkable prompt. Invert the dependency so the thin `kind: native-only` adapter depends on the checkable domain prompt.
- Use YAML frontmatter **only** for pure physical/OS plumbing with `0` Stories:

```yaml
---
kind: native-only
reason: <concrete physical effect bound ports cannot fake, e.g. fsync, live sockets, OS signals, subprocess TTYs, crypto>
---
```

- Every `kind: native-only` prompt is a complete executable boundary specification (never a thin stub). Include `## Dependencies` linking the checkable domain prompt(s) it wires (never the reverse) and three parts:
  1. **Boundary & runtime contract:** concrete DDL/SQL/HTTP/wire schemas (declarative `sql`/`ddl`/`openapi`/`yaml`/`json`/`protobuf`/`graphql` fences are exempt from fence-length limits), locking/concurrency rules, CLI/OS/TTY boundaries, and exact `<port>.<op>` bindings matching linked checkable prompts.
  2. **Error mapping & failure behavior:** how driver, transport, permission, sandbox, timeout, and malformed-input failures map fail-closed to observable exit codes, HTTP statuses, or domain errors.
  3. **Real-host verification cases:** concrete non-mocked probes exercising real binaries, drivers, local servers, OS sandboxes, `/dev/tty`, multi-turn CLI state, and payloads `> 4 KiB`.

## 4. Behavioral preservation and numerical meaning

- **Behavioral refinement** preserves named behavior and public interfaces while stating permitted variation. **Drop-in replacement** additionally preserves invocation forms, representation, identity, and side-effect ordering. With source alone and no chosen mode, default to behavioral refinement.
- Preserve domains, units, defaults, ties, duplicates, ordering, mutability, and serialization. Flag genuine evidence gaps instead of inventing narrower rules.
- For financial or metrics modules, represent money in integer minor units, state rounding rules explicitly, and preserve publication time, source identity, units, and nonfinite/overflow behavior.

## 5. Expected values, approvals, and merges

- **Expected values** come from the Story and the person — never from observed code or interpreter output, and never edited silently to force a pass.
- **Approvals (`--said`):** Show the prompt/Story changes, then judge the person's later reply in chat (a question, change request, or earlier message is not approval; no exact phrase is needed). Record actual attributed words with:

```sh
pdd approve PROMPT --said - <<'PDD_SAID'
<the person's exact words>
PDD_SAID
```

  Choose a delimiter absent as a whole line from the text, keep it quoted, and never interpolate untrusted words into shell strings. Blank input is refused; `"strict_approvals": true` in root `pdd.json` requires a person terminal.
- **Merges:** `pdd` has no merge command. Merge only on an explicit person request, after verifying required checks are green and posting the merge request comment; use `--match-head-commit <head>`.
