# PDD Prompt & Story Advisory Review Rules (`PROMPT-REVIEW-RULES.md`)

> **Design lineage:** Anthropic [`REVIEW.md`](https://claude.dev/blog/solving-code-review-at-anthropic/) + [`deslop-please`](https://github.com/deterministic-machines/deslop-please) (John Ousterhout, *A Philosophy of Software Design*: **deep modules, narrow interfaces**) + single owner per domain concept.

## Guardrails & Operating Contract

1. **Advisory only:** Never blocks merges, never returns a merge-blocking exit code, and never replaces deterministic structural lint or real-build verification.
2. **One pass only:** Run **1 read-only review pass** on the changed or selected prompts/Stories. Never run an iterative repair/review loop.
3. **Hard finding cap (`<= 7`):** Emit at most **7 findings per review run**, ranked highest-impact first. Drop the lower-signal tail.
4. **Verified `file:line` quotes only:** Every finding **must** quote exact verbatim text from `file:line`. Drop any finding whose quote does not match the target file at that line.
5. **Rule budget (`<= 15` rules total):** Currently **12 rules** (3 slots open). Keep the checklist short enough to read in one pass.
6. **Admission bar (`>= 2` real incidents):** Add a new rule only after **at least 2 distinct real incidents** that deterministic structural checks and upstream code linters could not catch.
7. **Automatic pruning (`> 50%` dismissal rate):** Prune any rule dismissed on **more than 50% of its first 10 findings**.

## Output Format

```markdown
- **[RXX] `<file>:<line>`** — <1-sentence concrete design issue>
  > Quote (`<file>:<line>`): `<exact verbatim substring from that line>`
  - **Suggestion:** <1-sentence first-principles fix>
```

If 0 high-signal findings remain after quote verification, emit: `No advisory findings (0/7).`

## Rules (12 / 15 Max)

### A. Module Depth & Boundaries

#### R01 — Deep module over pass-through wrapper
A prompt must encapsulate meaningful domain decisions behind a narrow set of operations; avoid pass-through prompts whose only job is forwarding identical inputs to one downstream prompt.

- **Bad:** `prompts/cli/wrapper-lint.prompt.md` defines `runWrapperLint(opts)` solely as "call `runLint` with one fixed flag" while mirroring all options.
- **Good:** `prompts/cli/lint.prompt.md` owns multi-provider review with a default provider, eliminating the shallow pass-through module.

#### R02 — Single owner per domain concept
Every policy rule, classification, or invariant belongs in one owning prompt; callers invoke that owner instead of duplicating decision criteria across sibling prompts.

- **Bad:** A CLI prompt embeds a multi-role access-control classification table inside its `## Ports` section instead of calling the owning authorization prompt.
- **Good:** `prompts/auth/policy.prompt.md` owns caller classification; the CLI prompt passes the request to `authorize` and maps the returned outcome to exit codes.

#### R03 — No internal helper or representation leaks in public contracts
Keep private helper names, internal composition flags, database transaction primitives, and raw storage key layouts out of public operation inputs/outputs and `## Ports`; expose only semantic domain contracts.

- **Bad:** Public operation `authorize` adds an input key `defer_persistence` marked "internal composition flag only; public callers omit it", or prose mandates calling `_derive_authority()`.
- **Good:** Public `authorize` exposes only caller-facing inputs (`actor`, `request`, `now`); internal boundaries keep persistence or pure evaluation private.

#### R04 — Acyclic one-way layering (checkable prompts never depend on `native-only`)
Dependencies flow strictly downward: `native-only` boundary adapters depend on checkable domain prompts and bind their ports; a checkable prompt never depends on a `native-only` adapter or forms a cycle with a peer prompt.

- **Bad:** Checkable `prompts/orders/posting.prompt.md` lists a `kind: native-only` database service prompt under `## Dependencies` to write rows directly.
- **Good:** `prompts/orders/posting.prompt.md` declares port `ledger_store.write` under `## Ports`; the `native-only` service depends on `posting.prompt.md` and binds that port.

#### R05 — Declare wired ports structurally, not scattered in prose
List every `<port>.<op>` wired by a `native-only` prompt (or required by a checkable prompt) in YAML frontmatter `ports:` or a dedicated `## Ports` / `## Port bindings` section or table — never bury port bindings inside narrative paragraphs.

- **Bad:** A `kind: native-only` prompt omits `## Ports` and embeds port names inside prose bullets under `## Domain decisions`.
- **Good:** Frontmatter `ports:` or a `## Ports` section/table declares each bound port so structural lint validates every port deterministically.

### B. Story Integrity & User Observability

#### R06 — Stories stay strictly user-observable (zero internal or schema leaks)
A Story describes only what a real user or external caller does and sees (inputs, visible outputs, error messages, exit codes, durable user outcomes) — never internal file paths, SQL tables, private helpers, or internal struct fields.

- **Bad:** "When `post_correction` runs inside a `BEGIN IMMEDIATE` transaction, `idempotency_records[].summary` omits `write_refs` and `ledger/history.py` writes `audit_events`."
- **Good:** "Submitting a correction twice with the same idempotency key returns the original revision ID without applying the adjustment a second time."

#### R07 — Specific actor and verifiable acceptance criteria
Name a concrete actor role ("As a billing operator", "As a developer running `pdd lint`") and write measurable acceptance criteria — avoid generic roles ("As a user/system") and unverifiable adverbs ("works cleanly", "handled gracefully", "properly").

- **Bad:** "As a user, I want invalid requests handled gracefully so the system works correctly."
- **Good:** "As an operator on a non-enrolled machine, requesting a protected record exits with code `4`, prints `Resource unavailable.`, reveals no record details, and records a `denied` audit entry."

#### R08 — One cohesive user loop per Story
Keep each Story focused on one user-visible loop (roughly `<= 6` acceptance criteria, readable in ~30 seconds). Move exhaustive edge-case matrices, wire schemas, and internal invariants into the owning `.prompt.md` or test fixtures.

- **Bad:** One 90-line Story listing 14 acceptance criteria spanning CLI flag parsing, SQL locking, CSV formatting, and backup recovery.
- **Good:** Separate Stories per user loop while the owning prompt covers flag-parsing edge cases.

### C. Human Readability & Signal Density

#### R09 — Behavior over implementation code dumps
Describe observable inputs, outputs, invariants, and failure rules in plain English, tables, or schemas rather than pasting imperative code (`if (...) { ... }`, `def ...`, loop mechanics) into prompts.

- **Bad:** A 35-line fenced code snippet inside a `.prompt.md` showing loop mechanics, temporary variables, and exception handlers.
- **Good:** A 4-row Markdown table specifying status eligibility, ordering key, and error code when no matching row exists.

#### R10 — Tabulate or diagram dense multi-branch logic
When an operation combines `>= 4` sequential guards, role-based permissions, or state transitions, express the decision matrix as a Markdown table or `mermaid` diagram rather than one dense prose paragraph.

- **Bad:** One 2,800-character bullet packing storage triggers, primary keys, hydration rules, delegation propagation, and rollback semantics into one paragraph.
- **Good:** Split into a short `## Storage invariants` table plus a concise transaction flowchart or named subsections.

#### R11 — Explicit fail-closed boundaries and non-silent errors
Every external port call, persistence write, and authorization check must state its failure outcome explicitly (refusal code, rollback vs. independent audit write, missing/`null` response handling) rather than leaving failure paths implicit.

- **Bad:** "Call `records.fetch` to load the documents and write them with `export.write`." (Silent on `null`, expired auth, or write failure.)
- **Good:** "If `records.fetch` returns `null` or a non-`ok` status, return `unavailable` (`exit_code: 4`) and write nothing; if `export.write` fails, return `temporarily_unavailable` (`exit_code: 6`) with no success payload."

#### R12 — Scannable structure free of duplicated prose or broken formatting
Keep each prompt cohesive, well-structured, and free of copy-pasted rule blocks or broken syntax (such as unclosed backticks swallowing prose). Consolidate repeated rules into one canonical section or split along domain seams.

- **Bad:** A prompt repeats the same 95-word help-flag rejection paragraph verbatim in two sections, or leaves an unclosed backtick that swallows prose into inline code.
- **Good:** Define the rule once in a compact table under `## Domain decisions` and reference it in one line from `## Failure edges`.
