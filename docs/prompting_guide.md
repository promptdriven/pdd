# Prompt‑Driven Development Prompting Guide

This guide shows how to write effective prompts for Prompt‑Driven Development (PDD). It distills best practices from the PDD whitepaper, the PDD doctrine, and working patterns in this repo. It also contrasts PDD prompts with interactive agentic coding tools (e.g., Claude Code, Cursor) where prompts act as ad‑hoc patches instead of the source of truth.

References: pdd/docs/whitepaper.md, pdd/docs/prompt-driven-development-doctrine.md, README.md (repo structure, conventions).

---

## Why PDD Prompts (Not Patches)

- Prompts are the source of truth; code is a generated artifact. Update the prompt and regenerate instead of patching code piecemeal.
- Regeneration preserves conceptual integrity and reduces long‑term maintenance cost (see pdd/docs/whitepaper.md).
- Prompts consolidate intent, constraints, dependencies, and examples into one place so the model can enforce them.
- Tests accumulate across regenerations and act as a regression net; prompts and tests stay in sync.

Contrast with interactive patching (Claude Code, Cursor): prompts are ephemeral instructions for local diffs. They are great for short, local fixes, but tend to drift from original intent as context is implicit and often lost. In PDD, prompts are versioned, explicit, and designed for batch, reproducible generation.

---

## The PDD Mental Model

- One prompt typically maps to one code file or narrowly scoped module.
- You explicitly curate the context to place in the model’s window (don’t “dump the repo”).
- Change behavior by editing the prompt; re‑generate the file; run crash/verify/test/fix; then update the prompt with learnings.
- Keep the “dev unit” synchronized: prompt + generated code + minimal runnable example + tests.

Key principles: everything is explicit, prompts are the programming language, and you regenerate rather than patch.

Dev Unit (Prompt with Code, Example, Test):

```mermaid
flowchart TB
  P[Prompt]
  C[Code]
  E[Example]
  T[Tests]

  P --> C
  P --> E
  P --> T
```

Notes:
- The prompt defines intent. Code, example, and tests are generated artifacts.
- Regenerate rather than patch; keep tests accumulating over time.

---

## Anatomy of a Good PDD Prompt

Use clear sections and explicit includes. A recommended structure (matching our templates) is:

1) Role and scope: one short paragraph defining what the module/file is responsible for.
2) Requirements: numbered bullets for functionality, contracts, errors, validation, logging, performance, security, and any SLOs.
3) Dependencies: explicit XML tags (one per dependency) with <include> of examples or prompt names.
4) Instructions: precise input/output specs, class/function responsibilities, edge cases, and testing notes.
5) Deliverables: what code artifact(s) to produce and the entry point(s).

See pdd/pdd/templates/generic/generate_prompt.prompt for a concrete scaffold. For broader principles and guardrails, see pdd/docs/prompt-driven-development-doctrine.md.

---

## Prompt Syntax Essentials

These patterns are used across prompts in this repo:

- Preamble and role: start with a concise, authoritative description of the task and audience (e.g., “You are an expert Python engineer…”).
- Includes for context: bring only what the model needs.
  - Single include: `<include>path/to/file</include>` (handles both text and images based on file extension)
  - Multiple: `<include-many>path1, path2, …</include-many>`
  - Grouping: wrap includes in a semantic tag to name the dependency or file they represent, for example:
    ```xml
    <render_js>
      <include>src/render.js</include>
    </render_js>
    ```
  - When including larger files inline for clarity, wrap with opening/closing tags named after the file, e.g. `<render.js>…</render.js>`.
- Inputs/outputs: state them explicitly (names, types, shapes). Prompts should define Inputs/Outputs and steps clearly.
- Steps: outline a short, deterministic plan the model should follow.
- Constraints: specify style, performance targets, security, and error handling.
- Environment: reference required env vars (e.g., `PDD_PATH`) when reading data files.

Tip: Prefer small, named sections using XML‑style tags to make context scannable and deterministic.

### Special XML Tags: pdd, shell, web

The PDD preprocessor supports additional XML‑style tags to keep prompts clean, reproducible, and self‑contained. Processing order (per spec) is: `pdd` → `include`/`include-many` → `shell` → `web`. When `recursive=True`, `<shell>` and `<web>` are deferred until a non‑recursive pass.

- `<pdd>…</pdd>`
  - Purpose: human‑only comment. Removed entirely during preprocessing.
  - Use: inline rationale or notes that should not reach the model.
  - Example: `Before step X <pdd>explain why we do this here</pdd>`

- `<shell>…</shell>`
  - Purpose: run a shell command and inline stdout at that position.
  - Behavior: executes during non‑recursive preprocessing; on non‑zero exit, inserts a bracketed error with the exit code instead of failing the pipeline.
  - Example: `<shell>git config --get user.name</shell>`

- `<web>URL</web>`
  - Purpose: fetch the page (via Firecrawl) and inline the markdown content.
  - Behavior: executes during non‑recursive preprocessing; on failure, inserts a bracketed error note.
  - Example: `<web>https://docs.litellm.ai/docs/completion/json_mode</web>`

Guidance: Use these tags sparingly to keep prompts deterministic. Prefer stable inputs and short outputs (e.g., `head -n 20` in `<shell>`) so that regenerated prompts remain consistent across runs.

---

## Why PDD Scales to Large Codebases

- Explicit, curated context: use minimal examples and targeted includes instead of dumping source, reducing tokens and confusion.
- Modular dev units: one prompt per file/module constrains scope, enabling independent regeneration and parallel work.
- Batch, reproducible flow: eliminate long chat histories; regeneration avoids patch accumulation and incoherent diffs.
- Accumulating tests: protect behavior across wide regenerations and refactors; failures localize issues quickly.
- Single source of truth: prompts unify intent and dependencies, improving cross‑team coordination and reducing drift.

---

Patch vs PDD at Scale (diagram):

```mermaid
flowchart LR
  subgraph Patching
    C0[Codebase] --> P0[Chat prompt]
    P0 --> D0[Local diff]
    D0 --> C0
  end

  subgraph PDD
    PG[Prompts graph] --> GZ[Batch regenerate]
    GZ --> CM[Code modules]
    CM --> XT[Examples and Tests]
    XT --> UP[Update prompts]
    UP --> PG
  end
```

---

## Example (Minimal, Python)

This simplified example illustrates a minimal functional prompt:

```text
% You are an expert Python engineer. Your goal is to write a function `get_extension` that returns the file extension for a given language.

<include>context/python_preamble.prompt</include>

% Inputs/Outputs
  Input: language (str), like "Python" or "Makefile".
  Output: str file extension (e.g., ".py"), or "" if unknown.

% Data
  The CSV at $PDD_PATH/data/language_format.csv contains: language,comment,extension

% Steps
  1) Load env var PDD_PATH and read the CSV
  2) Normalize language case
  3) Lookup extension
  4) Return "" if not found or invalid
```

This style:
- Declares role and outcome
- Specifies IO, data sources, and steps
- Uses an `<include>` to pull a shared preamble

---

## Scoping & Modularity

- One prompt → one file/module. If a prompt gets too large or brittle, split it into smaller prompts that compose via explicit interfaces.
- Treat examples as interfaces: create a minimal runnable example demonstrating how the module is meant to be used.
- Avoid “mega‑prompts” that try to implement an entire subsystem. Use the PDD graph of prompts instead. For how prompts compose via examples, see “Dependencies & Composability (Token‑Efficient Examples)”.

---

## Writing Effective Requirements

Focus on clarity, measurable outcomes, and determinism:

- Functional: list behaviors, invariants, and contract boundaries (API shape, props, return types, error codes).
- Non‑functional: performance budgets (latency, memory), logging, tracing, security (authn/z, secrets handling), compliance.
- Edge cases: input validation, missing data, timeouts, network failures, concurrency.
- Observability: what to log/measure and at what levels; how to verify success in tests.
- Testing: specify what tests should cover and any golden examples.

---

## Dependencies & Composability (Token‑Efficient Examples)

- Include only relevant dependencies; more context is not always better.
- Prefer curated few‑shot examples over raw source. Examples are typically a small fraction of full code size, which makes them far more token‑efficient while still conveying interfaces and intent.
- Examples are the composition mechanism: modules “use” each other by consuming their examples rather than importing full source. This stabilizes generation and keeps the context focused.
- Use XML tags to label each dependency block and `<include>` real files.
- If a dependency is defined by another prompt, list it under a "Prompt Dependencies" subsection and, where possible, pair it with a corresponding example file from `context/`.

Example dependency block that composes another module via its example:

```xml
<billing_service>
  <include>context/billing_service_example.py</include>
</billing_service>
```

Composability via Examples (diagram):

```mermaid
flowchart LR
  subgraph Module_B
    PB[Prompt B] --> GB[Generate] --> CB[Code B]
    CB --> EB[Example B]
  end

  subgraph Module_A
    PA[Prompt A] --> GA[Generate] --> CA[Code A]
    PA --> EB
  end

  EB --> CA
```

---

## Regenerate, Verify, Test, Update

The PDD workflow (see pdd/docs/whitepaper.md):

1) generate: produce the code for the module
2) example: create a minimal runnable example
3) crash → verify: fix runtime errors; ensure behavior matches intent
4) test: generate/augment tests
5) fix: iterate until tests pass
6) update: back‑propagate learnings into the prompt and parent specs

Key practice: never discard passing tests after regeneration; they accumulate as a regression safety net.

---

## PDD vs Interactive Agentic Coders (Claude Code, Cursor)

- Source of truth:
  - PDD: the prompt is primary and versioned; code is regenerated output
  - Interactive: the code is primary; prompts are ephemeral patch instructions
- Workflow:
  - PDD: batch‑oriented, reproducible runs; explicit context via includes
  - Interactive: live chat loops; implicit context; local diffs
- Scope:
  - PDD: scoped to modules/files with clear interfaces; compose via examples
  - Interactive: excels at small, local edits; struggles as scope and history grow
- Synchronization:
  - PDD: update prompts after fixes; tests accumulate and protect behavior
  - Interactive: prompt history rarely persists; documentation often drifts

When to use which: Use PDD for substantive new modules, refactors, and anything requiring long‑term maintainability and repeatability. Use interactive patching for trivial hotfixes; follow up with a prompt `update` so the source of truth remains synchronized.

---

## Patch vs PDD: Concrete Examples

Patch‑style prompt (interactive agent):

```text
Fix this bug in src/utils/user.ts. In function parseUserId, passing null should return null instead of throwing.

Constraints:
- Change the minimum number of lines
- Do not alter the function signature or add new functions
- Keep existing imports and formatting
- Output a unified diff only

Snippet:
  export function parseUserId(input: string) {
    return input.trim().split(":")[1];
  }
```

PDD‑style prompt (source of truth):

```text
% You are an expert TypeScript engineer. Create a module `user_id_parser` with a function `parseUserId` that safely extracts a user id.

% Role & Scope
  A utility module responsible for parsing user identifiers from various inputs.

% Requirements
  1) Function: `parseUserId(input: unknown): string | null`
  2) Accepts strings like "user:abc123" and returns "abc123"
  3) For null/undefined/non‑string, return null without throwing
  4) Trim whitespace; reject blank ids as null
  5) Log at debug level on parse failures; no exceptions for expected cases
  6) Performance: O(n) in input length; no regex backtracking pitfalls
  7) Security: no eval/exec; treat input as untrusted

% Dependencies
  <logger>
    <include>context/logger_example.ts</include>
  </logger>

% Instructions
  - Implement in `src/utils/user_id_parser.ts`
  - Export `parseUserId`
  - Add narrow helpers if needed; keep module cohesive
  - Include basic JSDoc and simple debug logging hooks

% Deliverables
  - Code: `src/utils/user_id_parser.ts`
  - Minimal usage example: `examples/user_id_parser_example.ts`
  - Tests: `tests/user_id_parser.test.ts` covering happy/edge cases
```

Key differences:
- Patch prompt constrains a local edit and often asks for a diff. It assumes code is the source of truth.
- PDD prompt defines the module’s contract, dependencies, and deliverables. It is the source of truth; code and tests are regenerated to match it.

---

## Checklist: Before You Run `pdd generate`

- Does the prompt state the module’s role and boundaries clearly?
- Are functional and non‑functional requirements explicit and testable?
- Are inputs/outputs and error handling specified?
- Are dependencies minimal and included explicitly (with `<include>`)?
- Is there a short, deterministic set of steps?
- Is there a small example you can generate and run?
- Did you add any new learnings back into the prompt (after prior runs)?

---

## Common Pitfalls (And Fixes)

- Too much context: prune includes; prefer targeted examples over entire files.
- Vague requirements: convert to explicit contracts, budgets, and behaviors.
- Mega‑prompts: split into smaller prompts (one per file/module) and compose.
- Patching code directly: make the change in the prompt and regenerate; then `update` with learnings.
- Throwing away tests: keep and expand; they are your long‑term leverage.

---

## Naming & Conventions (This Repo)

- One prompt per module/file, named like `${BASENAME}_${LanguageOrFramework}.prompt` (see templates under `pdd/pdd/templates`).
- Follow codebase conventions from README.md for Python and TypeScript style.
- Use curated examples under `context/` to encode interfaces and behaviors.

---

## Final Notes

Think of prompts as your programming language. Keep them concise, explicit, and modular. Regenerate instead of patching, verify behavior with accumulating tests, and continuously back‑propagate implementation learnings into your prompts. That discipline is what converts maintenance from an endless patchwork into a compounding system of leverage.
