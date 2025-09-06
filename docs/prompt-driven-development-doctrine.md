# Prompt‑Driven Development Doctrine

A concise set of principles for building and maintaining software where prompts are the primary artifact, regeneration is the default, and synchronization across code, examples, and tests is non‑negotiable.

## Why This Doctrine
- **Maintenance reality:** 80–90% of cost is post‑creation. Patching accretes complexity; regeneration preserves integrity.
- **Intent over implementation:** Prompts capture the “why”; code captures one “how.” We version the former and regenerate the latter.
- **Batch leverage:** Modern LLMs and batch economics make full‑module regeneration practical, reliable, and cost‑effective.

## Core Principles
- **Prompts As Source of Truth:** Versioned prompts define behavior and constraints. Code, examples, tests, infra, and docs are generated artifacts.
- **Regenerate, Don’t Patch:** Change the prompt, then regenerate affected surfaces. Avoid local edits that drift intent from implementation.
- **Synchronization Loop:** Always back‑propagate implementation learnings to prompts. Keep prompts, code, examples, and tests in continuous sync.
- **Test Accumulation:** Never discard passing tests after regeneration. Grow a regression net that preserves behavior as the system evolves.
- **Modular Prompt Graph:** Model systems as composable prompt modules linked via minimal usage examples that act as clear interfaces.
- **Intent First:** Capture goals (e.g., “Black Friday scale,” “HIPAA”), not just resource settings. Generation maps intent → implementation.
- **Batch‑First Workflow:** Prefer deterministic, scriptable batch generation over interactive patching. Optimize for reproducibility and cost.
- **Sharp Knives, Safe Defaults:** Provide powerful generation flows with sensible conventions (naming, structure, tests) to prevent foot‑guns.
- **Conceptual Compression:** Consolidate requirements, rationale, and constraints inside prompts to reduce scattered context across tickets and docs.
- **Progress Over Stasis:** Evolve prompts and regenerate even if code diffs are large. Preserve behavior with tests, not line‑level inertia.
- **Market Effects Matter:** Few‑shot examples and patterns compound. Treat examples as assets that improve quality and reduce cost over time.
- **Security & Compliance Built‑In:** Express compliance and threat models in prompts; verify via tests and infra policies on every regeneration.

## The PDD Workflow (At A Glance)
- **Define:** Draft or refine the prompt and select relevant few‑shot examples (auto‑deps, marketplace).
- **Generate:** Produce code, infra, and interfaces from prompts.
- **Crash/Verify:** Resolve runtime errors, then validate functional behavior against intent.
- **Test:** Generate/augment unit and integration tests; codify non‑functional requirements where feasible.
- **Fix:** Iterate until tests pass reliably.
- **Update:** Back‑propagate learnings into prompts and parent specs; keep examples current.

## What “Good” Looks Like
- **One Truth:** A reader can understand a module’s purpose and constraints by reading the prompt and its example.
- **Reproducible:** A clean regen reproduces functionally equivalent behavior; tests confirm it.
- **Small Surfaces:** Prompts are scoped, examples are minimal, interfaces are explicit.
- **Traceable:** Each fix yields a prompt update with rationale captured concisely.
- **Deterministic Enough:** Batch runs are stable; variance is constrained by prompts, examples, and tests.

## Anti‑Patterns
- **Prompt Drift:** Fixing code without updating prompts or tests.
- **Spec Sprawl:** Requirements scattered across chats, tickets, and READMEs instead of consolidated in prompts.
- **Interactive Dependence:** Relying on chat patches for structural changes that should be regenerated.
- **Test Reset:** Throwing away prior tests after regeneration.
- **Mega‑Prompts:** Unbounded prompts that do too much; prefer split and composition.

## Doctrine → Practice (This Repo)
- **Structure:**
  - Frontend in `frontend/` (Next.js App Router, TypeScript)
  - Backend in `backend/functions/` (Python 3.12, Firebase Functions)
  - Next.js hosting function in `nextjs-server-function/`
  - Prompts, seeds, and context in `prompts/` and `context/`
- **Conventions:**
  - TypeScript: 2‑space indent, Prettier single quotes/trailing commas; components in `src/components/` (PascalCase); `@/*` alias.
  - Python: 4‑space indent, snake_case modules, explicit imports; business logic under `models/` and `utils/`.
- **Commands:**
  - Setup: `make setup`
  - Dev: `make dev` (or `make run-backend` and `cd frontend && npm run dev`)
  - Tests: `make test`, `make test-backend`, `make test-frontend`
  - Lint/format: `cd frontend && npm run lint && npm run format`
- **Testing:**
  - Backend: `backend/tests/test_*.py` with pytest; preserve and expand coverage when regenerating backend modules.
  - Frontend: Jest/Vitest colocated tests; keep server/client boundaries explicit and tested.
- **Security & Config:**
  - No secrets in git. Frontend vars in `frontend/.env.local` (`NEXT_PUBLIC_*` to expose). Backend secrets in GSM; local in `backend/functions/.env`.
- **Regeneration Discipline:**
  - Update prompts in `prompts/` first; run batch generation; fix; then `update` prompts with learnings.
  - Treat examples as interfaces; keep them runnable and minimal.

## Authoring Prompts
- **Be Declarative:** State goals, constraints, and non‑functional requirements explicitly.
- **State Interfaces:** Describe inputs/outputs and example usage; keep examples short but executable.
- **Context Wisely:** Include only relevant examples; prefer curated few‑shot over dumping repos.
- **Encode Policies:** Compliance, security, performance SLOs belong in prompts and tests.
- **Version Clearly:** Commit prompt changes with rationale (“why” first), link to affected modules/tests.

## Working With Examples & Patterns
- **Examples As Interfaces:** Each module has a minimal example that compiles/runs and demonstrates intended use.
- **Pattern Reuse:** Prefer proven few‑shot examples from our library/marketplace over ad‑hoc hand‑holding.
- **Auto‑Submit:** Where applicable, allow successful examples to contribute back to the pattern library.

## Quality Bar
- **Functional Equivalence Over Textual Diff:** Large diffs are acceptable; unchanged behavior is required.
- **Green Tests Before Merge:** Regenerated code must pass existing tests plus any new ones.
- **Observability:** Add logging/metrics via prompts; verify with smoke tests.
- **Docs From Prompts:** Public‑facing docs are generated from the same sources of truth.

## Governance & Collaboration
- **PR Discipline:** Summarize prompt changes, regeneration scope, and test deltas. Attach screenshots for UI, note emulator/config changes.
- **Review Mindset:** Review prompts and examples first, then generated code for unsafe or leaky abstractions.
- **Rollbacks:** Prefer regenerating from the prior prompt version over reverting code patches.

## When To Patch
- **Local, Low‑Risk Hotfixes:** Trivial typos, comments, and non‑behavioral changes may be patched directly—but follow with an `update` to keep prompts in sync.
- **Everything Else:** Regenerate.

## North Star
Prompts encode intent. Tests preserve behavior. Regeneration sustains integrity. Together, they convert maintenance from an endless patchwork into a compounding system of leverage.

