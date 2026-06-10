# Prompt‑Driven Development Prompting Guide

This guide shows how to write effective prompts for Prompt‑Driven Development (PDD). It distills best practices from the PDD whitepaper, the PDD doctrine, and working patterns in this repo. It also contrasts PDD prompts with interactive agentic coding tools (e.g., Claude Code, Cursor) where prompts act as ad‑hoc patches instead of the source of truth.

Think of PDD prompts as source files in a prompt-native programming system. The
prompt suite, includes, examples, tests, architecture metadata, and `.pddrc`
configuration form the source; `pdd sync` compiles that source into conventional
code artifacts.

References: `pdd/docs/whitepaper.md`, [prompt-driven-development-doctrine.md](prompt-driven-development-doctrine.md), `README.md` (repo structure, conventions), [Effective Context Engineering](https://www.anthropic.com/engineering/effective-context-engineering-for-ai-agents), [Anthropic Prompt Engineering Overview](https://docs.anthropic.com/en/docs/build-with-claude/prompt-engineering/overview).

---

## The North‑Star Metric

Every recommendation in this guide ladders up to a single metric:

> **`verified_behavioral_change_per_unit_cost`** = (hidden‑test‑passing behavior changes) ÷ (edit + localization + generation + verification + review cost)

Read the numerator carefully: it counts **verified** behavior changes — changes that pass *hidden* tests, not just the visible ones a model can overfit to. The denominator is the *total* cost of making that change land: finding the right place, writing/editing the prompt, generating, verifying, and reviewing.

This metric, not "code volume" or "smallest possible prompt," is the thing to optimize. A terse prompt that produces plausible-but-unverified code scores *badly*: zero verified change over real cost. Contracts, grounding, tests, and review all exist to push this ratio up. The word that does the heavy lifting is **verified** — see the [Verification](#verification-the-spine-of-pdd) chapter, which is the spine of everything here.

---

## Quickstart: PDD in 5 Minutes

If you are new to Prompt-Driven Development (PDD), follow this recipe:

1.  **Think "One Prompt = One Module":** Don't try to generate the whole app at once. Focus on one file (e.g., `user_service.py`).
2.  **Use a Template:** Start with a clear structure: Role, Requirements, Dependencies, Instructions. (See the [Reusable Prompt Skeleton](#reusable-prompt-skeleton).)
3.  **Explicitly Include Context:** Use `<include>path/to/file</include>` to give the model *only* what it needs (e.g., a shared preamble or a dependency interface). This is a **PDD directive**, not just XML. (See [Directives & Context](#prompt-syntax-essentials).)
4.  **Regenerate, Don't Patch:** Change behavior by changing the prompt and regenerating. If generated code fails to satisfy a correct prompt/test, use `pdd bug` / `pdd fix`. If the intended behavior is missing or wrong in the prompt, update the prompt first.
5.  **Verify:** Run the generated code/tests. Without verification, regeneration just produces plausible wrong code faster — see [Verification](#verification-the-spine-of-pdd).

*Tip: Treat your prompt like source code. It is the single source of truth.*

Successful fixes can contribute to grounding, but the prompt remains the source of truth. If the fix changes intent, back-propagate that intent into the prompt.

**Already using a coding agent (Claude Code / Cursor / Codex / Copilot)?** The friendliest on-ramp is the [Using PDD With Your Coding Agent](#using-pdd-with-your-coding-agent) chapter — keep your agent's fast loop and add PDD as the verified build layer.

**Working in an existing codebase?** See [Brownfield Adoption](#brownfield-adoption) for the incremental, one-module-at-a-time recipe.

*For the conceptual foundation of why this works, see [The Mold Paradigm](prompt-driven-development-doctrine.md#the-mold-paradigm) in the doctrine.*

---

## Glossary

- **Context Engineering:** The art of curating exactly what information (code, docs, examples) fits into the LLM's limited "working memory" (context window) to get the best result.
- **Shared Preamble:** A standard text file (e.g., `project_preamble.prompt`) included in every prompt to enforce common rules like coding style, forbidden libraries, and formatting.
- **PDD Directive:** Special tags like `<include>` or `<shell>` that the PDD tool processes *before* sending the text to the AI. The AI sees the *result* (the file content), not the tag.
- **Source of Truth:** The definitive record. In PDD, the **Prompt** is the source of truth; the code is just a temporary artifact generated from it.
- **PDD Program:** A versioned prompt suite plus its includes, examples, tests, architecture metadata, and configuration.
- **Compilation:** Running `pdd sync` or related commands to regenerate conventional code artifacts from PDD source and validate them.
- **Grounding (Few-Shot History):** The process where the PDD system can use successful past pairs of (Prompt, Code) as "few-shot" examples during generation. This helps regenerated code follow established style and logic, reducing the chance of a completely different implementation. (See [Grounding & Critical Modules](#automated-grounding-pdd-cloud).)
- **Drift:** When the generated code slowly diverges from the prompt's intent over time, or when manual edits to code make it inconsistent with the prompt.
- **Mold / Mold Walls:** The constraints (frozen interface, behavioral tests, negative tests for MUST NOT rules) that make a module regeneration-safe. The model fills the mold; the walls determine the shape. (See [Verification](#verification-the-spine-of-pdd).)

---

## Why PDD Prompts (Not Patches)

- Prompts are the source of truth; code is a generated artifact. Update the prompt and regenerate instead of patching code piecemeal.
- Regeneration preserves conceptual integrity and reduces long‑term maintenance cost (see `pdd/docs/whitepaper.md`).
- Prompts consolidate intent, constraints, dependencies, and examples into one place so the model can use them during generation.
- Tests accumulate across regenerations and act as a regression net; prompts and tests stay in sync.

**Prompt capital appreciates; code capital depreciates.** The LLM "compiler" improves over time, so prompt-sourced code gets *better for free* on each model upgrade — regenerate the same prompt against a stronger model and get a better implementation. Traditional source code does not appreciate this way; it ages.

Contrast with interactive patching (Claude Code, Cursor): prompts are ephemeral instructions for local diffs. They are great for short, local fixes, but tend to drift from original intent as context is implicit and often lost. In PDD, prompts are versioned, explicit, and designed for batch, reproducible generation. The two approaches are **complements** — see [Using PDD With Your Coding Agent](#using-pdd-with-your-coding-agent).

For a deeper exploration of why this paradigm shift matters—and an analogy to manufacturing's wood‑to‑plastic transition—see [The Mold Paradigm](prompt-driven-development-doctrine.md#the-mold-paradigm) in the doctrine.

---

<a name="honest-task-fit-boundary"></a>
## Honest Task‑Fit Boundary

PDD is **not** "regenerate everything." It is a tool for behavior you will verify and regenerate repeatedly. Stating its limits honestly is what makes it trustworthy.

**Strong-fit — capture these as PDD modules:**

- Validation and business rules
- Adapters / API wrappers
- Data transforms
- Internal tools and scripts
- CRUD endpoints and services
- Customer-specific variants of a common pattern
- Test generation
- Policy enforcement

These are observable, testable in isolation, and have knowable interfaces — exactly what a regeneration-safe mold needs.

**Weak-fit — patch directly or keep as conventional code (for now):**

- Tiny hotfixes
- Performance micro-optimizations
- Legacy code with hidden coupling
- Hard-to-test behavior
- Novel algorithms
- Large architectural ambiguity
- Safety-critical code without a strong existing test suite

Weak-fit code isn't permanently off-limits — promote it to a PDD module once it has seams and tests and the contract becomes knowable. The discipline: **convert what's worth verifying repeatedly; leave the rest.** The [Brownfield Adoption](#brownfield-adoption) chapter applies this boundary to picking first modules; [Hybrid Agent Workflow](#using-pdd-with-your-coding-agent) applies it to choosing between PDD and your agent.

---

## The PDD Mental Model

- One prompt typically maps to one code file or narrowly scoped module.
- You explicitly curate the context to place in the model's window (don't "dump the repo").
- Change behavior by editing the prompt; re‑generate the file; run crash/verify/test/fix; then update the prompt with learnings.
- Keep the "dev unit" synchronized: prompt + generated code + minimal runnable example + tests.

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

The durable PDD chain:

```text
Prompt = source of truth
Contract rules = durable obligations
User stories = prompt-level acceptance tests
Generated tests = executable evidence
Accumulated tests = mold walls
Generated code = disposable artifact
```

That discipline converts maintenance from an endless patchwork into a compounding system of leverage.

---

---

## Using PDD With Your Coding Agent

**New to PDD? Start here.** If you already use an interactive coding agent — Claude Code, Cursor, Codex, GitHub Copilot — you already have most of what you need. This chapter shows how to add PDD as a *governance and build layer* on top of your agent, without giving up the fast, exploratory loop you like.

The one-sentence version: **your agent edits the intent (prompts, contract rules, tests); PDD turns that intent into verified code, reproducibly.** You keep the conversation; PDD gives it a source of truth and a build button.

---

## PDD and Agents Are Complements, Not Competitors

A common misconception is that PDD competes with agentic coders. It does not. They operate at different layers:

| | Interactive agent (Claude Code / Cursor / Codex / Copilot) | PDD |
|---|---|---|
| **Best at** | Exploring, proposing, local edits, fast feedback | Reproducible regeneration + verification of a scoped module |
| **Acts as** | The **editor** of intent (prompts, contracts, tests) | The **build step** that compiles intent into verified code |
| **Output** | Diffs, ideas, drafts | A regenerated module + passing tests + an evidence manifest |
| **Memory** | Ephemeral chat context | Versioned prompt suite + accumulated tests |

The agent is great at the part that is hard to specify in advance: *figuring out what to build.* PDD is great at the part agents are bad at: *making the result durable, reproducible, and verified.* Use both. The agent can even write your PDD prompts and tests for you — that is the intended workflow.

> This is the practical face of "complement, don't compete." For the conceptual contrast (source of truth, drift, scope), see [PDD vs Interactive Agentic Coders](#pdd-vs-interactive-agentic-coders-claude-code-cursor).

---

## The Hybrid Loop

```mermaid
flowchart LR
  A["Agent explores & proposes<br/>(chat, drafts, local edits)"] --> B["You capture intent:<br/>prompt + contract rules + tests"]
  B --> C["PDD regenerates the module<br/>(pdd generate / pdd sync)"]
  C --> D["Tests / verify gate<br/>(pdd verify, test runner)"]
  D -->|pass| E["Manifest captures<br/>what went into the call"]
  D -->|fail| B
  E --> A
```

Step by step:

1. **Agent explores & proposes.** Use your agent the way you already do — ask it to investigate, sketch an approach, draft an implementation, try things interactively. This is the cheap, creative phase. Nothing here is the source of truth yet.
2. **You capture intent as durable artifacts.** Once you know what you want, *promote* it out of the chat into PDD source: a module **prompt** (role, requirements, contract rules), **user stories** for product-level behavior, and **tests**. Your agent can write all three — ask it to "turn what we just built into a PDD prompt with contract rules and tests." (Authoring details: [Contracts](#natural-language-contracts).)
3. **PDD regenerates the module.** Run `pdd generate` (or `pdd sync`) so the code is produced *from the prompt*, not hand-carried out of the chat. Now the prompt — not the diff — is the source of truth.
4. **Tests / verify gate.** Run the tests and `pdd verify`. This is the [verification spine](#verification-the-spine-of-pdd): regeneration is only trustworthy because the gate is. If it fails, go back to step 2 and refine the prompt/tests (let the agent help).
5. **Manifest captures the call.** PDD records what went into the generation — prompt, included context, grounding examples used, and results — in the evidence manifest (`../evidence_manifest.md`). This is the audit trail the chat never gave you.

The loop closes: the manifest and passing tests feed back to the agent as context for the next exploration. Each turn leaves behind durable, versioned, verified artifacts instead of an ephemeral chat history.

---

## Worked Example: A Coupon Validation Helper

Suppose you're adding coupon support to a checkout flow.

### 1. Explore with the agent

You open Claude Code (or Cursor / Codex / Copilot) and say:

> "I need to validate coupon codes at checkout. Let's figure out the rules — expired coupons, already-redeemed coupons, minimum-cart-total coupons — and sketch a `validate_coupon` function."

The agent proposes a `validate_coupon(code, cart, now)` function, talks through edge cases, and writes a draft. You iterate in chat until the behavior feels right. **This draft is disposable** — it lives in the conversation, not in your repo's source of truth.

### 2. Capture intent as PDD source

Now you ask the agent to promote it:

> "Turn this into a PDD module prompt for `prompts/validate_coupon_python.prompt`. Add numbered contract rules for the MUST/MUST NOT behavior, and write executable tests including negative tests for the forbidden cases."

The agent produces a prompt like:

```text
% You are an expert Python engineer. Implement `validate_coupon`.

<include>context/project_preamble.prompt</include>

<responsibility>
Validates a coupon code against a cart at a point in time and returns a result.
</responsibility>

<non_responsibilities>
- Does not apply the discount to the cart.
- Does not record redemption.
</non_responsibilities>

<vocabulary>
- Redeemable: a coupon that is active, not expired, not already redeemed, and whose minimum cart total is met.
</vocabulary>

<contract_rules>
R1 - Expiry
For every coupon, the system MUST reject the coupon when `now` is at or after its expiry.

R2 - Single use
For every single-use coupon already marked redeemed, the system MUST reject the coupon.

R3 - Minimum cart total
For every coupon with a minimum cart total, the system MUST reject the coupon when the cart total is below that minimum.

R4 - No side effects
The system MUST NOT mutate the cart, MUST NOT mark the coupon redeemed, and MUST NOT emit any event.
</contract_rules>

<pdd-interface>
{"type":"module","module":{"functions":[
  {"name":"validate_coupon","signature":"(code, cart, now) -> CouponResult","returns":"CouponResult"}]}}
</pdd-interface>
```

…and tests, including a **negative test for R4** that fails if the cart is mutated or a redemption event is emitted. (Why the negative test matters: [Verification → minimum viable mold](#abc).)

### 3. Regenerate from the prompt

```bash
pdd generate prompts/validate_coupon_python.prompt
pdd test prompts/validate_coupon_python.prompt src/validate_coupon.py
```

The code now comes *from the prompt*. If you later change a rule (say, coupons become multi-use up to a cap), you edit R2 in the prompt and regenerate — you don't hand-patch the code.

### 4. Gate it

```bash
pytest tests/test_validate_coupon.py
pdd verify   # where configured
```

Green means the regenerated module satisfies every contract rule, including the forbidden-side-effects rule. Red means refine the prompt or tests (back to step 2 — bring the agent in).

### 5. The manifest

PDD records the generation — prompt, includes, any grounding examples used, results — in the evidence manifest. When a teammate asks "why does this module look the way it does?", the answer is the prompt + manifest, not a lost chat transcript.

---

## Who Owns What

A simple division of labor keeps the hybrid workflow clean:

- **The agent owns exploration and drafting.** Let it be fast, speculative, and chatty.
- **The prompt owns intent.** Once a behavior is decided, it lives in the prompt as requirements and contract rules — never only in the chat.
- **Tests own correctness.** They are the gate that makes regeneration safe and the [ratchet](#tests-as-generation-context) that prevents regression.
- **PDD owns the build.** `pdd generate` / `pdd sync` produce the code reproducibly; the manifest records how.

When you find yourself hand-editing generated code in the chat to fix behavior, that's the signal to **back-propagate** the change into the prompt or a test (see [When to Update the Prompt](#when-to-update-the-prompt-and-when-not-to)). The chat is where you discover intent; the prompt is where intent lives.

---

## Pick the Right Tool for the Task

PDD is not for everything, and neither is your agent. Use the [task-fit boundary](#honest-task-fit-boundary) on the landing page:

- **Reach for PDD** (capture as a module) for validation/business rules, adapters and API wrappers, data transforms, internal tools, CRUD, customer variants, test generation, and policy enforcement — anything you'll regenerate and must keep correct.
- **Stay in the agent / patch directly** for tiny hotfixes, perf micro-optimizations, hard-to-test behavior, novel algorithms, and large architectural ambiguity where the contract isn't yet knowable. (Then, if it stabilizes, promote it to a PDD module.)

The honest rule: promote to PDD when a behavior is worth verifying repeatedly. Until then, the agent's fast loop is the right tool.

---

---

## Verification: The Spine of PDD

Everything in PDD rests on one assumption: **you can verify, cheaply and repeatably, that a regenerated module still does what it must.** If that assumption is false, regeneration is not an advantage — it is a liability. Without strong verification, multi-shot regeneration just produces *plausible wrong code faster.*

This is why verification is the organizing principle of the whole guide. Contracts ([Contracts](#natural-language-contracts)) declare what must hold; grounding ([Grounding & Critical Modules](#automated-grounding-pdd-cloud)) keeps structure stable; directives ([Directives & Context](#prompt-syntax-essentials)) control what the model sees. But verification is what turns "a model wrote some code" into "a behavior change we trust." It is the term in the denominator-and-numerator of the north-star metric, `verified_behavioral_change_per_unit_cost`: the word *verified* is load-bearing.

---

## Why Verification Is the Spine

PDD's entire advantage is that you can throw away code and regenerate it. That only works if you have something that does not get thrown away and that tells you whether the new code is correct. That something is your verification suite: accumulated tests, user stories, contract rules with negative tests, and (optionally) property and mutation checks.

Two failure modes make this concrete:

- **Strong prompt, weak verification.** The model produces code that looks right, passes the one happy-path test you wrote, and silently violates a security or idempotency rule. Each regeneration is a fresh roll of the dice. You ship faster *and* regress faster.
- **Modest prompt, strong verification.** Even a terse prompt regenerates safely, because the tests catch any drift and the model sees the failing tests as behavioral context on the next pass. The walls do the work.

The takeaway: invest in verification *before* you invest in clever prompting. A module without verification is not a PDD module; it is a one-time generation.

---

## The Minimum Viable Mold

A module is **regeneration-safe** only when it has all three of the following. Below this bar, do not rely on repeated regeneration — treat the code as hand-owned until you can build the mold.

<a name="abc"></a>

**(a) A frozen / declared interface.**
The public surface — function signatures, return types, error types, route shapes — is written down and stable. Declare it in the prompt (`<pdd-interface>`, an Inputs/Outputs section) and, where it matters, pin it with `mode="interface"` includes of dependencies. Callers depend on this surface; regeneration must not silently change it. (See [Directives & Context](#architecture-metadata-tags).)

**(b) N behavioral tests.**
At least one executable test per requirement / contract rule, asserting *observable behavior* (return values, state transitions, emitted events, calls made) — not private helper names or exact message strings. "N" scales with risk: a CRUD helper might need a handful; an `auth` or `payments` module needs many, covering each lifecycle stage. These tests accumulate and persist across regenerations.

<a name="a-negative-test-for-every-must-not"></a>
**(c) A negative test for every MUST NOT rule.**
Every `MUST NOT` in the contract — every forbidden side effect, leak, or premature external call — needs a test that *fails if the forbidden thing happens.* Positive tests prove the module does the right thing; negative tests prove it does not do the wrong thing. A `MUST NOT` with no negative test is an unverified claim.

A module that has (a) + (b) + (c) can be regenerated freely: the interface constrains the shape, the behavioral tests constrain the behavior, and the negative tests constrain the failure space. That is the mold.

---

## The Mold-Walls Concept

Think of the generated code as molten material poured into a mold. The model fills the cavity; the **walls** determine the final shape. Weak walls → the material spreads wherever it wants (plausible, unconstrained, drifting code). Strong walls → every pour comes out the same usable shape.

The walls are made of:

| Wall | Supplied by | Constrains |
|------|-------------|-----------|
| **Interface wall** | `<pdd-interface>`, `mode="interface"` includes, declared I/O | The public shape callers depend on |
| **Behavior wall** | Accumulated executable tests (seen as generation context, enforced by the runner) | What the code must *do* |
| **Forbidden wall** | Negative tests for MUST NOT rules | What the code must *never* do |
| **Pattern wall** | Cloud grounding / pinned examples | Structural consistency (how it's written) |

Compression supplies *one* wall cheaply — sending only a dependency's interface, not its body, is a token-efficient way to define the interface wall (see [Compressed Context as a "Mold Wall"](#compressed-context-as-a-mold-wall)). But interface compression alone is not verification. The behavior and forbidden walls come from tests.

> **The conflict-resolution rule:** tests take precedence over grounding and examples. If a test demands a behavior, generation must satisfy it and the runner enforces it. Grounding shapes *how* code is written; tests decide *whether* it is correct. (See [Three Pillars](#the-three-pillars-of-pdd-generation).)

---

## Tests as Specification and Generation Context

In PDD, tests play two roles at once. They are the *specification* of behavior at the example level, and they are *generation context* fed back into the model.

### Tests as Generation Context

A key PDD feature: existing tests are automatically included as context when generating code. This means:

- The LLM sees the test file as behavioral context
- Generated code is expected to preserve those behaviors
- The test runner provides the actual enforcement
- New tests accumulate over time, progressively guiding and checking future generations
- This creates a **"ratchet effect"** — each bug fix adds a test, preventing regression

This is distinct from test *generation*. Executable tests are generated via `pdd test PROMPT_FILE CODE_OR_EXAMPLE_FILE`, which uses the module prompt, generated code or example code, and `context/test.prompt` for project-wide guidance. Story mode also uses `pdd test`, but it generates or updates Markdown stories and prompt links rather than executable test files. Executable tests accumulate over time via `--merge` as bugs are found. Requirements in the module prompt implicitly define what to test — each requirement should correspond to at least one test case.

```mermaid
flowchart LR
  subgraph Assets
    P[Module Prompt] --> G[pdd generate]
    T[Existing Tests] --> G
    G --> C[Generated Code]
  end

  subgraph Accumulation
    BUG[Bug Found] --> NT[New Test Written]
    NT --> T
  end
```

### Tests vs. Stories vs. Contract Rules

These three layers verify at different altitudes — author them in [Contracts](#natural-language-contracts), enforce them here:

- **Contract rules** state general obligations (MUST / MUST NOT). Durable, prompt-level.
- **User stories** are example-level acceptance tests, often cross-module, written from the user's perspective. They list which rules they `Cover`.
- **Executable tests** are concrete, fast, run on every change. They are the enforcement layer.

Stories are also the natural home for **negative cases**: every MUST NOT rule should be backed by a negative story and, eventually, a negative test. (See [Negative Stories](#negative-stories).)

---

## Contract Evidence Levels as Wall Strength

The four contract evidence levels are a direct measure of how strong a rule's wall is. Use them to grade each high-risk rule.

| Level | Wall strength | Verified by |
|-------|---------------|-------------|
| **1. Prompt-only** | Weakest — claim only | The rule is visible to model and reviewer; nothing enforces it |
| **2. Story-backed** | Documented example | A user story describes the expected behavior |
| **3. Test-backed** | Enforced | An executable test fails if the rule is violated |
| **4. Policy-backed** | Enforced + automated gate | Static analysis / CI / custom review checks the rule on every change |

**Production rule:** high-risk MUST / MUST NOT behavior must not ship at level 1. Either reach level 3+ or record an explicit, expiring [waiver](#contract-coverage-matrix). A waiver is an honest IOU; a silent prompt-only rule is a latent regression.

---

## Hidden vs. Public Tests

Not all verification should live where the model can read it.

- **Public tests** are included as generation context. The model sees them and writes code to satisfy them. This is the ratchet — most of your accumulated tests are public.
- **Hidden tests** are *not* shown to the model during generation; they only run in the verification gate (CI, `pdd verify`, the test runner). They measure whether the model produced genuinely correct behavior or merely **overfit to the visible tests.**

Why keep some tests hidden? Because a model that sees a test can write the narrowest code that passes that exact assertion. Hidden tests detect this overfitting: if public tests pass but hidden tests fail, the generated code learned the test, not the behavior. For high-risk modules, hold back a portion of behavioral and negative tests as a hidden gate.

> The north-star metric counts **hidden-test-passing behavior changes**, precisely because passing visible tests can be gamed by overfitting. Hidden tests are how you keep the metric honest.

---

## Strengthening the Walls: Mutation and Property Testing

Once you have basic behavioral and negative tests, two techniques make the walls harder to slip past.

### Mutation testing

Mutation testing deliberately introduces small faults ("mutants") into the code and checks whether your tests catch them. A surviving mutant means a behavior your tests do not actually constrain — a gap in the wall. Mutation testing answers "how good are my tests?" rather than "does my code pass?" It is especially valuable in PDD because regeneration is itself a source of "mutations": if a real mutant survives, a future regeneration could introduce the same fault undetected.

### Property-based testing

Property-based tests assert *invariants* over a large, generated space of inputs rather than a handful of hand-picked cases. They map naturally onto contract rules:

- An idempotency rule (R4-style) → property: "applying the operation twice equals applying it once."
- A validation invariant → property: "for all inputs in this class, the result is a `ValidationResult` and never throws."
- A monotonic-balance rule → property: "remaining refundable amount never goes negative across any sequence of valid refunds."

Properties widen the behavior wall from "these specific cases" to "this whole class of cases," which is exactly the kind of constraint that survives regeneration well.

Use these to *strengthen* walls, not as a prerequisite. A module with solid behavioral + negative tests is already regeneration-safe; mutation and property testing raise the ceiling for critical modules.

---

## The Regeneration-Safe Checklist

Before you rely on repeated regeneration of a module, confirm:

- [ ] **(a) Interface declared and frozen** — signatures, return types, error types, route shapes are written down and stable.
- [ ] **(b) N behavioral tests** — at least one per requirement / contract rule, asserting observable behavior, scaled to risk.
- [ ] **(c) Negative test per MUST NOT** — every forbidden side effect, leak, or premature call has a test that fails if it happens.
- [ ] High-risk rules are at evidence **level 3+** or have an explicit, expiring waiver.
- [ ] Tests assert **behavior**, not private helper names or exact message strings (prefer `pytest.raises(ExcType, match=r"keyword1|keyword2")`).
- [ ] Tests **accumulate** — `--merge` / append, never overwrite the test file.
- [ ] For critical modules: a portion of tests are **hidden** from generation context.
- [ ] **Drift check** passes — regenerating without changing the prompt still passes all tests (see [Workflow & Review](#regenerate-verify-test-update)).
- [ ] `pdd verify` and `pdd detect --stories` pass where applicable.

If a module cannot pass (a)/(b)/(c), it is not yet a regeneration-safe PDD module. Build the mold first — or, for an existing codebase, follow the [Brownfield Adoption](#brownfield-adoption) recipe to build it incrementally around current behavior.

---

---

This chapter covers how to write the *intent* half of a PDD prompt: the contract rules, vocabulary, capabilities, user stories, and requirements that survive regeneration. Contracts are what make a module a regeneration-safe **mold** rather than a one-off generation — see [Verification](#the-minimum-viable-mold) for how contracts + tests form the mold walls.

Everything here ladders up to the north-star metric: `verified_behavioral_change_per_unit_cost`. A contract rule only earns its keep when it is observable and testable; a rule no test can check is documentation, not a contract.

---

## Natural-Language Contracts

A natural-language contract is a testable obligation written in controlled language.

Use contract rules for behavior that must survive regeneration:

- Validation rules
- Error behavior
- Invariants
- Security constraints
- Permission boundaries
- State transitions
- Idempotency
- Data privacy
- External side effects

Contract rules should use stable IDs and modal verbs:

- **MUST**: required behavior
- **MUST NOT**: forbidden behavior
- **MAY**: allowed behavior
- **SHOULD**: preferred behavior, but not required
- **DOES NOT**: explicitly outside this module's responsibility

A good contract rule is observable, testable, scoped to this module, independent of implementation strategy, and written at the level of behavior rather than code structure.

### Contract Rule Format

```md
R<ID> - <Short name>

For every <entity/action>,
the system MUST/MUST NOT <observable behavior>
when <condition>.

This rule is violated if <specific forbidden outcome>.
```

Do not renumber existing rule IDs after stories or tests reference them. If a rule is removed, mark it deprecated or leave a gap. If a rule changes meaning substantially, create a new rule ID.

Example:

```md
R1 - Reject over-refunds

For every refund request,
the system MUST reject the request
when the requested amount is greater than the remaining refundable amount.

This rule is violated if the payment provider is called for an over-refund request.
```

### Vocabulary and Ambiguity Control

Define any term that could affect behavior. Common ambiguous terms include active user, valid request, duplicate record, safe HTML, recent transaction, successful import, authorized user, remaining balance, trusted input, and graceful error handling.

Weak:

```md
The system should reject duplicate uploads.
```

Better:

```md
Duplicate upload means an upload with the same normalized file hash and tenant ID as a previously accepted upload.
The system MUST reject duplicate uploads before writing new records.
```

Weak:

```md
Return safe HTML.
```

Better:

```md
Safe HTML means user-controlled text has been escaped before being written to an HTML sink.
The system MUST NOT write raw user-controlled display name, bio, or location text into an HTML sink.
```

Before committing a prompt, review every contract rule and ask:

- Which words could be interpreted in more than one way?
- Are those words defined in Vocabulary?
- Could a test writer implement this requirement without asking follow-up questions?

### Capabilities and Side Effects

For modules that touch external systems, add a capabilities section. The capabilities section says what this module may and may not do. This helps prevent accidental behavior expansion during regeneration.

Template:

```xml
<capabilities>
- MAY read <resource>.
- MAY write <resource>.
- MAY call <external API>.
- MAY emit <event>.
- MUST NOT call <forbidden API>.
- MUST NOT read <forbidden data>.
- MUST NOT write <forbidden data>.
- MUST NOT mutate <out-of-scope state>.
</capabilities>
```

Example:

```xml
<capabilities>
- MAY read payment records.
- MAY write refund records.
- MAY call the payment provider refund endpoint.
- MAY write audit events.
- MUST NOT send emails.
- MUST NOT update customer profile records.
- MUST NOT log provider secrets, bearer tokens, card PAN, or CVV.
</capabilities>
```

### Contract Rules vs. Edge Cases vs. Tests

Use contract rules for general obligations.

Use user stories for product-level examples and cross-module behavior.

Use executable tests for concrete edge cases, regressions, and implementation-level checks.

Do not put every edge case in the prompt. Instead:

- Summarize the general rule in the prompt
- Add representative user stories
- Accumulate executable tests as bugs and edge cases are discovered

Example:

```md
Prompt contract rule:
R1 - The system MUST reject malformed email addresses.

User story:
Given a signup form with malformed email "alice@", when submitted, then the user sees an email validation error.

Tests:
- rejects empty email
- rejects whitespace email
- rejects email without domain
- rejects email with invalid unicode
- accepts normalized valid email
```

### Contract Evidence Levels

1. **Prompt-only:** Contract rules are visible to the model and reviewer.
2. **Story-backed:** High-risk rules are covered by user stories.
3. **Test-backed:** Rules are covered by executable tests.
4. **Policy-backed:** Security/capability rules are checked by static analysis, CI, or custom review.

### Contract Exception States

- **Unchecked:** No story, test, policy check, or waiver exists yet.
- **Waived:** The rule is intentionally unchecked, with reason, approver, expiry, and follow-up.

Most modules do not need every evidence level. Production-critical modules should not rely on prompt-only contracts for high-risk behavior. The evidence ladder above is the same one [Verification](#contract-evidence-levels-as-wall-strength) uses to grade how strong a mold's walls are.

---

## Anatomy of a Good PDD Prompt

A well-designed prompt contains **only what can't be handled elsewhere**. With Cloud grounding or explicit examples plus accumulated tests, prompts can stay focused.

### Required Sections for Simple Modules

1. **Role and scope** (1-2 sentences): What this module does
2. **Requirements** (5-10 items): Functional and non-functional specs
3. **Dependencies** (via `<include>`): Only external or critical interfaces

### Required Sections for Non-Trivial Modules

Use more structure when the module has external side effects, security risk, cross-module behavior, state transitions, or business-critical rules:

1. **Role and scope**: One or two sentences describing what this module does.
2. **Responsibility**: What this module owns.
3. **Non-responsibilities**: What this module explicitly does not own.
4. **Vocabulary**: Definitions for domain terms that could be ambiguous.
5. **Contract rules**: Stable, numbered MUST/MUST NOT/MAY/DOES NOT rules.
6. **Inputs and outputs**: Types, shapes, accepted values, validation rules, and error conditions.
7. **Dependencies**: Use `<include>` for external APIs, critical interfaces, schemas, examples, or documentation.
8. **Deliverables**: Only when non-obvious.

For trivial modules, you may combine Responsibility, Vocabulary, and Contract Rules into a concise Requirements section. Do not bloat prompts with every edge case. Use user stories and accumulated tests for examples and regressions.

### Optional Sections

- **Instructions**: Only if default behavior needs overriding
- **Deliverables**: Only if non-obvious
- **Coverage**: Useful for non-trivial modules with named contract rules

### What NOT to Include

- **Coding style** (naming, formatting, imports) → Handled by shared preamble
- **Implementation patterns** (class structure, helpers) → Usually handled by Cloud grounding; local users may need explicit examples via `<include>`
- **Every edge case** → Handled by accumulated tests
- **Implementation steps** → Let the LLM decide (unless critical)

### Target Size: Prompt-to-Code Ratio

Aim for **10-30%** of your expected code size:

| Ratio | Meaning |
|-------|---------|
| **< 10%** | Too vague—missing contracts, error handling, or key constraints |
| **10-30%** | Just right—requirements and contracts without implementation details |
| **> 50%** | Too detailed—prompt is doing preamble's, examples', or grounding's job |

If your prompt exceeds 30%, ask: Am I specifying things that the preamble, Cloud grounding, examples, or tests should handle?

**Note:** Executable tests are generated from the module prompt plus generated code or example code, with `context/test.prompt` providing project-wide test guidance. Well-written requirements are inherently testable, so most module prompts do not need a separate Testing section.

See `pdd/pdd/templates/generic/generate_prompt.prompt` for a concrete scaffold.

---

## Reusable Prompt Skeleton

```xml
% Role:
% You are an expert <language/framework> engineer.
% Implement <module_name>.

<include>context/project_preamble.prompt</include>

<pdd-reason>Short architecture-facing reason this module exists.</pdd-reason>

<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {
        "name": "refund_payment",
        "signature": "(payment_id, amount, idempotency_key) -> RefundResult",
        "returns": "RefundResult"
      }
    ]
  }
}
</pdd-interface>

<responsibility>
This module validates and creates refunds for captured payments.
</responsibility>

<non_responsibilities>
- Does not authenticate the operator.
- Does not authorize whether the operator may refund.
- Does not perform currency conversion.
- Does not send customer notifications.
</non_responsibilities>

<vocabulary>
- Captured amount: the amount successfully captured from the customer.
- Successful refund: a refund confirmed by the payment provider.
- Pending refund: a refund submitted to the provider but not yet confirmed or failed.
- Remaining refundable amount: captured amount minus successful refunds minus pending refunds.
- Duplicate request: a request with the same payment ID and idempotency key.
</vocabulary>

<contract_rules>
R1 - Positive amount
For every refund request, the system MUST reject the request when the requested amount is less than or equal to zero.

R2 - Remaining balance
For every refund request, the system MUST reject the request when the requested amount is greater than the remaining refundable amount.

R3 - No provider call before validation
The system MUST NOT call the payment provider for requests rejected by R1 or R2.

R4 - Idempotency
For every duplicate request with the same payment ID and idempotency key, the system MUST NOT create more than one provider refund, MUST NOT write more than one successful-refund audit event, and MUST return the same logical result for repeated submissions.

R5 - Auditability
For every successful refund, the system MUST write exactly one durable successful-refund audit event.
Provider failures MAY write a failed-refund audit event, but MUST NOT write a successful-refund audit event.

R6 - Privacy
The system MUST NOT expose card PAN, CVV, API keys, bearer tokens, or raw provider secrets in logs, audit events, errors, or return values.
</contract_rules>

<capabilities>
- MAY read payment records.
- MAY write refund records.
- MAY call the payment provider refund endpoint after validation succeeds.
- MAY write audit events.
- MUST NOT send emails.
- MUST NOT modify customer profile records.
- MUST NOT read unrelated environment variables.
</capabilities>

<waivers>
W1:
  Rule: R6
  Status: temporary
  Reason: Provider error fixture is not available yet.
  Approved by: security-review
  Expires: 2026-06-01
  Follow-up: Add story__provider_secret_not_leaked.md and executable test.
</waivers>

<dependencies>
<include mode="interface">src/payments/provider.py</include>
<include>docs/refund_policy.md</include>
</dependencies>

<coverage>
R1: story__refund_invalid_amount.md
R2: story__refund_over_remaining.md
R3: story__refund_over_remaining.md
R4: TODO add idempotency story before production use
R5: story__refund_auditability.md
R6: WAIVED W1
</coverage>

<deliverables>
Generate the implementation only.
Executable tests are generated separately by `pdd test prompts/refund_payment_python.prompt src/refund_payment.py`.
</deliverables>
```

Use `<pdd-reason>`, `<pdd-interface>`, and `<pdd-dependency>` only for architecture metadata; they sync with `architecture.json` (see [Directives & Context](#architecture-metadata-tags)). Do **not** put contracts inside `<pdd>...</pdd>` comments because `<pdd>` content is removed before the model sees it. Use ordinary semantic tags such as `<contract_rules>`, `<vocabulary>`, `<capabilities>`, `<waivers>`, and `<coverage>`.

---

## User Stories as Contract Coverage

A user story is an example-level prompt test. A contract rule is a general obligation. A good story identifies which contract rules it covers.

Every high-risk MUST or MUST NOT rule should be covered by at least one of:

- A user story
- An executable test
- An explicit waiver

Use stories for cross-module behavior, product acceptance criteria, critical edge cases, negative behavior, regressions from bugs, and behavior that is easier to describe from a user perspective than a module perspective.

Story files live in `user_stories/`. Use `pdd detect --stories` to validate them, `pdd change` to run validation after prompt modifications, and `pdd fix user_stories/story__*.md` to apply a story to prompts and re-validate it. Link stories to prompts with `pdd-story-prompts` metadata.

### Two files: human-verified Story + AI-generated contract

A user story is split across **two files** with different owners:

- **The human Story** at `user_stories/story__<name>.md` is the *only* thing a
  person reads and signs off on — one plain-language sentence ("As a
  &lt;persona&gt;, I can &lt;capability&gt;, so that &lt;benefit&gt;.") they can
  verify by using the product. It is the **source of truth**. Keep flags, exit
  codes, JSON shapes, and internals out of it.
- **The contract** at `user_stories/contracts/<name>.contract.md` is
  **generated** from the human Story + the original issue. It holds the
  machine-checkable sections (`## Covers`, `## Acceptance Criteria`, `## Oracle`,
  …) plus a `## Candidate Prompts` list of other prompts the story could run
  against. `pdd detect --stories` / the LLM uses it to confirm the prompts
  deliver the Story. Humans don't hand-edit it.

**Edit the Story, not the contract.** When you change the human Story, the
contract is regenerated from the edited Story + the issue to re-align (a
`story-hash` in the contract header tracks this). Validation feeds the Story and
its contract **combined** to `detect_change`.

**Keep it readable.** A human can only verify the Story quickly if they can read
it quickly. Write the Story in plain, everyday language a newcomer who does not
know PDD/LLM internals would understand. Translate internal jargon to the plain
idea even when the issue uses it (e.g. "hydrated prompt" → "your fully assembled
prompt"); keep genuine interface terms (command names, `--json`, exit codes)
because those are the user's own vocabulary, not jargon.

**Write durable Stories.** Describe the user's *stable goal* and *observable
outcome*, never a comparison to a specific external product, tool, brand, or UI
("works like Claude Code's UI", "matches Codex") and never a time-/version-pinned
fact ("the current best model", "as of 2026") unless the issue itself makes that
exact version the requirement. Whichever tool is "best" today may be surpassed
tomorrow; a story pinned to it rots into a false failure. List the brittle things
the contract deliberately excludes under its `## Non-Oracle` so the durability
boundary is explicit.

### Story Template

The human Story file — `user_stories/story__<name>.md` (the only part you write
and verify by hand):

```md
<!-- pdd-story-prompts: prompts/<module>_<language>.prompt -->

# User Story: <name>

## Story

As a <persona>,
I want <behavior>,
so that <value>.
```

The generated contract — `user_stories/contracts/<name>.contract.md` (produced
from the Story + issue; shown here for reference, not for hand-authoring):

```md
<!-- pdd-story-contract derived-from-story="../story__<name>.md" story-hash="<auto>" issue-ref="<url|number|path>" -->

# Contract: <name>

## Covers

For a single-prompt story, keep one prompt in `pdd-story-prompts`.
For a cross-module story, list prompts comma-separated in `pdd-story-prompts`.

For single-prompt stories, reference contract rule IDs directly:

- R1: <rule name>
- R2: <rule name>

For cross-module stories, namespace rule IDs by prompt:

- prompts/<module_a>_<language>.prompt#R1: <rule name>
- prompts/<module_b>_<language>.prompt#R3: <rule name>

## Context / Fixtures

Describe relevant state, assumptions, fixtures, users, records, external services, mocks, spies, logs, events, or dependencies.

## Acceptance Criteria

1. Given ...,
   when ...,
   then ...

2. Given ...,
   when ...,
   then ...

## Oracle

List only the observations that matter for this story's pass/fail result.

Examples:

- The returned error type is <error type>.
- The state transition is <state change>.
- The external call <does/does not> happen.
- The emitted event is <event name>.
- The returned value has <required shape>.

## Non-Oracle

List details that should not affect pass/fail.

Examples:

- Private helper names do not matter.
- Internal class structure does not matter.
- Exact wording of non-user-facing messages does not matter.
- Deterministic but irrelevant ordering does not matter.
- Resemblance to any specific third-party tool's UI or behavior does not matter.
- Which provider/model is currently considered "best" does not matter.

## Negative Cases

List forbidden outcomes this story protects against.

For MUST NOT rules, this section is required.
For ordinary positive stories, it may be empty.

## Candidate Prompts

Other prompts in this codebase the story could also be run against:

- `prompts/<module>_<language>.prompt` — <one-line reason> (primary)
- `prompts/<other>_<language>.prompt` — <one-line reason> (related|possible)

## Non-Goals

What this story explicitly does not cover.

## Notes

Links, edge cases, fixture notes, rationale, follow-up work, or review notes.
```

The two worked examples below predate the two-file split; read them as the
*combined* content (the `## Story` belongs in the human file, the remaining
sections in the generated contract).

Example:

```md
<!-- pdd-story-prompts: prompts/refund_payment_python.prompt -->

# User Story: Refund requests are validated before provider calls

## Story

As a support operator,
I want invalid refund requests to be rejected before provider calls,
so that customers are not over-refunded and provider state stays consistent.

## LLM-Confirmed Contract

### Covers

- R1: Positive amount
- R2: Remaining balance
- R3: No provider call before validation

### Context / Fixtures

The payment has been captured for $100.
Successful prior refunds total $80.
Pending refunds total $0.
The payment provider refund API is observed with a spy or mock.
Payment state is observed from the payment record after the request.

### Acceptance Criteria

1. Given the payment above,
   when the operator requests a $30 refund,
   then the system returns OverRefundError.

2. Given the payment above,
   when the operator requests a $30 refund,
   then the payment provider is not called.

3. Given the payment above,
   when the operator requests a $30 refund,
   then the payment state is unchanged.

### Oracle

The error type is `OverRefundError`.
The payment provider is not called.
The payment state is unchanged.

### Non-Oracle

The exact error message text is not important.
The private helper names are not important.
The order of internal validation checks is not important, as long as provider calls do not happen before validation.

### Forbidden Outcomes

- The payment provider must not be called for an over-refund request.
- The payment state must not change.
- A successful-refund audit event must not be written.

### Non-Goals

This story does not test operator authorization.
This story does not test currency conversion.
This story does not test customer notification.

### Notes

This is a negative story: it verifies forbidden behavior does not occur.
```

### Negative Stories

Positive stories describe what should happen. Negative stories describe what must never happen.

Use negative stories for security requirements, invalid inputs, authorization failures, idempotency, forbidden side effects, privacy/data leakage, and provider failure behavior.

Every MUST NOT contract rule should ultimately be backed by a negative test — see [Verification](#a-negative-test-for-every-must-not).

Example:

```md
<!-- pdd-story-prompts: prompts/refund_payment_python.prompt -->

# User Story: Provider secrets are not leaked

## Story

As a security reviewer,
I want provider secrets removed from returned errors and logs,
so that generated code does not leak credentials.

## LLM-Confirmed Contract

### Covers

- R6: Privacy

### Context / Fixtures

The payment provider client is mocked to return an error that contains an API key.
Returned errors and log output are captured by test fixtures.

### Acceptance Criteria

1. Given the payment provider returns an error containing an API key,
   when the module returns an error to the caller,
   then the returned error does not contain the API key.

2. Given the payment provider returns an error containing an API key,
   when the module writes logs,
   then the logs do not contain the API key.

### Oracle

The returned error does not contain the API key.
Captured logs do not contain the API key.

### Non-Oracle

The exact sanitized error wording is not important.
The exact log message wording is not important.

### Forbidden Outcomes

- Returned errors must not contain the API key.
- Logs must not contain the API key.
```

### Contract Coverage Matrix

For non-trivial modules, maintain a lightweight coverage map from contract rules to stories, tests, and waivers. The purpose is not bureaucracy. The purpose is to make missing evidence visible.

Today, `<coverage>` is a PDD authoring convention, not a special preprocessor directive. It is visible to the model and useful for review, generation, and validation prompts. Tooling may later parse this section, but do not assume PDD enforces coverage automatically unless your project adds a checker.

Coverage source of truth:

- Story files are the primary place to declare `## Covers`.
- The prompt's `<coverage>` section is an optional summary for non-trivial modules.
- If both exist, keep them synchronized during prompt review.

```xml
<coverage>
R1: story__refund_invalid_amount.md
R2: story__refund_over_remaining.md
R3: story__refund_over_remaining.md
R4: story__refund_idempotency.md
R5: story__refund_auditability.md
R6: story__provider_secret_not_leaked.md
</coverage>
```

During development, unchecked rules may be visible:

```xml
<coverage>
R1: story__refund_invalid_amount.md
R2: story__refund_over_remaining.md
R3: story__refund_over_remaining.md
R4: TODO add idempotency story before production use
R5: TODO add audit-event test
R6: WAIVED W1
</coverage>
```

Unchecked rules are allowed during development, but they should be visible. Production-critical modules should not merge with unchecked high-risk MUST/MUST NOT rules unless there is an explicit waiver.

Structured waivers are easier to review and expire:

```xml
<waivers>
W1:
  Rule: R6
  Status: temporary
  Reason: Provider error fixture is not available yet.
  Approved by: security-review
  Expires: 2026-06-01
  Follow-up: Add story__provider_secret_not_leaked.md and executable test.
</waivers>
```

---

## Writing Effective Requirements

Requirements are the core of your prompt. Everything else should be handled by the shared preamble, Cloud grounding when available, explicit examples for local workflows, and accumulated tests.

### Structure (aim for 5-10 items)

1. **Primary function**: What does this module do? (one sentence)
2. **Input contract**: Types, validation rules, what's accepted
3. **Output contract**: Types, error conditions, return values
4. **Key invariants**: What must always be true
5. **Performance constraints**: If any (latency, memory, complexity)
6. **Security constraints**: If any (input sanitization, auth requirements)

### Each Requirement Should Be

- **Testable**: If you can't write a test for it, it's too vague
- **Behavioral**: Describe WHAT, not HOW
- **Unique**: Don't duplicate what preamble, grounding, explicit examples, or tests provide

### Example: Before/After

**Too detailed:**
```
1. Create a UserValidator class with validate() method
2. Use snake_case for all methods          ← belongs in preamble
3. Import typing at the top                ← belongs in preamble
4. Add docstrings to all public methods    ← belongs in preamble
5. Handle null by returning ValidationError
6. Handle empty string by returning ValidationError
7. Handle whitespace-only by returning ValidationError
```

**Just right** (requirements only):
```
1. Function: validate_user(input) → ValidationResult
2. Input: Any type (untrusted user input)
3. Output: ValidationResult with is_valid bool and errors list
4. Invalid inputs: null, empty, whitespace-only, malformed
5. Performance: O(n) in input length
6. Security: No eval/exec, treat input as untrusted
```

Style conventions (2-4) belong in a shared preamble. Edge cases (5-7) can be collapsed into a single requirement.

**Requirements as Test Specifications:** Each requirement implies at least one test case. If you can't test a requirement, it's too vague.

### Bad / Better / Best Contract Examples

Example 1:

```md
Bad:
Make refunds safe.

Better:
The system MUST reject over-refunds.

Best:
R2 - Remaining balance
For every refund request, the system MUST reject the request when the requested amount is greater than the remaining refundable amount.
Remaining refundable amount means captured amount minus successful refunds minus pending refunds.
The provider MUST NOT be called for rejected requests.
```

Example 2:

```md
Bad:
Handle provider errors gracefully.

Better:
Return ProviderRefundError when the provider fails.

Best:
R7 - Provider failure behavior
When the provider rejects a refund, the system MUST return ProviderRefundError, MUST preserve the original payment state, MUST write one failed-refund audit event, and MUST NOT expose provider secrets in logs or returned errors.
```

Example 3:

```md
Bad:
Support duplicate requests.

Better:
Duplicate requests should be idempotent.

Best:
R4 - Idempotency
For every duplicate request with the same payment ID and idempotency key, the system MUST NOT create more than one provider refund and MUST NOT write more than one successful-refund audit event.
```

---

## Prompt Abstraction Level

![Goldilocks Prompt](goldilocks_prompt.jpeg)

Write prompts at the level of *architecture, contract, and intent*, not line-by-line *implementation details*.

### Heuristics: Are You at the Right Level?

| Indicator | Too Detailed (> 30%) | Too Vague (< 10%) |
|-----------|----------------------|-------------------|
| **Content** | Specifying variable names, loop structures | Missing error handling strategy |
| **Style** | Dictating indentation, imports | No input/output types |
| **Result** | Prompt harder to maintain than code | Every generation is wildly different |

### If Your Prompt Is Too Long

Ask yourself:
- **Am I specifying coding style?** → Remove it (preamble handles this)
- **Am I specifying implementation patterns?** → Remove them when Cloud grounding or explicit examples already provide the pattern
- **Am I listing every edge case?** → Remove them (tests handle this)
- **Is the module too big?** → Split into multiple prompts

### Examples

- **Too Vague:** "Create a user page." (Model guesses everything; unrepeatable)
- **Too Detailed:** "Create a class User with a private field _id. In the constructor, set _id. Write a getter..." (Prompt is harder to maintain than code)
- **Just Right:** "Implement a UserProfile component that displays user details and handles the 'update' action via the API. It must handle loading/error states and match the existing design system."

**Rule of Thumb:** Focus on **Interfaces**, **Invariants**, and **Outcomes**. Let the preamble handle coding style; let Cloud grounding or explicit examples handle implementation patterns.

---

## Positive and Negative Constraints

Use positive constraints for normal desired behavior:

- Initialize all variables before use.
- Return `ValidationResult` for invalid input.

Use `MUST NOT` for forbidden behavior, especially security, privacy, and side effects:

- MUST NOT log bearer tokens.
- MUST NOT call the payment provider before validation succeeds.
- MUST NOT mutate customer profile records.

When possible, pair a negative rule with the allowed alternative:

- MUST NOT log raw provider secrets.
- Instead, log only redacted provider error codes and correlation IDs.

Every `MUST NOT` should eventually graduate to a negative test. See the [regeneration-safe checklist](#the-regeneration-safe-checklist) in the Verification chapter.

---

---

A PDD prompt is a *source file* that the preprocessor expands before the model ever sees it. This chapter covers the directive syntax (`<include>`, `<shell>`, `<web>`, `<pdd>`), architecture metadata tags, selective includes, semantic query, automated compression, dependency management, and how to position context so the model actually uses it.

The goal is always the north-star metric: maximize `verified_behavioral_change_per_unit_cost`. Curating context is how you keep generation cost (and confusion) down without losing the information the model needs to satisfy the contract.

---

## Prompt Syntax Essentials

These patterns are used across prompts in this repo:

- Preamble and role: start with a concise, authoritative description of the task and audience (e.g., "You are an expert Python engineer…").
- Includes for context: bring only what the model needs.
  - Single include: `<include>path/to/file</include>`. **Note:** This is a PDD directive, not standard XML. The PDD tool replaces this tag with the actual file content *before* the LLM sees it. (Handles both text and images). Use `<include optional>path/to/file</include>` to treat missing files as empty string (while still logging a warning).
  - Multiple: `<include-many>path1, path2, …</include-many>`
  - Grouping: wrap includes in a semantic tag to name the dependency or file they represent, for example:
    ```xml
    <render_js>
      <include>src/render.js</include>
    </render_js>
    ```
  - When including larger files inline for clarity, wrap with XML-safe opening/closing tags named after the file, e.g. `<render_js>…</render_js>`.
  - Note: `<include>`, `<include-many>`, `<shell>`, and `<web>` inside fenced code blocks (``` or ~~~) or inline backticks are treated as literal text.
- Inputs/outputs: state them explicitly (names, types, shapes). Prompts should define Inputs/Outputs and steps clearly.
- Steps & Reasoning: For complex logical tasks, ask the model to analyze requirements privately before writing code, then return only a concise implementation plan and the final artifact. Do not require hidden chain-of-thought output.
- Constraints: specify style, performance targets, security, and error handling.
- Environment: reference required env vars (e.g., `PDD_PATH`) when reading data files.

Tip: Prefer small, named sections using XML‑style tags to make context scannable and deterministic.

### Special XML Tags: pdd, shell, web

The PDD preprocessor supports additional XML‑style tags to keep prompts clean, reproducible, and self‑contained. Processing order (per spec) is: `pdd` → `include` → `include-many` → `shell` → `web`. When `recursive=True`, `<shell>`, `<web>`, `<include ... query="...">`, and `<include-many>` are deferred until a non‑recursive pass.

- `<pdd>...</pdd>`
  - Purpose: human‑only comment. Removed entirely during preprocessing.
  - Use: inline rationale or notes that should not reach the model.
  - Example: `<pdd>Before step X, explain why the fallback exists.</pdd>`

- `<shell>…</shell>`
  - Purpose: run a shell command and inline stdout at that position.
  - Behavior: executes during non‑recursive preprocessing; on non‑zero exit, inserts a bracketed error with the exit code instead of failing the pipeline.
  - Example: `<shell>git config --get user.name</shell>`

- `<web>URL</web>`
  - Purpose: fetch the page (via Firecrawl) and inline the markdown content.
  - Behavior: executes during non‑recursive preprocessing; on failure, inserts a bracketed error note.
  - Example: `<web>https://docs.litellm.ai/docs/completion/json_mode</web>`

> **Warning: Non-Deterministic Tags**
>
> `<shell>`, `<web>`, and `<include ... query="...">` introduce **non-determinism**:
> - `<shell>` output varies by environment (different machines, different results)
> - `<web>` content changes over time (same URL, different content)
> - `<include ... query="...">` relies on LLM interpretation (may vary by model or seed)
>
> **Impact:** Same prompt file -> different generations on different machines/times.

Use these tags sparingly. When you must use them, prefer stable commands with bounded output (e.g., `head -n 20` in `<shell>`).

### Determinism for Contract-Critical Context

For durable or contract-critical dynamic context, use PDD's snapshot workflow instead of relying on live expansion every time:

```bash
pdd preprocess prompts/refund_python.prompt --snapshot
pdd generate prompts/refund_python.prompt --snapshot-context
pdd sync refund --snapshot-context
pdd replay .pdd/evidence/runs/<run_id>.json
```

Snapshots capture the fully expanded prompt plus artifacts for nondeterministic context such as `<shell>`, `<web>`, and `<include ... query="...">`. The canonical run artifact is `.pdd/evidence/runs/<run_id>.json`; replayable context files live in `.pdd/evidence/runs/<run_id>/`. Replay reconstructs the same expanded prompt/context and checks its hash. It does not guarantee bit-for-bit identical generated code, because the LLM call itself may still be nondeterministic.

Snapshot shell and web output may contain sensitive data. Snapshot writers must redact known token, key, authorization header, URL credential, and secret-assignment patterns before hashing or storage, and must not persist raw environment dumps or unredacted bearer/API tokens. Keep commands bounded and avoid secret-bearing output even with redaction enabled.

**`context_urls` in Architecture Entries:**

When an architecture.json entry includes a `context_urls` array, the `generate_prompt` template automatically converts each entry into a `<web>` tag in the generated prompt's Dependencies section. This enables the LLM to fetch relevant API documentation during code generation:

```json
"context_urls": [
  {"url": "https://fastapi.tiangolo.com/tutorial/first-steps/", "purpose": "FastAPI routing patterns"}
]
```

Becomes in the generated prompt:
```xml
<fastapi_routing_patterns>
  <web>https://fastapi.tiangolo.com/tutorial/first-steps/</web>
</fastapi_routing_patterns>
```

Because `context_urls` generate `<web>` tags, they are dynamic context. Do not rely on them for contract-critical facts unless the fetched content is snapshotted into a stable file and included with `<include>`.

The tag name is derived from a sanitized version of the `purpose` field. This mechanism bridges architecture-level research with prompt-level context.

---

## Architecture Metadata Tags

PDD prompts can include optional XML metadata tags that sync with `architecture.json`. These tags enable bidirectional sync between prompt files and the architecture visualization, keeping your project's architecture documentation automatically up-to-date.

### Tag Format

Place architecture metadata tags at the **top of your prompt file** (after any `<include>` directives but before the main content):

```xml
<pdd-reason>Brief description of module's purpose (60-120 chars)</pdd-reason>

<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "function_name", "signature": "(...)", "returns": "Type"}
    ]
  }
}
</pdd-interface>

<pdd-dependency>dependency_prompt_1.prompt</pdd-dependency>
<pdd-dependency>dependency_prompt_2.prompt</pdd-dependency>
```

### Tag Reference

**`<pdd-reason>`**
- **Purpose**: One-line description of why this module exists
- **Maps to**: `architecture.json["reason"]`
- **Format**: Single line string (recommended 60-120 characters)
- **Example**: `<pdd-reason>Provides unified LLM invocation across all PDD operations.</pdd-reason>`

**`<pdd-interface>`**
- **Purpose**: JSON describing the module's public API (functions, commands, pages)
- **Maps to**: `architecture.json["interface"]`
- **Format**: Valid JSON matching one of the supported interface types (see below)
- **Example**:
  ```xml
  <pdd-interface>
  {
    "type": "module",
    "module": {
      "functions": [
        {"name": "llm_invoke", "signature": "(prompt, strength, ...)", "returns": "Dict"}
      ]
    }
  }
  </pdd-interface>
  ```

**`<pdd-dependency>`**
- **Purpose**: References other prompt files this module depends on
- **Maps to**: `architecture.json["dependencies"]` array
- **Format**: Prompt filename (e.g., `llm_invoke_python.prompt`)
- **Multiple tags**: Use one `<pdd-dependency>` tag per dependency
- **Example**:
  ```xml
  <pdd-dependency>llm_invoke_python.prompt</pdd-dependency>
  <pdd-dependency>path_resolution_python.prompt</pdd-dependency>
  ```

### Interface Types

The `<pdd-interface>` tag supports the architecture.json interface types:

**Module Interface** (Python modules with functions):
```json
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "func_name", "signature": "(arg1, arg2)", "returns": "Type"}
    ]
  }
}
```

**CLI Interface** (Command-line interfaces):
```json
{
  "type": "cli",
  "cli": {
    "commands": [
      {"name": "cmd_name", "description": "What it does"}
    ]
  }
}
```

**Command Interface** (PDD commands):
```json
{
  "type": "command",
  "command": {
    "commands": [
      {"name": "cmd_name", "description": "What it does"}
    ]
  }
}
```

**Frontend Interface** (UI pages):
```json
{
  "type": "frontend",
  "frontend": {
    "pages": [
      {"name": "page_name", "route": "/path"}
    ]
  }
}
```

**Entrypoint Interface** (framework/runtime-discovered files with no named exports):
```json
{
  "type": "entrypoint",
  "entrypoint": {}
}
```

### Sync Workflow

1. **Add/edit tags** in your prompt files using the format above
2. **Click "Sync from Prompt"** in the PDD Connect Architecture page (or call the API endpoint)
3. **Tags automatically update** `architecture.json` with your changes
4. **Architecture visualization** reflects the updated dependencies and interfaces

Prompts are the **source of truth** - tags in prompt files override what's in `architecture.json`. This aligns with PDD's core philosophy that prompts, not code or documentation, are authoritative.

### Validation

Validation is **lenient**:
- Missing tags are OK - only fields with tags get updated
- Malformed XML/JSON is skipped without blocking sync
- Circular dependencies are detected and prevent invalid updates
- Missing dependency files generate warnings but don't block sync

### Best Practices

**Keep `<pdd-reason>` concise** (60-120 chars)
- Good: "Provides unified LLM invocation across all PDD operations."
- Too long: "This module exists because we needed a way to call different LLM providers through a unified interface that supports both streaming and non-streaming modes while also handling rate limiting and retry logic..."

**Use prompt filenames for dependencies**, not module names
- Correct: `<pdd-dependency>llm_invoke_python.prompt</pdd-dependency>`
- Wrong: `<pdd-dependency>pdd.llm_invoke</pdd-dependency>`
- Wrong: `<pdd-dependency>context/example.py</pdd-dependency>`

**Validate interface JSON before committing**
- Use a JSON validator to check syntax
- Ensure `type` field matches a supported architecture interface type, such as `module`, `cli`, `command`, `frontend`, `page`, `component`, or `entrypoint`
- Include the required nested keys for that type where applicable (`functions`, `commands`, `pages`, etc.)

**Run "Sync All" after bulk prompt updates**
- If you've edited multiple prompts, sync all at once
- Review the validation results for circular dependencies
- Fix any warnings before committing changes

### Relationship to Other Tags

**`<pdd-dependency>` vs `<include>`**:
- `<pdd-dependency>`: Declares architectural dependency (updates `architecture.json`)
- `<include>`: Injects content into prompt for LLM context (does NOT affect architecture)
- Use both when appropriate - they serve different purposes

**`<pdd-*>` tags vs `<pdd>` comments**:
- `<pdd-reason>`, `<pdd-interface>`, `<pdd-dependency>`: Metadata tags (processed by sync tool)
- `<pdd>...</pdd>`: Human-only comments (removed by preprocessor, never reach LLM)
- Unlike `<pdd>...</pdd>` comments, `<pdd-reason>`, `<pdd-interface>`, and `<pdd-dependency>` are not human-only comments. The standard prompt preprocessor does not remove them, so they may be visible during generation and are also consumed by architecture sync.

### `contract_summary` in architecture.json

When you run `pdd sync-architecture`, each module entry may include a generated
`contract_summary` object (see `pdd/schemas/architecture_contract_summary.schema.json`).
It is derived from `<contract_rules>`, linked user stories, test coverage, and the
latest `.pdd/evidence/devunits/<module-slug>.latest.json` manifest (slug from
`infer_module_identity`, with path segments normalized like `frontend-page`). Fields include
`rules`, `critical`, `stories`, `capabilities`, `coverage_status`, `evidence_status`,
`waived`, `unchecked`, and optional `rules_detail`. Legacy prompts without contract
sections are left unchanged. (For how these contract sections are authored, see [Contracts](#natural-language-contracts).)

### Example: Complete Prompt with Metadata Tags

See `docs/examples/prompt_with_metadata.prompt` for a full example showing all three metadata tags in context.

---

## Selective Includes

Use `select=` to include only specific parts of a file instead of the whole thing:

```xml
<include select="def:parse_user_id">src/utils.py</include>
<include select="class:User">src/models.py</include>
<include select="section:Environment Variables">docs/config.md</include>
<include select="lines:10-50">src/config.py</include>
<include select="pattern:/^API_.*=/">src/constants.py</include>
```

| Selector | File types | Example |
|----------|-----------|---------|
| `lines:N-M` | Any | `lines:10-20`, `lines:5-`, `lines:-3` |
| `def:name` | Python | `def:process_request` |
| `class:Name` | Python | `class:UserModel` |
| `class:Name.method` | Python | `class:UserModel.validate` |
| `section:Heading` | Markdown | `section:Installation` |
| `pattern:/regex/` | Any | `pattern:/^import/` |
| `path:key.nested` | JSON/YAML | `path:config.database.host` |
| `pytest:test_name` | Python (pytest) (Python only) | `pytest:test_auth,test_login` |
| `contract:symbol` | Python only | `contract:run_worker,_get_job_secrets` |

Selectors are composable: `select="lines:1-5,def:main,def:helper"`. If a selector fails to match, PDD falls back to the full file with a warning.

**`pytest:` selector** (Python only): Specifically designed for testing context. It uses AST slicing to extract only the requested tests and their transitive closure of dependencies (fixtures, helper functions, decorators, and imports). It automatically resolves fixtures from the same file or `conftest.py` files.

**`contract:` selector** (Python only): Preserves a seed symbol and its transitive local dependencies (helpers, constants, classes, required imports) for compressed generation. Use when generated code must keep patch targets and private helpers referenced from tests. Seeds can be listed explicitly (`contract:run_worker`) or derived in code via `ApiContractSlicer.seeds_from_test(test_source, module_qualname)` before slicing. Output is verified so missing symbols fail fast instead of silently drifting.

**Interface mode** (`mode="interface"`, Python only) extracts signatures, docstrings, and type hints with bodies replaced by `...`. Useful when you only need the contract, not the implementation:

```xml
<include select="class:BillingService" mode="interface">src/billing/service.py</include>
<include mode="interface">src/billing/service.py</include>
```

**Compressed mode** (`mode="compressed"`, Python only) produces dense implementation snippets optimized for few-shot examples (grounding). It strips docstrings and logic-external comments while preserving all executable code.

```xml
<include mode="compressed">src/core/utils.py</include>
```

Use `mode="compressed"` when you need implementation details (unlike `mode="interface"`) but want to save tokens by removing documentation. This mode reduces line counts by 20-40% for typical modules. PDD handles token budget management automatically: if a compressed include exceeds 30,000 tokens, it falls back to `mode="interface"` (preserving sibling-test `patch()` targets), then to a truncated full copy if still over budget.

**Attribute priority:** `select=` always wins over `query=` (deterministic, no LLM cost). `mode="interface"` and `mode="compressed"` are applied to the result of `select=`.

### Interfaces for Contracts, Examples for Usage

Use `mode="interface"` when the dependency's public contract matters. Use examples when the dependency's usage pattern matters. Use full source only when implementation details are genuinely required.

```xml
<provider_contract>
<include mode="interface">src/payments/provider.py</include>
</provider_contract>

<provider_usage_example>
<include>examples/refund_provider_example.py</include>
</provider_usage_example>
```

### Semantic Query (`query=`)

For large documents where structural selectors aren't enough, use `query=` for LLM-powered extraction:

```xml
<include query="Authentication flow and JWT handling">docs/large_api_reference.md</include>
```

Results are cached in `.pdd/extracts/` and auto-refreshed when the source file changes. Run `pdd extracts prune` to garbage-collect orphaned cache entries.

---

## Automated Context Compression

To manage large context windows and reduce costs, PDD supports automated context compression. This feature reduces the token count of dependencies while maintaining their behavioral contract.

### How It Works

Users can enable compression via **global** CLI flags (before the subcommand), `.pddrc` defaults, or command-local flags on `pdd sync` / `pdd fix`:

- **`--compress-examples`**: Automatically applies `mode="interface"` to all example files in the `<include>` graph. This extracts signatures and docstrings, replacing function bodies with `...`.
- **`--compress-test-context`**: Uses AST-based slicing to include only failing tests and their necessary fixtures from the test context during `pdd fix` or `pdd test`.
- **`--context-compression {off,test,examples,contracts,all}`**: Enables one or more compression modes for the invocation.

Place global flags before the subcommand, for example `pdd --context-compression test generate prompts/foo_python.prompt`. The `generate` and `preprocess` commands do **not** accept `--context-compression` after the subcommand; `sync` and `fix` may pass the same flags after their subcommand as well.

### Compressed Context as a "Mold Wall"

Compressed context acts as a "mold" that constrains the generated code. By sending only the interface of a dependency, you define the boundaries (the "mold walls") without cluttering the context with implementation details. This ensures the generated code respects the dependency's contract while staying within token budgets.

> The mold-walls metaphor is the organizing idea of PDD. Compression supplies *one* wall (the dependency's interface); contracts and accumulated tests supply the rest. See [Verification](#the-mold-walls-concept) for the full picture.

### Fallback Behavior

If compression fails (e.g., due to AST parsing errors in a dependency), the system defaults to full file inclusion to ensure correctness. This behavior can be controlled with the `--compression-fallback {full,error}` flag.

### Reporting

PDD reports active compression modes in the execution summary, lists successfully compressed include targets (path and mode), and records any fallback events (including the file path when slicing or selection fails).

---

## Dependencies

### When to Use `<include>`

Include dependencies explicitly when:
- **External libraries** not in your grounding history
- **Critical interfaces** that must be exact
- **New modules** with no similar examples in Cloud grounding

```xml
<billing_service>
  <include>context/billing_service_example.py</include>
</billing_service>
```

### When to Rely on Grounding

If you've successfully generated code that uses a dependency before and PDD Cloud grounding is available, grounding often suffices—the usage pattern is already in the cloud database. (See [Grounding & Critical Modules](#automated-grounding-pdd-cloud) for how automated grounding works and when to override it.)

**Prefer explicit `<include>` for:** External APIs, critical contracts, cross-team interfaces
**Rely on grounding for:** Internal modules with established patterns when Cloud grounding is available

### Documentation as Dependencies

In addition to code examples, prompts can include documentation files (schema docs, API references, PRD sections) as dependencies. This prevents prompts from becoming "islands" that duplicate shared information.

Use `pdd auto-deps` to automatically discover both code and documentation dependencies. The command will:
- Find relevant `.md`, `.txt`, and `.rst` files alongside code examples
- Insert `<include>` directives for discovered documents
- Remove redundant inline content that duplicates what the included documents provide

**Prefer `<include>` over inline duplication:**
- Good: `<include>docs/api_schema.md</include>` (single source of truth, auto-updates)
- Bad: Copy-pasting the schema content directly into the prompt (creates drift)

### Token Efficiency

Real source code is heavy. A 500-line module might have a 50-line usage example. By including only the example, you save ~90% of tokens. Use `pdd auto-deps` to automatically populate relevant examples and documentation references.

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

### Automatic Update Propagation via Includes

A key benefit of `<include>` directives is **automatic propagation**: when the included file changes, all prompts that reference it automatically reflect those changes on the next generation—without editing the prompts themselves.

Use this pattern when:
- **Authoritative documentation exists elsewhere** (e.g., a README that defines environment variables, API contracts, or configuration options). Include it rather than duplicating the content.
- **Shared constraints evolve** (e.g., coding standards, security policies). A single edit to the preamble file updates all prompts.
- **Interface definitions change** (e.g., a dependency's example file). Prompts consuming that example stay current.

### Shared Preamble for Consistency

Use a shared include (e.g., `<include>context/project_preamble.prompt</include>`) at the top of every prompt. You should create this file in your project's `context/` directory to define your "Constitution": consistent coding style (e.g., indentation, naming conventions), preferred linting rules, and forbidden libraries. This ensures all generated code speaks the same language without cluttering individual prompts.

---

## Hierarchy of Attention

### Positioning Critical Instructions

LLMs exhibit "middle-loss" – they pay more attention to the **beginning** (role, preamble) and the **end** (steps, deliverables) of the prompt context. If a critical constraint (e.g., security, output format) is ignored, ensure it's placed in your shared preamble, explicitly reiterated in the final "Instructions" or "Steps" section, or even pre-filled in the expected output format if applicable.

---

## Command-Specific Context Files

Some PDD commands (e.g., `pdd test`, `pdd example`) can automatically include project-specific context files like `context/test.prompt` or `context/example.prompt` during their internal preprocessing. Use these to provide instructions tailored to your project, such as preferred testing frameworks or specific import statements, without modifying the main prompt.

### `pdd test` Has Two Relevant Modes

**Unit test mode**

```bash
pdd test prompts/foo_python.prompt src/foo.py
pdd test prompts/foo_python.prompt examples/foo_example.py
```

Generates or enhances executable unit tests from the module prompt plus generated code or example code.

**Story mode**

```bash
pdd test prompts/upload_python.prompt prompts/notify_python.prompt
pdd test user_stories/story__my_flow.md
```

Generates or updates Markdown user stories and prompt links.

**`context/test.prompt`** is particularly important:
- Defines testing conventions, frameworks, and patterns for your project
- Included automatically when running executable unit test generation (alongside the module prompt and generated code or example code)
- Tests accumulate over time via `--merge` as bugs are found
- Tests persist when the module prompt changes—only code is regenerated, not tests
- This ensures tests remain stable "permanent assets" while code can be freely regenerated

For contract-aware test generation, add guidance like this to `context/test.prompt`:

```md
When generating tests from a PDD prompt:

1. Read the `<contract_rules>` section.
2. For each MUST or MUST NOT rule, generate at least one test unless the rule is explicitly marked non-testable.
3. Name tests so they reference the rule ID when practical.
   Example: `test_R2_rejects_over_refund`.
4. Include negative tests for MUST NOT rules.
5. Prefer observable behavior over private implementation details.
6. Do not assert private helper names, internal class structure, or exact error-message wording. For exception message assertions, prefer `pytest.raises(ExcType, match=r"keyword1|keyword2")` with semantic keyword patterns over exact strings — exact strings fail when regeneration rewords a message.
7. Preserve existing tests; never overwrite accumulated regression tests.
8. If a rule cannot be tested with the available fixtures, add a comment explaining the missing fixture or dependency.
```

---

---

Grounding is how PDD keeps regenerated code structurally consistent with what came before. This chapter covers automated grounding (Cloud), the `<pin>` / `<exclude>` overrides, the review-and-policy controls for high-risk modules, an auth-heavy domain pattern, and how prompt + grounding + tests divide the labor.

Grounding directly serves the north-star metric: it lowers generation cost and reduces drift, so more of your spend goes to *verified behavioral change* rather than re-litigating structure on every run. But grounding is not verification — for critical modules, pair it with the controls below and with the [minimum viable mold](#the-minimum-viable-mold).

---

<a name="automated-grounding"></a>
## Automated Grounding (PDD Cloud)

Unlike standard LLM interactions where every request is a blank slate, PDD Cloud uses **Automated Grounding** to reduce implementation drift.

### How It Works

When you run `pdd generate`, the system:
1. Embeds your prompt into a vector
2. Searches for similar prompts in the cloud database (cosine similarity)
3. Auto-injects the closest (prompt, code) pair as a few-shot example

**This is automatic.** You don't configure it. As you edit your prompt:
- The embedding changes
- Different examples may be retrieved
- Generation naturally adapts to your prompt's content

On first generation: Similar existing modules in your project may provide grounding.
On re-generation: Your prior successful generation is typically the closest match.

### Why This Matters for Prompt Writing

- **Your prompt wording affects grounding.** Similar prompts retrieve similar examples.
- **Implementation patterns can be handled automatically in Cloud workflows.** Grounding can provide structural consistency from similar modules (class vs functional, helper patterns, etc.).
- **Prompts can be minimal in Cloud workflows.** Focus on requirements; Cloud grounding handles many implementation patterns when enough relevant history exists.

*Note: This is distinct from "Examples as Interfaces" (which teach how to **use** a dependency, covered in [Directives & Context](#interfaces-for-contracts-examples-for-usage)). Grounding teaches the model how to **write** the current module.*

> **Local users (no cloud):** Without grounding, prompts must be more detailed—include structural guidance and explicit examples via `<include>`. Use a shared preamble for coding style. The minimal prompt guidance in this guide assumes cloud access.

---

## Grounding Overrides: Pin & Exclude (PDD Cloud)

For users with PDD Cloud access, you can override automatic grounding using XML tags:

**`<pin>module_name</pin>`** — Force a specific example to always be included
- Use case: Ensure a critical module always follows a "golden" pattern
- Use case: Bootstrap a new module with a specific style

**`<exclude>module_name</exclude>`** — Block a specific example(s) from being retrieved
- Use case: Escape an old pattern that's pulling generation in the wrong direction
- Use case: Intentionally break from established patterns for a redesign

These tags are processed by the preprocessor (like `<include>`) and removed before the LLM sees the prompt.

**Most prompts don't need these.** Automatic grounding works well for:
- Standard modules with similar existing examples
- Re-generations of established modules
- Modules following common project patterns

### When to Pin, Exclude, or Review for Critical Modules

For high-risk modules — typically `auth`, `payments`, and `compliance` — the
automatic top-similarity example is not enough evidence on its own. For these,
explicitly choose **at least one** of:

- **`<pin>module_name</pin>`** — pin a vetted "golden" example so regeneration
  cannot silently drift to a different prior implementation.
- **`<exclude>old_module</exclude>`** — block any superseded or known-bad
  implementation from being retrieved.
- **`pdd ... --review-examples`** — interactively approve each `<pin>` tag in the
  prompt **before** cloud/local generation runs. `generation.grounding.reviewed`
  is `true` only when every cloud `examplesUsed` entry was pre-approved via a
  matching `<pin>` (module/slug/id). Cloud-selected examples that were not
  pinned and pre-approved are still recorded in the manifest but leave
  `reviewed` false.

These decisions land in the evidence manifest (`generation.grounding`, see
`../evidence_manifest.md`), so reviewers can audit exactly which examples
shaped a critical module's generation.

To enforce this in CI, declare a policy in `.pdd/grounding_policy.yaml`:

```yaml
grounding:
  require_review_for_critical_modules: true
  require_pinned_examples_for:
    - auth
    - payments
    - compliance
```

See `../grounding_policy.md` for the full schema and behavior, including how
local / no-cloud runs are reported (`mode: unavailable`) instead of failing.

---

## Domain Pattern: Auth-Heavy Modules

This pattern applies primarily to PRD/issue-driven generation workflows. For ordinary module prompts, use the requirements below as guidance rather than assuming PDD will automatically split and prioritize auth modules.

Auth modules (OAuth, JWT, session auth, API key management) are one of the most common sources of test failures in generated code. This is because auth inherently depends on external identity providers that can't be called during testing, and because token lifecycle management spans multiple concerns.

### Why Auth Modules Fail

1. **External provider dependency**: OAuth flows require real network calls to providers (Google, GitHub, Auth0). Generated tests that attempt these calls fail without credentials.
2. **Complex lifecycle**: Token issuance, validation, refresh, and revocation are separate operations that must all work correctly. Missing any stage causes subtle production failures.
3. **Tight coupling**: Auth logic embedded in business modules makes both untestable. The auth logic can't be mocked because it's not a separate dependency.

### Writing Prompts for Auth Modules

When writing prompts for auth-related modules, include these requirements:

1. **Testability**: "Use dependency injection for the OAuth client and token verifier. Accept these as constructor/function parameters so tests can substitute mock implementations without calling real identity providers."
2. **Token lifecycle**: "Handle the full token lifecycle: issuance (or exchange), validation, refresh, revocation, and expiry detection."
3. **Error handling**: "Handle auth-specific errors: expired tokens (return 401 with refresh hint), invalid tokens (return 401), missing scopes (return 403), CSRF state mismatch (return 400), and network failures during token exchange (retry with backoff)."
4. **Security**: "Never log tokens or secrets at INFO level or above. Use CSRF state parameters for all OAuth redirect flows. Validate redirect URIs against an allowlist."
5. **Test fixtures**: "Tests should use mock OAuth fixtures and pre-generated JWT tokens (see context/test.prompt Pattern 14 for concrete examples)."

### Example Requirements Section for an OAuth Module

```text
Requirements
1. Function: exchange_code_for_token(code, redirect_uri, oauth_client) -> TokenResponse
2. Function: refresh_access_token(refresh_token, oauth_client) -> TokenResponse
3. Function: revoke_token(token, oauth_client) -> bool
4. Accept oauth_client as a parameter (dependency injection for testability)
5. Handle errors: invalid_grant, expired refresh token, network timeout (retry 3x)
6. Never log token values; log only token metadata (expiry, scopes)
7. Validate redirect_uri against configured allowlist before exchange
```

### Architecture Guidance

When using `pdd generate <issue>` with a PRD that mentions auth:
- PDD may detect auth technologies and create separate auth modules
- Auth modules may be tagged with "auth" and given low priority numbers
- Business modules depend on auth modules, not the reverse
- Completeness validation can check for full token lifecycle coverage in workflows that enable it

Auth is also a canonical example of a module that needs the strongest mold walls (dependency-injected provider, negative tests for every leak path, pinned grounding). Pair this section with the [regeneration-safe checklist](#the-regeneration-safe-checklist).

---

## The Three Pillars of PDD Generation

Understanding how prompts, Cloud grounding, examples, and tests work together is key to writing minimal, effective prompts.

| Pillar | What It Provides | Maintained By |
|--------|-----------------|---------------|
| **Prompt** | Requirements and constraints (WHAT) | Developer (explicit) |
| **Cloud Grounding / Examples** | Implementation patterns (HOW) | System grounding when available; explicit examples via `<include>` otherwise |
| **Tests** | Behavioral correctness | Accumulated over time |

### How They Interact

- **Prompt** defines WHAT → "validate user input, return errors"
- **Cloud Grounding / Examples** define HOW → class structure, helper patterns, and dependency usage patterns
- **Tests** define CORRECTNESS → edge cases discovered through bugs

### Conflict Resolution

- **Tests take precedence over grounding/examples**: If a test requires new behavior, generation should satisfy it and the test runner enforces it
- **Explicit requirements override grounding/examples**: If prompt says "use functional style", that overrides OOP examples in grounding
- **Cloud grounding / explicit examples fill gaps**: They can guide patterns not specified in the prompt or checked by tests

### Why Prompts Can Be Minimal

You don't need to specify:
- **Coding style** → preamble provides it
- **Implementation patterns** → Cloud grounding or explicit examples provide them
- **Edge cases** → tests encode them

You only specify:
- What the module does
- What contracts it must satisfy
- What constraints apply

---

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
  The CSV at $PDD_PATH/data/language_format.csv contains: language,comment,extension,run_command,run_test_command,outputs

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

This chapter covers the day-to-day loop: regenerate → verify → test → update, the features-vs-bugs cheatsheet, when (and when not) to change the prompt, how PDD differs from interactive agentic coders, and the review checklist + PR evidence summary you use to merge a prompt change.

Every step here is in service of the north-star metric, `verified_behavioral_change_per_unit_cost`: keep code and examples disposable, keep prompts and tests as appreciating assets, and only spend prompt edits on genuine intent changes.

---

## Regenerate, Verify, Test, Update

**Crucial Prerequisite:** Before regenerating an established module, ensure you have **high test coverage** for its current functionality. Because PDD overwrites the code file entirely, your test suite is the critical safety net that prevents regression of existing features while you iterate on new ones. For new modules, create the prompt, generate code and examples, then generate or write the first executable tests before relying on repeated regeneration. (This is the "minimum viable mold" — see [Verification](#the-minimum-viable-mold).)

The PDD workflow (see `../whitepaper.md`):

1) **Generate:** Fully regenerate (overwrite) the code module and its example.
2) **Crash → Verify:** Run the example. Fix immediate runtime errors.
3) **Test (Accumulate):** Run existing tests. If fixing a bug, **write a new failing test case first** and append it to the test file. *Never overwrite the test file; tests must accumulate to prevent regressions.*
4) **Fix via Command:** When you use `pdd fix`, successful Prompt+Code pairs may be recorded for grounding, depending on your local or Cloud configuration. Treat this as part of your project's privacy and retention policy.
5) **Fix via Prompt:** If the logic is fundamentally flawed, update the prompt text to clarify the requirement or constraint that was missed, then **go to step 1**.
6) **Drift Check (Optional):** Occasionally regenerate the module *without* changing the prompt (e.g., after upgrading LLM versions or before major releases). If the output differs significantly or fails tests, your prompt has "drifted" (it relied on lucky seeds or implicit context). Tighten the prompt until the output is stable.
7) **Update:** Once tests pass, back-propagate any final learnings into the prompt.

Key practice: Code and examples are ephemeral (regenerated); Tests and Prompts are permanent assets (accumulated and versioned).

**Important:** Tests ARE generated from the module prompt (plus code and `context/test.prompt`). The key distinction is their lifecycle:
- Code is regenerated on prompt changes; tests accumulate and persist
- Requirements implicitly define test coverage—each requirement implies at least one test
- Use `context/test.prompt` for project-wide test guidance (frameworks, patterns)
- Existing tests are included as context during code generation
- This creates a "ratchet effect" where each new test gives future generations more behavioral context and gives the test runner more regression coverage

### Workflow Cheatsheet: Features vs. Bugs

| Task Type | Where to Start | The Workflow |
| :--- | :--- | :--- |
| **New Feature** | **The Prompt** | 1. Add/update contract rules in the prompt.<br>2. Add or update user stories for product-level behavior.<br>3. Regenerate code (LLM sees existing tests as behavioral context).<br>4. Generate or merge executable tests.<br>5. Run story validation and tests. |
| **Bug Fix (Code)** | **The Test File** | 1. Use `pdd bug` to create a failing test case (repro) in the Test file.<br>2. Clarify the Prompt to address the edge case if needed.<br>3. Run `pdd fix`; the LLM sees the new test as behavioral context, and the test runner enforces the result.<br>**Tip:** Use `pdd fix --protect-tests` if the tests from `pdd bug` are correct and you want to prevent the LLM from modifying them. |
| **Bug Fix (Prompt Defect)** | **The Prompt** | When `pdd bug` determines the prompt specification itself is wrong (Step 5.5), it auto-fixes the prompt file. The workflow then continues to generate tests based on the corrected prompt. |

**Key insight:** When you run `pdd generate` after adding a test, the LLM sees that test as behavioral context. The generated code should satisfy it, but the test suite is still the enforcement mechanism.

**Why?** Features represent *new intent* (Prompt). Bugs represent *missed intent* which must first be captured as a constraint (Test) before refining the definition (Prompt).

### When to Update the Prompt (and When Not To)

After a successful fix, ask: "Where should this knowledge live?"

| Knowledge Type | Where It Lives | Update Prompt? |
|---------------|----------------|----------------|
| New edge case behavior | Test file | **No** |
| Implementation pattern fix | Cloud grounding or local history, when configured | **No** |
| Missing requirement | Prompt | **Yes** |
| Wrong constraint | Prompt | **Yes** |
| Security/compliance rule | Prompt or preamble | **Yes** |

**Rule of thumb:** Update the prompt only for **intent changes**:
- "The module should also handle X" → Add requirement
- "The constraint was wrong" → Fix requirement
- "This security rule applies" → Add requirement

**Don't update for implementation fixes:**
- "There was a null-handling bug, and the prompt already implies null behavior" → Add test; grounding may capture the implementation fix
- "The code style was inconsistent" → Update preamble (not prompt)
- "Private naming/style preference" → Update preamble, not module prompt
- "Public API name changed" → Update prompt/interface

If the intended behavior changed, update the prompt. For example, "The module should now accept null as a valid input" is a prompt/interface change, not just a test addition.

### Prompt Defects vs. Code Bugs

In PDD, the prompt is the source of truth. However, prompts themselves can contain defects. The `pdd bug` agentic workflow (Step 5.5: Prompt Classification) distinguishes between two types of bugs:

| Defect Type | Definition | Detection | Action |
|-------------|------------|-----------|--------|
| **Code Bug** | Code doesn't match the prompt specification | Tests fail because implementation diverges from requirements | Fix the code via `pdd fix` |
| **Prompt Defect** | Prompt doesn't match the intended behavior | User-reported expected behavior contradicts the prompt | Fix the prompt, then regenerate |

**How Prompt Classification Works:**

After root cause analysis (Step 5), the workflow examines whether:
1. The code correctly implements the prompt, but the prompt is wrong (→ Prompt Defect)
2. The code incorrectly implements the prompt (→ Code Bug)

**Output markers** for automation:
- `DEFECT_TYPE: code` - Proceed with normal test generation
- `DEFECT_TYPE: prompt` - Auto-fix the prompt file first
- `PROMPT_FIXED: path/to/file.prompt` - Indicates which prompt was modified
- `PROMPT_REVIEW: reason` - Request human review for ambiguous cases

**Default behavior:** When classification is uncertain, the workflow defaults to "code bug" to preserve backward compatibility.

This classification prevents the "test oracle problem" - where tests generated from a flawed prompt would encode incorrect behavior, causing `pdd fix` to "fix" correct code to match the buggy specification.

---

## Prompt Review Checklist

Before merging a prompt change, check the contract, story, test, context, and evidence surfaces together.

### Contract Quality

- [ ] Does every important behavior have a contract rule?
- [ ] Are MUST/MUST NOT rules observable?
- [ ] Are ambiguous domain terms defined?
- [ ] Are non-responsibilities explicit?
- [ ] Are capabilities and forbidden side effects explicit?

### Story Coverage

- [ ] Does every high-risk rule have a story, test, or waiver?
- [ ] Do stories list `Covers: R...`?
- [ ] Are negative stories included for forbidden behavior?
- [ ] Is `pdd-story-prompts` metadata present or intentionally omitted?

### Test Quality

- [ ] Are tests behavioral rather than implementation-specific?
- [ ] Do new tests accumulate instead of replacing old tests?
- [ ] Are regressions captured as tests before fixes?

### Context Quality

- [ ] Are critical dependencies included explicitly?
- [ ] Are large files included with targeted excerpts or interface mode?
- [ ] Are dynamic `<shell>`, `<web>`, or semantic-query includes avoided for contract-critical context?

### Evidence

- [ ] Did `pdd detect --stories` pass?
- [ ] Did generated tests pass?
- [ ] Did `pdd verify` pass where appropriate?
- [ ] Are any skipped checks or waivers documented?

## PR Evidence Summary

For non-trivial prompt changes, include a short evidence summary in the PR.

```md
Prompt changes:
- Added R4 idempotency rule to `prompts/refund_payment_python.prompt`.
- Clarified "remaining refundable amount" vocabulary.

Stories:
- `story__refund_idempotency.md` added.
- `story__refund_over_remaining.md` still passes.
- `pdd detect --stories` passed.

Generated artifacts:
- `src/refund_payment.py`
- `examples/refund_payment_example.py`
- `tests/test_refund_payment.py`

Verification:
- `pdd verify` passed.
- Unit tests passed.
- New tests cover R4.

Unchecked or waived:
- R6 provider-secret leakage has no provider fixture yet.
- Waiver expires after provider mock fixture is added.
```

---

## PDD vs Interactive Agentic Coders (Claude Code, Cursor)

> PDD and agentic coders are **complements**, not competitors. The friendly on-ramp for using both together is the [Hybrid Agent Workflow](#using-pdd-with-your-coding-agent) chapter; this section is the conceptual contrast.

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

When to use which: Use PDD for substantive new modules, refactors, and anything requiring long‑term maintainability and repeatability. Use interactive patching for trivial hotfixes; follow up by updating the PDD prompt so the source of truth remains synchronized. For a fuller, honest accounting of where PDD fits and where it doesn't, see the [task-fit boundary](#honest-task-fit-boundary) on the landing page.

### Patch vs PDD: Concrete Examples

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
```

Key differences:
- Patch prompt constrains a local edit and often asks for a diff. It assumes code is the source of truth.
- PDD prompt defines the module's contract, dependencies, and deliverables. It is the source of truth; code is regenerated to match it, while tests accumulate over time.

---

## Scoping & Modularity

- One prompt → one file/module. If a prompt gets too large or brittle, split it into smaller prompts that compose via explicit interfaces.
- Treat examples as interfaces: create a minimal runnable example demonstrating how the module is meant to be used.
- Avoid "mega‑prompts" that try to implement an entire subsystem. Use the PDD graph of prompts instead. For how prompts compose via examples, see [Dependencies](#dependencies) in the Directives & Context chapter.

---

## Why PDD Scales to Large Codebases

- Explicit, curated context: use minimal examples and targeted includes instead of dumping source, reducing tokens and confusion.
- Modular dev units: one prompt per file/module constrains scope, enabling independent regeneration and parallel work.
- Batch, reproducible flow: eliminate long chat histories; regeneration avoids patch accumulation and incoherent diffs.
- Accumulating tests: protect behavior across wide regenerations and refactors; failures localize issues quickly.
- Single source of truth: prompts unify intent and dependencies, improving cross‑team coordination and reducing drift.
- Automated Grounding: By feeding successful past generations back into the context, the system can stabilize code over time and make regeneration more reliable for complex modules.

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

## Checklist: Before You Run `pdd generate`

### Must Have
- [ ] Module purpose is clear (1-2 sentences)
- [ ] Requirements are testable and behavioral (5-10 items)
- [ ] Dependencies included (if external or critical)
- [ ] High-risk MUST/MUST NOT rules have stable IDs
- [ ] Ambiguous terms are defined in Vocabulary

### For Established Modules
- [ ] Tests exist for known edge cases
- [ ] Previous generation was successful (Cloud grounding can use it)
- [ ] Coverage map lists stories, tests, TODOs, or waivers for high-risk rules

### For New Modules
- [ ] Similar modules exist in codebase or examples are included explicitly
- [ ] Or: Consider `<pin>` to reference a template module (Cloud)
- [ ] Non-responsibilities and forbidden side effects are explicit

### You Don't Need to Specify
- Coding style (preamble handles this)
- Implementation patterns (Cloud grounding or explicit examples handle this)
- Every edge case (tests handle this)

---

## Common Pitfalls (And Fixes)

- Too much context: prune includes; prefer targeted examples over entire files.
- Vague requirements: convert to explicit contracts, budgets, and behaviors.
- Mega‑prompts: split into smaller prompts (one per file/module) and compose.
- Prompt outweighs the code: if the prompt is larger than the generated file, it's usually over‑specifying control flow. Aim for prompts to be a fraction of the target code size; keep them at the interface/behavior level and let the model fill in routine implementation.
- Patching code directly: make the change in the prompt and regenerate; then back-propagate any learnings into the prompt.
- Throwing away tests: keep and expand; they are your long‑term leverage.

---

## Naming & Conventions (This Repo)

- One prompt per module/file, named like `${BASENAME}_${LanguageOrFramework}.prompt` (see templates under `pdd/pdd/templates`).
- Follow codebase conventions from README.md for Python and TypeScript style.
- Use curated examples under `context/` to encode interfaces and behaviors.

---

## Final Notes

Think of prompts as your programming language. Keep them concise, explicit, and modular. Regenerate instead of patching, verify behavior with accumulating tests, and continuously back‑propagate implementation learnings into your prompts.

The durable PDD chain is:

```text
Prompt = source of truth
Contract rules = durable obligations
User stories = prompt-level acceptance tests
Generated tests = executable evidence
Accumulated tests = mold walls
Generated code = disposable artifact
```

That discipline is what converts maintenance from an endless patchwork into a compounding system of leverage.

---

---

## Brownfield Adoption

The realistic starting point for most teams is **not** a green field. It's an existing 50K–500K-line codebase that already works, already has customers, and already has parts nobody fully understands. You do not rewrite it as prompts in a weekend, and you should not try. PDD adoption in a brownfield codebase is **incremental**: you convert one well-chosen module at a time, building the verification mold *around current behavior* before you ever change anything.

This chapter is the recipe. It is conservative on purpose: the north-star metric is `verified_behavioral_change_per_unit_cost`, and in a brownfield codebase the biggest cost is *accidentally changing behavior you didn't mean to.* The recipe front-loads verification so regeneration can't silently break what already works.

---

## Pick Good First Modules (The Honest Task-Fit Boundary)

Not every module is a good first PDD candidate. Choosing badly is the most common reason brownfield adoption stalls. Use this boundary:

**Strong-fit — convert these first:**

- Validation and business rules
- Adapters / API wrappers
- Data transforms
- Internal tools and scripts
- CRUD endpoints and services
- Customer-specific variants of a common pattern
- Test generation
- Policy enforcement

These share three properties: their behavior is **observable**, they are **testable in isolation**, and their interface is **knowable**. That is exactly what a regeneration-safe mold needs (see [Verification → minimum viable mold](#the-minimum-viable-mold)).

**Weak-fit — leave these alone for now:**

- Tiny hotfixes (just patch them; the overhead isn't worth it)
- Performance micro-optimizations (hard to specify as intent; easy to regress)
- Legacy code with hidden coupling (behavior depends on undocumented global state)
- Hard-to-test behavior (UI timing, real network/clock dependence without seams)
- Novel algorithms (the contract isn't yet knowable)
- Large architectural ambiguity (you don't yet know what "correct" means)
- Safety-critical code **without** an existing strong test suite

Weak-fit modules aren't permanently off-limits — but convert them only after you've added seams and characterization tests, and ideally after you've practiced on strong-fit modules first.

**A useful first pick:** a *high-churn* strong-fit module. High churn means it changes often, so the payoff from a regenerable, verified version is highest, and the team already has context on it.

---

## The Recipe

### 1. Pick a high-churn module

Look at your VCS history for the strong-fit files that change most often. High churn = high regeneration payoff and fresh team knowledge. Scope to a single file/module — one prompt, one module (see [Scoping & Modularity](#scoping--modularity)).

### 2. Write characterization tests around current behavior — first

Before touching the prompt, **pin down what the code does today.** Characterization tests (a.k.a. "golden master" tests) capture *current* observable behavior — not necessarily *correct* behavior. Their job is to make any behavioral change visible.

- Cover the happy paths the module is actually used for.
- Cover the edge cases you can find: empty inputs, nulls, boundary values, error paths.
- Add **negative** assertions for any side effect the module must not have (no extra writes, no leaked secrets, no premature external calls) — these become your forbidden-wall tests.
- Assert **observable behavior** (return values, state changes, calls made), not private helper names or exact message strings.

Your coding agent is excellent at this: point Claude Code / Cursor / Codex / Copilot at the file and ask it to write characterization tests that capture current behavior, including edge and error cases. This is the safety net for everything that follows. (Why first? Because without it, regeneration is the [plausible-wrong-code-faster](#why-verification-is-the-spine) failure mode.)

```bash
# Establish the baseline: these must pass against the existing code, untouched.
pytest tests/test_legacy_module.py
```

### 3. Reverse-derive a prompt from the existing code

Now write a module prompt that *describes* what the code does, at the level of intent — role, requirements, contract rules, interface — not line-by-line implementation.

- Where PDD tooling exists, use it as a starting draft, then review and tighten by hand. (For example, `pdd auto-deps` can discover the module's code and documentation dependencies and insert `<include>` directives; see [Dependencies](#dependencies).)
- Otherwise, derive the prompt manually — or have your coding agent draft it: "read this module and write a PDD prompt with numbered contract rules and a declared interface that would regenerate equivalent behavior." This is the hybrid loop applied to existing code (see [Hybrid Agent Workflow](#using-pdd-with-your-coding-agent)).
- Freeze the interface in `<pdd-interface>` / an Inputs–Outputs section so regeneration cannot change the public surface callers depend on.
- Turn the must-not behaviors from step 2 into explicit `MUST NOT` contract rules. (Authoring details: [Contracts](#natural-language-contracts).)

The goal of this step is a prompt that is faithful to current intent — not aspirational. Save improvements for *after* the module is stable under regeneration.

### 4. Drift-check: regenerate and diff behaviorally

This is the crux. Regenerate the module from your new prompt and check it against the existing implementation **behaviorally** — the characterization tests must still pass.

```bash
pdd generate prompts/legacy_module_python.prompt
pdd test prompts/legacy_module_python.prompt src/legacy_module.py   # accumulate tests
pytest tests/test_legacy_module.py                                   # the gate
```

Interpreting the result:

- **All characterization tests pass** → your prompt captures the module's behavior. The diff in *source* may look large (different structure, different helpers) — that's fine. What matters is that *behavior* is unchanged. Proceed.
- **Some tests fail** → either (a) the prompt is missing a requirement/rule the old code embodied (tighten the prompt), or (b) you've discovered an undocumented behavior worth deciding about explicitly. Capture the decision as a contract rule or a test; don't paper over it.
- **Tests pass but you're nervous about high-risk paths** → hold back a portion of tests as a [hidden gate](#hidden-vs-public-tests) and/or add property and mutation testing to confirm the walls are real, not overfit.

Repeat regenerate → diff until regeneration is **stable**: the same prompt produces behavior that passes every characterization test, run after run (this is the same drift check as in the [day-to-day loop](#regenerate-verify-test-update)).

### 5. Promote to a PDD module

Once regeneration is stable, the module is a real PDD module. From here on:

- The **prompt is the source of truth.** Change behavior by editing the prompt and regenerating — stop hand-patching the code.
- Tests **accumulate** (`--merge` / append). Every future bug fix starts with a failing test (see [Workflow & Review → features vs. bugs](#workflow-cheatsheet-features-vs-bugs)).
- For high-risk modules (`auth`, `payments`, `compliance`), add the grounding and review controls from [Grounding & Critical Modules](#automated-grounding-pdd-cloud) so regeneration can't drift to a different prior implementation.
- Now — and only now — make the improvements you deferred in step 3, one behavioral change at a time, each gated by the test suite.

Then pick the next high-churn strong-fit module and repeat. Adoption compounds: each converted module makes the next one easier, and Cloud grounding gets stronger as your prompt/code history grows.

---

## What Success Looks Like

You are not "done" when the whole codebase is prompts. You are succeeding when:

- Your **highest-churn, highest-risk** modules are regeneration-safe (interface + behavioral tests + negative tests).
- Behavior changes to those modules go *through the prompt*, with the test suite as the gate.
- Code capital is depreciating gracefully — the generated code is disposable — while **prompt capital appreciates**: each model upgrade can regenerate better code from the same prompts, for free.
- The parts that are genuinely weak-fit are honestly left as conventional code, patched directly, until they earn a mold.

That last point is the discipline that keeps adoption credible: **convert what's worth verifying repeatedly; leave the rest.**

---

---

## Final Notes

Think of prompts as your programming language. Keep them concise, explicit, and modular. Regenerate instead of patching, verify behavior with accumulating tests, and continuously back‑propagate implementation learnings into your prompts. Optimize for `verified_behavioral_change_per_unit_cost` — not the smallest prompt, and not the most code.
