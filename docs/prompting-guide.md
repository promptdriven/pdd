# Prompting guide

Write one canonical `.prompt.md` per module, including independently generated
frontend children. Explain **what it must do and why**, with traceable decisions
and edges.

**Preservation sets the boundary; abstraction chooses the expression.** Keep
required observations and reasons. Use domain rules, leaving algorithms, helpers
and representations free within the [preservation promise](#preservation).

## First pass: build one contract with three owners

Select the preservation promise from permitted evidence. Organize decisions and
exact boundaries under these owners; combine them for small contracts:

| Owner | Required meaning | Placement |
|---|---|---|
| Domain decisions | Purpose, responsibility, inputs, outcomes, guards and precedence; why consequential rules exist | Visible first; enough to trace ordinary flow and a consequential edge |
| Public contract | Exact signatures, defaults, bindings, metadata and output schema | Beside a small rule, otherwise one named interface reference |
| Consequential operations | Evaluation boundaries and effects that qualify a decision, including failure | Beside the affected rule, otherwise one linked compatibility reference |

The public contract names **every output key, field or tuple position**, its
meaning, units and representation. Include conditional presence, ordering and
identity where observable. A quantity's description cannot substitute for its
external name. Group repeated shapes once and refer to them from outcomes.
Recover declarations from interfaces or callers only if they are declared
consumer context; never require inference from excluded source.

Retain each public owner and binding kind: module function, instance method,
staticmethod or classmethod. Preserve public annotations and declaration metadata,
including evaluation timing and stored representation. Equivalent resolved types
can expose different raw annotations. Include observable docstrings within the
selected promise. Retain identifier values exposed through public operations,
even when stored privately; unrelated private organization remains free.

Give consequential operations one compact expression or ordered table. For each
boundary, state its guard, evaluation and surviving effects if it fails; include
skipped work and winning errors. Trace truth conversion, attribute access, hashing,
equality, formatting and path operations across public calls. Preserve order,
count, lock state, reentry, captures and repeated reads where observable. Operand
selection and later consumption may require separate truth tests. Assignment
order may change surviving state even when successful results match.

This reference qualifies domain decisions; it must not retell their normal route.
Link each affected rule to its exact boundary and name the local consequence.
Distinguish optional absence from malformed required values, early exit from
completion or budget exhaustion, and comparison values from retained or returned
values. Keep full error class, message and structured data. An annotation or
unsupported-input disclaimer cannot exclude source-visible consequences.

Use compact grouped mappings for aliases: canonical spellings once, additional
spellings by target, complete accepted set and unknown-value behavior. Do not
make readers guess spelling or decode invented codes. Name disclosures by the
question they answer; keep domain decisions visible when references are closed.

Keep module policy in the root. Shared-policy links state authority and local
consequence; dependencies declare loading without repeating rules. Inaccessible
references cannot supply meaning, and new sidecars are not compression.

## Choose a representation for a consequential question

Use Mermaid when it clarifies branches or returns; prefer prose or a table for a
single rule, conjunction, lookup or short sequence. The diagram and adjacent
rules jointly own the answer, replacing repeated structure at equal completeness.
Label decisions and endings, including exceptions, shared interrupts and precedence.
Define predicates once, scope negation and resolve overlaps. Keep guards, equations,
identity and effects near their routes.

Use domain states and responsibilities, not invented lifecycles for independent
gates or stateless components. Prefer short top-to-bottom diagrams with plain
labels and few branch lanes. Simplify before shrinking labels or introducing codes.
Mermaid explains relationships; SVG supplies appearance.

### Synthetic example: a small contract with one compatibility boundary

A fictional exhibition owns caption approval and permits one correction. The
supplied caption has an identity and Boolean `accurate` and `fits` attributes.
**Ready** means `accurate AND fits`. Initially `revision_used` is false. New-work
requirements authorize this input domain; they are not a source-preservation
exclusion. Review returns a fresh mapping with exactly `outcome` (one of
`approved`, `declined`, `pending`) and `caption_id` (the current supplied identity,
without conversion).

```mermaid
flowchart TD
    R{Ready?} -->|Yes| A([approved])
    R -->|No| U{Revision used?}
    U -->|Yes| D([declined])
    U -->|No| P([pending])
```

Accept a replacement only while pending; otherwise raise
`ValueError("correction unavailable")` without state change.
An accepted replacement consumes the correction and becomes current before review.
Without replacement, review leaves state unchanged. Accuracy assessment is outside
this task. The figure owns review routes; the mapping above owns all outputs.

**Replacement compatibility.** The accepted contract permits assignment hooks;
keep these two observable commits in order. Errors propagate unchanged, with no
rollback. A failure returns no mapping and skips review.

| Commit | If this assignment raises before storing |
|---|---|
| Set `revision_used` true | Current caption and flag remain unchanged; skip replacement |
| Set current caption to the supplied replacement | Flag remains true; old caption remains current |

The table owns failure effects; private helpers and storage remain free.

## Make dependencies navigable and usable

Link to the canonical dependency prompt or public contract with an ordinary
relative Markdown link. Use a stable fragment when only a section is relevant,
for example `[status rules](../../contracts/review-record.md#status-values)`.
Resolve paths from the file containing the link. **Clickable does not mean
loaded:** a navigation link alone supplies no context to a generator or runtime.

Use one explicit `## Dependencies` section as the loading declaration. For each
required input, identify its canonical file or selection, role, purpose and required uses
(authoring, generation, runtime, verification or testing, as applicable). The
canonical prompt owns what a fragment or selection includes and why it is needed;
a transport adapter must preserve that meaning.
Identify any other accepted mechanism that supplies required context. Other
links are navigation-only unless explicitly designated as required; avoid a
second manual loading list.

Required shared rules must be available with all transitively required context
for the declared use. Loading only direct links does not establish completeness.
A missing file or fragment, or a cycle in required context, leaves the affected
use incomplete: identify the unresolved chain rather than inventing a
replacement or claiming completeness. Navigation-only cycles are allowed. A
changed shared contract can affect consumers whose prompt text is unchanged.

Declare necessary runtime dependencies and deterministic arithmetic facilities.
Runtime adapters derive transport formats and interfaces from the canonical
contract without inventing policy. Keep installed commands, workarounds and
current tool limitations in runbooks, not module prompts. A limitation leaves
the affected use unsupported or incomplete; it does not narrow the contract.

## Include readable SVG previews for frontend modules

Every frontend module must have an embedded SVG mockup, including badges,
buttons and labels. A small component may reuse a canonical shared view that
clearly identifies it. Keep previews minimal and show representative states
needed to explain the owned appearance, without an exhaustive state gallery.
Shared views and imports do not merge module ownership. Mark surrounding regions
`context-only`.

SVG owns appearance; prose owns behavior, responsive conditions and accessibility,
including click and keyboard outcomes, focus, names and announcements. SVG shape
order is not DOM or focus order. Give each fact one owner across these views and
the behavioral rules.

Use `views/<state>[--<variant>]__<layout-mode>.ui.svg` for materially distinct
arrangements. Name the arrangement, such as `split-pane` or `stacked`, rather than
a device or pixel size. Beside each view identify its ID, state, layout condition,
fidelity and relevant reference viewport.

Declare fidelity once:

- **Relational:** visual direction and named relationships, without pixel
  equivalence.
- **Measured:** declared geometry, alignment, spacing, fold, control placement,
  type hierarchy and resolved design tokens at a named viewport.
- **Exact:** a fixed external image contract within its stated bounds.

When preserving an existing UI's appearance, default to measured fidelity unless
authorized requirements permit redesign or select another level. State missing
reference evidence; do not present an invented layout as a measured
reconstruction. For measured or exact work, name the accepted comparator, scope
and applicable tolerances. Do not infer tolerances from the SVG or turn a
reference viewport into a fixed runtime screen size.

State whether the content is **illustrative** or a **comparison reference for
named states**. An illustration identifies its sample content and the authority
for actual values. A comparison reference shows the named state and all
module-owned appearance facts within its declared scope. Keep fidelity, state
and ownership consistent between prose and image. These declarations belong to
the canonical contract; runtime metadata must derive from them without changing
a view's purpose or fidelity. Shared status/text rules stay
with their owner; sample labels and context-only surroundings do not silently
become additional requirements.

Embed each primary SVG using Markdown image syntax
(`![Descriptive alt text](relative/path.svg)`) beside the requirement it
illustrates so GitHub displays the preview. Additional views may be disclosed,
with blank lines around the Markdown image. Use the same asset in the image and
dependency declaration; do not copy its contents into a second authority.

Each SVG needs a `viewBox`, `title`, `desc` and stable intent-based region IDs.
Preserve meaningful bounds, hierarchy, alignment, spacing, controls and resolved
tokens. Simplify ornament without losing those facts. Exclude event handlers,
framework structure/classes, external resources, base64 media and hidden alternate
designs. Keep meaningful labels readable at displayed size. A focused detail view
may clarify a necessary label or region while retaining its ownership and
relationship to the overview; it must not duplicate behavioral policy.

## Second pass: remove duplicate explanations, then inspect both reading paths

Review the whole contract, disclosures and assets at equal completeness. Remove
normal-path narration from operation references, behavior from signature lists
and declaration paraphrases from prose. Consolidate shared errors and returns.
Keep one readable ordered expression where native semantics matter, with guards
and effects explicit; remove its parallel prose translation.

Readers should find decisions immediately and exact details in named references. Count both closed-disclosure
text and total required context, including captions, companions and SVG. Moving
unchanged repetition into disclosures does not improve total economy; a shorter
total does not excuse an overloaded first read. Remove duplication before moving
necessary detail. Keep meaningful exceptions visible and references navigable.

Aim for no net growth; necessary meaning or legibility may earn space. Do not use
word caps, diagram quotas, opaque shorthand or hidden sidecars. Preserve exact
defaults, boundaries, payloads and failure precedence. Dependencies name required
context and facilities, without absent-package lists or repeated independence
claims. Keep editing records outside the business prompt.

Using only declared context, explain purpose, locate a consequential decision and
trace an edge. Check preservation after editing. Resolve links and images from
the prompt's location; check SVG XML and rendering. Inspect Markdown, Mermaid and
SVG closed and expanded at declared narrow and desktop widths. Read labels and
trace returns at displayed scale; containment is not legibility. Fix defects or
mark unavailable inspection unverified.

## Required independent reviews in the surrounding task

For every execution route, before generation or interpretation, a separate reader
reconciles the prompt against permitted source and accepted contracts, without
generated code, tests or outcomes. Check
each of the three owners against that evidence: complete declarations and output
schema, decisions and exits, then consequential evaluation and failure effects.
Try a semantics-changing fusion, cache or reorder: if the text permits it, repair
the exact boundary. Cite evidence and the affected passage for each finding.

Reconcile findings and independently repeat the economy pass on the final prompt.
Check revised passages and affected boundaries against evidence. Preserve the
initial draft and accepted audit outside the business prompt. Missing evidence
or review leaves readiness incomplete. Source conflicts need authorized
requirements; observations cannot authorize policy changes. Without independent
policy, source preservation remains provisional behavioral refinement.

For routes that generate code, before any candidate execution, require a separate
static prompt-to-code review.
The reviewer receives only the frozen final prompt and first implementation,
not source, tests, source audits or earlier outcomes. Compare the whole public
contract and consequential operations; cite prompt and code for changes or gaps.
Do not invent absent requirements. Preserve first code unchanged and submit one
reviewed implementation and audit, including an unchanged copy when appropriate.
Freeze both code sets and audits before functional testing of either set; in a
matrix, this barrier covers every artifact. No feedback-driven repair or selection.

For interpreted-runtime routes with no generated implementation, mark the
prompt-to-code review inapplicable and identify the actual execution artifacts
and checks in the surrounding workflow. Do not invent code or claim code-review
evidence. Runtime safety and schema admission check execution eligibility; they
do not establish semantic preservation or replace independent authoring review.

The surrounding workflow owns roles, freezes, tests, cost and records. Expose both
first and reviewed results, including regressions. Review is an additional
intervention, not first-generation success or proof that guide wording caused
improvement. Reviewed success cannot automatically satisfy first-generation
reconstruction or repeatability criteria; assess compatibility with the unchanged
rubric and leave unresolved claims explicit.

Keep rationales, inspections, proofs and execution machinery outside the business
prompt; they cannot supply missing requirements. Task permissions govern context;
author access does not permit generator access to excluded targets. Clarity proves
neither correct execution nor human understanding.

<a id="preservation"></a>
<details>
<summary><strong>Required reference — preservation and numerical meaning</strong></summary>

### Select the promise before compressing it

Establish policy from authorized requirements and accepted consumer or shared
contracts. Distinguish obligations, source observations, authorized changes and
unresolved conflicts. Source mechanisms are not automatically policy; generated
code is not its own independent specification.

**Behavioral refinement** preserves named behavior and essential interfaces;
state permitted variation and exclusions. **Drop-in replacement** additionally
preserves promised invocation, representation, identity and effects. With source
alone and no selected mode, use provisional behavioral refinement: conservatively
retain module-owned public declarations and metadata, explicit exports and
consequential observed behavior. Declaration preservation includes annotation
evaluation and storage, not only resolved type meaning. Values exposed through
public operations remain observable even when held by private bindings; preserve
their identifier values without prescribing unrelated private organization. Identify uncertain reexports and unavailable consumer
contracts; do not claim unseen compatibility. Interface changes need
authorization; new work may expressly permit interface design. Unknown evidence
does not authorize narrower inputs or changed semantics.

State conditions and required results, errors, state changes and external effects,
including consequential forbidden behavior, so readers can determine compliance.
Preserve relevant domains, units, defaults, absence, equality boundaries, ties,
duplicates, order, identity, mutability, serialization, errors, effects, concurrency
and termination. Missing, null, empty, zero and false may differ. Name shared rules
and explain nonobvious reasons beside them.

Names and annotations do not establish business meaning or runtime validation.
Under provisional source preservation, retain visible public failures for unsupported
values as well as successes. Distinguish error categories, including failures before
explicit rejection, and consequential effects without requiring their private
container or operation. “Errors propagate” is incomplete when replacement operations
can fail differently.

Excluding such behavior requires an authorized boundary, not an author's generic
“out of domain” or “unspecified” disclaimer. Separate a genuinely missing fact
from a visible consequence; mark only the affected unknown promise incomplete.
Imported utilities are not automatically owned exports. Author access does not
imply generator or runtime access.

For financial or evidence-related modules, retain consequential publication time,
source identity, metric definition, fiscal period and vintage. Do not invent
funding, counterparties, dates, quantities or probabilities. Label synthetic
examples as synthetic.

### Separate domain arithmetic from compatibility

Define each financial quantity once: units, valid states, equations, inputs and
outputs, rounding and consequential decisions. Preserve accepted nonfinite and
intermediate-overflow behavior; finite inputs do not guarantee finite results.
Unresolved behavior is a stated gap, not permission to invent rejection or admit
invalid financial states.

Exact machine compatibility, when promised, additionally requires relevant
formats, comparisons, grouping, accumulation order and output representation.
Keep this mechanical reference distinct from financial rationale. A source loop
alone does not establish domain policy; an equation does not authorize changing
observed numbers through finite-precision algebraic rewrites. If the numerical
preservation boundary is unresolved, provisionally retain consequential observed
semantics and mark the compatibility claim incomplete. Do not silently substitute
exact-real arithmetic, change rounding or restrict inputs for agreement.

An authorized approximation needs a metric, bound, units and scope. Distinguish
decision tolerance, allowed output error and evaluation tolerance. An output
allowance cannot loosen eligibility, rejection or status: establish boundary
stability across the error envelope or state the permitted decisions. Scoring
and proof models do not redefine the contract.

</details>
