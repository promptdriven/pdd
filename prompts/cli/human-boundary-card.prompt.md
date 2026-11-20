# Human boundary card

Own `src/human-boundary-card.mjs`. It reads local repository files and saved `pdd test`, `pdd lint --local`, `pdd owner`, and workflow native-evidence records to build a compact, advisory 1-screen Human Boundary Card (`<= 25` lines) for `pdd approve` and PR 1 (`layout: "spec"`). It never calls GitHub, Herdr, the PDD interpreter or a model, never writes a file, and never blocks approval, PR publication, exploratory standalone simulations or `kind: "native-only"` prompts.

## Domain decisions

1. **Advisory, read-only, non-blocking:** all card construction and formatting are read-only, never mutate caller inputs, never block approval or PR publication, and preserve `kind: "native-only"` prompt routes.
2. **Actual scope and source per review-summary observation:** when owner resolution (`pdd owner`), local lint (`pdd lint --local`), hosted Story checks (`pdd test`), and native target-host checks appear together in a review summary, report each with its own scope, source, label, and credit boundary—never conflating one kind of evidence into credit for another:
   - **`pdd owner` resolution** identifies an owning prompt path (`resolved` vs. `unmapped`) with its lookup source (`binding`, `header`, `prose`, `path`, or `none`) and certainty. It establishes ownership mapping only and gives no credit for checking prompt rules, modeled assertions, or native behavior.
   - **`pdd lint --local` (SVG layout only)** always retains the `"partial"` label even when `exitCode === 0` with zero warnings and zero problems (or if a caller passes a mislabeled raw state with `localOnly: true`). It states `"SVG layout only; prompt rules not checked"` (plus `"incomplete local save"` when `incompleteSave` is `true`) and gives **no credit** for checking prompt rules (`creditsPromptRules: false`, `localLintCreditsPromptRules: false`).
   - **Hosted Story run (`pdd test`)** reports the modeled policy assertions it passed together with its hosted Story source and loaded prompt paths. It credits modeled assertions and checked prompt rules only when `state === "passed"`, `missingOwnerConnection === false`, `loadedPrompts` is non-empty, and `passedAssertions` is non-empty. It never credits an unconnected owning prompt and never credits native target-host behavior (`creditsNativeBehavior: false`).
   - **Native behavior (such as target-host smoke tests)** receives native credit (`label: "verified"`, `creditsNativeBehavior: true`) **only** when backed by a non-null passing native receipt (`receipt.status === "passed"`) that has a nonblank `receiptId`, a nonblank `source`, and a `verifiedBehaviors` list containing that exact trimmed behavior string. Unreceipted claims, bare `## Native validation` headings, missing/blank receipt metadata, non-passing receipts (`failed`, `skipped`, `unverified`), or receipts covering different behaviors receive **no native credit** (`creditsNativeBehavior: false`).

## Purpose

A person approving a prompt or reviewing PR 1 must see, on one screen above raw schema and prose details:

1. **Owned policy and invariants:** the slice's Story policy rules (its `## Rules to check` forbidden outcomes and numbered criteria) or, when no Story applies, the prompt's boundary role.
2. **Source and observation provenance per consequential rule or criterion check:**
   - Which owning prompt or code boundary was actually exercised by the scenario vs. whether an owning source or rule has a **`missing owner connection`**.
   - What kind of observation backed the check: `supplied fact`, `model-returned value`, `observed simulated port call` (including explicit `0 observed port calls` where a port is instrumented and observed at zero calls), or `native test` (only where a native receipt backs execution).
   - Whether `port spy or native observation still needed` applies because an effect, command or outbound action is reported only inside model-returned data (`result` or `world`) without an observed port call or native receipt.
3. **Review-summary evidence provenance (`summarizeBoundaryEvidence`):** each observation from `pdd owner`, `pdd lint --local`, hosted `pdd test` Story runs, and native target-host checks shown with its actual source, scope, label, and explicit credit limits.
4. **Verification split:** Runtime-checked operations vs. `kind: "native-only"` declarations (with their `reason`) and `## Native validation` / native test responsibilities, preserving the `native-only` route without turning declarations into execution receipts.
5. **Complexity budget and advisory divergences:** prompt prose line counts (`> 500` warning, `> 1000` elevated, falling back to the scenario's loaded prompts when the slice only edits Stories or tests), Story scenario step counts (`> 15` steps or `> 1000` lines warning), and any latest-batch multi-sample divergences across samples or reruns, shown strictly as advisory notes.

## Review-summary evidence (`summarizeBoundaryEvidence`)

Export pure deterministic function `summarizeBoundaryEvidence({ownerLookups, localLint, hostedStoryRuns, nativeChecks})`. Perform no filesystem, Git, network, clock or model I/O, and never mutate inputs.

### Input contract

- `ownerLookups`: array of `{ targetPath: string, ownerPrompt: string | null, source: "binding" | "header" | "prose" | "path" | "none", certain: boolean }`.
- `localLint`: `null` or `{ exitCode: integer, state: string, localOnly: boolean, scope: string, warningCount: integer, problemCount: integer, incompleteSave: boolean, inspectedPrompts: string[], inspectedTests: string[] }`.
- `hostedStoryRuns`: array of `{ storyPath: string, testPath: string, loadedPrompts: string[], missingOwnerConnection: boolean, state: "passed" | "failed" | "partial" | "refused" | "not_run" | "unknown", passedAssertions: string[], totalAssertions: integer }`.
- `nativeChecks`: array of `{ behavior: string, targetHost: string, runner: string, receipt: { receiptId: string, source: string, status: "passed" | "failed" | "skipped" | "unverified", verifiedBehaviors: string[] } | null }`.

### Output contract

Return `{ advisory, entries, credits, lines }` where `advisory` is `true`, `entries` preserves fixed section order (`ownerLookups`, then `localLint` if non-null, then `hostedStoryRuns`, then `nativeChecks`), and every entry has exact fields `{ kind, label, source, scope, exitCode, ownerPrompt, loadedPrompts, passedAssertions, receiptId, creditsPromptRules, creditsModeledAssertions, creditsNativeBehavior, note }`:

| `kind` | `label` | `source` | `scope` | Credit booleans |
| --- | --- | --- | --- | --- |
| `"owner-resolution"` | `"resolved"` if trimmed `ownerPrompt` is nonblank, else `"unmapped"` | `source === "none"` ? `"pdd owner"` : `"pdd owner (" + source + ")"` | If resolved: `"ownership lookup: " + targetPath + " -> " + ownerPrompt + (certain ? " (certain)" : " (uncertain)")`; else `"ownership lookup: " + targetPath + " -> no owner"` | `creditsPromptRules: false`, `creditsModeledAssertions: false`, `creditsNativeBehavior: false`. `ownerPrompt` is trimmed path or `null`; `exitCode: null`, `loadedPrompts: []`, `passedAssertions: []`, `receiptId: null`; `note: "ownership lookup only; checks no prompt rules or behavior"`. |
| `"local-lint"` | When `localOnly === true`: always `"partial"` (even when `exitCode === 0`, `warningCount === 0`, `problemCount === 0`, or raw `state === "passed"`). When `localOnly === false`: trimmed `state` or `"unknown"`. | When `localOnly === true`: `"pdd lint --local"`; else `"pdd lint"`. | Let `cleanScope` be trimmed `scope` or `"SVG layout only"`. When `localOnly === true`: `cleanScope + (incompleteSave ? "; incomplete local save" : "") + "; prompt rules not checked"`; else `cleanScope`. | `creditsPromptRules: false`, `creditsModeledAssertions: false`, `creditsNativeBehavior: false`. `exitCode` is `localLint.exitCode`; `ownerPrompt: null`, `loadedPrompts: []`, `passedAssertions: []`, `receiptId: null`; `note`: `"partial local lint; no credit for checking prompt rules"` when `localOnly === true`, else `""`. |
| `"hosted-story"` | `"unconnected"` when `missingOwnerConnection === true`; else `"passed"` when `state === "passed"`, `loadedPrompts` has `>= 1` nonblank path and `passedAssertions` has `>= 1` nonblank string (`connectedPass`); else `state`. | `"pdd test (hosted): " + storyPath` | `"modeled policy assertions (" + passedAssertions.length + "/" + totalAssertions + ") via " + (loadedPrompts.length ? loadedPrompts.join(", ") : "none")` | `creditsPromptRules: connectedPass`, `creditsModeledAssertions: connectedPass`, `creditsNativeBehavior: false`. `loadedPrompts` and `passedAssertions` keep trimmed nonblank items in input order; `exitCode: null`, `ownerPrompt: null`, `receiptId: null`. `note`: `"missing owner connection; no credit for unexercised owner"` when unconnected, `"modeled assertions only; native host behavior requires a native receipt"` when `connectedPass`, else `"hosted run did not pass modeled assertions"`. |
| `"native-check"` | Let `validReceipt` be `receipt !== null`, trimmed `receipt.receiptId` nonblank, trimmed `receipt.source` nonblank, `receipt.status === "passed"`, and `receipt.verifiedBehaviors` containing trimmed `behavior`. `"verified"` when `validReceipt`; else `"failed"` when `receipt !== null && receipt.status === "failed"`; else `"unverified"`. | When `receipt` has nonblank `receiptId` and `source`: `runner + " on " + targetHost + " (receipt " + receiptId + ", " + receipt.source + ")"`; else `runner + " on " + targetHost + " (no native receipt)"`. | `"target-host native behavior: " + trimmedBehavior` | `creditsPromptRules: false`, `creditsModeledAssertions: false`, `creditsNativeBehavior: validReceipt`. `receiptId` is trimmed nonblank `receipt.receiptId` or `null`; `exitCode: null`, `ownerPrompt: null`, `loadedPrompts: []`, `passedAssertions: []`. `note`: `"credited via native receipt"` when `validReceipt`, `"no native receipt; native behavior credit withheld"` when `receipt` or its `receiptId`/`source` is missing, `"native receipt failed; native behavior credit withheld"` when `status === "failed"`, `"native receipt status is " + status + "; native behavior credit withheld"` for other non-passed statuses, else `"behavior not listed in native receipt; native behavior credit withheld"`. |

`credits` summarizes exact aggregate proof boundaries:

- `resolvedOwners`: deduplicated ascending-sorted array of nonblank `ownerPrompt` strings from `"owner-resolution"` entries.
- `localLintPartial`: `true` if any `"local-lint"` entry has `label === "partial"`, else `false`.
- `localLintCreditsPromptRules`: `true` only if any `"local-lint"` entry has `creditsPromptRules === true` (always `false` for `pdd lint --local` or when absent).
- `hostedPassedAssertions`: deduplicated array (preserving first-seen order) of `passedAssertions` from `"hosted-story"` entries where `creditsModeledAssertions === true`.
- `nativeVerifiedBehaviors`: deduplicated array (preserving first-seen order) of trimmed `behavior` strings from `"native-check"` entries where `creditsNativeBehavior === true`.
- `nativeUnverifiedBehaviors`: deduplicated array (preserving first-seen order) of trimmed `behavior` strings from `"native-check"` entries where `creditsNativeBehavior === false`.

`lines` returns at most `25` plain-text lines starting with `"Human boundary card (advisory):"` followed by `"  Evidence:"` (or `"  Evidence: none"` when empty) and one two-level-indented line per entry showing its kind, `[label]`, actual scope, source, and credit boundary (summarizing overflow with `"  … +N more evidence entries omitted"` while staying `<= 25` lines). Never start any line with `"Text"` or `"Approve "`, and emit no forbidden PR-top words (`batch`, `request`, `Acceptance criteria`, `<details`, `Agent note`).

## Source selection and missing owner connection

Export `buildHumanBoundaryCard({root, focusPrompt = null, promptPaths = [], storyPaths = [], changedPaths = null, since = 0, env = process.env, evidence = null})`.

For each matched Story scenario (`schema_version: "prompt-runtime.program-scenario.v1"`):

1. **Selected source closure:** start from each step's `entry_path` (or the prompt declaring `step.operation` among `entry_path`, `entry_paths` and any Story `pdd-boundary` prompt list) plus `context` prompt paths (`string`, `{path}`, `{prompt_path}` or `{paths}`), and follow transitive `## Dependencies` prompt links (`promptMarkdownTargets` plus Markdown links resolved relative to the linking file or repository root after masking HTML comments and fenced or inline code spans, retaining any `#fragment` heading target) and `interface.calls[].target` prompt paths inside the Git-visible repository.
2. **Owning sources in scope:** collect `focusPrompt` (for `pdd approve`), changed `*.prompt.md` files in the slice (`promptPaths` or Git changes against `HEAD` / `main`), owning prompts resolved via `pdd owner` (`findOwners`) for changed production code files in the slice, Story `pdd-boundary` fenced prompt lists (newline-separated ```` ```pdd-boundary ```` or JSON `prompts`), and Git-visible `*.prompt.md` files named in Story prose outside `## Out of scope`, `## What must not change`, `## Non-goals` and `## Not in scope` sections. Exclude misplaced test prompts and `kind: "native-only"` prompts from required Runtime scenario loading (`native-only` prompts appear under the native side of the verification split with their `reason`).
3. **Missing owner connection:** never credit a passing scenario to an unexercised owner or a disconnected rule:
   - **Unloaded owning source:** if any checkable owning prompt in scope is absent from the scenario's selected source closure (for example, a standalone simulator prompt passes checks while changed implementation or guide prompts are never linked or loaded, or a `## Dependencies` link to the owner was removed), record `missing owner connection` naming the unloaded owning source and the selected source that actually ran.
   - **Broken, stripped or disconnected `#fragment` section or removed owning rule in selected source:** extract each prompt heading's section body up to the next heading of equal or higher level. If a `## Dependencies` or Story link targets `owner.prompt.md#section` whose heading slug is absent or whose section body is empty, or if a consequential rule or criterion fails salient domain coverage (`>= 2` matched signals and `>= 50%` of backticked policy identifiers plus non-topic domain stems when `>= 2` signals exist, checked within the targeted `#section` body when an owner is linked via `#section`) while a synthetic scenario still passes, record `missing owner connection` instead of crediting the selected owner.

## Observation kinds

| Observation kind | Classification rule | Advisory note |
| --- | --- | --- |
| `observed simulated port call` | Check with `target: "calls"`, or saved step evidence on an instrumented port (`interface.resources`, `interface.calls`, `simulation`, `simulation_overrides`). | Report `0 observed port calls` when a `target: "calls"` check asserts `0` or `[]`, or when saved step evidence explicitly records `0` observed calls on an instrumented port. |
| `supplied fact` | `result` or `world` check (with no observed port call or native receipt) referencing `step.input` (`check.ref_target: "input"`, `check.value.ref_target: "input"`, or `integer_relation` input refs), matching an unchanged `step.input` value, or matching `initial_world` (`$seed` and `initial_world.set`). | Distinguishes echoed inputs and seeded world state from computed behavior. |
| `model-returned value` | `result`, `world` or `error` check produced by the interpreter model without an observed simulated port call or native receipt and not a `supplied fact`. | Append `(port spy or native observation still needed)` when the check inspects returned effect, action, call, alert, event or command claims without a `target: "calls"` check or native receipt on that criterion. |
| `native test` | Backed by a saved passing `pdd.native-evidence-record.v1` native receipt in `.git/pdd/runs` for that Story/criterion, or a valid passing native check receipt covering that behavior (standalone `kind: "native-only"` prompt approvals also retain their `reason` without requiring Runtime scenarios). Bare `## Native validation` headings or unreceipted claims appear only in the verification split or as unverified—never as native execution credit. | Native behavior has credit only where there is a native receipt; preserves the `native-only` route. |

## Saved check, local-lint and native-receipt records

Inspect saved check and local-lint records for `root` under `PDD_STATE_DIR` (or `HOME/.pdd/runtime/batches`, filtered by `since` when positive):

- **Hosted `pdd test` records (`intent: "check"`):** keep only the latest saved check record per test path so superseded historical batches never leak stale divergences. Match saved step observations by `step_id` first and by step index or unkeyed check identity when `step_id` is omitted. Record passed modeled policy assertions per Story/test alongside their loaded prompt sources and `missingOwnerConnection` state. When a test's latest saved check report contains multiple `samples` whose step `result`, `error`, `world`, `calls` or check pass states differ—or `rerun.steps` with `changed_paths` or mixed runs—include a concise advisory divergence note naming the step and differing surface. Multi-sample agreement (`k/k samples agreed`) or single-sample runs are noted neutrally.
- **Local `pdd lint --local` records (`intent: "lint-only"`, `local_only: true`):** read the latest valid local-layout record for `root` (matching `version: 1`, `local_scope`, `lint.state: "partial"`, `lint.reason.code: "local-only"`, checking `summary.json` agreement for incomplete-save detection). Always pass it to `summarizeBoundaryEvidence` with `localOnly: true` so exit 0 retains `"partial"` and gives no credit for checking prompt rules.
- **Owner lookups and native receipts:** gather `pdd owner` resolutions (`findOwners`) for changed production files and saved `pdd.native-evidence-record.v1` receipts in `.git/pdd/runs`, merge any explicit caller-supplied `evidence` observations, and attach `evidenceSummary = summarizeBoundaryEvidence(...)` to the returned card. Never allocate or mutate state; saved read failures are ignored safely.

## Compact rendering (`<= 25` lines)

- `formatApproveBoundaryCard(card)` returns at most `25` plain-text lines starting with `Human boundary card (advisory):` and two-space-indented body lines (`Policy:`, `Owner gap:` when unloaded owning sources exist, `Evidence:` when `card.evidenceSummary?.entries?.length` is non-empty, `Provenance:`, `Verification split:`, `Budget & samples:`). Prioritize `missing owner connection`, `local lint [partial]`, unverified native checks, `port spy or native observation still needed`, and `0 observed port calls` rows before ordinary rows when compacting, and summarize overflow with `… +N more` while always retaining `Verification split:` and `Budget & samples:`. Never start any card line with `Text` or `Approve `.
- `readablePrTop` in [readable workflow PR descriptions](workflow-pr-body.prompt.md) renders `facts.boundary` on PR 1 (`layout: "spec"`) as a `## Boundary` section of at most `25` lines right after `## Summary` (including `evidenceSummary` entries with actual scope and source when present), sanitizing all dynamic text as inert Markdown with no forbidden jargon, extra URLs, HTML tags or closing keywords.

## Dependencies

None. `summarizeBoundaryEvidence` and `formatApproveBoundaryCard` are pure calculation and formatting; `buildHumanBoundaryCard` binds host repository, owner, Story-lint, test-selection, and saved-result adapters listed below.

## Host adapters and navigation

In native execution, `buildHumanBoundaryCard` binds host repository/file/owner/test/result adapters outside the pure `summarizeBoundaryEvidence` contract:

- [Runtime seam](runtime-seam.prompt.md): shared authored-file, Markdown dependency, Story criteria and scenario JSON readers (`readPrompt`, `promptMarkdownTargets`, `storyCriteria`, `parseScenarioJson`, `findTests`, `gitFiles`).
- [Story quality lint](story-lint.prompt.md): Story path classification (`isLintableStoryPath`).
- [Test selection](test-selection.prompt.md): Story path and acceptance matching (`isStoryPath`, `hasAcceptance`).
- [File owner lookup](file-owner.prompt.md): `findOwners` and `isTestPromptPath` for `pdd owner` resolution and test-prompt exclusion.
- [Workflow results](workflow-results.prompt.md#saved-local-layout-record): saved `pdd lint --local` partial record shape and `pdd.native-evidence-record.v1` native receipt contract.
