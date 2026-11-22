# Autopilot pre-flight intake classifier

Own `src/autopilot-intake-preflight.mjs`. Classify open GitHub issues deterministically before Autopilot claims them or spends build tokens, and roll up recorded pre-flight skip reasons with Classifier Conversion for `pdd metrics`. Perform no filesystem, network, process, AI, or clock I/O, and never mutate caller inputs.

## Domain decisions

- **Zero-token pre-flight boundary (`#3534`, building on `#3500`):** Evaluate every candidate issue from sanitized issue text, trusted comments, optional `repoFiles`, optional `siblingRepos`, optional `decisionNote`, and optional `workerCapabilities` before claiming a slot, allocating a worktree, or starting an AI build.
- **Text sanitization (`sanitizeIssueText`):** Before matching pre-flight signals in an issue body or comment, strip HTML comments (`<!-- ... -->`), fenced Markdown code blocks (`` ``` `` or `~~~` blocks), and Markdown blockquote lines (optional leading spaces followed by `>`). Pasted error logs, stack traces, and quoted examples inside stripped blocks never trigger pre-flight skips. Strip ASCII/C1 control characters from every returned `reason` and `question` string (single-line plain text, at most 300 characters).
- **Strict category precedence:** Evaluate categories in fixed order so an issue with multiple blockers always receives one deterministic primary `reasonCode`:

```mermaid
flowchart TD
    S[Sanitize title, body, trusted comments] --> C{Cross-repo or coordinated external edit?}
    C -->|Yes| R(["reject · cross_repo · needs-other-repo"])
    C -->|No| H{Unanswered product, pricing, or UX policy decision?}
    H -->|Yes| P1(["park · human_decision · pdd:needs-decision"])
    H -->|No| U{Unavailable external or human verification boundary?}
    U -->|Yes| P2(["park · unverifiable_boundary · pdd:needs-decision"])
    U -->|No| Q{Empty/stub, explicit draft/needs-repro, or edit-only missing local target?}
    Q -->|Yes| P3(["park · unclear_or_unsound · pdd:needs-decision"])
    Q -->|No| A(["allow · null · null"])
```

- **Category 1 — `cross_repo` (`decision: "reject"`, `intakeClass: "elsewhere"`, `label: "needs-other-repo"`):**
  - Repository-agnostic sibling detection (`normalizeSiblingRepos(siblingRepos)`): accept caller-configured `siblingRepos` (from `autopilot.siblingRepos` in `pdd.json`), where each entry is either a string (`"acme-api"`, `"acme/mobile"`, `"extensions/my-app"`) or `{ canonical, short?, aliases?, roots?, prefixes? }`. Never hardcode repository or user names. Also recognize any explicit foreign `OWNER/REPO` slug or GitHub `blob`/`tree` URL whose `owner/repo` differs case-insensitively from `repository`, and any absent non-local root path named inside an explicit multi-repo coordination clause.
  - Canonical `targetRepo`: when named as an explicit `OWNER/REPO` slug or GitHub URL, return lowercase `"owner/repo"`; when matched via configured `siblingRepos` without an owner prefix, return its configured `canonical` name; when inferred from an absent foreign root path in a multi-repo coordination clause, return that top-level root segment; when an unnamed external service requires edits or deployment, return `"external-service"`.
  - Triggers when either:
    1. **Foreign-only target:** Leading title `[REPOSITORY]` / `REPOSITORY:` prefix or standalone `Repo:` / `Repository:` / `Target repo:` / `Target repository:` / `Service:` / `Target service:` field naming another repository or configured sibling, a foreign GitHub `blob`/`tree` URL with no local code paths, an absent configured sibling root path, or explicit configured sibling framing with zero local targets; OR
    2. **Coordinated multi-repository edit:** Even when local files or the current `repository` are also referenced, the sanitized text explicitly requires coordinated edits, paired PRs, or deployments in another repository or external service — evidenced by (a) an absent configured sibling root path, absent foreign root path inside an explicit multi-repo coordination clause, or foreign `blob`/`tree` URL cited as files to edit alongside local paths; (b) an explicit foreign `Repository:` / `Service:` field alongside local targets; or (c) explicit coordinated-change phrasing paired with a configured sibling, same-org foreign slug, or external service.
  - **False-positive guards:** Passive mentions of calling, mocking, documenting, or handling HTTP/CLI errors from another repository or external service without editing it stay `allow`. Dependency-bump clauses (including scoped package bumps `@scope/pkg`) stay `allow`. Missing **local-root greenfield paths** (under an existing local top-level directory present in `repoFiles` such as `src/`, `prompts/`, `test/`, `tests/`, `bin/`, `scripts/`, `docs/`, `user_stories/`, `pkg/`, `cmd/`, `internal/`, `lib/`, `app/`) never count as foreign paths.
  - Set `question: null`, crisp single-line `reason`, and `signals` to one or more of `["repo_header", "foreign_url", "foreign_root_path", "sibling_service", "coordinated_multi_repo"]`.
- **Category 2 — `human_decision` (`decision: "park"`, `intakeClass: "person"`, `label: "pdd:needs-decision"`):**
  - Triggers when sanitized issue title/body (or latest unresolved trusted comment) poses an **unanswered** product, pricing, billing/tier, or UX policy decision that only a person can answer — evidenced by explicit unresolved markers (`Open question:`, `Needs decision:`, `Decision needed:`, `Product decision:`, `Pricing decision:`, `UX decision:`, `Question for <role/team>:`) or explicit unanswered product/pricing/UX option prompts (`Should we ... or ...?`, `Options: (A) ... (B) ...` choosing pricing, tier limits, product direction, or user-facing UX policy).
  - **Trusted resolution override:** Do not park when a trusted comment (`trusted !== false`) posted after the question clearly settles or approves the choice (for example `"Decision: ..."`, `"Approved: ..."`, `"Confirmed: ..."`, `"Go with ..."`), when `decisionNote` is a non-empty string, or when the body itself records a settled decision (`"Decision:"`, `"Resolved:"`, `"Locked-in:"`) with no remaining open product/pricing/UX question. Ignore untrusted comments (`trusted === false`) completely: they can neither trigger nor resolve a decision.
  - **Engineering guard:** Normal engineering bugs, refactors, rhetorical problem statements ("Why does X crash? Fix it to exit 1."), or missing file-level scope/reproduction without a product, pricing, or UX policy question stay `allow` (subject to Category 4 mechanical checks).
  - Set `targetRepo: null`, crisp single-line `reason`, one concise `question`, and `signals` to one or more of `["open_product_question", "pricing_policy_choice", "ux_policy_choice"]`.
- **Category 3 — `unverifiable_boundary` (`decision: "park"`, `intakeClass: "person"`, `label: "pdd:needs-decision"`):**
  - Default `workerCapabilities` when omitted: `{ localTests: true, liveExternalServices: false, productionCredentials: false, humanManualQa: false, availableRecipes: [] }`.
  - Triggers when sanitized acceptance criteria or verification instructions require proving completion against an external or human-only boundary unavailable under `workerCapabilities` — including live third-party/production service, live payment/checkout, or live registry publish verification requiring secrets/2FA when `liveExternalServices` or `productionCredentials` is `false`; required manual human visual/QA sign-off or physical hardware/mobile device verification when `humanManualQa` is `false`; or a named external E2E verification recipe explicitly unavailable upfront (absent from `workerCapabilities.availableRecipes`).
  - **Local-boundary override:** Stay `allow` whenever the issue authorizes verification via local unit/integration tests, fake/mocked ports, dry-run fixtures, or PDD Runtime checks (`localTests === true`), or when `workerCapabilities.availableRecipes` includes the required recipe (case-insensitive).
  - Set `targetRepo: null`, crisp single-line `reason`, one concise `question` asking a person to authorize a runnable local/stubbed verification boundary or handle verification manually, and `signals` to one or more of `["unavailable_external_e2e", "missing_prod_credentials", "manual_human_qa_only"]`.
- **Category 4 — `unclear_or_unsound` (`decision: "park"`, `intakeClass: "person"`, `label: "pdd:needs-decision"`):**
  - Deterministic, mechanical check (skipped when `decisionNote` is non-empty) that parks issues that cannot be soundly executed as written:
    1. **Empty or placeholder stub (`empty_or_stub_issue`):** sanitized body plus trusted comments is empty or purely a placeholder token (`TBD`, `TODO`, `WIP`, `placeholder`, `draft`, `coming soon`, `...`, `N/A`, `none`, `FIXME`) with no concrete repository file path in the title;
    2. **Explicit draft or needs-repro marker (`explicit_draft_or_needs_repro`):** title begins with `[WIP]`, `[DRAFT]`, `WIP:`, or `DRAFT:`, or labels contain a draft/triage blocker (`draft`, `wip`, `needs-repro`, `needs-info`, `needs-triage`, `incomplete`, `invalid`);
    3. **Edit-only missing local targets (`missing_target_paths`):** `repoFiles` has file inventory under the cited top-level directory, zero cited specific paths exist locally, one or more local-root paths are missing, and the issue asks to edit/fix/update/refactor/delete them with zero creation verbs (`add`, `create`, `introduce`, `new`, `scaffold`).
  - Set `targetRepo: null`, crisp single-line `reason`, one concise actionable `question`, and `signals` to one or more of `["empty_or_stub_issue", "explicit_draft_or_needs_repro", "missing_target_paths"]`.
- **Crisp skip reasons and precision rollup (`summarizeIntakeFilterPrecision`):**
  - `PREFLIGHT_REASON_CODES` is `["cross_repo", "human_decision", "unverifiable_boundary", "unclear_or_unsound"]`.
  - Deduplicate valid `skips` (positive integer `issue`, `reasonCode` in `PREFLIGHT_REASON_CODES`, normalized by lowercase `repo`) keeping the latest record per `(repoLower, issue)`. Count `skipped` and `byReasonCode: { cross_repo, human_decision, unverifiable_boundary, unclear_or_unsound }`.
  - Expand each valid run in `runs` (`issues` array of positive integers, else single positive integer `issue`) and deduplicate per `(repoLower, issue)` by winning status rank (`"merged"` / `"would-merge"` > `"running"` > `"needs-person"` > all other non-merged statuses).
  - Compute:
    - `taken`: count of deduplicated taken `(repoLower, issue)` entries;
    - `merged`: count of taken entries whose winning status is `"merged"` or `"would-merge"`;
    - `unmerged`: `taken - merged`;
    - `classifierConversionPct`: `taken === 0 ? null : Math.round((merged / taken) * 1000) / 10`;
    - `classifierConversionDisplay`: `taken === 0 ? "0/0 (n/a)" : "${merged}/${taken} (${classifierConversionPct.toFixed(1)}%)"`;
    - `skipSummary`: `skipped === 0 ? "Pre-flight skipped (0): none" : "Pre-flight skipped (${skipped}): "` followed by nonzero buckets in fixed order `cross_repo`, `human_decision`, `unverifiable_boundary`, `unclear_or_unsound` formatted as `"${count} ${code}"` joined by `" · "`.

## Public contract

- Export `PREFLIGHT_REASON_CODES`, `normalizeSiblingRepos(siblingRepos)`, `sanitizeIssueText(text)`, `classifyPreflightIssue(input)`, and `summarizeIntakeFilterPrecision(input)`.
- `classifyPreflightIssue({repository, issue, repoFiles?, siblingRepos?, decisionNote?, workerCapabilities?})`:
  - Input:
    - `repository`: string (`OWNER/REPO`, e.g. `"acme/app"`).
    - `issue`: `{ number: integer, title: string, body: string, labels?: string[], comments?: Array<{ author: string, body: string, trusted?: boolean, at?: string }> }`.
    - `repoFiles` (optional): array of repository-relative existing file path strings.
    - `siblingRepos` (optional): array of sibling repository names/slugs or `{ canonical, short?, aliases?, roots?, prefixes? }` descriptors.
    - `decisionNote` (optional): string or `null`.
    - `workerCapabilities` (optional): `{ localTests?: boolean, liveExternalServices?: boolean, productionCredentials?: boolean, humanManualQa?: boolean, availableRecipes?: string[] }`.
  - Output (all 8 keys always present):
    - `decision`: `"allow" | "reject" | "park"`.
    - `reasonCode`: `null | "cross_repo" | "human_decision" | "unverifiable_boundary" | "unclear_or_unsound"`.
    - `intakeClass`: `null | "elsewhere" | "person"`.
    - `label`: `null | "needs-other-repo" | "pdd:needs-decision"`.
    - `targetRepo`: string or `null`.
    - `reason`: crisp non-empty single-line string (`<= 300` chars) when `reject` or `park`, else `null`.
    - `question`: concise single-line question string (`<= 300` chars) when `park`, else `null`.
    - `signals`: array of signal code strings (`[]` when `allow`).
- `summarizeIntakeFilterPrecision({skips, runs})`:
  - Input:
    - `skips`: array of `{ repo: string, issue: integer, decision?: string, reasonCode: string, reason?: string, at?: string }`.
    - `runs`: array of `{ repo: string, issue?: integer, issues?: integer[], status: string }`.
  - Output (all 8 keys always present):
    - `skipped`: non-negative integer.
    - `byReasonCode`: `{ cross_repo: integer, human_decision: integer, unverifiable_boundary: integer, unclear_or_unsound: integer }`.
    - `taken`: non-negative integer.
    - `merged`: non-negative integer.
    - `unmerged`: non-negative integer.
    - `classifierConversionPct`: number (`0` to `100`, 1 decimal place) or `null`.
    - `classifierConversionDisplay`: string (`"${merged}/${taken} (${pct.toFixed(1)}%)"` or `"0/0 (n/a)"`).
    - `skipSummary`: string (`"Pre-flight skipped (0): none"` or `"Pre-flight skipped (${skipped}): ..."`).

## Dependencies

None. This module is pure classification and metrics rollup.
