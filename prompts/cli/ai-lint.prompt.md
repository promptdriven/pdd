# Adaptive AI prompt and Story lint engine

Own `src/autopilot/ai-lint-engine.mjs`. Export `AI_LINT_MODES`, `REVIEW_CHECKLISTS`, `MAX_AI_LINT_FINDINGS`, `loadBaseTrustedReviewScope`, `collectLinkedManifest`, `selectReviewChecklists`, `normalizeQuoteText`, `verifyQuoteOnDisk`, `verifyCandidateFindings`, `buildAdaptiveLintPrompt`, `buildVerifierPrompt`, `applyVerifierDecisions`, `rankAndCapFindings`, `computeAiLintCacheKey`, and `runAdaptiveAiLint(options, ports)`.

Run adaptive, advisory-only AI prompt and Story lint for `pdd lint --ai` and its hidden host-plumbing modes (`--ai-emit-pack`, `--ai-emit-verify`, `--ai-apply`) with zero `runtime-seam` imports.

## Domain decisions

### Modes and providers

- Read `mode` from `options.mode` or `env.PDD_AI_LINT_MODE` (default `"adaptive"`). Valid values: `"adaptive"`, `"single"`, `"single-verify"`. Any other non-empty value refuses immediately with exit `2`.
- Read `provider` from `options.provider` or `env.PDD_AI_LINT_PROVIDER` (default `"codex"`). Valid values are strictly `READONLY_PROVIDERS` (`codex`, `claude`, `gemini`). Unsupported values (including `agy`) refuse with exit `2`.
- Read `model` from `options.model` or `env.PDD_AI_LINT_MODEL` (optional).
- Advisory-only exit policy: AI warnings never cause a non-zero exit code. Exit `1` occurs only when offline deterministic Tier-0 structural lint reports errors on the target scope. Usage, non-Git, unmatched target, invalid mode/provider, or unreadable plumbing input errors exit `2`.

### Target selection and merge-base `review.scope`

- Require a Git repository root (`git rev-parse --show-toplevel`, exit `2` otherwise). Enforce `workspace.policy({root})`, canonical in-repo paths, `!isSecretPath`, and safe regular non-symlink UTF-8 reads.
- Load optional `review.scope` from merge-base `pdd.json` (`git show <merge-base>:pdd.json`, falling back to working-tree `pdd.json` only when no base commit exists). Accept either an array of include globs or `{include?: string[], exclude?: string[]}`. Working-tree edits on a feature branch never override merge-base `review.scope`.
- Target modes:
  - Explicit `words`: accept ANY existing regular non-symlink, non-secret repo-relative or `cwd`-relative file (prompts, Stories, scenario `.json`, `app-map.json` / `app/maps/*.json`, `.ui.svg` drawings, `product/*.md`, `contracts/*.md`, owned code files via `// Prompt:` header or `pdd-bindings.json`, or any other existing repo file), plus directories and Story stems. Keep every targeted file in `targets` with its content in the pack; refuse with exit `2` only when a requested path does not exist on disk (`ENOENT`) or violates workspace/symlink/secret safety.
  - `--diff [BASE]` / `--base REF`: select changed and untracked PDD targets (prompts, Stories, contracts, product docs, scenarios, app-maps, `.ui.svg`, and owned code) against merge-base, recording other changed supporting files (such as native tests) and marking added/untracked prompts as `isNew: true`.
  - Default repo-wide: select all non-fixture Git-visible `.prompt.md` and lintable Story files matching `review.scope`, marking prompts absent from merge-base (or untracked) as `isNew: true`.

### Unbounded linked-file manifest and compact graph facts

For the selected target set, scan all allowed repo files with **no neighbor cap** and build:

- `outgoing_links`: every canonical relative Markdown link from any target file.
- `incoming_links`: every repo file linking to any target file (reverse links).
- `contracts`: linked shared contract files (`contracts/**` or contract docs).
- `paired_stories`, `paired_scenarios`, `paired_tests`: all Stories, scenario JSONs, and matching native test files paired with targets or owned code.
- `svg_drawings`: all `.ui.svg` drawings linked by any target.
- `owned_code`: all code files owned by target prompts (`// Prompt:` header or `pdd-bindings.json`).
- Bidirectional discovery for non-prompt targets: scenario `.json` targets link their paired Story and referenced prompts; `.ui.svg` targets link their referencing prompts, app-maps, and paired Stories/scenarios; `app-map.json` / `app/maps/*.json` targets link their referenced prompts, `.ui.svg` drawings, and Stories; owned code targets link their owning prompt(s) (via `// Prompt:` header or `pdd-bindings.json`) and those prompts' paired Stories/scenarios/tests; `product/map.md` and `product/plan.md` link both Markdown links and backticked/in-repo PDD paths.
- `all_linked`: sorted deduplicated union of every linked path above (never truncated to 4 or any fixed cap).
- Compact `graph_facts`: target `kind` (`native-only` vs `checkable` vs `story`), `declared_links` (`## Dependencies`), directed `cycles`, `layering_violations` (`checkable -> native-only`), and `native_only_targets`.

### Adaptive checklist routing (`skills/pdd/references/review/*.md`)

| Checklist | `single` / `single-verify` | `adaptive` auto-selection rule |
|---|---|---|
| `contract` | Always | Always |
| `interfaces` | Off | Any target is a contract, `.ui.svg`, app-map, or code file, OR has outgoing links, incoming links, linked contracts, or `kind: native-only` target/neighbor |
| `trace` | Off | Any target is a Story, scenario `.json`, `product/map.md`/`product/plan.md`, or test file, OR Stories/scenarios/product docs/tests are changed or paired with targets |
| `abuse` | Off | Any target is `kind: native-only` or touches auth/trust/identity/role/tenant/permission, money/pricing/billing/payment/ledger/balance, or security/crypto/secret/sandbox/injection/path-traversal (never triggered solely by generic ports) |
| `design` | Off | Only when at least one target `.prompt.md` is brand-new (`isNew`) or huge (`> 350` lines); never on ordinary edits |

Record `checklist_reasons` mapping each selected checklist to the triggering rule(s).

### Anti-noise funnel, read-only execution, cache, and fail-visible behavior

1. **Read-only repo access & active tool-read directives:** Standalone runs invoke `runReadonlyAgent` via `runStepAgentProcess` with `disableTools: false`, `cwd: realRoot`, and `tools: "Read,Glob,Grep"` so the reviewer can read or search any repo file in OS/plan read-only mode without editing files. When `interfaces` is active, `buildAdaptiveLintPrompt` includes an explicit `REQUIRED TOOL STEP (interfaces)` directing the reviewer to read linked neighbor prompts/contracts from `LINKED-FILE MANIFEST` on disk before emitting JSON; when `trace` is active, it includes an explicit `REQUIRED TOOL STEP (trace)` directing the reviewer to read paired Stories and scenario/test JSON files on disk before emitting JSON.
2. **Normalized verbatim quote verifier:** Normalize smart quotes (`“”‘’`) to ASCII quotes and collapse whitespace. Search `±10` lines around the reported `line` first, then fall back to full-file search, rewriting `line` to the exact verified disk line. For `interfaces` findings or any finding supplying `cross_file` / `cross_file_quote`, require two distinct valid files and verify BOTH quotes on disk. Drop any unverified candidate, never display it, record `quote_dropped` in JSON, and print `<N> findings dropped (unverified quote)` whenever `quote_dropped > 0`.
3. **Single-finding-per-defect Finder rule & fresh second-eyes verifier:** The Finder prompt instructs the model to emit at most one finding per root defect using the single strongest checklist tag (`interfaces` > `abuse` > `trace` > `contract` > `design`). The fresh second-eyes verifier is skipped in `single` mode and invoked in `single-verify` and `adaptive` modes when `quote_verified >= verifyMin` (default `2`, or `parsePositiveInt(env.PDD_AI_LINT_VERIFY_MIN, 2)`). It tries to disprove weak, stylistic, duplicate, or out-of-scope warnings (dropping `abuse` findings lacking a concrete `test_idea`), while explicitly keeping `trace` findings when a concrete prompt rule, Story acceptance criterion, or `product/map.md` rule genuinely lacks a covering test/scenario step or contradicts its paired Story/test.
4. **Ranking, 7-cap, and funnel metrics:** Deduplicate, sort by severity (`high` > `medium` > `low`) then checklist priority (`abuse`, `contract`, `interfaces`, `trace`, `design`) then original order, and cap at `7` findings (`cap7_dropped`). Always emit exact funnel counts in `--json` (`schema_version: "pdd.ai-lint.v2"`): `raw_candidates`, `quote_verified`, `quote_dropped`, `verifier_ran`, `verifier_kept`, `verifier_dropped`, `cap7_dropped`, `final_count`.
5. **SHA-256 input-hash cache:** Hash mode, provider, model, `verifyMin`, `review.scope`, active checklist contents, target contents and `isNew` flags, every file in `manifest.all_linked`, and `graph_facts` into `.pdd/cache/lint/<sha256>.json` using atomic writes and symlink checks. Bypass read/write when `PDD_AI_LINT_NO_CACHE=1`. Never cache incomplete or failed runs.
6. **Fail-visible incomplete runs:** If Pass 1 or Pass 2 fails, times out, or returns unparseable JSON, set `ai_status: "incomplete"` or `"unavailable"`, emit a clear `AI lint incomplete/unavailable (<provider>): <reason>` warning, never print a green `0 advisory findings` summary, and do not cache the run.

### Hidden host-plumbing modes

- `--ai-emit-pack`: Emit `pdd.ai-lint-pack.v1` JSON (metadata, cache status, manifest, graph facts, prompt, JSON schema) with `0` AI calls.
- `--ai-emit-verify PATH`: Read raw Pass 1 JSON from `PATH` (or `-` for stdin), run deterministic quote verification, and emit `pdd.ai-lint-verify-pack.v1` JSON (`needs_verify`, `candidates`, `quote_dropped`, `funnel`, `verify_prompt`, `json_schema`).
- `--ai-apply PATH`: Read raw Pass 1 JSON or `{candidates, verifier}` bundle from `PATH` (or `-` for stdin), run quote verification if needed, apply verifier decisions and 7-cap, persist cache (when complete and cache enabled), merge offline Tier-0 errors, and render standard text or `pdd.ai-lint.v2` JSON output.

## Dependencies

- [Repo hygiene and extensible project lint](repo-hygiene-lint.prompt.md): `lintRepoProject`, `extractDependencyLinkTargets`, `isNativeOnlyPrompt`, `countFileLines`, `scanMarkdownLinesAndFences`, `extractDeclaredPorts`, `compileGlobMatcher`, `scenarioPromptRefs`, `isContractDocPath`, `isCustomRuleTestFile`, `resolveDefaultBaseRef`.
- [Story quality lint](story-lint.prompt.md): `isLintableStoryPath`.
- [Agent adapters](agent-adapters.prompt.md): `runStepAgentProcess`.
- [Secret redaction](secret-redaction.prompt.md): `knownSecretValues`, `redactSecrets`.
