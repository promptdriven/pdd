# Autopilot universal validator

Own `src/autopilot-validator.mjs`. Provide the universal, repository-agnostic validation policy for Autopilot core and backside validation lint rules for repo hygiene lint. Works on any outside user repository (CLI, web UI, API, GCP/`gcloud`, AWS, Stripe, Postgres, Docker, OAuth, and general runtime code) without coupling to any internal smoke repository and without loading rules from `origin/main`. Never calls GitHub, external CLIs, the PDD interpreter, or a model, and never writes files.

## Domain decisions

- **No silent skips — strict fail-closed in both `auto` and `observe` modes:** Never treat `real-binding-unavailable`, an expired login, an unreachable daemon, a missing secret, or missing real end-to-end execution as a local skip, pass, `merged`, or `would-merge`. Both `auto` and `observe` modes enforce the exact same validation gate: when validation does not pass 100%, `eligible` is `false` in both modes. Only when Bucket 1 passes 100% does `auto` return `"allow-merge"` and `observe` return `"allow-would-merge"`.
- **Surface detection (`detectChangedSurfaces`):** Classify each repository-relative path in `changedFiles` (case-insensitive) into zero or more surfaces:
  - `docs`: Markdown/text documentation (`*.md` excluding `*.prompt.md`, `*.txt`, `*.rst`, `LICENSE*`, `CHANGELOG*`, `docs/**`).
  - `cli`: CLI entrypoints or scripts (`bin/**`, `cli/**`, `cmd/**`, `scripts/**`, `*.sh`, or filenames containing `cli`).
  - `api-server`: servers, routers, API endpoints, HTTP/WS/GraphQL/gRPC handlers (`api/**`, `server/**`, `routes/**`, `handlers/**`, `controllers/**`, or filenames containing `server`, `router`, `api`, `http`, `ws`, `websocket`, `graphql`, `grpc`).
  - `database`: schemas, migrations, queries, DB adapters (`db/**`, `database/**`, `migrations/**`, `prisma/**`, `sql/**`, `*.sql`, or filenames containing `postgres`, `mysql`, `sqlite`, `mongo`, `redis`, `db`).
  - `web-ui`: frontend views, components, pages, styles, screens (`web/**`, `ui/**`, `frontend/**`, `pages/**`, `components/**`, `views/**`, `app/**`, `*.jsx`, `*.tsx`, `*.vue`, `*.svelte`, `*.html`, `*.css`, `*.ui.svg`).
  - `external-tool`: cloud, payment, container, auth, or external CLI/SDK integrations (`Dockerfile`, `docker-compose*`, or paths mentioning `gcloud`, `gcp`, `aws`, `azure`, `stripe`, `docker`, `kubernetes`, `k8s`, `oauth`, `auth`, `webhook`, `terraform`).
  - `runtime-code`: any other production source code file (`.js`, `.mjs`, `.cjs`, `.ts`, `.mts`, `.cts`, `.py`, `.go`, `.rs`, `.rb`, `.java`, `.kt`, `.cs`, `.php`, `.swift`, `.c`, `.cpp`) outside `test/`, `tests/`, `__tests__/`, `spec/`, `fixtures/`, `examples/`, `prompts/`, `user_stories/`, and `docs/`.
  - `runtimeSurfaces` is the sorted unique list of non-`docs` surfaces. `docsOnly` is `true` only when `changedFiles` is non-empty, `runtimeSurfaces` is empty, and every changed file is in `docs`. `requiresRealE2e` is `runtimeSurfaces.length > 0`.
  - `requiredProofKinds` maps detected `runtimeSurfaces` to sorted unique kinds: `cli` → `"subprocess-cli"`, `api-server` or `database` → `"local-server-or-db"`, `web-ui` → `"browser-playwright"`, `external-tool` → `"live-binding"`, and `runtime-code` → `"real-execution"` only when no more specific boundary surface is present.
- **Real end-to-end execution and bug-fix control:** When `requiresRealE2e` is `true`, unit mocks (`kind: "unit-mock"`) never satisfy the gate. Real execution requires at least one executed check (`executed: true`) whose `kind` is in `["subprocess-cli", "local-server-or-db", "browser-playwright", "live-binding", "real-execution"]`. A 100% pass requires `offlinePassed: true`, empty `lintBlockingCodes`, every executed real E2E check having `exitCode === 0`, `passed > 0`, `failed === 0`, and `skipped === 0`, every kind in `requiredProofKinds` covered by a passing executed real E2E check (matching either exact kind or `"real-execution"` when `requiredProofKinds` is `["real-execution"]`), and when `isBugFix` is `true`, `bugFixBaseControl === "ran-and-failed-on-base"`.
- **Universal 3-Bucket outcome precedence:** Evaluate in exact priority order so environment/auth outages spend zero repair rounds and human-only or untested boundaries hard-stop in both modes:

```mermaid
flowchart TD
    S[Evaluate validation] --> D{docsOnly AND no binding/auth/human blocker?}
    D -->|Yes & offlinePassed| B1P([Bucket 1: allow-merge or allow-would-merge])
    D -->|Yes & offline failed| B1R{repairAttempts < 3?}
    D -->|No| H{Human interaction required?}
    H -->|Yes| B3H([Bucket 3: needs-person + 3-line card, free slot])
    H -->|No| E{Expired login / unavailable tool / real-binding-unavailable?}
    E -->|Yes| B2([Bucket 2: park-auth-wait, 0 repairs, cooldown, free slot])
    E -->|No| Z{requiresRealE2e AND 0 executed real E2E?}
    Z -->|Yes| B3M([Bucket 3: needs-person + 3-line card, free slot])
    Z -->|No| P{100% real E2E + offline + lint + bugfix control pass?}
    P -->|Yes| B1P
    P -->|Bug fix control not-run| B3M
    P -->|No| B1R
    B1R -->|Yes| REP([Bucket 1: repair, +1 attempt])
    B1R -->|No| ESC([Bucket 1: needs-person repair-exhausted, free slot])
```

- **Bucket 1 (Tool/login healthy & real E2E ran):**
  - 100% pass → `bucket: 1`, `decision: mode === "observe" ? "allow-would-merge" : "allow-merge"`, `waitKind: "none"`, `eligible: true`, `freeSlot: false`, `keepPr: false`, `repairRoundsToSpend: 0`, `repairAttemptsNext: repairAttempts`, `cooldownTool: null`, `resumeMode: "none"`, `checkCommand: null`, `proof` populated with sorted unique `surfaces`, executed `commands`, and their `exitCodes`, and `humanVerificationCard: []`.
  - Real code/E2E failure, missing required surface coverage among executed checks, blocking lint error, or `isBugFix: true` with `bugFixBaseControl === "passed-on-base"` → cap repairs cleanly at `MAX_VALIDATION_REPAIRS = 3`:
    - When `repairAttempts < 3`: `bucket: 1`, `decision: "repair"`, `waitKind: "none"`, `eligible: false`, `freeSlot: false`, `keepPr: true`, `repairRoundsToSpend: 1`, `repairAttemptsNext: repairAttempts + 1`, `cooldownTool: null`, `resumeMode: "none"`, `checkCommand: null`, `proof: {surfaces: [], commands: [], exitCodes: []}`, `humanVerificationCard: []`.
    - When `repairAttempts >= 3`: `bucket: 1`, `decision: "needs-person"`, `waitKind: "repair-exhausted"`, `eligible: false`, `freeSlot: true`, `keepPr: true`, `repairRoundsToSpend: 0`, `repairAttemptsNext: repairAttempts`, `cooldownTool: null`, `resumeMode: "none"`, `checkCommand: null`, `proof: {surfaces: [], commands: [], exitCodes: []}`, `humanVerificationCard: []`.
- **Bucket 2 (External tool or login expired / unavailable on runner):**
  - Trigger when `realBindingUnavailable` is `true` OR any diagnostic (case-insensitive) matches:
    - `gcloud`: `"reauthentication required"`, `"gcloud auth login"`, `"invalid_grant"`, `"do not currently have an active account"` → `cooldownTool: "gcloud"`, `checkCommand: "gcloud auth list --filter=status:ACTIVE --format='value(account)'"`.
    - `aws`: `"token has expired"`, `"expiredtoken"`, `"unable to locate credentials"`, `"sso session"`, `"aws sso login"` → `cooldownTool: "aws"`, `checkCommand: "aws sts get-caller-identity"`.
    - `docker`: `"cannot connect to the docker daemon"`, `"docker daemon is not running"`, `"is the docker daemon running"` → `cooldownTool: "docker"`, `checkCommand: "docker info"`.
    - Auth/secret failure: `"401 unauthorized"`, `"invalid api key"`, `"expired api key"`, `"missing env"`, `"secret not set"`, `"credentials not configured"` → `cooldownTool`: lowercased nonblank `toolHint` if supplied, else `"stripe"` if diagnostics mention `"stripe"`, else `"auth"`; `checkCommand`: nonblank `verifyCommand` if supplied, else `"env | grep -i token"`.
    - Service connection refused: `"connection refused"`, `"econnrefused"` → `cooldownTool`: lowercased nonblank `toolHint` if supplied, else `"postgres"` if diagnostics mention `"postgres"` or `"5432"`, else `"service"`; `checkCommand`: nonblank `verifyCommand` if supplied, else `"pg_isready"` (for `"postgres"`) or `"curl -sf http://127.0.0.1"`.
    - `real-binding-unavailable` (`realBindingUnavailable: true` or diagnostic contains `"real-binding-unavailable"`): `cooldownTool`: lowercased nonblank `toolHint` if supplied, else `"runtime-binding"`; `checkCommand`: nonblank `verifyCommand` if supplied, else `"pdd test --files"`.
  - Recognize as an environment/auth blocker, NEVER a code defect: `bucket: 2`, `decision: "park-auth-wait"`, `waitKind: "auth-environment"`, `eligible: false`, `freeSlot: true`, `keepPr: true`, `repairRoundsToSpend: 0`, `repairAttemptsNext: repairAttempts`, `resumeMode: "validate-only-same-head"`, `proof: {surfaces: [], commands: [], exitCodes: []}`, `humanVerificationCard: []`, and `message` as 1 concise sentence naming `cooldownTool` and `checkCommand`.
- **Bucket 3 (Needs human interaction OR zero runnable E2E):**
  - Trigger when `needsHumanInteraction` is `true` or diagnostics mention browser OAuth click, `2fa`, `mfa`, `captcha`, `live payment`, or `physical hardware` (`waitKind: "human-boundary"`), OR when `requiresRealE2e` is `true` and zero real E2E checks executed (including mock-only tests) or `isBugFix` is `true` with `bugFixBaseControl === "not-run"` (`waitKind: "missing-e2e"`).
  - Hard-stop in BOTH `auto` and `observe` modes: `bucket: 3`, `decision: "needs-person"`, `eligible: false`, `freeSlot: true`, `keepPr: true`, `repairRoundsToSpend: 0`, `repairAttemptsNext: repairAttempts`, `cooldownTool: null`, `resumeMode: "none"`, `checkCommand: null`, `proof: {surfaces: [], commands: [], exitCodes: []}`, and `humanVerificationCard` containing **exact 3 nonblank lines**:
    1. `"Passed offline: <offlineSummary or 'none'>"`
    2. `"Unverified boundary: <humanBoundaryDetail or detected unverified surfaces>"`
    3. `"Verify command: <verifyCommand or a single concrete verification command>"`
- **Tool cooldown intake guard (`shouldClaimWithCooldowns`):** Normalize tool keys by trimming and lowercasing. If any tool in `issueRequiredTools` matches a `toolCooldowns` entry with `active: true`, return `{claimable: false, blockedByTool: <first matching normalized tool>, reason: "tool-cooldown"}`. Otherwise return `{claimable: true, blockedByTool: null, reason: null}` so freed workers immediately pick up unrelated issues.
- **Auto-resume without rebuilding (`planValidationResume`):**
  - If `currentPrHeadSha !== headSha`, refuse validate-only resume: `{action: "head-changed-abort", pr, headSha, rebuildCode: false, runValidationOnly: false, clearCooldown: false, targetTool: cooldownTool}`.
  - If `preflightExitCode === 0` or `userResumed === true`, resume validate-only at the exact saved commit head with zero code rebuild: `{action: "resume-validate-only", pr, headSha, rebuildCode: false, runValidationOnly: true, clearCooldown: true, targetTool: cooldownTool}`.
  - Otherwise keep parked: `{action: "stay-parked", pr, headSha, rebuildCode: false, runValidationOnly: false, clearCooldown: false, targetTool: cooldownTool}`.
- **Backside deterministic validation lint (`lintValidationCode`):**
  - `silent-validation-skip` (applies to `kind: "code"` and `kind: "test"`): flag code or tests that rewrite or excuse `real-binding-unavailable` as a local skip, pass, or non-blocker (such as `"local skip"`, `"not a defect or needs-person blocker"`, `localSkipRow`, or filtering `real-binding-unavailable` out of refusals) or unconditionally skip an E2E/validation test (`test.skip(`, `it.skip(`, `t.skip(` on validation/e2e tests).
  - `boundary-mock-only-test` (applies to `kind: "test"`): when the test targets a boundary surface (`cli`, `api-server`, `database`, `web-ui`, or `external-tool`, detected from its path or imported production module paths), uses mocks/stubs/fakes (`mock.`, `vi.mock`, `jest.mock`, `sinon.stub`, `fakeClient`, `fakeServer`, `fakeTransport`, or stubbed handlers), contains zero real execution calls (`spawn`, `spawnSync`, `execFile`, `execFileSync`, `createServer`, `listen(`, `fetch(`, `http.request`, `playwright`, `chromium.launch`, `page.goto`), AND `hasRealE2eCoverage` is `false`, emit `boundary-mock-only-test`. When `hasRealE2eCoverage` is `true` OR the test itself runs real end-to-end execution, do NOT emit `boundary-mock-only-test`.
  - Return `{ok: codes.length === 0, codes, warnings}` with `codes` sorted uniquely and each warning formatted `"Warning: validation lint: <path>:<line> [<code>] <detail>"`.

## Public contract

Export:

- `MAX_VALIDATION_REPAIRS = 3`.
- `detectChangedSurfaces({changedFiles})` → `{surfaces, runtimeSurfaces, docsOnly, requiresRealE2e, requiredProofKinds}`.
- `evaluateValidationOutcome({mode, changedFiles, isBugFix, offlinePassed, offlineSummary?, e2eChecks, bugFixBaseControl, diagnostics, realBindingUnavailable, needsHumanInteraction, humanBoundaryDetail?, verifyCommand?, toolHint?, lintBlockingCodes, repairAttempts})` → `{bucket, decision, waitKind, eligible, freeSlot, keepPr, repairRoundsToSpend, repairAttemptsNext, cooldownTool, resumeMode, checkCommand, message, proof, humanVerificationCard}`.
- `formatHumanVerificationCard({offlineSummary, unverifiedBoundary, verifyCommand})` → 3-element string array (`["Passed offline: …", "Unverified boundary: …", "Verify command: …"]`).
- `shouldClaimWithCooldowns({issueRequiredTools, toolCooldowns})` → `{claimable, blockedByTool, reason}`.
- `planValidationResume({pr, headSha, currentPrHeadSha, cooldownTool, preflightExitCode, userResumed})` → `{action, pr, headSha, rebuildCode, runValidationOnly, clearCooldown, targetTool}`.
- `lintValidationCode({path, kind, text, hasRealE2eCoverage})` → `{ok, codes, warnings}`.

## Failure and safety boundaries

- Treat malformed or missing E2E check fields (`executed !== true`, non-integer `exitCode`, `passed <= 0`, `failed > 0`, `skipped > 0`, or `kind === "unit-mock"`) as non-passing real E2E evidence (fail closed).
- Never allow `"auto"` or `"observe"` mode to return `eligible: true` when `requiresRealE2e` is `true` and real E2E did not run and pass 100%.
- Never load rules from `origin/main` or require an internal smoke repository.

## Dependencies

None. This is a pure universal policy module with zero native-only, network, or external repository dependencies; Autopilot core and repo hygiene lint depend on this contract.
