# PDD Architecture Map

In `pdd`, prompts are the source of truth and code follows them.
Every behavior prompt in `prompts/` declares the files it owns in its `claims:` frontmatter.
Run `node bin/pdd.mjs owner <path>` before you edit any file to see which prompt owns it.
Check the shared helpers table below before you write any file, GitHub, secret, or state helper.

## Six Core Domains

```mermaid
flowchart TD
  subgraph D1["1. CLI and Routing"]
    CLI["bin/pdd.mjs, pdd-cli.mjs<br/>command-catalog.mjs, argument-parser.mjs"]
  end

  subgraph D2["2. Preflight, Lint and Contracts"]
    LINT["runtime-preflight.mjs, contracts.mjs<br/>runtime-bindings.mjs, project-files.mjs"]
  end

  subgraph D3["3. Runtime Client and Native Replay"]
    RUN["runtime-client.mjs, try-doors.mjs<br/>screen-compare.mjs, product.mjs"]
  end

  subgraph D4["4. Workflow Gates and Runs"]
    WF["workflow-runner.mjs, workflow-runs.mjs<br/>workflow-replay.mjs, workflow-prove.mjs"]
  end

  subgraph D5["5. Autopilot Core and Machine Guard"]
    AUTO["autopilot-launcher.mjs, autopilot-core.mjs<br/>agent-job.mjs, issue-dependencies-github.mjs"]
  end

  subgraph D6["6. Shared Foundations"]
    BASE["secret-redaction.mjs, github-calls.mjs<br/>file-owner.mjs, cost-ledger.mjs, scenario-json.mjs"]
  end

  CLI --> LINT
  CLI --> RUN
  CLI --> WF
  CLI --> AUTO
  WF --> LINT
  WF --> RUN
  AUTO --> WF
  LINT --> BASE
  RUN --> BASE
  WF --> BASE
  AUTO --> BASE
```

### Domain Guide

1. **CLI & Routing** (`bin/pdd.mjs`, `pdd-cli.mjs`, `command-catalog.mjs`, `argument-parser.mjs`, `completion.mjs`, `skills-install.mjs`, `project-setup.mjs`, `agent-mcp-setup.mjs`, `interpreter-version.mjs`)
   Parses command flags, routes public commands, prints help, and installs skills or project settings.
2. **Preflight, Lint & Contracts** (`runtime-preflight.mjs`, `runtime-markdown.mjs`, `contracts.mjs`, `contract-refs.mjs`, `interface-draft.mjs`, `prompt-approve.mjs`, `runtime-bindings.mjs`, `runtime-binding-plan.mjs`, `project-files.mjs`, `svg-layout.mjs`)
   Parses prompts, validates `pdd-interface` blocks, checks approvals, resolves bindings, and checks SVG or JSON contracts.
3. **Runtime Client & Native Replay** (`runtime-client.mjs`, `runtime-check-plan.mjs`, `runtime-outcome.mjs`, `runtime-output.mjs`, `runtime-slots.mjs`, `runtime-lint-receipt.mjs`, `try-doors.mjs`, `try-http.mjs`, `try-mcp.mjs`, `screen-compare.mjs`, `agent-chat.mjs`, `product.mjs`, `product-composition.mjs`)
   Runs `pdd test`, `pdd lint`, `pdd simulate`, `pdd try`, `pdd chat`, and multi-part `pdd product` checks.
4. **Workflow Gates & Runs** (`workflow-runner.mjs`, `workflow-runs.mjs`, `workflow-worktree.mjs`, `workflow-chat.mjs`, `workflow-story-card.mjs`, `workflow-replay.mjs`, `workflow-results.mjs`, `workflow-prove.mjs`, `workflow-pr-body.mjs`, `workflow-pr-evidence.mjs`, `workflow-github.mjs`, `workflow-view.mjs`, `workflow-inventory.mjs`)
   Manages isolated worktrees, PR 1 and PR 2 gates, saved replay evidence, native proof, and readable PR bodies.
5. **Autopilot Core & Machine Guard** (`autopilot-launcher.mjs`, `autopilot-core.mjs`, `agent-job.mjs`, `autopilot-doctor.mjs`, `autopilot-intake.mjs`, `autopilot-alerts.mjs`, `autopilot-reports.mjs`, `autopilot-regressions.mjs`, `autopilot-audit.mjs`, `autopilot.mjs`, `issue-dependencies-github.mjs`, `issue-dependency-graph.mjs`, `issue-sort.mjs`)
   Polls ready GitHub issues, checks machine capacity and slots, runs isolated agent jobs, and writes status reports.
6. **Shared Foundations** (`secret-redaction.mjs`, `github-calls.mjs`, `file-owner.mjs`, `cost-ledger.mjs`, `path-diagnostic.mjs`, `scenario-json.mjs`, `approval-policy.mjs`, `approval-evidence.mjs`, `runtime-workspace.mjs`, `agent-adapters.mjs`, `agent-packet.mjs`, `machine-resources.mjs`, `test-suite-queue.mjs`, `metrics-store.mjs`)
   Provides one shared home for secret redaction, GitHub API budgets, ownership lookup, cost ledgers, exact JSON, and machine checks.

## Where to Put Things

| Path | What Belongs Here | Rule |
| :--- | :--- | :--- |
| `prompts/cli/*.prompt.md` | Module behavior specs and Runtime `pdd-interface` contracts. | Declare owned files in `claims:`. Keep prose clear and free of code details. |
| `src/*.mjs` | ESM modules using `node:*` built-in packages only. | Follow the owning prompt in `prompts/cli/`. Reuse helpers from Domain 6. |
| `bin/pdd.mjs` | Thin CLI entry script. | Keep startup minimal and delegate routing to `src/pdd-cli.mjs`. |
| `user_stories/*.md` | Human-readable product Stories with `## Acceptance criteria`. | Describe user outcomes, not helper unit checks. Add a ````pdd-boundary` block when linking docs. |
| `test/runtime/*.json` | Paid Runtime scenario fixtures paired with `user_stories/<slug>.md`. | Reserve for user-facing Story checks that exercise a Runtime `pdd-interface`. |
| `test/*.test.mjs` | Fast deterministic `node:test` suites and regression checks. | Put helper checks, parser vectors, edge cases, and state rules here. Run with `test/helpers/test-home.mjs`. |
| `skills/<name>/SKILL.md` | Agent workflow playbooks (`pdd-prompting`, `pdd-feature`, `pdd-bug`, `pdd-small-change`, `pdd-product`, `pdd-setup`, `pdd-graph`). | Keep steps short and aligned with `docs/cli.md`. |
| `docs/*.md` | User-facing reference guides (`cli.md`, `prompting-guide.md`, `replay-evidence.md`). | Write for a first-time reader in the present tense. Do not add version history notes. |
| `~/.pdd/` (outside git) | Local workflow runs, GitHub ETag caches, cost ledgers, and Autopilot state. | Never commit runtime state, logs, receipts, or evidence JSON to a git repository. |

## Canonical Shared Helpers (Reuse, Do Not Duplicate)

Import these existing helpers instead of writing private copies inside feature modules.

| Need | Canonical Module | Exported Functions to Reuse |
| :--- | :--- | :--- |
| **Secret redaction** | `src/secret-redaction.mjs` | `redactSecrets(text, extra)`, `rememberSecrets(values)`, `redactingValues(extra)`, `knownSecretValues()` |
| **GitHub API calls, pagination & budget** | `src/github-calls.mjs` | `githubCall(spec, run)`, `githubListItems(spec, runPage)`, `githubEtagCache()`, `githubBudget()`, `githubFloorGuard()`, `countGithubCalls()` |
| **File & prompt ownership lookup** | `src/file-owner.mjs` | `resolveOwners(root, paths)`, `findOwners(root, paths)`, `promptClaims(root)`, `headerPrompts(root)` |
| **Workflow run state, atomic writes & Git root** | `src/workflow-runs.mjs` | `readRun(dir)`, `writeRun(dir, run)`, `updateRun(dir, fn)`, `resolveRun(opts)`, `stateDirFor(repo)`, `gitContext(cwd)` |
| **Run, batch & mode file locks** | `src/workflow-runner.mjs`, `src/autopilot-launcher.mjs`, `src/runtime-client.mjs` | `acquireRunLock(...)`, `withAutopilotModeLock(...)`, `acquireRuntimeBatchLock(...)` |
| **Exact JSON parse & stringify (64-bit safe)** | `src/scenario-json.mjs` | `parseScenarioJson(text)`, `stringifyScenarioJson(value)`, `jsonSafe(value)`, `withExactIntegers(value)` |
| **Prompt reading, interface blocks & SHA-256** | `src/runtime-preflight.mjs` | `readPrompt(path)`, `interfaceBlocks(markdown)`, `proseSha256(text)`, `sha256(bytes)`, `preflight(opts)` |
| **Path refusal & symlink diagnostics** | `src/path-diagnostic.mjs` | `pathDiagnostic(targetPath, opts)` |
| **Token, Runtime & GitHub cost ledger** | `src/cost-ledger.mjs` | `captureCosts(...)`, `applyCostMeasurement(...)`, `recordCostGithub(...)`, `costReport(...)`, `costStatusLines(...)` |
| **Prompt approvals & policy** | `src/approval-policy.mjs` | `readApprovalPolicy(root)`, `readPromptApprovals(root)`, `recordPromptApproval(root, entry)`, `approvalActor(env)` |
| **Saved native session & approval evidence** | `src/approval-evidence.mjs` | `readApprovalEvidence(opts)`, `findNativeSessions(opts)` |
| **Bounded workspace & path guards** | `src/runtime-workspace.mjs` | `loadRuntimeWorkspace(root)`, `allowsRuntimePath(ws, target)`, `requireRuntimePath(ws, target)` |
| **Agent CLI discovery, auth & stdin packets** | `src/agent-adapters.mjs`, `src/agent-packet.mjs` | `discoverAgents(opts)`, `parseAgentAuthStatus(...)`, `runAgentProcess(...)`, `askAgent(...)`, `buildAgentInput(...)` |
| **Machine CPU/RAM checks & shared suite queue** | `src/machine-resources.mjs`, `src/test-suite-queue.mjs` | `readMachineResources()`, `runTestSuite(opts)`, `calculateCheckCapacity(...)`, `readCheckStatus(...)` |
| **Metrics event log & snapshots** | `src/metrics-store.mjs` | `appendEvents(...)`, `readEvents(...)`, `exportMetrics(...)`, `importMetrics(...)`, `validateSnapshot(...)` |

> **State file rule:** Do not add another private temp-file `writeFileSync` + `renameSync` helper, private `JSON.parse(readFileSync(...))` wrapper, or local `gh api --include` header parser. Reuse `writeRun` / `updateRun` for workflow state, `parseScenarioJson` / `stringifyScenarioJson` for exact JSON, `sha256` from `src/runtime-preflight.mjs`, and `githubCall` / `githubListItems` from `src/github-calls.mjs`.

## Layering and Test Boundaries

Keep dependencies flowing downward toward Domain 6 (`Shared Foundations`):

- **Domain 6 stays leaf-level.** Modules in Shared Foundations (`secret-redaction.mjs`, `github-calls.mjs`, `file-owner.mjs`, `scenario-json.mjs`, `path-diagnostic.mjs`) must not import CLI routers, workflow runners, or Autopilot modules.
- **Domain 2 stays local and fast.** Preflight, lint, and contract checks (`runtime-preflight.mjs`, `contracts.mjs`, `runtime-bindings.mjs`) inspect repo files without paid network calls.
- **Paid Runtime Story vs. Native Unit Test:**
  - Create a `user_stories/<slug>.md` + `test/runtime/<slug>.json` pair only for real user-facing product behavior that exercises an entry prompt's `pdd-interface`.
  - Always add a ````pdd-boundary` block in a Story when linking `AGENTS.md`, `RUNBOOK.md`, or reference docs so `pdd test` checks only the Story's own prompt closure.
  - Put parser edge cases, JSON field checks, state-file locks, and shared helper rules in fast native `test/*.test.mjs` files instead of separate micro-Stories.

## Before You Open a Pull Request

1. Run `node bin/pdd.mjs owner <file>` on every file you plan to edit.
2. Update the owning prompt first when module behavior or contracts change.
3. Reuse the canonical helpers above instead of writing duplicate GitHub, hash, secret, or state helpers.
4. Run focused tests on your machine (`node --import ./test/helpers/test-home.mjs --test test/<file>.test.mjs`).
5. Run the full test suite on the runner VM, not on a laptop.
6. State exact `+added / -removed` line counts in your PR description and keep diffs small.
