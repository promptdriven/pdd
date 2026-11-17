# Autopilot pre-run repository forensics

Own `src/autopilot-forensics.mjs`. Provide deterministic external-repository label
skip helpers, a linear string-aware JSON object scanner across agent CLI logs, and
a fast, bounded read-only repository forensics pass on the fresh `origin/BASE`
worktree right before [Autopilot core](autopilot-core.prompt.md) starts a build
(#3454).

## External-repository and configured skip labels

- `EXTERNAL_REPO_LABELS` is `["external", "other-repo", "elsewhere", "pdd:elsewhere"]`.
- `findExternalRepoLabel(labels)` inspects an issue row or label array (strings or
  `{name}` objects) case-insensitively on trimmed label names and returns the
  matched trimmed label name or `null`, with zero AI calls and zero hardcoded
  directory or path-guessing rules.
- `findConfiguredSkipLabel(labels, skipLabels)` matches optional configured
  `autopilot.skipLabels` entries case-insensitively on trimmed nonblank strings and
  returns the matched trimmed label name or `null`.

## Linear JSON extraction across agent harnesses

- `extractJsonObjects(value)` scans text in one linear `O(N)` pass while tracking
  brace depth, JSON string literals (entered inside balanced braces so stray quotes
  in surrounding log prose never swallow objects), and backslash escapes, returning
  every valid top-level plain JSON object in order.
- `parseForensicsText(value)` inspects extracted objects from newest to oldest across
  direct JSON answers, Codex `--output-last-message` text, Claude single-line or
  multiline `--output-format json` / `stream-json` envelopes (`result` string,
  rejecting `is_error: true`), Gemini `--output-format json` envelopes (`response`
  string), and Antigravity JSON outputs, returning the last plain object with a
  Boolean `already_fixed` field or `null`.

## Pre-run repository forensics

- Right before launching a new build on a freshly created `origin/BASE` worktree,
  Autopilot asks one grounded question against real files and tests on disk:
  **"Is this issue already fixed on `BASE` right now, or does it still happen?"**
- `forensicsEnvironment(env)` applies `jobEnvironment(env)` and strips every
  `GH_*TOKEN` and `GITHUB_*TOKEN` variable so the forensics subprocess has zero
  GitHub write credentials.
- `forensicsCommand(agent, {model, reasoningEffort, resultFile})` builds a bounded
  read-only headless CLI invocation for every supported Autopilot agent kind:
  - `codex`: `exec --ignore-user-config --sandbox read-only --ephemeral --color never`
    with `approval_policy="never"`, `web_search="disabled"`, `mcp_servers={}`,
    `model_reasoning_effort` (`low` default), non-essential agent features disabled (preserving `code_mode_host` so read-only tool inspection works),
    optional `--output-last-message FILE`, optional `--model MODEL`, and `-` stdin.
  - `claude`: `-p --safe-mode --tools Read,Glob,Grep --permission-mode plan
    --permission-prompts none --strict-mcp-config --no-chrome
    --no-session-persistence --output-format json` with optional `--effort` and
    `--model`.
  - `gemini`: `-p "" --output-format json --approval-mode plan --extensions none
    --allowed-mcp-server-names pdd-disabled-none` with optional `--model`.
  - `agy`: `--input-format text --output-format json --mode plan --sandbox
    --disable-slash-commands` with optional `--effort` and `--model`.
  Unknown agent kinds throw an Error.
- `runPreRunForensics(input, ports)` runs in `cwd: worktree` with a bounded timeout
  (default 90 seconds, 128 KiB output cap), honors optional worker-tier model
  routing via `resolveStepModelTier` (`step: "intake"`) and pooled/Cloud step
  overlays (`selected.prepareStep`, always cleaned up in `finally`), reports quota
  exhaustion to `ports.exhaustLogin` when applicable, and fails open to
  `already_fixed: false` (`disposition: "still_needed"`) on any error, timeout,
  non-zero exit without valid proof, or uncertainty so real bugs are never skipped.

## Proof gate, comment safety, and builder brief

- `evaluateForensicsResult(parsed, {worktree, fs})` normalizes candidate repository
  paths via `normalizeAreaList` and verifies that each cited path resolves strictly
  inside `worktree` and exists on disk as a regular file (`statSync(full).isFile()`).
- `already_fixed: true` (`disposition: "fixed"`) is accepted **only** when
  `parsed.already_fixed === true`, at least one cited path in `verifying_files` or
  `verifying_tests` exists as a regular file on disk in `worktree`, and sanitized
  `summary` or `evidence` is non-empty. Missing disk file proof or blank evidence
  downgrades safely to `already_fixed: false` (`disposition: "still_needed"`,
  `status: "unverified_proof"`).
- `stripForbiddenIdentifiers(text)` and `formatForensicsComment({issue, baseBranch,
  result})` redact secrets and strip commit hashes, SHA-256 digests, and UUIDs from
  all user-facing comment fields and end with the non-hash hidden marker
  `<!-- pdd:autopilot-forensics:fixed:ISSUE -->`.
- When `already_fixed` is `false`, `formatForensicsBrief(result, baseBranch)`
  formats verified existing `target_files`, `verifying_tests`, `summary`, and
  `reproduction` notes so the builder prompt starts grounded on `origin/BASE`.

## Public contract

- Export `EXTERNAL_REPO_LABELS`, `FORENSICS_FIXED_MARKER_PREFIX`,
  `forensicsFixedMarker`, `findExternalRepoLabel`, `findConfiguredSkipLabel`,
  `extractJsonObjects`, `parseForensicsText`, `stripForbiddenIdentifiers`,
  `forensicsEnvironment`, `forensicsCommand`, `forensicsPrompt`,
  `evaluateForensicsResult`, `formatForensicsComment`, `formatForensicsBrief`, and
  `runPreRunForensics`.

## Dependencies

- [Agent adapters](agent-adapters.prompt.md): required for `runAgentProcess` bounded
  subprocess execution.
- [Headless job runner](agent-job.prompt.md): required for `jobEnvironment`.
- [Areas](autopilot-areas.prompt.md): required for `normalizeAreaList` path
  normalization.
- [Autopilot telemetry](autopilot-telemetry.prompt.md): required for
  `resolveStepModelTier` worker-tier model routing.
- [Multi-harness login pool](login-pool.prompt.md): required for
  `isQuotaExhaustionMessage` and `isAuthFailureMessage` when rotating pooled logins.
- [Secret redaction](secret-redaction.prompt.md): required for `redactSecrets` on
  user-facing comment text and builder briefs.
