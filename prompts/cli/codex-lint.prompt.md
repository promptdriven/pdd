# Codex readability and quality lint

Own `src/codex-lint.mjs`. Export `runCodexLint({cwd, words, issue, timeoutMinutes, json, env}, ports)`, `buildCodexLintPrompt(files, options)`, `groupCodexLintBatches(targetEntries, promptsByStory, maxPerBatch)`, `runAiLint`, `buildAiLintPrompt`, `groupAiLintBatches`, and `runAdaptiveAiLint` (re-exported from `src/autopilot/ai-lint.mjs`; read-only providers are `codex`, `claude`, and `gemini`). Run local deterministic project lint together with read-only Codex readability, semantic Story-vs-Prompt alignment, and optional issue-coverage checks on selected `.prompt.md` and `user_stories/*.md` files, printing clear per-file `PASS` / `FAIL` verdicts, an optional `Issue coverage` verdict, and a final summary line (or `schema_version: "pdd.codex-lint.v1"` JSON with `--json`).

## Selection and workspace safety

Require a Git repository root (`git rev-parse --show-toplevel` with a 10-second timeout, else exit 2). Apply `workspace.policy({root: realRoot})`, `workspace.allows(policy, path)`, `!isSecretPath(path)`, and regular in-root no-symlink file reads (`lstatSync` across every path component, `openSync(..., O_NOFOLLOW)`, and `fstatSync` `dev`/`ino` parity plus bounded byte size). Always discover scenario JSON files (`tests/*.json`, `test/*.json`, `__tests__/*.json`, excluding fixture directories) to build `promptsByStory` and `scenariosByStory` both when `words` is empty and when `words` is supplied, resolving `entry_path`, `entry_paths`, `steps[].entry_path` and `context`, and resolving omitted Short JSON `story_path` by unique Story filename-stem pairing. Without `words`, select all non-fixture Git-visible `.prompt.md` and `isLintableStoryPath` files. With `words`, accept repository or `cwd`-relative prompt/Story file or directory paths and Story names (expanding selected Stories to their scenario-referenced prompts); refuse any unmatched word on `stderr` with exit 2 before invoking Codex.

## Batching and Story-vs-Prompt alignment

`groupCodexLintBatches(targetEntries, promptsByStory, maxPerBatch = 6)` returns an array of `{entries, pairs}` batches where each `pairs` item is `{story, prompts}`:

- Never split a Story across batches from its selected scenario-referenced `.prompt.md` files, even when `1 + prompts.length > maxPerBatch` (keep them together in one dedicated batch).
- When a `.prompt.md` file is shared by two Stories in different batches, grade it once in its first batch and attach it with `contextOnly: true` in later batches so later Stories receive full Story-vs-Prompt checking without duplicating or overwriting the prompt's verdict.
- Pack standalone prompts cleanly up to `maxPerBatch`.

`buildCodexLintPrompt(files, {secrets, pairs, issueContext, scenarios, otherFilesOutline})` keeps single-argument `buildCodexLintPrompt(files)` backwards-compatible. When `pairs` is non-empty, include a `=== STORY-PROMPT PAIRS ===` section, label any `contextOnly: true` file so Codex omits a verdict entry for it, and instruct Codex to verify every Story acceptance criterion and `## Rules to check` invariant against the paired prompt's rules and `## Domain decisions`, flagging missing rules, conflicting defaults or error behavior, or silent scope drift with `rule: "story-prompt-mismatch"`.

## Optional issue-coverage check (`--issue`)

When `issue` is supplied, resolve it before invoking Codex:

| `--issue` value | Source & safety check | Error exit |
|---|---|---|
| Positive integer (`/^[1-9]\d*$/`) | `ports.readIssue` if injected, else `execFileSync('gh', ['issue', 'view', N, '--json', 'number,title,body'], {cwd: realRoot, env, timeout: 15_000})` (parent `env` for `gh`; child Codex env stays scrubbed) | Exit `1` if unreadable or empty |
| Zero, leading-zero, signed digits, or leading `-` | Refused immediately before any external call or file lookup (prefix literal leading-dash filenames with `./`) | Exit `2` |
| Local file path | `cwd`-relative or repo-relative regular non-symlink UTF-8 text file inside the repository (`workspace.allows(policy, path)`, `!isSecretPath`, no NUL binary bytes, max 128 KiB, component `lstatSync` + `O_NOFOLLOW` + `fstatSync` `dev`/`ino` parity) | Exit `2` if escaping repo, disallowed by workspace policy, symlinked, secret, binary, oversized, unreadable, or empty |

Redact secrets from issue text (bounded to 16,000 chars) and from bounded matching scenario JSON summaries for the selected Stories (`scenarios`, prioritizing the active batch's Stories and parsing compact JSON fields before secret redaction), attaching both (plus compact outlines of other selected files on multi-batch runs) to `buildCodexLintPrompt` strictly as untrusted data. Extend the expected Codex JSON schema only when `issueContext` is set with `issue_coverage: {status: "pass"|"fail", summary, missed: [{requirement, rule: "issue-requirement-missed", message}]}`. Fail closed with exit 1 when Codex omits `issue_coverage`, when `missed` is missing, not an array, or contains malformed elements, when `status` is invalid or `"fail"`, when `missed` is non-empty, or when zero files are selected for an issue check.

## Evaluation and output

1. Run `lintRepoProject` on the selected scope. Deterministic `errors` fail their owning file immediately; advisory `warnings` stay visible without failing passing files.
2. Strip machine-generated `Runtime interface` blocks from prompt text and redact `knownSecretValues(env)` via `redactSecrets` before building the Codex review prompt so Codex grades human-authored prose, domain clarity, scannability, diagrams/tables where needed, concrete user-facing Story acceptance criteria (explicitly inspecting the entire Story including fenced code blocks, failing pasted implementation code or internal plumbing while instructing authors to move implementation details to the owning `.prompt.md` and large sample fixtures to `tests/` or `fixtures/`, and allowing exact values or short examples when they define what the user actually sees), Story-vs-Prompt alignment, and optional issue coverage without receiving secret values.
3. Clamp `timeoutMinutes` to `[0.1, 120]` under a single overall deadline across batches (`Math.max(1000, deadline - now())` per batch, stopping with a timeout diagnostic and exit 1 once the deadline expires). Scrub GitHub/PDD/NPM/cloud/API credential variables (`GH_*`, `GITHUB_*`, `PDD_*TOKEN*`, `NPM_TOKEN`, `AWS_SECRET_ACCESS_KEY`, `AWS_SESSION_TOKEN`, `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`) and parent session markers (`CODEX_THREAD_ID`, `CODEX_SANDBOX*`, `CLAUDECODE`, `CLAUDE_CODE_*`, `CLAUDE_PID`, `HERDR_*`, `PDD_AGENT_SESSION`, `PDD_AUTOPILOT_CONTEXT`) from the child environment. Invoke Codex in read-only mode via `runStepAgentProcess` (`codex exec --sandbox read-only --skip-git-repo-check --ephemeral --color never --ignore-rules -c 'approval_policy="never"' -c 'web_search="disabled"' -c 'mcp_servers={}' --output-last-message <resolved-tmp> -- -`, step `review`), allowing `ports.runAgentProcess` and `ports.readIssue` injection for offline tests.
4. Ignore any Codex verdict row for a `contextOnly: true` path. Redact all verdict summaries, issue messages, issue-coverage fields, warnings, and error diagnostics through `redactSecrets(..., knownSecretValues(env))` before writing to `stdout` or `stderr`. Print `PASS <path> — <summary>` or `FAIL <path> — <summary>` with indented `<path>:<line> [<rule>] <message>` lines; when `issue` is supplied, also print `Issue coverage (<ref>): PASS|FAIL — <summary>` with indented `  [issue-requirement-missed] <requirement>: <message>` lines and include `issue_coverage` in `pdd.codex-lint.v1` JSON (omitting `issue_coverage` when `issue` is absent for backwards compatibility). Print `Lint (Codex): PASS|FAIL (<passed>/<total> files passed…)`, returning exit 0 when all pass and exit 1 when any file fails, issue coverage fails, or Codex cannot run.

## Dependencies

- [Repo hygiene and extensible project lint](repo-hygiene-lint.prompt.md): required generation context for `lintRepoProject` and `stripPromptMetadata`.
- [Story quality lint](story-lint.prompt.md): required generation context for `isLintableStoryPath`.
- [Agent adapters](agent-adapters.prompt.md): required generation context for `runStepAgentProcess`.
- [Secret redaction](secret-redaction.prompt.md): required generation context for `knownSecretValues` and `redactSecrets`.
- [PDD to Runtime seam](runtime-seam.prompt.md): required generation context for `causeText`, `gitFiles`, `isSecretPath` and `workspace`.
