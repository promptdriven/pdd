# Codex readability and quality lint

Own `src/codex-lint.mjs`. Export `runCodexLint({cwd, words, timeoutMinutes, json, env}, ports)` and `buildCodexLintPrompt(files)`. Run local deterministic project lint together with read-only Codex readability and quality checks on selected `.prompt.md` and `user_stories/*.md` files, printing clear per-file `PASS` / `FAIL` verdicts and a final summary line (or `schema_version: "pdd.codex-lint.v1"` JSON with `--json`).

## Selection and workspace safety

Require a Git repository root (`git rev-parse --show-toplevel` with a 10-second timeout, else exit 2). Apply `workspace.policy({root: realRoot})`, `workspace.allows(policy, path)`, `!isSecretPath(path)`, and regular in-root no-symlink file reads. Without `words`, select all non-fixture Git-visible `.prompt.md` and `isLintableStoryPath` files. With `words`, accept repository or `cwd`-relative prompt/Story file or directory paths and Story names (including prompts reached by matching scenario JSON files); refuse any unmatched word on `stderr` with exit 2 before invoking Codex.

## Evaluation and output

1. Run `lintRepoProject` on the selected scope. Deterministic `errors` fail their owning file immediately; advisory `warnings` stay visible without failing passing files.
2. Strip machine-generated `Runtime interface` blocks from prompt text and redact `knownSecretValues(env)` via `redactSecrets` before building the Codex review prompt so Codex grades human-authored prose, domain clarity, scannability, diagrams/tables where needed, and concrete user-facing Story acceptance criteria without receiving secret values.
3. Clamp `timeoutMinutes` to `[0.1, 120]` under a single overall deadline across batches (`Math.max(1000, deadline - now())` per batch, stopping with a timeout diagnostic and exit 1 once the deadline expires). Scrub GitHub/PDD/NPM/cloud/API credential variables (`GH_*`, `GITHUB_*`, `PDD_*TOKEN*`, `NPM_TOKEN`, `AWS_SECRET_ACCESS_KEY`, `AWS_SESSION_TOKEN`, `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`) and parent session markers (`CODEX_THREAD_ID`, `CODEX_SANDBOX*`, `CLAUDECODE`, `CLAUDE_CODE_*`, `CLAUDE_PID`, `HERDR_*`, `PDD_AGENT_SESSION`, `PDD_AUTOPILOT_CONTEXT`) from the child environment. Invoke Codex in read-only mode via `runStepAgentProcess` (`codex exec --sandbox read-only --skip-git-repo-check --ephemeral --color never --ignore-rules -c 'approval_policy="never"' -c 'web_search="disabled"' -c 'mcp_servers={}' --output-last-message <resolved-tmp> -- -`, step `review`), allowing `ports.runAgentProcess` injection for offline tests.
4. Redact all verdict summaries, issue messages, warnings, and error diagnostics through `redactSecrets(..., knownSecretValues(env))` before writing to `stdout` or `stderr`. Print `PASS <path> — <summary>` or `FAIL <path> — <summary>` with indented `<path>:<line> [<rule>] <message>` lines and `Lint (Codex): PASS|FAIL (<passed>/<total> files passed…)`, returning exit 0 when all pass and exit 1 when any file fails or Codex cannot run.

## Dependencies

- [Repo hygiene and extensible project lint](repo-hygiene-lint.prompt.md): required generation context for `lintRepoProject` and `stripPromptMetadata`.
- [Story quality lint](story-lint.prompt.md): required generation context for `isLintableStoryPath`.
- [Agent adapters](agent-adapters.prompt.md): required generation context for `runStepAgentProcess`.
- [Secret redaction](secret-redaction.prompt.md): required generation context for `knownSecretValues` and `redactSecrets`.
- [PDD to Runtime seam](runtime-seam.prompt.md): required generation context for `causeText`, `gitFiles`, `isSecretPath` and `workspace`.
