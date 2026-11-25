# Automated non-destructive guard mutation control for `pdd prove --mutation-check`

Own `src/core/prove-mutation.mjs` (Layer-1 Core: imports only Layer-1 `src/core/*`, `file-owner.mjs`, and Layer-0 `src/shared/*`; zero `autopilot/` or `cli/` imports). Generate 1 to 3 deterministic conditional and return guard mutations on changed lines of touched formal-bound production files, execute them strictly inside an isolated temporary copy outside the repository working tree, and fail closed with `Not proved` whenever any formal-covered guard mutation survives.

## Domain decisions

- **Guard mutation generation (`generateGuardMutations`):**
  - Target only changed/added lines (`base..WORKTREE`) in touched canonical production files (`isProductionCodeFile`) that are imported or covered by the passing code-bound formal suite.
  - **Python (`.py`):** Parse exact Python AST via `python3` stdlib `ast.parse` (read-only stdin, zero repo writes) on changed lines — including continuation lines of multiline `if`/`elif`/`while` conditions (matching any `ast.Compare`/`ast.BoolOp`/`ast.If`/`ast.While`/`ast.IfExp`/`ast.Return` whose line span overlaps changed lines and recording enclosing `statementLine` so header-attributed coverage still marks it `formalCovered`) — mutating `ast.Compare` operators (`<` <-> `>=`, `<=` <-> `>`, `==` <-> `!=`, `is` <-> `is not`, `in` <-> `not in`), `ast.BoolOp` (`and` <-> `or`), `ast.If` test negation (`not (...)`), and boolean/None `ast.Return` guards (`True` <-> `False`, `None` -> `0`). Validate every candidate with `ast.parse(mutated)` before emitting.
  - **JS / TS (`.mjs`, `.js`, `.cjs`, `.ts`, `.tsx`, `.jsx`):** Use comment-stripping and string-isolating lexing so strings, template literals, regexes, and comments are never mutated. Mutate changed-line comparison operators (`===` <-> `!==`, `==` <-> `!=`, `<` <-> `>=`, `<=` <-> `>`), boolean operators (`&&` <-> `||`), `if (...)` / ternary guard negation (including continuation lines inside multiline `if`/`while` headers, recording enclosing `statementLine`), and boolean `return true` <-> `return false` guards. Pre-validate JS/MJS/CJS syntax via `node --check` so invalid syntax candidates are discarded before running tests.
  - **Go (`.go`):** Use comment/string-isolating lexing on changed lines to mutate comparison operators (`<` <-> `>=`, `<=` <-> `>`, `==` <-> `!=`), boolean operators (`&&` <-> `||`), `if` guard negation, and `return true` <-> `return false`.
- **Deterministic candidate selection (`selectGuardMutations`):**
  - Rank candidates deterministically by: (1) `formalCovered === true` first, (2) mutation kind priority (`comparison-flip` > `boolean-op-flip` > `guard-negate` > `return-flip`), (3) round-robin spread across distinct files (sorted by path), (4) line number ascending.
  - Cap at `maxMutations` (default `3`, clamped to `1..3`) with at most 1 selected mutation per `(file, line)`. When `formalCoveredLines` is supplied and zero changed guards were covered by the formal suite, fall back to selecting up to `maxMutations` uncovered changed guards from formal-bound files so sham imports cannot pass silently.
- **Outcome classification (`evaluateMutationOutcome`):**

| Observed mutation run outcome | Counts as killed? | Effect on `pdd prove --mutation-check` |
| --- | --- | --- |
| Formal suite exits non-zero with real assertion failure or non-syntax runtime guard throw (`failedOnMutation: true`, `syntaxOnlyCrash: false`, `signal: null`) | Yes (`killed`) | Contributes to kill rate; `Proved` when all selected guard mutations are killed (`attempted > 0`) |
| Formal suite passes (`exitCode === 0`, 0 failures) | No (`survived`) | Fails closed as `Not proved`: `[mutation-survived]` 4-part diagnostic when `formalCovered === true`, or `[mutation-uncovered-guard]` 4-part diagnostic when `formalCovered === false` |
| Syntax, import, or compile crash (`syntaxOnlyCrash: true`) | No (`syntax-error`) | Ignored as non-kill (never inflates `killed`); if zero real assertions were evaluated (`killed === 0 && survived === 0`), fails closed as `Not proved` |
| Timeout, signal interruption, fatal child signal (`SIGKILL`/`SIGABRT`/`SIGSEGV`), or missing runner (`error`) | No (`error`) | Aborts remaining mutations immediately on signal interruption (never misclassifying as `survived`); fails closed as `Not proved` or re-raises parent signal |
| Zero mutable guards on changed lines of formal-bound files | N/A | `status: "not-applicable"`, `ok: true` (never fabricates a kill rate) |

- **Zero workspace pollution guarantee (`runProveMutationCheck`):**
  - Never open or modify any file inside `root`. Create one isolated temporary directory under `os.tmpdir()` (`pdd-prove-mut-`), copy the repository working tree excluding `.git`, `node_modules`, `.venv`, `venv`, `__pycache__`, `.pytest_cache`, and `*.py[co]` (refusing symlinked targets and escaping paths; symlinking real `node_modules` directory read-only when present; resolving repo `.venv/bin/pytest` from `realRoot`).
  - For CLI async execution (`runProveMutationCheckAsync`), run child processes non-blockingly in their own process group so `SIGINT`, `SIGTERM`, and `SIGHUP` immediately kill the active child group, remove the temporary sandbox directory, and re-signal without swallowing the signal or running further mutations; synchronous `runProveMutationCheck` also aborts immediately if any child is terminated by a signal, never misclassifying a signal-killed run as `survived`, and removes the sandbox in `finally`.
  - Apply each mutation sequentially ONLY inside the isolated sandbox copy, execute the discovered formal suite in per-file subprocess isolation (`scrubChildEnv`), and restore the sandbox file before the next mutation.

## Public contract

- `selectGuardMutations({ candidates, formalCoveredLines, maxMutations })` -> `{ selected }` where `selected` is an array of 0 to 3 mutation descriptors `{ id, file, line, kind, description, original, mutated, mutatedContent, formalCovered }` (evaluating `formalCovered` against either `line` or optional enclosing `statementLine`).
- `evaluateMutationOutcome({ results, formalFiles })`:
  - Inputs: `results` array of mutation run records `{ id: string, file: string, line: number, kind: string, description: string, original: string, mutated: string, formalCovered: boolean, executed: boolean, failedOnMutation: boolean, syntaxOnlyCrash: boolean, timedOut?: boolean, missingRunner?: boolean, exitCode: number | null, failedFile?: string | null, summary: string }`, and `formalFiles: string[]`.
  - Classification per record:
    - If `timedOut === true` or `missingRunner === true` or `executed === false`: `outcome: "error"`.
    - Else if `syntaxOnlyCrash === true`: `outcome: "syntax-error"` (ignored as non-kill; increments `syntaxErrors`, never increments `killed`).
    - Else if `failedOnMutation === true`: `outcome: "killed"` (increments `killed`).
    - Else: `outcome: "survived"` (increments `survived`; when `formalCovered === true`, appends `"<file>:<line> [mutation-survived] Formal-covered guard mutation (<description>) survived formal suite (<formalFiles joined by ', '>) with 0 assertion failures. Fix: Strengthen the formal test assertions to cover the guard at <file>:<line>. Rerun: \`pdd prove --mutation-check\`."` to `notProvedReasons`; when `formalCovered === false`, appends `"<file>:<line> [mutation-uncovered-guard] Changed guard mutation (<description>) in formal-bound module was not executed or killed by formal suite (<formalFiles joined by ', '>). Fix: Add formal test inputs and assertions exercising <file>:<line>. Rerun: \`pdd prove --mutation-check\`."` to `notProvedReasons`).
  - Returns `{ status, ok, isolated: true, workingTreeMutated: false, attempted, killed, survived, syntaxErrors, errorsCount, killRate, mutations, notProvedReasons, summary }`:
    - `attempted`: total records in `results`.
    - `status`: `"not-applicable"` when `attempted === 0`; `"not-proved"` when `notProvedReasons.length > 0` or `errorsCount > 0` or (`killed === 0 && survived === 0` with `syntaxErrors > 0`); otherwise `"proved"`.
    - `ok`: `true` when `status === "proved"` or `status === "not-applicable"`, else `false`.
    - `killRate`: percentage rounded to 1 decimal place (`Math.round(killed * 1000 / effectiveAttempted) / 10`), where `effectiveAttempted = killed + survived`, or `null` when `effectiveAttempted === 0`.
- `generateGuardMutations({ root, diffLinesByFile, targetFiles, formalCoveredLines, maxMutations })` -> `{ candidates, selected }`.
- `runProveMutationCheck({ root, baseSha, touchedFiles, diffLinesByFile, formalResult, formalCoverageFiles, baseVerify, maxMutations, timeoutMs, env }, ports)` and async non-blocking `runProveMutationCheckAsync(input, ports, signalCtrl)` -> mutation receipt object matching `evaluateMutationOutcome` plus `mutations[]`.

## Consequential operations

- If `formalResult` already failed (`ok: false` with `errors.length > 0`) or is not code-bound (`tier: "proved_spec_model"`), skip mutation execution (`status: "skipped"`) without masking the primary formal failure.
- If no formal verification applies (`formalResult.applicable === false` and zero formal files), return `status: "not-applicable"`, `ok: true`, and zero `notProvedReasons`.
- Every surviving formal-covered guard mutation produces a 4-part diagnostic (`<file>:<line> [mutation-survived] ... Fix: ... Rerun: \`pdd prove --mutation-check\`.`) causing `pdd prove` to exit `3` (`Not proved`).

## Dependencies

None (pure mutation selection/evaluation and isolated sandbox runner; `src/core/prove-mutation.mjs` imports internal helpers from `formal-verify.mjs`, `prove-coverage.mjs`, `lint/diagnostics.mjs`, and `shared/safe-read.mjs`).
