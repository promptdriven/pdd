# Diff-line and per-file coverage split for `pdd prove --coverage`

Own `src/core/prove-coverage.mjs` (Layer-1 Core: imports only Layer-1 `src/core/*`, `file-owner.mjs`, and Layer-0 `src/shared/*`; zero `autopilot/` or `cli/` imports). Measure real per-file and PR diff-line (`base..WORKTREE`) code coverage split across `formal`, `vectors`, and `all` suites using real repository coverage tools, writing all temporary coverage artifacts exclusively inside an isolated `os.tmpdir()` directory with zero workspace pollution.

## Domain decisions

- **PR diff-line extraction (`parseUnifiedDiffAddedLines`, `collectDiffLines`):**
  - Parse unified diff text generated with `git diff --no-ext-diff --no-textconv --no-renames --src-prefix=a/ --dst-prefix=b/ -U0 <baseSha> --` (tracking hunk line counts so added lines beginning with `++ ` inside hunk bodies never hijack file headers) to map each added or modified repository-relative file path to its sorted, deduplicated 1-based added/modified line numbers. Ignore pure deletion hunks (`+N,0`) and `/dev/null` targets.
  - For untracked production code files, mark every non-blank line `1..N` as an added diff line. Restrict diff-line targets strictly to canonical production code files (`isProductionCodeFile`).
- **Three-suite discovery (`discoverCoverageSuites`):**
  - **Formal suite (`formal`):** Repository files matching `FORMAL_TEST_FILE_RE` (`*.formal.test.*`, `test_formal_*.py`, `*_formal_test.py`, `formal/test_*.py`, `formal/*_test.py`, `*_formal_test.go`, `tests/*formal*.rs`), skipping symlinks and non-canonical paths.
  - **Vector replay suite (`vectors`):** Repository files matching `VECTOR_TEST_FILE_RE` (`*.vectors.test.*`, `*.vector.test.*`, `test_vectors.*`, `test_*vectors*.py`, `*_vectors_test.py`, `vectors/test_*.py`, `vectors/*_test.py`, `*_vectors_test.go`, `tests/*vectors*.rs`).
  - **Full suite (`all`):** The merge-base trusted `verify.test` command (or auto-detected repository test command).
- **Real coverage tool selection and zero-pollution isolation:**

| Repo language | Primary tool | Fallback / config | Isolation mechanism |
| --- | --- | --- | --- |
| JS / TS (`package.json`, `*.mjs`/`*.js`/`*.ts`) | Native Node V8 (`NODE_V8_COVERAGE`) or local `c8` | Native `NODE_V8_COVERAGE` (zero installs) | Per-suite subdir under `mkdtempSync(tmpdir(), 'pdd-prove-cov-')` |
| Python (`pyproject.toml`, `pytest.ini`, `*.py`) | `coverage.py` (`coverage run --branch` + `coverage json`) via untracked `.venv`/`venv` or `python3 -m coverage` | Stdlib Python `ast` + `sys.settrace` (`python-trace`, line coverage only, `branches: null`) | `COVERAGE_FILE=<tmpDir>/cov.<suite>`, `PYTHONDONTWRITEBYTECODE=1` |
| Go (`go.mod`, `*.go`) | `go test -covermode=count -coverprofile=<tmpDir>/<suite>.out` | None (`unavailable` if `go` absent) | Coverprofile file strictly in `<tmpDir>` |
| Other / missing runner | None | Fail closed (`status: "unavailable"`) | Zero files written in repo |

- **Security and trust parity:** Refuse symlinked or git-tracked `.venv`/`venv` executables (matching `resolvePytestBinary`), scrub credential env families (`scrubChildEnv`), and always clean up `<tmpDir>` in `finally`. For CLI async execution (`runProveCoverageAsync`), execute child processes non-blockingly in their own process group so `SIGINT`/`SIGTERM`/`SIGHUP` immediately kills the active child group, removes `<tmpDir>`, and re-raises the signal without swallowing interruption or continuing further suites.
- **Compound Python `verify.test` commands:** Parse `&&`-chained Python test commands (`pytest` / `python -m unittest`) cleanly by running each segment with `--append` (or merging trace records) into the same isolated coverage file; reject unsupported shell operators (`||`, `;`, `|`, subshells, redirections) fail-closed as `status: "unavailable"` (`Not proved`, exit `3`) rather than passing shell tokens as test filenames.
- **Honest executable-line denominator and suite split (`aggregateCoverageSplit`):**
  - Intersect each file's `diffLines` with its canonical `executableLines` (the union of instrumented executable lines observed across `formal`, `vectors`, and `all` for that file, or a source-level non-comment executable-line scan if no suite imported the touched production file).
  - Never report an unimported touched production file as `100%` or `0/0`: when a suite does not execute a touched file that has `N > 0` diff executable lines, report `0/N (0.0%)` with all `N` lines listed in `diffMissedLines`.
  - Compute `unionFormalVectors` (`total`, `diff`, `formalOnlyLines`, `vectorsOnlyLines`) and `uncoveredDiffLines` (each touched production file's diff lines missed by `all` or by both `formal` and `vectors`, naming exact `missingIn` suites).
  - Percentages round to 1 decimal place (`Math.round(covered * 1000 / total) / 10`); when `total === 0`, percentage is `null` (never `NaN`).

## Public contract

- `VECTOR_TEST_FILE_RE`: RegExp matching vector replay test files across JS/TS, Python, Go, and Rust.
- `validateProveOptInFlags({ coverage, mutationCheck, test, expect })`:
  - Pure validator for opt-in flag combinations.
  - When `(coverage === true || mutationCheck === true)` and `(test !== undefined || expect !== undefined)` (where `test` or `expect` is provided as a non-null value), returns `{ ok: false, exitCode: 2, error: "pdd prove --coverage and --mutation-check cannot be combined with bug-contrast --test/--expect mode." }`.
  - Otherwise returns `{ ok: true, exitCode: 0, error: null }`.
- `parseUnifiedDiffAddedLines({ diffText })` -> `{ files }` where `files` maps each canonical relative path string to a sorted ascending array of unique 1-based added/modified line numbers.
- `resolveV8FileCoverage({ sourceText, functions })` -> `{ executedLines, missedLines, executableLines, totalBranches, coveredBranches }` resolving nested V8 block coverage intervals accurately (inner `count: 0` ranges override outer `count > 0` ranges).
- `parseCoveragePyJson({ jsonText, root })` -> map from canonical repo-relative path to `{ executedLines, missedLines, executableLines, totalBranches, coveredBranches }`.
- `parseGoCoverProfile({ profileText, modulePath })` -> map from canonical repo-relative path to `{ executedLines, missedLines, executableLines, totalBranches: null, coveredBranches: null }`.
- `aggregateCoverageSplit({ tool, diffLinesByFile, suites, fallbackExecutableLinesByFile })`:
  - Inputs: optional `tool` string (`"node-v8"`, `"c8"`, `"coverage.py"`, `"python-trace"`, `"go-cover"`, or `null`); `diffLinesByFile` (open object mapping repo-relative file path to sorted unique 1-based changed line numbers); `suites` with keys `formal`, `vectors`, and `all` where each suite input has `{ status: string, testFiles: string[], command: string | null, files: open object mapping repo-relative path to { executedLines: number[], missedLines: number[], executableLines?: number[], totalBranches?: number | null, coveredBranches?: number | null } }`; optional `fallbackExecutableLinesByFile` (open object mapping repo-relative path to 1-based executable line numbers for files not imported by any suite).
  - Returns `{ status, suites, unionFormalVectors, files, uncoveredDiffLines, summary }`:
    - `status`: `"ok"` when at least one suite succeeded without errors, `"not-applicable"` when there are zero production files in `diffLinesByFile` and all suites, `"failed"` if any suite has `status: "failed"`, or `"unavailable"` if no suite succeeded.
    - `suites`: object with keys `formal`, `vectors`, `all`, each `{ status, testFiles, command, total: { statements, covered, missed, pct, branches, coveredBranches, branchPct }, diff: { lines, covered, missed, pct }, files }` where each per-file entry has `{ statements, covered, missed, pct, branches, coveredBranches, branchPct, executedLines, missedLines, diffLines, diffCoveredLines, diffMissedLines, diffPct }`.
    - `unionFormalVectors`: `{ total: { statements, covered, missed, pct }, diff: { lines, covered, missed, pct }, formalOnlyLines, vectorsOnlyLines }` where `formalOnlyLines` counts executable lines hit by `formal` and not `vectors`, and `vectorsOnlyLines` counts executable lines hit by `vectors` and not `formal`.
    - `files`: sorted array of `{ file, touched, diffLines, formal, vectors, all }` rows.
    - `uncoveredDiffLines`: sorted array of `{ file, lines, missingIn }` entries where `lines` are the sorted diff executable lines missed by at least one of `formal`, `vectors`, or `all` (specifically lines missed in `all` or missed in both `formal` and `vectors`), and `missingIn` lists which of `["formal", "vectors", "all"]` missed one or more of those lines.
    - `summary`: concise 1-line human summary naming tool and diff percentages across `formal`, `vectors`, and `all`.
- `discoverCoverageSuites({ root, allFiles, testCommand })` -> `{ formalFiles, vectorFiles, testCommand, language }`.
- `scanFallbackExecutableLines(filePath, sourceText)` -> sorted 1-based executable line numbers for unimported source files; `collectDiffLines({ root, baseSha, touchedFiles })` -> `{ diffLinesByFile, fallbackExecutableLinesByFile }`.
- `parsePythonTestPipeline(command)` -> `{ ok, segments, reason }` parsing single or `&&`-chained Python test commands (`pytest` / `python[3[.x]] -m unittest`) while rejecting unsupported shell operators (`||`, `;`, `|`, subshells, redirections) fail-closed.
- `createSignalController()`, `withSignalSafeTempDir(prefix, fn)`, `withSignalSafeTempDirAsync(prefix, asyncFn, parentSignalCtrl)`, `collectFormalLineCoverage(opts, ports)`, `collectFormalLineCoverageAsync(opts, ports, signalCtrl)` -> shared temporary-directory isolation, signal handling, and formal-only runtime line-coverage helpers consumed by `prove.mjs` and `prove-mutation.mjs`.
- `runProveCoverage({ root, baseSha, baseRef, touchedFiles, allFiles, testCommand, timeoutMs, env }, ports)` and async non-blocking `runProveCoverageAsync(input, ports, signalCtrl)` -> `{ tool, status, baseRef, baseSha, suites, unionFormalVectors, files, uncoveredDiffLines, errors, notProvedReasons, summary }`.

## Consequential operations

- If any suite command fails with non-zero exit (non-timeout), record `suites.<name>.status = "failed"` and add an error to `errors`.
- If a suite times out or no coverage tool is available for touched production code, record `status = "unavailable"` / `"timed-out"` and add an explicit diagnostic to `notProvedReasons` (fail closed as `Not proved`).
- Coverage collection never modifies any file inside `root` and removes its temporary directory on normal return, error, or signal.

## Dependencies

None (pure domain math and standard Node/OS coverage collectors; `src/core/prove-coverage.mjs` imports internal helpers from `formal-verify.mjs`, `polyglot-runners.mjs`, `lint/diagnostics.mjs`, and `shared/safe-read.mjs`).
