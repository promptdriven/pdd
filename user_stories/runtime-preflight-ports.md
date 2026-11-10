# Check runtime preflight through declared ports

The [runtime preflight prompt](../prompts/cli/runtime-preflight.prompt.md) discovers Stories, scenarios and prompts, validates scenario shapes, inputs and interface declarations, fills draft hashes, and captures source through declared file, Git, compute and handle-collection ports.

```pdd-boundary
prompts/cli/runtime-preflight.prompt.md
```

## Acceptance criteria

1. `storyCriteria`, `expectedTestPath`, `matchTests`, `discoveryRefusal`, `scenarioShapeRefusal`, `checkInput`, `interfaceKindProblems` and `interfaceSchemaProblems` parse Acceptance headings, pair Story and test paths by the test name rule, detect scenario and input problems, and validate Runtime interface kind, limits and schema rules.
2. `findTests`, `readPrompt`, `promptRefusal`, `promptSchemaRefusals`, `preflight` and `fillHashes` read Git-visible files through `git.listFiles` and `files`, compute SHA-256 prose hashes through `compute.hash_utf8`, report stale or invalid declarations and unchecked criteria, and update draft `prose_sha256` values through `files.write`.
3. `sourceFilePort` (`portStat`, `portRead`), `captureSource`, and `createStrictSourceAccess` (`strictSourceFilePort`, `strictFindTests`, `strictCaptureSource`) read bounded repository source, compute `raw_file_hashes` and `source_sha256`, and enforce the strict no-symlink rule on symlinked paths.
4. Invalid inputs, nonzero `git.listFiles` replies, secret paths, and strict symlink accesses raise the declared entry error (`invalid-story-source`, `invalid-story-path`, `invalid-match-input`, `invalid-test-descriptor`, `invalid-scenario-path`, `invalid-check-input`, `invalid-interface-input`, `invalid-prompt-descriptor`, or `PreflightError`).
