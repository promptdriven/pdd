# Affected native tests

Own `src/affected-tests.mjs` and the repository adapter `scripts/affected-tests.mjs`.
The issue #3065 authorizes this new interface. Preserve all existing workflow,
approval, test expectations and merge gates. This selector only reduces native
tests during work; it never replaces the full-suite gate or runs an interpreter.

Export `selectAffectedTests({files, changed, smoke})`. `files` maps safe POSIX
repository paths to UTF-8 contents, `changed` lists paths (including removed and
renamed old names), and `smoke` defaults to `SMOKE_TESTS`, the fixed sorted set
`test/cli-node-version.test.mjs`, `test/command-catalog.test.mjs`. Return exactly
`{mode, reasons, tests, total}`: mode is `affected` or `full`; reasons is a sorted
unique list of affected paths or fallback causes; tests is a sorted unique list
of existing top-level `test/*.test.mjs` entries; total is the full entry count.
Missing smoke entries, invalid inventory/paths, an empty test inventory, unknown
changed paths, shared test helpers/fixtures, package/configuration files, test
runner scripts, external imports other than Node builtins, and unsupported code
or unresolved local imports require `full`. An unresolved import in a consumer
already treated as depending on every changed path can retain that conservative
selection instead; the consumer and its reverse consumers must always run. Full means every discovered entry;
a fallback is explicit, never an empty successful selection.

For supported repository files, include changed tests and smoke. Follow reverse
local import, reexport, literal dynamic import, require and literal file-reference
dependencies transitively, with cycle protection. Include matching test names.
Map `prompts/cli/NAME.prompt.md` to `src/NAME.mjs` when present, and include scenario
files that name that prompt, their Story and native replay consumers. Follow local
Markdown dependency links, including fragments, as file dependencies. A changed
prompt without a source owner or scenario mapping requires full. Deleted and
renamed modules retain their old dependency edges from the base inventory.

Dependency discovery must overselect rather than miss computed access: JavaScript
with computed imports, filesystem reads/traversal or child process execution can
depend on any repository file. Treat such a consumer as depending on every changed
path, then follow its reverse consumers too. Literal matching may overselect;
source text or a comment can add tests but cannot remove them. A graph alone cannot
prove semantic equivalence; keep the full gate. No test result is used as an oracle.
JavaScript block and line comments between dependency tokens, arguments and
specifiers must preserve local dependencies, computed-consumer selection and
external-import full fallback. Ignore comment markers inside string literals.
When dependency syntax inside a template interpolation cannot be classified
safely, require full fallback for its reachable consumer. The scanner does not
parse interpolation expressions: any reachable interpolated template requires
full fallback before masking, including nested templates, braces, comments and
computed dependencies. Uncertainty must select more tests, never fewer.
Executable references to `require` outside a direct call can alias the loader.
Unclassified Unicode escapes in executable identifiers can also hide loaders.
Treat either consumer as depending on every changed path and include its reverse
consumers, or require full fallback; never discard them for lacking a literal edge.
An unclassified slash outside a string or comment can start a regex literal or
division expression. Require full fallback for its reachable consumer before
quotes or comment markers in that syntax can hide later dependencies.
For extensionless references, retain every existing plausible file and directory
index target, including CommonJS `.js` and JSON targets. An ESM candidate cannot
exclude the target loaded by CommonJS. Directory package entry points require
full fallback when their loader rules are not modeled.

The adapter accepts `--base REF`, optional `--run`, and optional `--report PATH`.
With no run, print the JSON plan only and execute no test. Resolve base to a commit
and compare its merge-base with committed HEAD plus staged, unstaged and untracked
Git-visible files. Use NUL-delimited inventories, preserve old and new rename names,
and load both base and current text into the graph. Missing base, Git/read errors,
symlinks or nonregular inputs select full with a cause. Capture a SHA-256 source
fingerprint over exact path/bytes, including dirty files, and the committed head.
A result describes these bytes, never just an uncommitted head claim.

Run selected entries with Node's native test runner via argument arrays. Full mode
runs `npm test` through the repository's `scripts/vm-suite-lock.sh`, which uses the
shared suite queue. Never run a full suite outside that queue. Propagate failures
and signals. Record mode, reasons, test list, base, head, source fingerprint,
start/finish times in epoch ms, `elapsedMinutes` (wall time including any queue
wait), `suiteMinutes` (execution minutes for affected runs; null for a queued
full fallback whose execution-only duration is owned by the queue), exitCode and complete native TAP
counts (`tests`, `pass`, `fail`, `cancelled`, `skipped`, `todo`) or null if unavailable.
Never report a plan as a pass. A source change during execution or an incomplete byte inventory invalidates its
result. Include Boolean `inventoryComplete`; unreadable or nonregular files
make it false. Preserve child signals as conventional 128-plus-signal exit codes
in the callable adapter and re-signal the CLI process after writing evidence. Keep reports outside the repository. Reports are local evidence, not
approvals or tamper-proof attestations. Never publish a PR or status here.

During work, workers and checkers use the affected plan plus smoke, or the full
fallback. Before merge, the owner obtains one queued full-suite result on the exact
current clean PR head, reusing an already green result for that head instead of
running it again. Changed heads require a fresh result. The PR must show working
test commands, selected files, fallback causes and counts, and separately show the
full-suite head/result or pending. Missing, stale or failed full results block merge.
Existing repository-required checks and human reviews still apply.

## Dependencies

- [Shared VM queue](../../scripts/vm-suite-lock.sh): native full-suite execution
  adapter. On the autopilot-next integration line it routes to the shared queue
  from #3056. This module does not own admission or queue state.
- Native Git, filesystem, clock and child-process operations belong to the adapter;
  the exported selector is pure. Node builtin path and crypto facilities supply
  normalized local paths and SHA-256. No runtime interpreter calls are introduced.
