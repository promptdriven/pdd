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
runner scripts, external imports other than Node builtins, and recognized
unresolved local imports require `full`. Full means every discovered entry;
a fallback is explicit, never an empty successful selection.

For supported repository files, include changed tests and smoke. Follow reverse
local import, reexport, literal dynamic import, require and literal file-reference
dependencies transitively, with cycle protection. Include matching test names.
Map `prompts/cli/NAME.prompt.md` to `src/NAME.mjs` when present, and include scenario
files that name that prompt, their Story and native replay consumers. Follow local
Markdown dependency links, including fragments, as file dependencies. A changed
prompt without a source owner or scenario mapping requires full. Deleted and
renamed modules retain their old dependency edges from the base inventory.

A test may be omitted only when static analysis proves its whole transitive
import graph, including the test itself. Every dependency must be a static ESM
import or reexport with a literal relative specifier resolved to an existing
JavaScript file. Cycles must not hide an unproved module. Any unproved module
always selects itself and all reverse consumers, even with no changed paths.
This includes dynamic `import()` (even with a literal), `require` in any form,
aliases, `createRequire`, computed loader members such as `module['re' + 'quire']`,
`eval`/`Function`, template or computed specifiers, unresolved or nonrelative
specifiers (including Node builtins), non-JavaScript loaders and parse errors.
Never infer safety from the absence of recognized unsafe spellings.

The proof may support a conservative subset of JavaScript. Unclassified syntax
must always select the module's test consumers. In particular, the native proof
supports static ESM declarations and scalar variable/export declarations in
explicit `.mjs` modules. It does not prove the package loader scope of `.js`
files or arbitrary executable expressions. It must consume the entire
source and validate syntax without executing it. Filesystem/process operations,
regex or division syntax, templates, identifier escapes and unsupported syntax
therefore cannot establish omission. Comments between tokens preserve dependency
meaning; comment markers within strings remain literal. Reachable interpolated
templates, unclassified slash syntax, external packages and directory package
entry points retain full fallback. Literal matching can add dependency edges and
tests, but cannot establish proof or remove a test. Keep all plausible
extensionless file/index targets, including CommonJS and JSON candidates, when
adding such conservative edges. No test result supplies the proof. The separate
full-suite gate still applies; a static graph cannot prove semantic equivalence.

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
  normalized local paths and SHA-256. Node's native VM syntax compiler validates
  the supported declaration subset without executing source. No runtime
  interpreter calls are introduced.
