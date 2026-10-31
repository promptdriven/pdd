# Program data

Own src/program-data.mjs. Export module function
`programData({root, program, flags: {fresh, data}}, ports)` returning
`{dir, fresh, startingData}`. program identifies the repository-relative entry without `.prompt.md`.
A unique entry basename uses `.pdd/run/<basename>/`. When repository prompt entries
share a basename, flatten the complete relative path with `__` separators.
Preserve valid spaces, Unicode and punctuation. Escape delimiter occurrences,
reserved names and literal escape markers injectively and stably, with no hash;
only unrepresentable or reserved names need encoding. Reject absolute/traversal
identities and empty segments. Distinct valid entry paths never share metadata:
flattening must remain injective across segment boundaries, including an underscore
at the end of one segment or start of the next. A unique ordinary basename such as
place_order remains unchanged; spaces, Unicode and nonreserved punctuation remain
readable, while literal escape markers cannot alias escaped names.
Flattened program directories keep a parent program's internal bin/world files
separate from child prompt identities. programData.dir is the program directory
itself, so world.json is directly in `.pdd/run/<program>/`. Use this mapping for
B and C helpers.
Git-ignore `.pdd/` locally through `.git/info/exclude` (including worktree Git
metadata); never create or modify the project's `.gitignore`.
No Story is required and all outside program effects remain fake.

Starting data precedence: explicit data file, else saved world.json unless fresh,
else {}. A data file is a JSON world or a scenario's initial_world and simulation;
never execute its steps or require its Story. Explicit data wins even with fresh.
startingData carries the selected initial_world and optional simulation; fresh is
the requested boolean. Resolve explicit data from the invocation current folder, before repository-root
normalization; callers may pass the resolved absolute filename without changing
this public signature. Missing files, bad JSON and nonobject worlds are local
input errors: exit2, a plain message naming the file and problem, no send.

Before a fresh selection replaces saved world.json, atomically preserve it as
world.prev.json. This happens once per invocation/shell selection, including
fresh plus explicit data. Informational fresh backup notice follows quiet.
Persist only confirmed world snapshots in dir/world.json. Never replace confirmed
data with an invented world after refusal or unknown outcome. dir/last-run.json records
confirmed input, output, data_before, data_after and ai_calls, plus session_id,
session link, report_url, exit_code, outside_calls, call_chain and total when
supplied. Preserve exact JSON worlds; credential protections apply to actual
credentials, not arbitrary world strings that merely resemble tokens. Show-data reads the
selected world without dispatch. Private files and directories retain safe regular
file/symlink checks on every directory segment and credentials never enter data
or records. Export module function acquireProgramLock(dir), returning a release
function: one active owner per program directory; a second live owner refuses
with the plain busy message and cannot enter until release. Different program
directories remain independent; release must permit a later owner.

## Dependencies

- [Try doors](try-doors.prompt.md): required native generation/verification/testing
  private regular-file and safe local persistence protections.

## Runtime interface

Native filesystem behavior is verified with temporary files and injected ports;
no model-executed operation is declared.
