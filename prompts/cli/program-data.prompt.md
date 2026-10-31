# Program data

Own src/program-data.mjs. Export module function
`programData({root, program, flags: {fresh, data}}, ports)` returning
`{dir, fresh, startingData}`. program is the repository-relative entry prompt path without `.prompt.md`,
for example `prompts/todo`; dir is `.pdd/run/prompts/todo/`. Preserve readable
path segments and isolate equal basenames in different directories; use no hash.
Reject absolute identities, empty segments, `.` or `..` segments and unsafe
characters directly in programData, before touching data outside its directory.
Git-ignore `.pdd/` locally through `.git/info/exclude` (including worktree Git
metadata); never create or modify the project's `.gitignore`.
No Story is required and all outside program effects remain fake.

Starting data precedence: explicit data file, else saved data.json unless fresh,
else {}. A data file is a JSON world or a scenario's initial_world and simulation;
never execute its steps or require its Story. Explicit data wins even with fresh.
startingData carries the selected initial_world and optional simulation; fresh is
the requested boolean. Resolve explicit data from the invocation current folder, before repository-root
normalization; callers may pass the resolved absolute filename without changing
this public signature. Missing files, bad JSON and nonobject worlds are local
input errors: exit2, a plain message naming the file and problem, no send.

Persist only confirmed world snapshots in dir/data.json. Never replace confirmed
data with an invented world after refusal or unknown outcome. dir/last.json records
confirmed input, output, data_before, data_after and ai_calls. Show-data reads the
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
