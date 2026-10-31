# Program data

Own src/program-data.mjs. Export module function
`programData({root, program, flags: {fresh, data}}, ports)` returning
`{dir, fresh, startingData}`. program is the entry prompt's name; dir is
`.pdd/run/<program>/`, Git-ignored. Keep entries' data isolated, including same
basenames in different paths: the dispatcher supplies distinct program identities.
No Story is required and all outside program effects remain fake.

Starting data precedence: explicit data file, else saved data.json unless fresh,
else {}. A data file is a JSON world or a scenario's initial_world and simulation;
never execute its steps or require its Story. Explicit data wins even with fresh.
startingData carries the selected initial_world and optional simulation; fresh is
the requested boolean. Read data relative to root; invalid JSON or nonobject world
is a plain local input error before any interpreter send.

Persist only confirmed world snapshots in dir/data.json. Never replace confirmed
data with an invented world after refusal or unknown outcome. dir/last.json records
confirmed input, output, data_before, data_after and ai_calls. Show-data reads the
selected world without dispatch. Private files and directories retain safe regular
file/symlink checks and credentials never enter data or records.

## Dependencies

- [Try doors](try-doors.prompt.md): required native generation/verification/testing
  private regular-file and safe local persistence protections.

## Runtime interface

Native filesystem behavior is verified with temporary files and injected ports;
no model-executed operation is declared.
