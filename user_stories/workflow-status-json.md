# Read workflow status as versioned data

I can read all workflow statuses as stable versioned JSON for a phone or service caller.

## Acceptance criteria

1. `pdd workflow status --all --json` prints one JSON object with `schema_version` equal to `pdd.workflow-status.v1` and a `runs` array, with no human-readable status lines mixed into stdout.
2. Each run in `runs` has exactly the documented fields `ref`, `repo`, `number`, `workflow`, `area`, `group`, `words`, `prs`, `stories`, `updatedAt`, `root`, `runDir` and `viewCommand`; each PR has `number`, `url` and `state`.
3. The JSON rows contain the same runs in the same waiting, working, PR-open, done and cancelled ordering as text status; cancelled rows remain hidden unless `--cancelled` is supplied.
4. A row with no compatible Story evidence has `stories: null`; a row with evidence reports `pass`, `total`, `failing` and any applicable `unknown` or `evidence` fields without changing the status words.
5. JSON mode writes only the versioned document to stdout; progress and diagnostics stay outside stdout.

## Rules to check

- `schema_version` is the exact public marker `pdd.workflow-status.v1`; changing it requires a new documented version.
- The row and nested PR field sets are closed: adding a field is a contract change that requires a new Story decision and documentation update.
- `--cancelled` changes selection only. It must not change the envelope, field names, or ordering of rows that are present.
- `viewCommand` is read-only and names the row's `ref`; consumers must not infer approval authority from its presence.

## Out of scope

This Story does not change human-readable status text, saved run records, C3 `v:1` views, gate behavior, or external status refresh rules.
