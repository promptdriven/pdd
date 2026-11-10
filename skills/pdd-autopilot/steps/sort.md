# Sort and route before dependency review

Read the bundled prompts/cli/issue-sort.prompt.md and issue-sort-github.prompt.md.
Use the same dependency request and trusted evidence. Make no separate AI call.

On the first visit without autopilot.areas, show contextJson.sort.draft. It uses
local CODEOWNERS, top folders, observed labels and past assignees. Ask the person
to edit and save an `autopilot.areas` block in root pdd.json once. Do not approve
or save it for them. Until then, use CODEOWNERS or the single default area.

Before each subject's dependency answer, sort it against the current release.
Read code and Git history. Name the fixing commit, PR or code locator for fixed
issues. Reuse a current record from contextJson.sort.records. Otherwise put a
record in analysis.sorts. It has this shape (values below are illustrative):

```json
{
  "schema_version": "pdd.issue-sort.v1",
  "issue": "https://github.com/example/project/issues/12",
  "base": [],
  "inputs": [{"key": "https://github.com/example/project/issues/12", "revision": "copy-current-row"}],
  "belongs": {"kind": "area", "area": "cli", "repository": ""},
  "status": {"state": "still-happens", "release": "1.0.0", "fix": "", "evidence": ["src/cli.mjs:12"]},
  "genuine": {"kind": "bug", "duplicateOf": "", "reason": ""},
  "paths": ["src/cli.mjs"],
  "owningModule": "src/cli.mjs",
  "symbol": "parseArgs",
  "component": "arg-parser",
  "errorCode": "",
  "route": "",
  "duplicateOf": "",
  "rootCause": "missing-current-context",
  "severity": "medium",
  "question": ""
}
```

Copy the subject, area/release row and all trusted requirement comment revisions
from the snapshot. Add every examined source row. `base` names the unsuperseded
sort comment IDs on this issue. Use unknown/unclear and one question when evidence
cannot decide. Never invent a fix or owner. For mixed issues include touchedAreas, one
{area,evidence:[files,commands,error text]} row for every area. For split work,
include splitOrder:{first:<area>,evidence:[reason for the work order]}. Missing
area evidence or order means one owner question. Whole sends every part to the
owner; never start it. Split makes independently closable part issues under the
original tracker. Only the local part can start, after its prerequisites. A
trusted person can use pdd:owner-whole or pdd:owner-split (label wins), or a
comment with one of those directives or "mixed: whole" / "mixed: split".
Do not bypass a person assignee or live claim. Keep expected cases separate from
code output. PDD validates the record; it does not verify the semantic assessment.

PDD routes closed proposals, external owners and questions. Do not start them.
In auto, a close comment gives evidence and a reopen hint before closure. Observe
keeps it open with pdd:close-proposed. Person assignees and live claims win.

Read the graph again after completion. Group before claiming: issues form a group
of 2 to 5 members when they share the same owning module (canonical prompt/src
path, excluding shared routing/doc/config files like `src/command-catalog.mjs`
and `docs/cli.md`) plus a shared `component`, `symbol`, `errorCode` or `route`
(or when one is a `duplicateOf` an open local work issue) — never from free-text
`rootCause` equality alone. Human-assigned issues and Runtime-owned issues never
join a group. Larger clusters split deterministically into groups of 2 to 5
issues. The lowest-numbered member issue is the group leader (`umbrella`); never
create a synthetic `Global fix:` umbrella issue. Confirm or split the group
after the `reproduce` step: if a member fails or turns out to have a different
module or cause, split it out to its own run while the others continue. Each
closed member in the group PR (`Closes #A, Closes #B ...`) requires its own
reproduce result and its own passing test (`member-evidence.json`). Claims,
trust and merge rules still apply. A conflicting group or dependency cycle needs
a question, not a guess.
