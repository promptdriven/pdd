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
  "rootCause": "missing-current-context",
  "severity": "medium",
  "question": ""
}
```

Copy the subject, area/release row and all trusted requirement comment revisions
from the snapshot. Add every examined source row. `base` names the unsuperseded
sort comment IDs on this issue. Use unknown/unclear and one question when evidence
cannot decide. Never invent a fix or owner. Keep expected cases separate from
code output. PDD validates the record; it does not verify the semantic assessment.

PDD routes closed proposals, external owners and questions. Do not start them.
In auto, a close comment gives evidence and a reopen hint before closure. Observe
keeps it open with pdd:close-proposed. Person assignees and live claims win.

Read the graph again after completion. Compare each new or changed issue with all
open saved sorts and groups in contextJson.sort. Equal causes join or form groups;
a changed cause leaves. PDD creates one Global fix umbrella at three members or
across locally owned areas. Keep each member's requirements and prerequisites.
Claimed or open-PR work finishes before it can join. A running umbrella gets a
membership note. Give its owner every member, shared cause and one fix statement.
Both PRs reference members. After the global fix merges, sort every member again
against the fixing PR and current release. Close only fresh fixed decisions with
evidence; leave remaining problems open. Read status or the graph for group size,
cause and umbrella. Claims, trust and merge rules still apply. A conflicting group
or dependency cycle needs a question, not a guess.
