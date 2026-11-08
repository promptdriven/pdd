# Autopilot areas

Own the local area map and its draft. Preserve existing Autopilot mode, trust,
claims and gates. No network or model calls belong here.

`resolveArea({areas,codeowners,evidence})` returns `{state,area,owner,source}`.
State is resolved or unsure; missing area/owner are empty strings. Source is
config, codeowners, evidence or default. Evidence has paths, keywords, labels,
repository and area. Explicit areas take precedence over CODEOWNERS. Each area
has name, owner and match, whose paths, keywords, labels and repositories are
optional string lists. Each area optionally has mixed: whole|split. Invalid mixed values hold. Any matching rule selects an area; multiple different
matches wait in resolveArea. resolveAreas accepts the same input and returns an array of resolved area rows, retaining all distinct matches. It returns an empty array for invalid maps or uncertain CODEOWNERS. Single-area callers keep resolveArea compatibility. Owners are autopilot, a GitHub login, or repo:OWNER/NAME.
Invalid maps wait, rather than falling through to Autopilot. With an explicit
map and no match, use the coordinator's named area when valid, else wait.

Parse CODEOWNERS locally. Follow GitHub order: the last matching path rule wins.
Ignore comments and unsupported patterns. Multiple owners or teams need a person;
never select one. Different owners across examined paths wait. Without an
explicit map or a matching CODEOWNERS entry, one area named default belongs to Autopilot, regardless of the coordinator's area hint.
An external repository with no owner rule waits.

`draftAreas({codeowners,folders,labels,assignees})` returns a proposed areas list
and the supplied signals. Use CODEOWNERS and top folders as suggestions; labels
and past assignees are evidence for a person, never automatic authority. The skill
shows this map once for a person to edit and save in root pdd.json. This module
never approves or writes it.

## Dependencies

None. All inputs are values. Files are read by issue-sort-github.


<details><summary>Runtime interface</summary>

```json
{"status":"approved","prose_sha256":"fa06eb6c993e888d0c4ebcca63039ab990073d255f104b0a9ac73b6b6b6daac1","entries":[{"operation":"resolveArea","input_schema":{"type":"object","properties":{"areas":{"type":"array","items":{"type":"object","properties":{"name":{"type":"string"},"owner":{"type":"string"},"match":{"type":"object","properties":{"paths":{"type":"array","items":{"type":"string"}},"keywords":{"type":"array","items":{"type":"string"}},"labels":{"type":"array","items":{"type":"string"}},"repositories":{"type":"array","items":{"type":"string"}}},"required":[],"additionalProperties":false},"mixed":{"type":"string","enum":["whole","split"]}},"required":["name","owner","match"],"additionalProperties":false}},"codeowners":{"type":"string"},"evidence":{"type":"object","properties":{"paths":{"type":"array","items":{"type":"string"}},"keywords":{"type":"array","items":{"type":"string"}},"labels":{"type":"array","items":{"type":"string"}},"repository":{"type":"string"},"area":{"type":"string"}},"required":[],"additionalProperties":false}},"required":[],"additionalProperties":false},"result_schema":{"type":"object","properties":{"state":{"type":"string","enum":["resolved","unsure"]},"area":{"type":"string"},"owner":{"type":"string"},"source":{"type":"string","enum":["config","codeowners","evidence","default"]}},"required":["state","area","owner","source"],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[],"limits":{"max_steps":4,"max_model_calls":2},"conventions":[]}
```
</details>
