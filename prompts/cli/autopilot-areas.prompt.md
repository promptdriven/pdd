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

Path rules support `*`, `**`, `**/` and `?`. Other regular-expression special
characters are literal. Escape every regular-expression metacharacter, including
backslashes, when encoding literal pattern segments. Patterns containing a
backslash, brackets or `!` remain unsupported and cannot select an owner in
either explicit maps or CODEOWNERS. Leading `/` anchors a rule; a trailing `/`
includes descendants. Unanchored basenames can match in nested folders.

`draftAreas({codeowners,folders,labels,assignees})` returns a proposed areas list
and the supplied signals. Use CODEOWNERS and top folders as suggestions; labels
and past assignees are evidence for a person, never automatic authority. The skill
shows this map once for a person to edit and save in root pdd.json. This module
never approves or writes it.

For active intake grouping and parallel slot serialization (#3189), export pure
helpers `normalizeAreaPath`, `normalizeAreaList`, `parseGitHubIssueUrl`,
`ownerAreas`, `issueAreas`, `areasOverlap`, `isSmallCard`, and
`groupReadyIssues`. Normalize repository-relative paths (up to 6 per card),
`area:*` labels, canonical `owner:<promptPath>` tokens and
`uncertain:<folder|root>` reservations while stripping URLs and validating
GitHub issue links via `new URL` host checks (`github.com` only).

When optional resolved ownership facts (`owners` — a `Map`, plain object,
`ownerRead` result or `findOwners` inventory mapping repository paths to owning
prompt paths or `{prompt, state}` / `{owner, owners, certain}` records) are
supplied to `ownerAreas(paths, owners)`, `issueAreas(issue, card, {owners})`,
`areasOverlap(left, right, {owners})` or
`groupReadyIssues(rows, cards, {maxGroupSize, owners})`:

- Map each resolved path to `owner:<promptPath>` so multiple production files
  owned by the same prompt serialize across parallel slots even when their file
  stems differ in a flat `src/` or `app/` folder.
- Treat `*.prompt.md` paths directly in a footprint as `owner:<promptPath>` so
  direct prompt edits collide with every module owned by that prompt.
- Include `docs/cli.md` whenever `src/command-catalog.mjs` appears in an issue
  or overlap footprint so CLI catalog edits cannot race on command reference docs.
- Reserve `uncertain:<nestedFolder>` or `uncertain:root` when an owner entry has
  `state: "uncertain"`, an unchecked record without a prompt, or an unknown
  owner on a `src/` or `app/` code file while `owners` is supplied, so uncertain
  ownership serializes conservatively without blocking known-owner or non-code
  paths.
- Preserve existing file, nested module folder, prompt-module stem and `area:*`
  overlap rules, and preserve fallback behavior when `owners` is omitted.
- In `groupReadyIssues`, cluster 2 to 3 small ready issues (keeping medium or
  large issues solo) only when they share an explicit `group_with` link or, when
  `owners` is supplied, the same single resolved `owner:*` prompt with no
  `uncertain:*` reservation (falling back to module-area overlap when `owners`
  is omitted), preventing unrelated issues in the same folder or label bucket
  from being grouped when prompt ownership differs.

## Dependencies

None. All inputs are values. Files are read by issue-sort-github.


<details><summary>Runtime interface</summary>

```json
{"status":"approved","prose_sha256":"f8b7875e28c06df580fcb4835ba01f4a3101e7dec5462d812db8a3730a77980c","entries":[{"operation":"resolveArea","input_schema":{"type":"object","properties":{"areas":{"type":"array","items":{"type":"object","properties":{"name":{"type":"string"},"owner":{"type":"string"},"match":{"type":"object","properties":{"paths":{"type":"array","items":{"type":"string"}},"keywords":{"type":"array","items":{"type":"string"}},"labels":{"type":"array","items":{"type":"string"}},"repositories":{"type":"array","items":{"type":"string"}}},"required":[],"additionalProperties":false},"mixed":{"type":"string","enum":["whole","split"]}},"required":["name","owner","match"],"additionalProperties":false}},"codeowners":{"type":"string"},"evidence":{"type":"object","properties":{"paths":{"type":"array","items":{"type":"string"}},"keywords":{"type":"array","items":{"type":"string"}},"labels":{"type":"array","items":{"type":"string"}},"repository":{"type":"string"},"area":{"type":"string"}},"required":[],"additionalProperties":false}},"required":[],"additionalProperties":false},"result_schema":{"type":"object","properties":{"state":{"type":"string","enum":["resolved","unsure"]},"area":{"type":"string"},"owner":{"type":"string"},"source":{"type":"string","enum":["config","codeowners","evidence","default"]}},"required":["state","area","owner","source"],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[],"limits":{"max_steps":4,"max_model_calls":2},"conventions":[]}
```
</details>
