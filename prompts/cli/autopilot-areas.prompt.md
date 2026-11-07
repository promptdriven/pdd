# Autopilot areas

Own the local area map and its draft. Preserve existing Autopilot mode, trust,
claims and gates. No network or model calls belong here.

`resolveArea({areas,codeowners,evidence})` returns `{state,area,owner,source}`.
State is resolved or unsure; missing area/owner are empty strings. Source is
config, codeowners, evidence or default. Evidence has paths, keywords, labels,
repository and area. Explicit areas take precedence over CODEOWNERS. Each area
has name, owner and match, whose paths, keywords, labels and repositories are
optional string lists. Any matching rule selects an area; multiple different
matches wait. Owners are autopilot, a GitHub login, or repo:OWNER/NAME.
Invalid maps wait, rather than falling through to Autopilot. With an explicit
map and no match, use the coordinator's named area when valid, else wait.

Parse CODEOWNERS locally. Follow GitHub order: the last matching path rule wins.
Ignore comments and unsupported patterns. Multiple owners or teams need a person;
never select one. Different owners across examined paths wait. Without an
explicit map or a matching CODEOWNERS entry, one default area belongs to Autopilot.
An external repository with no owner rule waits.

`draftAreas({codeowners,folders,labels,assignees})` returns a proposed areas list
and the supplied signals. Use CODEOWNERS and top folders as suggestions; labels
and past assignees are evidence for a person, never automatic authority. The skill
shows this map once for a person to edit and save in root pdd.json. This module
never approves or writes it.

## Dependencies

None. All inputs are values. Files are read by issue-sort-github.
