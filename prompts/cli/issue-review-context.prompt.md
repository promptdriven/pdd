# Incremental backlog review context

Own `src/issue-review-context.mjs`. Keep saved sort and dependency records as the
backlog memory. Their storage and trust remain with their existing owners.
This module has no outside effects and makes no AI calls.

Export `namedReviewSources(repository,text)` as sorted unique canonical local
`blob/HEAD` URLs for safe relative paths explicitly named in trusted issue text.
Bare filenames must have a recognized source/document extension; version numbers
and domain names are not filenames. Directory paths admit alphabetic extensions.
Sentence punctuation around links is not part of a path; encoded filename punctuation remains literal. Exclude
other repositories, traversal and absolute paths. Export
`namedReviewSourceLinks(repository,text)` as sorted unique same-repository GitHub
`blob` links, preserving their encoded ref and path tail. This parser has no
outside effects. The repository evidence reader checks exact local refs and exact
tree paths to resolve each link. A unique path becomes a canonical local
`blob/HEAD` source. A missing or ambiguous link stays unavailable required
context; it cannot validate a cached review. Do not infer the ref boundary from
the first path component, fetch refs, or enumerate the source tree.
`tracksReviewInput(issue,key)`
is false only for a local source locator outside the issue's `namedSources` list.
Missing namedSources preserves legacy direct-caller freshness. Reading a file as
background must not make every future edit to it require semantic review.

Export `reviewPacket(snapshot,subjects,{limit=20})`. Return a fresh normalized
snapshot with the subjects, their likely neighbours and all explicitly linked
context. Rank without AI from saved trusted intact sort heads: equal root cause,
area, named/sort paths, and shared title/summary words. Prefer cause, then area,
then files, then words; break ties by full issue URL. Select at most limit
neighbours per subject. Conflicting saved sort heads supply no classification.
Always include native links to/from subjects, saved prerequisites, duplicate links,
trusted issue references and group umbrellas even when outside the top limit.
Retain the reachable native prerequisite closure for those issues. Mandatory
links can exceed the limit. This is retrieval, never evidence of independence.

Subjects retain their trusted requirements and sort heads. Neighbours carry short
summaries (at most 600 characters), current identity/revision/state/authority and
short area/owner, status, duplicate, cause and path metadata, without bodies,
record histories or repeated candidate lists. Retain subject review identities and base relations. Keep neighbouring review link
provenance with empty analysis, inputs, candidates and questions, so PDD-written
links remain distinguishable from person links. In retained subject reviews,
keep candidate rows only for named prerequisites; historical full-backlog candidate
lists must not expand the packet.
Retain compact current issue observations named in retained subject review inputs,
even when they are not prerequisites and fall outside the ranked neighbours.
Keep their coverage rows; a historical examined issue must not become missing
context merely because retrieval omitted it. Actual unavailable observations
remain unavailable.
Retain trusted intact incoming PDD-link provenance for subjects independently of
host selection, including confirmed links now absent from native edges. For an
unselected host keep only dependencies targeting subjects, with empty analysis,
inputs, candidates and questions. This preserves subject link rows and person
removal semantics without loading that host's body or history into issue rows.
Filter edges, input, coverage, impact and group rows to this scope. An edge is retained only when both endpoints are selected. Keep full state
outside the packet for validation and map updates. Do not change the full graph.

Export `reviewConsistency(snapshot)` returning sorted unique issue URLs for saved
groups whose present member cause disagrees, missing group members/umbrellas,
and links whose endpoint is absent. This cheap local check never invents links,
closes issues or resets completed semantic work. A weekly reconciliation records
its findings for inspection, without another whole-backlog AI pass.

Saved sort head fields used for retrieval are `base` (superseded IDs), `belongs`
(area and repository), `status.state`, `genuine.duplicateOf`, `paths`, `rootCause`
and optional `summary`. Owner is the configured area owner, saved destination repository or area hint;
it never supplies routing authority. Optional `reviewSummary` on packet neighbours
has exactly summary, area, owner, status, duplicate, rootCause (strings) and paths
(string list). Existing dependency normalized fields keep their existing meanings.
