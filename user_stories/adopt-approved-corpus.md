# Adopt an existing approved regression corpus

I can start a fresh workflow using the exact complete declared regression corpus I already approved.

## Acceptance criteria

1. I can start a fresh evidence-enabled workflow with my complete declared unchanged corpus from an explicitly identified approved commit, without editing its scenarios or reapproving unchanged prompt content.
2. I see adoption refused for a foreign source, unavailable approved snapshot, an approved commit unrelated to my selected base, or missing explicit external human approval assertion.
3. I see adoption refused when a declared scenario is omitted or missing, the selected inventory has extra rows, or its raw bytes or original check identities change.
4. I see adoption refused when the current prompt or any required dependency differs from the approved source.
5. I keep the original repository, commit, declared scenario scope and human approval reference, with a clear warning that pdd cannot independently authenticate that external authorization.

## Rules to check

Draft command: `pdd workflow start feature 2640 --adopt-corpus approved-corpus.json`.
The declaration identifies one immutable same-repository approved commit and entry
prompts and a nonempty unique list of at most 200 canonical scenario paths, and
explicitly asserts human authorization covering that complete declared inventory
and required prompt context. Both selected approved/current inventories must exactly
match the declaration; unrelated fixture scenarios outside it do not block adoption.
The approved commit must be an ancestor of the selected base, and of current HEAD
on subsequent validation. Even whitespace or newline changes
invalidate reused authorization. Missing or malformed declarations fail closed.
An external assertion is attributed evidence, not independently authenticated approval.
A declaration under a symlinked folder is accepted after resolving that folder;
a final symlink or hardlink is refused. Native failures show a useful cleaned single
line without private paths or Simulate links. Declaration refusals identify the 200-path
limit, missing scenarios key, duplicate path or noncanonical path, with the relevant
repo-relative path retained. A missing declared scenario names its approved/current
source and repo-relative path, even after worktree deletion. A failed startup fetch
says that fetch failed. A `.git` segment in any letter case, including `.GIT`, is
refused before temporary-view writes. Empty causes for those declaration failures,
private absolute paths and silently accepting `.GIT` are forbidden. PR replay sections show adopted repository,
commit, reference, asserting identity and external-assertion-unverified, even blocked.

## What must not change

Without adoption, use the ordinary changed-scenario flow. Keep workflow opt-in,
person gates, original raw bytes/check identities, source-bound frozen replay,
public executions, mutation/formal controls and honest blocked/not_replayed results.
Do not edit historical runs or infer execution/PASS from adoption. Revalidate covered
content before code entry/publication; changed requirements need ordinary approval.

## Verification boundary

The interpreter cases exercise the real adoption helper with a supplied native snapshot
port. They do not prove Git enumeration, raw-byte hashing, file safety, dependency
closure resolution, CLI dispatch, persistence or lifecycle freeze. The code area must
exercise those paths with real temporary repositories, including declared subset/extra rows, unrelated malformed fixture scenarios,
successful adoption under symlinked TMPDIR (the success test must fail on the old
source), symlinked declaration-parent folders, final declaration symlink/hardlink
refusal, ancestor checks against selected base and current HEAD, safe native causes,
PR adoption provenance even when blocked, one scan after the publication commit,
newline changes, an unlisted second scenario entry prompt, changed transitive
dependencies, scenario context and Story changes, selected-base vs dirty caller
content, allocated-worktree races, removed external declarations and publication
retries. No interpreter
test or Simulate has run in this Story area; CLI-only Simulate was declined.
