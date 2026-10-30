# Adopt an existing approved regression corpus

I can start a fresh workflow using the exact complete regression corpus I already approved.

## Acceptance criteria

1. I can start a fresh evidence-enabled workflow with the complete unchanged corpus from an explicitly identified approved commit, without editing its scenarios or reapproving unchanged prompt content.
2. I see adoption refused for a foreign source, unavailable approved snapshot or missing explicit external human approval assertion.
3. I see adoption refused when any original scenario is omitted, missing or added, or its raw bytes or original check identities change.
4. I see adoption refused when the current prompt or any required dependency differs from the approved source.
5. I keep the original repository, commit and human approval reference, with a clear warning that pdd cannot independently authenticate that external authorization.

## Rules to check

Draft command: `pdd workflow run feature 2640 --adopt-corpus approved-corpus.json`.
The declaration identifies one immutable same-repository approved commit and entry
prompts, and explicitly asserts human authorization covering the whole snapshot's
scenario corpus and required prompt context. Whole-repository enumeration, rather
than a caller subset, establishes completeness. Even whitespace or newline changes
invalidate reused authorization. Missing or malformed declarations fail closed.
An external assertion is attributed evidence, not independently authenticated approval.

## What must not change

Without adoption, use the ordinary changed-scenario flow. Keep workflow opt-in,
person gates, original raw bytes/check identities, source-bound frozen replay,
public executions, mutation/formal controls and honest blocked/not_replayed results.
Do not edit historical runs or infer execution/PASS from adoption. Revalidate covered
content before code entry/publication; changed requirements need ordinary approval.

## Verification boundary

The runtime cases exercise the real adoption helper with a supplied native snapshot
port. They do not prove Git enumeration, raw-byte hashing, file safety, dependency
closure resolution, CLI dispatch, persistence or lifecycle freeze. The code area must
exercise those paths with real temporary repositories, including subset/extra files,
newline changes, an unlisted second scenario entry prompt, changed transitive
dependencies, scenario context and Story changes, selected-base vs dirty caller
content, allocated-worktree races, removed external declarations and publication
retries. No runtime
check or Try has run in this Story area; CLI-only Try was declined.
