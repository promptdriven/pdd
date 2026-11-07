# Structured code replay evidence

For an area with `replay_evidence: "pdd.replay-evidence.v1"`, the agent writes one UTF-8 JSON object to
`<run-folder>/replay-evidence.json` before completing a code-space step. The start message names the run folder.
Read `status.json` for `runId`, `root` and `replayBaseline`. The saved baseline contains the original paths,
raw SHA256 hashes, scenario snapshots and step/check identities. For ordinary runs, pdd refreshes it after every prompt-space publication/push,
through the final approval publication before code space. Final approval refuses unpublished scenario edits;
publish those approved edits in prompt space first. On entry into code space the published anchor is frozen.
Do not replace the baseline or derive new expected values from code. Agents still must not edit test
values in code space. Saved-value diagnostics do not authorize edits. Saved-value changes are advisory:
pdd keeps every changed JSON value with its file, full JSON Pointer, before and after values in
status.json at /replayEvidence/warnings. Command output shows the complete list. The PR fits whole
warning items within its description budget, naming the exact overflow count and that saved location.
Escaped paths, URLs and Unicode remain distinct and reviewable. A long warning list never locks publication.
The code step continues; the checker or person decides. Older anchors without
snapshots show hash changes and say that original values are unavailable.

The replay test must load the current scenario JSON, execute each public operation in order with shared state, and
map each assertion to its actual result, error, world or calls target. Record every check and execution,
including failures and blocked/not-replayed work. Record the semantic mutation run and formal outcome.
Keep the manifest outside Git-visible source. pdd reads it; it never executes the commands in it.

## Source identity

Compute the current content identity after all source/test edits with `sourceFingerprint(root)`, exported
by the installed pdd package's `src/workflow-replay.mjs`. This helper makes local Git/file reads only.
It returns null when source cannot be read. The algorithm is SHA256 of JSON.stringify of lexically sorted
Git-visible path tuples (tracked and untracked non-ignored files): regular `[path, mode & 0o111, SHA256(bytes)]`,
symlink `[path, "link", linkTarget]`, missing tracked `[path, "missing"]`. The hash is independent of commit
identity, so committing byte-identical content preserves it; source edits, new visible files and executable
bit changes invalidate it. Use lowercase hexadecimal SHA256 of the current raw vector bytes, not reserialized JSON.

## Versioned fields

The manifest must be a regular single-link file of at most 2 MiB, with no symlink ancestors. Current vectors
must be Git-visible, readable, nonempty regular single-link files to establish replay. Limits: 200 vectors,
2 MiB each, 10 MiB aggregate, and 10,000 current steps/checks. `check_index` is zero-based within its step.
Identity strings are copied exactly from the current scenario. A missing check or operation is counted
as not replayed, never success; counts must reflect that. Unsupported versions and wrong types are blocked.

- schema_version: pdd.replay-evidence.v1; run_id: the saved run ID.
- source: {kind:"git-content-v1",sha256:64hex}.
- vectors: unique exact current {path,sha256} rows; no substituted hashes.
- checks: at most10000 rows, each {vector,step_id,check_index,entry_path,operation,criterion_id,target,path,op,
  outcome}. outcome is pass, fail, blocked or not_replayed. A blocked/not_replayed row needs a nonblank reason.
  Each row must match a current identity exactly and occur once; unknown/duplicate identities are malformed.
  Missing identities are counted as not_replayed. Empty checks cannot pass.
- operations: unique {vector,step_id,entry_path,operation,executed,outcome,boundary,command,exit_code} rows,
  one per current step. boundary is {kind:function|command|route,name:nonblank}. command is the agent's
  recorded test command, not a command for pdd to execute. executed is boolean; outcome is returned,
  expected_error, crash or not_run. exit_code is an integer0..255 for executed steps, null for not_run.
  Only executed+returned/expected_error is public-boundary execution evidence. A missing or unexecuted
  operation makes its checks not_replayed, even if the supplied check rows say pass. An unknown/duplicate
  operation is malformed. Missing/unexecuted operations need no invented success metadata.
- counts: {total,pass,fail,blocked,not_replayed}, nonnegative safe integers exactly equal to the derived current
  check outcomes (including missing/unexecuted checks). No extra checks or zero-total pass.
- mutation: {kind:"semantic",description:nonblank,command:nonblank,exit_code:integer0..255,
  outcome:assertion_failure|crash|survived|not_run,failed_checks:[{vector,step_id,check_index}],reason?}.
  Detection requires assertion_failure, nonzero exit and at least one unique known failed-check reference.
  A crash, empty failure list, unknown assertion, survived control or not-run control is never detection.
  For not_run, command and exit_code may be null and a nonblank reason is required; never invent an exit.
- formal: {result:proved_bounded|proved_solver|failed|not_run|not_applicable,scope:nonblank,reason:nonblank,
  control_outcome:assertion_failure|crash|survived|not_run,counterexample?}. failed requires a counterexample;
  proved results require assertion_failure control. Not-run/not-applicable remain explicit scoped results.

All identifier/reason/command strings are bounded (at most1000characters); collections stay within the limits
above. Reject wrong types and unsupported versions; never coerce truthy flags or counts. SHA256 comparison
uses the actual current bytes. The manifest is agent-supplied evidence, not an independently verified execution.

## Example shape

This is a one-check illustration. Replace the run ID, hashes, identities, commands, outcomes and scope with
actual recorded data. A copied example is not execution evidence.

```json
{
  "schema_version": "pdd.replay-evidence.v1",
  "run_id": "saved-run-id",
  "source": {"kind": "git-content-v1", "sha256": "<current-content-sha256>"},
  "vectors": [{"path": "tests/add.json", "sha256": "<current-raw-file-sha256>"}],
  "checks": [{
    "vector": "tests/add.json", "step_id": "add", "check_index": 0,
    "entry_path": "prompts/add.prompt.md", "operation": "add", "criterion_id": "sum",
    "target": "result", "path": "", "op": "equals", "outcome": "pass"
  }],
  "operations": [{
    "vector": "tests/add.json", "step_id": "add", "entry_path": "prompts/add.prompt.md",
    "operation": "add", "executed": true, "outcome": "returned",
    "boundary": {"kind": "function", "name": "add"},
    "command": "node --test test/add.vectors.test.mjs", "exit_code": 0
  }],
  "counts": {"total": 1, "pass": 1, "fail": 0, "blocked": 0, "not_replayed": 0},
  "mutation": {
    "kind": "semantic", "description": "Replace addition with subtraction",
    "command": "node --test test/add.vectors.test.mjs", "exit_code": 1,
    "outcome": "assertion_failure",
    "failed_checks": [{"vector": "tests/add.json", "step_id": "add", "check_index": 0}]
  },
  "formal": {
    "result": "not_run", "scope": "Integer addition over the approved bounded domain",
    "reason": "Formal runner unavailable", "control_outcome": "not_run"
  }
}
```

## Reading the PR status

The canonical section appears above free-form summaries and prompt Runtime-check results. It reports
replay PASS/FAIL/BLOCKED/NOT REPLAYED, derived counts, executed operations, control result, formal scope/reason,
source hash, manifest hash and current vector hashes. Full JSON remains in the run folder.
A pass requires complete current check coverage through recorded public operations and a detected semantic
assertion failure in the mutation control. A crash is not detection. Formal proved outcomes also require an
assertion-failure control. Formal not-run/not-applicable stays explicit and is not a proof claim.

Before code-space publication, pdd independently lists the current changed scenario files against the saved
run base using exact NUL-delimited Git paths. Added, removed, moved or edited scenarios produce
warnings without locking code work or publication. Replay uses the current readable cases; an old
manifest that does not cover them is NOT REPLAYED. Missing/unreadable vectors remain unproved.
An unavailable inventory cannot establish PASS. Missing/stale/malformed manifests cannot pass. Real assertion/formal failures may
still publish with failure lines. When updating an existing code-space PR, pdd sets publication-pending
before pushing source, then refreshes the validated result; a failed final update leaves it pending.

Agents execute the tests and supply this record. pdd validates structure and identity; it does not
independently prove execution or prompt/code equivalence. The schema does not authenticate the agent's
execution claims. Review commands, results and committed replay tests before merging.

New bundled feature/bug code areas opt in explicitly. Saved areas and custom workflows without the field,
and small-change, keep their publication behavior. A custom opt-in with an approved prompt area uses
`then: "ask-code"` to establish the original-vector anchor. A workflow whose code area has no such earlier area
gets the [approved scenarios on the base](#approved-scenarios-on-the-base) that link to its changes.
[Corpus adoption](#adopt-an-unchanged-approved-corpus) can instead supply a declared anchor to a fresh workflow whose first area is code. Absent anchors are blocked, never reconstructed
from code-space files.

## Approved scenarios on the base

A file on the run's base branch counts as approved: it was reviewed and merged there. So the anchor also
holds the approved scenario files on the base commit that belong to the area that the run changes. You give
no flag. Manual and Autopilot runs work the same. pdd reads the base with local Git only and makes no GitHub
or AI call.

A base scenario belongs to the run when one of its links names a file in the changed area:

- Its links are its `story_path`, each step `entry_path` and its `entry_paths`.
- The changed area is every file that the run changed against its base, the links of each changed scenario,
  and, for each changed file that the base `pdd-bindings.json` declares as a `module`, its `stories` and
  `prompt` (see [module binding inventory](runtime-bindings.md)).

pdd uses no other link: no folder, file name or text match. When the repository records no link, pdd adds
no base file and the PR says why. A changed code file links to scenarios only through `pdd-bindings.json`.

With an approved prompt area, pdd builds the anchor at each prompt-space publication. A base file that PR 1
changes is a changed scenario, with its PR 1 bytes. When code space starts, the anchor freezes. Without a
prompt area before code, pdd builds the anchor at each code step and publication from the files changed so
far. It always takes those files from the base commit, so a code-space edit cannot change their values.

Each base file in `replayBaseline` keeps its path, raw SHA256, snapshot, check identities and `base` (the
full base commit). The PR shows, for example:

```text
Anchor: 3 changed scenarios + 18 approved on base 6b58b76 (1,722 checks).
```

When pdd adds no base file, the line gives the reason. All anchor limits apply to the whole anchor; a
blocked anchor names its file or check count and the limit. Base approval never gives a pass by itself.
The agent still replays every anchored check. Changed, removed and added files follow the same rules as
other anchored files: in prompt space a removed file blocks the anchor; in code space the saved-value rule
above lists each change, and a record of the old bytes cannot pass. The explicit `--adopt-corpus` route
below keeps its declared inventory and never adds base files.

## Adopt an unchanged approved corpus

A fresh workflow with an explicit replay evidence policy can use the complete
scenario corpus already approved at an immutable commit. For a custom workflow
named `replay`, put its definition in `.agents/skills/pdd-replay/workflow.json`:

```json
{"version":2,"areas":[{"name":"code","steps":["build","verify","formal"],"gate":"pr","replay_evidence":"pdd.replay-evidence.v1"}]}
```

Give the declaration to the workflow you selected:

```sh
pdd workflow run replay 123 --adopt-corpus /path/to/approval.json
```

The first area can be the code area. Adoption supplies its original vector anchor
without requiring an earlier prompt publication. Workflow gates still apply.
Without adoption, an absent original anchor remains BLOCKED.

The declaration names the canonical repository, full approved commit, entry prompts
the nonempty unique canonical `scenarios` inventory and an explicit assertion covering that inventory and all required context:

```json
{
  "schema_version":"pdd.replay-adoption.v1",
  "repository":"example/project",
  "commit":"0123456789abcdef0123456789abcdef01234567",
  "prompts":["prompts/count.prompt.md"],
  "scenarios":["test/runtime/count.json"],
  "approval":{
    "kind":"external-human-assertion",
    "reference":"review:123",
    "asserted_by":"Reviewer"
  }
}
```

The commit must be available locally and be an ancestor of the selected base, including an explicit topic base. Later checks require it to be an ancestor of the worktree HEAD. Equal bytes on an unrelated branch do not establish ancestry. pdd selects exactly the declared scenarios from immutable blobs and current files, and compares raw scenario bytes, check identities, prompts and required context. Unrelated scenarios, fixture corpora and malformed JSON outside that selection cannot block adoption. Before code entry, added, removed or edited covered files block reuse. In code space, scenario changes
follow the advisory rule above; the original prompt and dependency closure still requires exact bytes.
Use an ordinary approval workflow for changed prompt/dependency requirements. Other implementation edits
are allowed and bind replay evidence to the current source fingerprint.

The new run saves the declaration bytes, digest, source and approval reference.
Prompt publication never refreshes this adopted anchor. Later validation uses that saved copy, so editing or removing the caller's file
cannot change its authority. Historical runs remain separate.

The trust label is `external-assertion-unverified`: pdd cannot independently
authenticate the asserted human authorization. The person is responsible for its
truth. Adoption proves content identity only. Agents still execute the original
cases and record public operations, mutation controls and formal results.

The declaration parent folder is resolved with realpath, so symlinked ancestors (including macOS temporary folders) are supported. The final declaration must remain a regular single-link file; final symlinks and hardlinks are refused. Scratch folders also use their real paths. Native refusals include a bounded cleaned cause without private absolute paths, credentials or Simulate URLs.
