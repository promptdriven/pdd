# Local shared-contract commands

Own `src/contracts.mjs`. Module function
`runContracts({words,options,cwd}, {env,stdout,stderr})` returns an exit code.
`words: []` lists contracts; `words: ['sync']` previews migration;
`options['--write'] === true` applies it. Syntax belongs to the command catalog.
These routes read working files and private local Check history. They never
authenticate, reserve a runtime slot, upload, lint remotely or call a model.

Find the Git root as preflight does. Read Git-visible Markdown/JSON files under
`contracts/`, prompts and discovered scenarios using preflight's bounded native
reads. Do not follow symlinks or secret paths, including during writes. Bind
`access = createStrictSourceAccess(root)` from `src/runtime-preflight.mjs`, using
its [scoped strict source access](runtime-preflight.prompt.md#scoped-strict-source-access)
contract. Use `access.sourceFilePort(visible)` for catalog, prompt, expansion and
original-byte checks, `access.findTests({files})` for discovery, and
`access.captureSource({tests})` for current Story footprints. Fresh write-time
visibility uses the same capability's `sourceFilePort` method. All nested reads
must remain within this boundary; a direct-port wrapper alone is insufficient.
This command owns the no-follow requirement; preflight owns the scoped adapter
and physical source/snapshot checks. Use the
contract-reference module's catalog, expansion, comparison and migration APIs;
this command owns orchestration and presentation, not another resolver.

## Listing and freshness

`pdd contracts` lists every catalog record's canonical target and owner file,
its current prompt/test users, and their Stories. Supply current used targets to
the catalog, including seeds and leaf schemas. Include transitive uses; ignore
literal business/expected values. Show unused records with no users. Report
catalog warnings without inventing a record or a user. Skip or warn for an
oversized catalog/discovery-only document before reading its contents; it cannot
abort independent listing, preview or selected good work. Report any affected
record/use or footprint evidence as unavailable rather than complete. Required
selected source retains preflight's bounded safe-read refusals.

Use `readContractHistory` from the runtime client for the most recent actual
Check baseline for each Story. Compare canonical target snapshots, including
removed targets, against that Story's current uses. Say `changed since the last
check` with the affected record identities and `stale: needs a new check` with
the affected Stories. A changed common record affects all its users. Another
record in the same file and another Story in the same batch do not become stale
merely because they shared a file or batch. Other source changes retain ordinary
source freshness behavior. Each Story's current effective footprint is independent
of which other tests were selected: checking one file, all tests for that Story,
or a multi-Story batch must produce the same footprint for unchanged Story
inputs. Account for all discovered tests belonging to that Story and their own
closures, without adding another Story's files. Preflight's
[unavailable-footprint rule](runtime-preflight.prompt.md#source-capture) applies:
report an incomplete current footprint as unavailable with its cause, never as
current or as a selected-source refusal merely because an unselected sibling is
broken. A baseline records a check, not necessarily a pass;
never display a failed result as passing.

With no actual Check baseline or a legacy baseline lacking reference provenance,
show `not checked` or `baseline unavailable`, respectively. Do not invent an old
value or a change. Lint, Try and file previews never advance these baselines.
Current user discovery reflects working files even without history. Unreadable
history is reported as unavailable, never treated as proof of freshness.

## Preview and write

`pdd contracts sync` prints proposed paths, schema locations, canonical targets
and constraint differences. It writes nothing. Ambiguous candidates warn and
skip while independent proposals remain available. Exact copies may migrate as
well as near copies; differing near copies explicitly adopt the canonical shape.

`pdd contracts sync --write` explicitly authorizes applying these proposals.
Before each write require the same safe destination and exact previewed `before`
bytes; a concurrent edit refuses that file without overwriting it. Write the
complete planned bytes into a new exclusive temporary regular file in the safe
destination directory, then atomically rename it into place. Recheck destination
identity, safe ancestors and exact `before` bytes immediately before replacement;
a concurrent content/identity change or symlink refuses without overwriting it
or its target. Failed preparation or replacement leaves the original complete
and removes only this operation's temporary file. Readers see the complete
original or complete replacement, never a truncated/intermediate file. Preserve
unrelated files, prose and unmatched schemas. Write only planned `after` bytes;
report changed paths and skipped/failed paths. Use the planner's draft transition
for edited approved interfaces; never approve, fill hashes or change expectations.
A repeated write with unchanged inputs performs no writes.

Exit 0 for completed listing/preview/write, including advice and ambiguity;
2 for invalid syntax or no repository; 4 for an unsafe/missing required consumer,
reference or refused write; 5 for unavailable local I/O. Keep a finite cause on
stderr; every nonempty output line ends with one newline. No history or source
write happens while merely listing or previewing.

## Dependencies

- [References](contract-refs.prompt.md): required generation and verification
  context for record, expansion, comparison and migration rules.
- [Preflight](runtime-preflight.prompt.md): required generation and verification
  context for Git discovery, the `createStrictSourceAccess` module export and
  all bound-method inputs/results, and safe native reads.
- [Runtime client](runtime-client.prompt.md#shared-contract-check-history):
  required generation and verification context for the local history API only.

The native discovery/history/write effects are not bound by the expansion
Runtime entry. Supplied blob replies do not prove host-file or history safety.
