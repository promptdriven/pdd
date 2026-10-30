# Resume workflows in independent clones

I can start or reopen my saved workflow from a verified clone of the same GitHub repository while another clone has its own active workflow. Each clone keeps its own Herdr workspaces, and the other person's work stays untouched.

## Acceptance criteria

1. With a valid existing workspace for clone A of "promptdriven/pdd", I can open a saved workflow in separately verified clone B. B gets its own parent and run workspace with an unused stable checkout-qualified parent name; A's registry records, names, workspaces and tabs stay unchanged.
2. Opening another workflow from A reuses A's existing parent, including its legacy ownership record. Calling from a linked checkout reuses the verified parent for that same Git directory; a verified bare primary stays supported.
3. Reopening my saved workflow keeps its original run identity and assigned checkout. Changed saved checkout, Git directory, parent binding or workflow label refuses before any new allocation. Unknown allocation outcomes and lost replies do not trigger duplicate allocation on retry.
4. A changed or forged workspace identity, uncertain ownership, duplicate ownership for one checkout, or occupied chosen qualified name refuses without adopting a workspace or trying another name. A different checkout never justifies taking over existing work.
5. Closing B's last workflow closes only B's safely owned idle parent. A and its active workflow stay intact. Added tabs or panes, changed identities and uncertain close replies still prevent unsafe cleanup.
6. Existing repository naming and qualification for different GitHub repositories stay supported. Folder names do not replace GitHub origin identity, and adding another clone never renames a peer clone.

## Rules to check

Ownership is the verified GitHub repository together with its canonical shared Git directory. Selection, reuse and idle cleanup must use both values. Forbidden: choosing the first repository-name match across independent clones, mutating any peer during same-repository allocation or cleanup, or rebinding an existing run to make recovery succeed.

Keep checkpoint, durable intent, returned ownership and agent-start order. Confirmed pre-agent linked-checkout refusals alone retain their guarded explicit retry; other interrupted or lost replies remain uncertain. Forbidden: auto-retry after uncertainty, guessed opaque IDs, allocation under an occupied name, or a second dispatch justified by an old refusal warning.

## Native cases to implement and replay

These are requirement-derived plans, not executed checks or Runtime vectors. Use the public layout functions with deterministic Herdr/Git replies and disposable real registry directories; inspect exact mutation calls and peer-record preservation. Each action below is a separate bounded step, with shared state only where stated.

- Seed version 1 with ready legacy A as the first repository record, valid public inventory and no B entry/run workspace; open B's original saved UUID/cwd. Expect a second parent under the common-directory digest-qualified name, B's run and area tab, and zero changes to A. The 0.1.10 semantic control must refuse instead of returning B's layout; a crash is not detection. (1, 6)
- From that resulting world, open A again; expect A's original parent, B unchanged. Repeat the same-directory linked-caller and verified bare-primary variants in separate fixtures. (2)
- From that resulting world, close B's area/run then call idle cleanup for B; expect exactly B's saved workspace closed and only B's repository record removed. Put A first to expose repository-only selection. Cleanup A separately while B is active in the mirrored fixture. (5)
- Separately vary saved run commonDir, cwd, parent binding and label; assert refusal with no allocation/rebinding and original UUID/cwd retained. Retain legacy run labels. (3)
- Separately seed uncertain parent intent, uncertain run intent, lost parent/create reply and lost worktree/open reply; explicitly reopen once and expect no duplicate mutation/agent dispatch. Test fresh confirmed refusal, then lost retry reply: an older refusal cannot authorize a third attempt. (3, 4)
- Separately alter selected parent/root identity, run checkout/Git metadata/root IDs, duplicate an exact namespace or occupy the deterministic candidate. Expect refusal, no suffix fallback, no peer mutation and no adoption. (4)
- Give B an extra tab or split pane, then an uncertain close acknowledgement in separate fixtures. Expect no unsafe parent removal or repeated close. (5)
- Retain different-repository short-name collision and unregistered short-label collision cases; assert original origin qualification, and no same-repository peer rename. (6)

Runtime check: NOT RUN. Canonical native layout/worktree owners lack accepted Runtime interfaces and host-filesystem resource bindings (#2548). No synthetic adapter or passing report is claimed. Native implementation/replay, bounded ownership checks with the old-code control, and an owned-run live Herdr startup remain required after contract review.
