# Verify prompt recovery

Use Node.js 22.16.0 or newer. No installation or hosted service is needed. Run from the repository root with a temporary HOME and XDG_CONFIG_HOME:

```sh
scratch=$(mktemp -d)
HOME="$scratch" XDG_CONFIG_HOME="$scratch/config" node --test \
  test/workflow-prompt-reentry.test.mjs \
  test/workflow-prompt-reentry-safety.test.mjs \
  test/workflow-prompt-reentry-card.test.mjs \
  test/workflow-prompt-merged-base.test.mjs
result=$?
rm -rf "$scratch"
exit "$result"
```

These tests call the public workflow functions. They create temporary projects, Git worktrees, local bare remotes and peer clones. The safety cases use real Git fetch, push and merge. The card cases write check results through the native check client against a local fake Runtime. GitHub, Herdr and native agent launches use the repository fakes. They make no hosted call and start no live chat.

Check the reported test counts and exit status. Recovery must keep PR identities and code commits, place prompt edits on PR 1, clear code evidence, integrate the saved base, recheck prompt source and refresh the replay anchor before code. A peer's changed expected value at the final fetch must reopen Story work with no new code decision. A reference that moves after capture must not alter the pinned merge. Unchanged automatic recovery needs a recorded operator action and current claim ownership; strict or unscoped recovery must not advance automatically.

Final-fetch deletion cases remove either the Story or scenario from the peer branch before terminal or explicit-reply code approval. Each must preserve the peer commit on PR 1, reopen the Story gate and save no code decision. Unavailable tree and present-file reads must refuse entry and keep the existing code gate and branches. Successful code entry must publish the durable code approval in PR 1 after validation. The approval gate identity tests check that order. A terminal override of an incomplete legacy gate binds the current Story contract before confirmation and preserves unrelated decisions and evidence. An explicit reply still requires displayed coverage.

Merged-base cases publish PR 1, add an unrelated prompt or scenario on main in a peer clone, then merge PR 1 there. After status completes the run at PR 1, terminal and explicit-reply approval must enter code from that pinned merged commit. Both legacy and Story-card gates must keep the run's approved files and replay anchor unchanged. The concurrent base file must remain present on the new code branch.

The tests remove their temporary projects after each case. TAP output is native evidence. It is not prompt-interpreter evidence or a live GitHub or Herdr integration result. For an old-code control, put the same tests and fixtures into a temporary copy of the base source. Keep the failed assertions. A setup failure does not detect the defect.
