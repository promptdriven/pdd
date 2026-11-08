# Verify prompt recovery

Use Node.js 22.16.0 or newer. No installation or hosted service is needed. Run from the repository root with a temporary HOME and XDG_CONFIG_HOME:

```sh
scratch=$(mktemp -d)
HOME="$scratch" XDG_CONFIG_HOME="$scratch/config" node --test \
  test/workflow-prompt-reentry.test.mjs \
  test/workflow-prompt-reentry-safety.test.mjs \
  test/workflow-prompt-reentry-card.test.mjs
result=$?
rm -rf "$scratch"
exit "$result"
```

These tests call the public workflow functions. They create temporary projects, Git worktrees, local bare remotes and peer clones. The safety cases use real Git fetch, push and merge. The card cases write check results through the native check client against a local fake Runtime. GitHub, Herdr and native agent launches use the repository fakes. They make no hosted call and start no live chat.

Check the reported test counts and exit status. Recovery must keep PR identities and code commits, place prompt edits on PR 1, clear code evidence, integrate the saved base, recheck prompt source and refresh the replay anchor before code. A peer's changed expected value at the final fetch must reopen Story work with no new code decision. A reference that moves after capture must not alter the pinned merge. Unchanged automatic recovery needs a recorded operator action and current claim ownership; strict or unscoped recovery must not advance automatically.

The tests remove their temporary projects after each case. TAP output is native evidence. It is not prompt-interpreter evidence or a live GitHub or Herdr integration result. For an old-code control, put the same tests and fixtures into a temporary copy of the base source. Keep the failed assertions. A setup failure does not detect the defect.
