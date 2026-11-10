As an Autopilot operator, I want blocked runs to wait without using a working slot, chat memory or a pane, so that ready work can progress.

## Acceptance criteria

1. A named external blocker parks an automatic run. The run keeps its claim, worktree, branch, saved session and completed work. Its chat and shell panes close before its slot becomes free.
2. Only working runs count against the run limit. Unknown process or check custody stays occupied. Other ready issues can use free capacity under the normal limits.
3. A cleared blocker resumes the same saved session. Ready parked runs wake before new issues, oldest first. A dispatch failure keeps a reservation and does not start a second session.
4. One no-verdict does not enable interpreter test mode. Three consecutive no-verdict observations enable one-at-a-time interpreter tests. A verdict restores normal interpreter capacity. Code and native tests can progress.
5. An issue in the same root-cause group joins that group's existing run through its saved requests. File overlap alone does not prevent other work.
6. A park older than 48 hours, or an oldest surplus park above twice the working cap, releases its claim to the existing queue. Saved branch work remains. One marked release comment is posted. Both limits can be configured.
7. Status shows working and parked counts by named blocker and the interpreter test-mode streak. Tick decisions need no AI call.
