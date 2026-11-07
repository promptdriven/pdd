# Sort issues before starting work

As a repository owner, I can let Autopilot sort the backlog, send work to the
right owner and fix a shared cause once.

## Acceptance criteria

1. A trusted issue needs a current sort record before new work. Changed issue text, trusted comments, examined source, release or area settings require a new record. An unrelated issue does not.
2. Explicit areas take precedence over local CODEOWNERS. One, two and three areas can resolve local work and another owner. An unknown owner waits for one question. A repo without a rule has one Autopilot area.
3. Auto closes fixed, duplicate and old-code issues after one evidence comment with a reopen hint. Observe proposes closure and leaves the issue open.
4. Another login gets an assignment and one note. Another repository gets a link note. Neither starts work. An unsure issue gets pdd:needs-owner and one question.
5. A person assignment or live claim prevents closure and reassignment. Writes run one at a time, at least one second apart.
6. Three current issues in one area with one cause wait for one umbrella run. Its code PR closes all members. Separate areas and causes keep separate work.

## Rules to check

For every combination of mode, ownership and route, a person-owned or claimed
issue cannot close or change assignee. Only local work can start. A group has at
most one eligible umbrella. Native dependency review and merge gates still apply.
