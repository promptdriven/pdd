# Sort issues before starting work

As a repository owner, I can let Autopilot sort the backlog, send work to the
right owner and fix a shared cause once.

## Acceptance criteria

1. A trusted issue needs a current sort record before new work. Changed issue text, trusted comments, examined source, release or area settings require a new record. An unrelated issue does not.
2. Explicit areas take precedence over local CODEOWNERS. One, two and three areas can resolve local work and another owner. An unknown owner waits for one question. A repo without a rule has one Autopilot area.
3. Auto closes fixed, duplicate and old-code issues after one evidence comment with a reopen hint. Observe proposes closure and leaves the issue open.
4. Another login gets an assignment and one note. Another repository gets a link note. Neither starts work. An unsure issue gets pdd:needs-owner and one question.
5. A person assignment or live claim prevents closure and reassignment. Writes run one at a time, at least one second apart.
6. New and changed issues join, form or leave groups by their current saved cause. Three members or members across local areas wait for a dedicated Global fix umbrella. Claimed and open-PR work finishes before it can join; a running umbrella gets a membership note.
7. Both global fix PRs reference members. After the fixing PR merges, every member needs a fresh sort. Only members confirmed fixed close with evidence; the rest stay open.
8. Autopilot status and the graph show each group's size, cause and umbrella. Each invocation routes at most 10 unfinished issues and attempts at most 20 sort writes. A low or reserve GitHub budget stops further effects.

## Rules to check

For every combination of mode, ownership and route, a person-owned or claimed
issue cannot close or change assignee. Only local work can start. A group has at
most one eligible umbrella. A member cannot start before its required umbrella,
and a pre-merge sort cannot authorize post-merge closure. Native dependency review and merge gates still apply.
