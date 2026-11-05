# Refresh workflow PR descriptions

I can rely on my workflow PR description to reflect the latest approved drafts and area evidence.

## Acceptance criteria

1. PR descriptions refresh after approval or area updates even when the installed gh cannot use pr edit because of the Projects classic query; the complete description stays intact.
2. If an update fails, I see a safe one-line gh cause and how to retry the workflow. Existing publication safety remains in force. The printed retry refreshes only the description and does not advance the workflow.

## Rules to check

A failed pre-push publication-pending update must not allow a source push. A failed informational refresh warns rather than undoing publication. Replay and final-body safety still apply.

## Regression cases

- An approval refresh and an area refresh each preserve the complete description, including Unicode, newlines and the ownership marker, when `gh pr edit` would fail on the Projects classic query.
- A nonzero exit or rejected update reports a useful safe first-line reason and a retry command; a rejection with code zero is still a failure. Missing stderr uses a useful fallback. Credentials, control characters and private paths do not appear in the reason.
- A failed pending update prevents the source push. A failed final update after a push leaves the pending description and reports the retry; an informational-only failure warns and retains the previous inventory description.

## Focused native cases for the retry route

These cases are authored expectations for later native tests. The current Runtime
interface does not bind approval, publication, or their outside effects; these
cases do not claim Runtime coverage.

- After an approval refresh fails and the run advances to Code, execute the exact
  printed `pdd workflow refresh-description ISSUE PR` through the real CLI parser,
  using its printed issue and PR numbers. The existing PR description is refreshed
  and the gate, decisions, steps, area, chats and later progress remain unchanged.
- With public head older than the working tree, retry does not attach working-tree
  evidence to that head or push source; if a safe body cannot be established it
  refuses and leaves the existing body and pending state unchanged.
- A rejected retry reports the safe one-line cause and the same executable retry
  command; it leaves publication-pending intact. A successful final update clears
  pending only when the existing final-body rules permit it.
- Missing or extra operands and unsupported options are rejected by the real parser
  before the runner is invoked; help includes the description-only command.
