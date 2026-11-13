As a person reviewing a code change, I want to finish the review step without publishing, so that I or another checker can inspect the local result before anything leaves the machine.

Issue: https://github.com/promptdriven/pdd/issues/2947

## Acceptance criteria

1. In a code PR area, `pdd workflow done review --no-publish --summary "Local review complete"` saves the review and its evidence without committing, pushing, creating or editing a PR, or starting a chat.
2. When the area's steps are complete, the response and workflow status show that publication is deferred and give `pdd workflow publish ISSUE`. Further step recording preserves that hold.
3. `pdd workflow publish ISSUE` publishes the finished area's current local result through the ordinary safety checks, without replacing any step's summary, evidence or timestamp. A retry after publication failure preserves the local result and records.
4. Publication refuses an unfinished area, a pending question, an approval gate, a stopped run; it never substitutes for approval.
5. `--no-publish` refuses outside a code PR area before changing steps. Without the option or a saved hold, finishing review retains automatic publication.
6. Deferring a finished small-change PR works in the same way. Updating an existing PR can also be deferred without editing its published description or pushing the update.

## Rules to check

The local record is neither publication nor approval. Explicit publication uses the existing publication checks and never records review a second time. Existing Story and prompt approval gates remain required.

## Verification boundary

Native public runner and CLI tests cover this Story. The existing workflow runner Runtime interface is partial and does not expose stepDone or publication; this change does not invent a replacement interface for its native Git and workflow execution.
