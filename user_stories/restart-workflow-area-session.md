# Open a saved area or replace an exhausted agent session

As a person whose workflow agent has reached its session limit, I want to open a saved area or start a fresh session for the current area, so that I can continue the same run without losing its worktree, completed work or approvals.

## Acceptance criteria

1. `pdd workflow open 2627` keeps its existing behavior: it focuses the current chat or resumes that chat's saved native session when it ended.
2. `pdd workflow open 2627 --new` replaces only the current area's owned chat with one new native session in the same worktree and saved agent configuration; the old native session is not resumed.
3. A replacement keeps the run identity, branch, worktree, active area, completed steps, step summaries, open gate, pending question, decisions, approvals and PR records. Its first message explains the saved progress and what remains; it does not restart or approve the workflow.
4. `pdd workflow open 2627 story` opens that run's recorded story chat without changing the current area or approvals. An unknown or not-yet-started area refuses before a launch, close or saved-run change. A historical-area request with --new refuses with guidance to select the current area.
5. Before replacing a chat, PDD confirms the saved tab, pane, workspace and worktree identity. A changed identity, unavailable inspection or unresolved earlier launch refuses before closing or launching anything.
6. PDD closes only the selected owned area tab and confirms that it is gone before launching once. It preserves the replaced chat's recorded identities and first-message artifact. Other area tabs and peer workflows stay untouched.
7. An interrupted or lost close/launch reply cannot cause a second launch on retry; concurrent requests cannot both start replacements. A request from the chat being replaced refuses and tells the person to use another terminal.
8. Canceled and completed runs keep their existing refusal. No open or replacement request pushes, opens a PR, approves a prompt, runs a Check/Try or changes the global agent installations or sign-ins.

## Rules to check

A fresh-session request may launch at most one new native session, after confirmed closure of its selected predecessor. It must preserve all workflow progress and human decisions; uncertainty never authorizes another launch. A historical-area open must not change which area can record progress or approve the run.

Runtime check: NOT RUN. The existing CLI Runtime entry does not bind saved-run, native session, Herdr ownership/close acknowledgement or cross-process persistence effects. Native tests and a private Herdr transcript with waiting stub agents must establish these criteria; syntax acceptance alone is not evidence of replacement.
