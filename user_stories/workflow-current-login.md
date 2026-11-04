# Continue a workflow after changing the current Codex login

I can change the login in my machine's one default Codex home and continue the
same saved conversation, issue and worktree with my completed work intact.

## Acceptance criteria

1. After I change the login in the same default Codex home, I can type Continue in the existing conversation. PDD does not create a fresh conversation just because that login changed.
2. When PDD starts a default-home Codex chat, its child uses the machine home selected when the run started and no unrelated CODEX_HOME inherited from the Herdr server or pane. Later areas keep that home even when approved from another terminal.
3. If the original process has ended and a restart is needed, ordinary `pdd workflow open 2575` resumes the exact saved native conversation in the assigned worktree, using that selected home. The issue, run, branch, completed steps, gate, question, decisions, approvals and PR records stay intact.
4. Opening a healthy live conversation focuses it without another launch. A quota error, missing observation, unknown ownership or unresolved launch does not authorize a duplicate process, a fresh conversation or a blind restart. A live question dialog keeps its existing protection.
5. PDD recognizes the exact conversation resumed in its owned pane as running. A retained pending request reaches that conversation once on safe explicit retry, with the same request identity; it is never redirected to another area or session and does not rewind workflow progress.
6. Older runs without a saved machine home remain readable. Before their next required native start or resume, PDD selects and saves the invoking machine home once; status or focus alone does not select one, and a failed checkpoint launches nothing.
7. Explicit CODEX_HOME plus `--new` remains the separate fresh-conversation fallback, preserving its existing profile selection, attempt recovery, cancellation and identity safeguards. Other agents keep their existing behavior. PDD does not read or change credentials, migrate homes or change global sign-ins.
8. The CLI documentation explains Continue in the same default home, exact-conversation resume when needed, and the separate fresh-conversation fallback, without claiming that a selected folder proves the active login or authentication reload.

## Rules to check

The selected machine home and saved null/default config must determine both
Codex child environment and native session lookup. An unrelated server/pane
HOME or CODEX_HOME must never choose the child's default home or lookup root.
A later terminal cannot replace an already saved machine home.

For an existing saved Codex conversation, ordinary open launches zero new conversations:
a positively ended owned chat may
resume only its exact saved UUID. Live, blocked-dialog, unknown, unconfirmed,
cancelled and completed controls retain their existing dispatch restrictions.
A quota error alone is insufficient end evidence. Observations may update only
the same run/area/chat identity; late results must not revive or rewind progress.

Pending request retry preserves accepted identity and existing delivery rules.
When the original Codex conversation is known, the same pane with a different
UUID, or an unavailable required identity, must send zero prompts and retain
that request's identity, original custody and workflow progress.
Other agents keep their existing area/pane and readiness rules, including delivery
without an observed native UUID.
Do not replay an acknowledged or possibly dispatched request, redirect a stale
target, or treat submission acknowledgement as proof the agent acted.

## Checks and acceptance limits

Requirement-derived cases and mutation controls:
[native case inventory](../test/workflow-current-login/cases.json).
This inventory is a draft plan, not executable tests or an Interpreter scenario.
Current Runtime entries do not bind start/open, child environment, native lookup,
Herdr custody or durable checkpoints. No prompt-check or simulation verdict is
claimed. PR 2 adds ordinary Node checks through the real public boundaries.

Real login switching, Continue reloading authentication and successful provider
work in the same native conversation require separately coordinated observation.
Safe synthetic environment/UUID evidence cannot prove those effects. Documentation
must state any remaining acceptance limit when these observations are unavailable.
