# Use an agent that is ready

As a person who has signed in to one coding agent, I want PDD to use that agent, so that another agent being missing or signed out does not stop setup or leave my workflow without a working chat.

## Acceptance criteria

1. With Codex signed in and Claude Code missing or signed out, setup succeeds and a workflow without --agent uses Codex.
2. With Claude Code signed in and Codex missing or signed out, setup succeeds and a workflow without --agent uses Claude Code.
3. With both signed in, a workflow without --agent keeps Codex as its first choice; --agent claude uses Claude Code and --agent codex uses Codex.
4. An explicit agent that is missing or signed out refuses before a workflow is allocated or launched, names that agent's install/sign-in command, and does not silently switch to the other ready agent.
5. Setup with both agents missing refuses with `Install Codex or Claude Code first.` and installation links. With both signed out, it refuses and gives `codex login` and `claude auth login` on separate lines. It does not install skills or edit agent configuration first.
6. A ready Claude Code in a custom CLAUDE_CONFIG_DIR counts as ready. Readiness checks and the selected workflow use the caller's HOME, PATH and agent configuration folders; no global setting or sign-in is changed.
7. If an agent's status is malformed or cannot be checked, PDD does not claim that agent is signed in. Another ready agent still works; when no agent is ready, the refusal gives the appropriate status command without printing private authentication output.
8. Readiness uses only noninteractive status commands. Help, version, completion and unrelated commands remain local and do not check agent sign-in. The checks make no AI call and never sign an agent in or out.

## Rules to check

A workflow is admitted only with a ready selected agent. Explicit choice cannot fall back; omitted choice prefers ready Codex, otherwise ready Claude Code. Missing, signed-out and unknown status never count as ready. A failing unselected agent must not veto a ready selected agent.
