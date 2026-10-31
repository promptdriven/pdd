# Area chats in Herdr

Own `src/workflow-chat.mjs`. An area chat is one native Codex or Claude session in its own tab of the Herdr session `pdd`. pdd starts it and then leaves. pdd never watches it.

- Use only the session `pdd` (`herdr --session pdd …`). Never touch the person's default session or another session.
- If the `pdd` server is not running, start `herdr --session pdd server` in the background. Remove agent-session markers (`CLAUDECODE`, `CLAUDE_CODE_*` session values, `CODEX_THREAD_ID`, `HERDR_*`, `PDD_AGENT_SESSION`) from its environment, so chats in it save their transcripts. Wait for it only while that server process is alive.
- `homeVariable(agent)` is `CLAUDE_CONFIG_DIR` for Claude and `CODEX_HOME` for Codex. `expandHome(dir, env)` returns null for an empty value, the home folder (`HOME`, else `os.homedir()`) for `~`, `<home>/x` for `~/x`, and any other value as it is. `isFolder(dir)` says whether a folder is there. Every place that starts or resumes a chat, or reads its sessions, expands the saved config folder first, so a run saved with the `~` text still works.
- `startChat({run, area, message}, ports)`: use the [run layout](workflow-herdr-layout.prompt.md) (a workspace per repository, a workspace `#N NAME` per run, a new tab per area named after the area). Write the first message to `<run folder>/<area>-start.md`. In the tab, run one short shell line: `env PDD_AGENT_SESSION=1 [CLAUDE_CONFIG_DIR=…|CODEX_HOME=…] claude --dangerously-skip-permissions --session-id <new uuid> "$(cat '<file>')"`, or for Codex `codex --no-daemon --dangerously-bypass-approvals-and-sandbox -c 'projects={"<worktree>"={trust_level="trusted"}}' "$(cat '<file>')"`. The config folder is the run's `configDir`: the `CLAUDE_CONFIG_DIR` or `CODEX_HOME` of the terminal that started the run. So every area chat of a run uses the same account, even when someone approves from another terminal. Return the chat record (tab, pane, workspace, label, start time, session `{agent,id}` when known, config folder). Prepare that identity before the pane launch. If its reply fails, attach that same record as `error.chat` with `startUnconfirmed: true`; the caller saves it because the command may have dispatched.
- `sendToChat(chat, text, ports)`: `herdr agent prompt <pane> <text>`. Return `{ok}` or `{ok:false, code}` (`agent_not_found`, `agent_blocked`, …).
- `chatSession(chat, ports)`: read `herdr agent get <pane>`. Return `{alive, status, sessionId}`; when Herdr fails, `{alive: false, status: null, sessionId: null, code, message}` with Herdr's error code (`agent_not_found` when no agent runs in the pane).
- `openChat({run, chat}, ports)`: if the tab is gone, make a new tab in the run workspace, except for an unconfirmed launch: inspect its saved agent first. If the tab and agent/pane are both confirmed missing, return restartAvailable without creating a tab, launching or resuming. The caller archives that stale start and offers an explicit new open to start this area again in the same run. A live agent or an unavailable inspection retains the original identity and refuses replacement. If no agent runs in the pane, resume the native session there (`claude --resume <id>`, `codex resume <id>`, with the same full-access flags), and set `chat.resumedAt` to now. An inspection failure other than confirmed `agent_not_found` must throw before any native launch/resume; unavailable Herdr is not proof of an empty pane. For a retained `startUnconfirmed` chat, an observed live agent confirms the original launch. Without it, refuse another launch/resume and tell the person to inspect that same pane; never send a fresh first message blindly after a lost reply. A failed resume request marks that same chat unconfirmed too. Successful positive observation clears the unconfirmed flag. Focus the tab. Attach with `herdr session attach pdd` only when the caller has a terminal and is not inside Herdr. Otherwise print where the chat is.
- `closeChats(run, ports)`: close each chat tab, then the run workspace, then the repository workspace when no other run uses it. Failures are warnings. Chat labels are `<repo name>#N NAME › AREA`.

Pass input preAgentRefusal to the layout only for a saved first-start run with no chats, completed steps or
PRs and the canonical linked_worktree_source chat failure (or its exact saved startup warning on legacy runs).
The layout owns inventory-backed recovery; neither chat startup nor recovery allocates another Git worktree.
Forward the command execFile port to the layout's verified repository-parent lookup.

Herdr transport reads complete stdout/stderr before interpreting JSON or a nonzero exit. Responses larger than a pipe buffer must retain their full content, and a nonzero response must keep its structured error code. Attaching to a session waits for stream closure before reporting its exit status.

Full-access flags stay. Do not pin tool versions. No timeouts. Shell-quote every path and the resume id in the shell line. A native session id (from Herdr, a session file or the run record) is stored or used only when it is a UUID; `chatCommand` refuses any other resume id.

## Thread policy at native launch

For each actual Codex first start, stopped-session resume or explicit fresh
session, call the [thread selector](workflow-agent-limits.prompt.md) with the saved
area's budget. `chatCommand` accepts optional `threadBudget` (the selector result);
add a shell-quoted `-c features.multi_agent_v2.max_concurrent_threads_per_session=N`
only for its nonnull override, preserving trust flags and UUID safeguards. Claude
and absent budgets keep the exact existing command and do not inspect config.

Acquire configuration through injected ports, with production filesystem defaults.
Use expanded saved chat configDir, then saved run configDir, then CODEX_HOME, then
HOME/.codex (os.homedir fallback). Read only config TOML and necessary active
configuration layers; never authentication files. Establish effective active
system/user/project/profile values using Codex precedence, or supply layersSafe=false
and a visible reason. Check whether extra system/project layers or an active
profile are present: unsupported present layers may conservatively skip injection.
When these extra layers are absent and user config is parseable or confirmed
absent, selection must proceed; never mark every opted-in chat unknown. A missing
user config alone does not prove layers absent.
Do not assume a read/parse failure means no setting. Never edit these files.

Save optional `threadBudget: {total,source,override,reason}` on each launch's chat
record before dispatch, including error.chat on uncertain starts. On a later
actual launch reselect from current configuration, archiving the prior selection
in `threadBudgetHistory` with its launch time before replacing the current one;
observing/focusing a live chat does not reselect. Fresh-session archived chat
records retain their original setting. A newly explicit setting always controls
the new launch, even when the historical workflow selection differs.

## Dependencies

- [Thread selection](workflow-agent-limits.prompt.md): required authoring,
  generation, runtime and testing context for selection and record meaning.
- [Run layout](workflow-herdr-layout.prompt.md): required generation/testing
  context for the existing layout operations.
- Native filesystem/config-layer acquisition, Herdr dispatch and native agent
  acceptance are outside this module's unsupported Runtime effects; native
  tests bind injected read/config/environment/Herdr/process ports.
