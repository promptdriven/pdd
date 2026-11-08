# Working on PDD

Before you write or change a Story or a prompt, read the full [Prompting guide](docs/prompting-guide.md) in this conversation. Follow its method for module ownership, public behavior, what must not change, required dependencies and the edge cases that matter. A link or a Story template is not enough. If you lose the context, read the guide again before you write.

Read [skills/pdd-prompting/SKILL.md](skills/pdd-prompting/SKILL.md) for the core rules. Prompts are the source: change the prompt that owns the behavior before you change the code. Keep expected cases apart from what the code returns. Review changes to the contract with the person. Never invent their decision. `skills/pdd-prompting/guide.md` must stay the same as `docs/prompting-guide.md`, byte for byte. A test checks this, so change both together.

What this package contains:

- Ten skills in `skills/`: `pdd-prompting`, `pdd-setup`, `pdd-small-change`, `pdd-bug`, `pdd-feature`, `pdd-product`, `pdd-graph`, and the Autopilot skills `pdd-autopilot`, `pdd-check` and `pdd-merge`. People install them with `npx skills add promptdriven/pdd` (`-g` for all projects). The order is: install the skills, then the `pdd-setup` skill once for each repo, then the pdd command only for runs with PRs and for `pdd test`, `pdd lint`, `pdd simulate` and `pdd approve`. The pdd command does not copy skills on each command: `pdd setup` copies them to the user skills folders (`~/.agents/skills`; `~/.claude/skills`, or `$CLAUDE_CONFIG_DIR/skills` when it is set) only when they are missing, and replaces an older copy that has the `.pdd-skill.json` marker. It never touches a copy without the marker, or a symlink. pdd never copies them into the person's repo. Each `SKILL.md` has `pdd-skills: VERSION` under `metadata:` in its frontmatter: change it with the package version. Keep each workflow skill small and its step files short. Do not repeat a rule that `SKILL.md` already states. Write each `description` so that an agent picks the skill by itself.
- People open Codex or Claude Code as usual and call `pdd-feature`, `pdd-bug`, `pdd-small-change` or `pdd-prompting`. Call a skill with `$pdd-feature` in Codex or `/pdd-feature` in Claude Code (or ask for it by name). `pdd setup` and the `pdd-setup` skill add one short block (at most 10 lines, between `<!-- pdd:start -->` and `<!-- pdd:end -->`) to `CLAUDE.md`, else `AGENTS.md`. They never paste the guide.
- `pdd workflow run` makes a worktree and a branch for an issue, opens the area chats in Herdr (session `pdd`) and returns at once. pdd has four jobs: start, gates, PRs and status. There is no controller process, no polling loop and no time limit.
- `feature` and `bug` show the person a Story card from the run's real files at the Story gate, and the person approves each Story. In a normal run, pdd then opens PR 1 (prompt, Story and tests) by itself when its saved check results pass in full on the current prompts, and follows the code-or-stop choice from the card. A changed Story or expected value shows the card again. Strict mode keeps the try-and-approve gate before PR 1 and the code question after it. PR 2 (code) is stacked on PR 1 while PR 1 is open. `small-change` makes one PR.
- A big feature request gets a plan first: `user_stories/PLAN.md`, many Stories, one test file for each Story, and one `Prompt tests` line for each Story. `status` shows `Stories: N of M pass`.
- Agents run the tests. A fresh subagent that did not write the code verifies it. pdd does not run tests. Autopilot merges through the guarded `pdd autopilot merge` route and pdd-merge skill. For manual gates and gates outside delegated scope, show the gate, then judge the person's later reply in any chat. Never treat a question, change request or earlier message as that later approval; no exact phrase is needed. An operator’s explicit auto setup and start authorizes ordinary automatic workflow gates within its scope; an applicable standing delegation can also authorize them. Record the actual attributed operator action or standing delegation through the supported native approval command, without presenting it as a later reply or using checker words as approval. Strict approval and repository-required human reviews still apply. pdd records nonblank words without grading them; blank input is refused. Only explicit approve calls advance person gates. Chat and steps never do; `done` opens PR 1 only for a normal run's verified full check pass under a valid Story approval (route `automatic-check-pass`). If a selected prompt changes, show the gate again; in a normal run, a prompt-only repair that passes the check in full keeps the Story approval. Terminal y/N covers the gate and its drafts once. Workflow strict mode comes from the main checkout (`sourceRoot`), outside the run worktree; standalone approval uses the current checkout's Git root. `"strict_approvals": true` in that root's `pdd.json` requires a person terminal. Never edit approval fields or decide expected values. See [approval commands](docs/cli.md#record-a-chat-approval). Agents use `pdd workflow done` and `pdd workflow ask`.
- Main agents merge only on an explicit person request. Follow [RUNBOOK §2](RUNBOOK.md#2-the-files). The operator’s explicit auto setup and start or an applicable standing delegation can supply that request; a configuration read alone cannot. For the delegated Autopilot gate and merge route, see [pdd-merge](skills/pdd-merge/SKILL.md).

```sh
pdd workflow approve N --said - <<'PDD_SAID'
<the person's exact words, or the actual attributed operator action for a covered automatic gate>
PDD_SAID
```

For one prompt, use:

```sh
pdd approve PROMPT --said - <<'PDD_SAID'
<the person's exact words, or the actual attributed operator action for a covered automatic gate>
PDD_SAID
```

Choose a delimiter absent as a whole line from the words. Keep it quoted. Stdin preserves newlines. Never put untrusted words into shell quotes or interpolate them into shell code.

- `docs/cli.md` shows every command form of `pdd --help`. `test/docs-commands.test.mjs` fails when a form is missing, so update `docs/cli.md` with each change to the command catalog.
- The README and the docs describe pdd as it is today, as if this were the first version. Put history and change notes only in the GitHub release notes. The one exception is the short note for people who have the Python pdd installed. `test/docs-first-time.test.mjs` fails on history words.
- Agents start in full-access mode. `pdd setup` previews per-agent MCP config changes and asks y/N before writing them. pdd does not copy credentials or touch the person's default Herdr session.

Keep the package self-contained: no private dependencies and no credentials. Only `pdd test`, `pdd lint`, `pdd simulate` and the Try tools in `pdd mcp` call the PDD interpreter, with the user's gh token; the address is one setting (`PDD_RUNTIME_URL`, default `DEFAULT_RUNTIME_URL` in `src/runtime-client.mjs`). Do not import captured conversations or operational fixtures.

Each path has one active writer. Use a topic branch, keep other work and keep implementation prompts with their code. Use ordinary Node tests for changed public behavior. Avoid tests that only check prose or repeat the implementation. The public full suite is `npm test`. It needs no live service and no model call. A real agent run that the person asked for is a separate activity.

Report what changed, the real check results and any behavior that is not proved. A local draft or PR summary is not publication. Keep execution notes outside the repository. Public source publication needs a review and a green public full suite. Follow the route of the named integrator. Never force-push, rewrite private repository history or publish a package to npm as a routine check.
