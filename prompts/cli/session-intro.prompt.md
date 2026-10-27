# Session intro

Own `src/session-intro.mjs`. Export `renderSessionIntro({packageRoot, cwd, request, workflowName})`. It returns the short first message for `pdd session` and for the manual `pdd workflow NAME` shortcut. The message is about 600 tokens. It does not paste the guide, a skill or a workflow. The agent loads the skills on demand from the folders that [skills install](skills-install.prompt.md) fills.

## The message

Fill in the values in braces. Lines end with `\n`. There is no blank line at the end.

```
This is a PDD session in {cwd}.
In PDD, prompts are the source. Write the prompt, Story and test cases first, then the code.

Prompting guide = the pdd-prompting skill. Read its guide.md in full before you write or change a prompt, Story or test cases.
Core rules:
{core rules}

Workflows = the skills pdd-small-change, pdd-bug and pdd-feature.
- To do the work in this chat, follow the matching skill here.
- To turn a GitHub issue into a PR: {pdd} workflow run <name> <issue> (you can start it for the person when they ask).
When a request fits a workflow, suggest it.

Use this pdd: {pdd}
If a skill is missing, read it in {packageRoot}/skills.
{request, or: Ask what the person wants to work on.}
```

- `{cwd}` is the folder where pdd runs.
- `{core rules}` are the `- ` lines of the `## Core rules` section in `<packageRoot>/skills/pdd-prompting/SKILL.md`, unchanged and in order. The intro and the skill cannot drift apart. If the file cannot be read or the section has no rule, throw an error.
- `{pdd}` is the absolute Node executable (`process.execPath`) and the absolute `<packageRoot>/bin/pdd.mjs`, joined by a space. Quote a word for a POSIX shell only when it has characters outside `A-Z a-z 0-9 _ @ % + = : , . / -`. A login shell can find another `pdd` on PATH, so the agent must use this command.
- `{request}` is the person's request text, unchanged. Without a request, the last line is `Ask what the person wants to work on.`
- With `workflowName`, add one last line: `Use the pdd-{workflowName} skill for this request.` If `<packageRoot>/skills/pdd-{workflowName}/SKILL.md` is not a readable file, throw an error.

## Dependencies

Read the full [Prompting guide](../../docs/prompting-guide.md) before you change this prompt. Follow the [alpha boundary](public-boundary.prompt.md). The [CLI](pdd-cli.prompt.md) passes the message to the [native session launcher](native-session.prompt.md).
