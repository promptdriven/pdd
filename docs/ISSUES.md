# Report a problem with pdd

Use this guide to report a problem with pdd itself: the `pdd` command, the PDD skills, the PDD runtime (`pdd check` and `pdd try`) or these docs. The guide is for people and for their coding agents. Most issues come from agents, so each step is an instruction that an agent can follow.

For a bug in your own project, use the `pdd-bug` skill. For access to the runtime, see [Access](../README.md#access).

**Agent:** do the steps in order. Get each fact from a command or from the person. Never invent a fact. When you do not know a fact, ask the person.

## 1. Check that it is pdd v2

```sh
pdd --version
```

| It prints | What to do |
|---|---|
| `0.1.` and a number, for example `0.1.9` | This is pdd v2. Go to step 2. |
| A version that starts with `0.0.` | This is the Python pdd (v1). v1 is retired. Do not file an issue. Tell the person to install pdd v2 (below). |
| `command not found` | pdd is not installed. Tell the person to install pdd v2 (below). |

Install pdd v2 with the lines from the [README](../README.md#install):

```sh
npm install -g github:promptdriven/pdd
npx skills add promptdriven/pdd#alpha -g
pdd --version
```

If the person installed pdd v2 and `pdd --version` prints `0.0.` and a number, the Python pdd comes first on the PATH. See [USAGE §3](USAGE.md#3-if-you-have-the-old-python-pdd).

If the version is older than the version in the [README](../README.md#install), update pdd first: run the install lines again. Then run the failing command again. Report the problem only if it stays.

## 2. Look for the problem first

1. Read the tables in [When something goes wrong](../README.md#when-something-goes-wrong) and [USAGE §13](USAGE.md#13-troubleshooting), and the known limits in [USAGE §12](USAGE.md#12-known-limits) and [RUNBOOK §16](../RUNBOOK.md#16-known-limits-today). If a table tells what to do, do it.
2. Search the open issues with 2 or 3 words from the error message or the command:

   ```sh
   gh issue list -R promptdriven/pdd --state open --search "lint result unknown"
   ```

3. If an open issue has the same problem, add a comment to it. Do not open a second issue. Add only the facts that the issue does not have, for example your versions, your command and your output:

   ```sh
   gh issue comment 123 -R promptdriven/pdd --body-file comment.md
   ```

4. If you are not sure that it is the same problem, open a new issue. Write "Maybe the same problem as #123" in the body.

## 3. Collect the facts

Run these commands:

```sh
pdd --version
node -v
uname -sr    # the OS. On macOS, also run: sw_vers -productVersion
```

Then collect:

- **The goal.** What the person tried to do, in one sentence.
- **The command.** The exact command that failed.
- **The output.** The full output, copied as text. Do not retype it. Add the exit code: run `echo $?` directly after the command.
- **The link or ID.** The report link that `pdd check` printed (`https://…/r/…`), or a request ID that pdd printed. For a workflow run, the issue number and the output of `pdd workflow status N`, `git --version` and `herdr --version`.
- **The expected result.** What the person expected to see.
- **The smallest example.** The smallest repo or set of files that shows the problem. For example: one prompt, one Story with 2 criteria and its test file. `pdd check --files` lists the files that a check sends.
- **The agent.** The name and version of the agent that ran pdd. Write "none" when the person typed the command.

A report link shows the steps, the checks and the answers of the check, and anyone with the link can open it. Add it only when the person agrees. Never add a Try link (`…/s/…`). Anyone with a Try link can use it and spend its AI calls.

## 4. Remove secrets and private data

A public issue stays public. Read all the text before you file it. Remove:

- tokens, passwords, keys and the output of `gh auth token`;
- Try links and private chat links;
- links to private repos, and private code;
- personal data: names, email addresses and paths that contain a user name. Write `~/my-app`, not `/Users/ana/my-app`.

## 5. Write the title

Start the title with `[alpha]`. Then write what fails for the person, in the person's words.

- Say what the person did and what they saw.
- Do not put a guessed cause in the title.
- Do not put a fix in the title.

## 6. Write the body

Write one problem in each issue. When you find two problems, file two issues and link them.

Use these headings. The [issue form](https://github.com/promptdriven/pdd/issues/new?template=bug.yml) has the same fields.

~~~markdown
### pdd version
The output of pdd --version.

### What you did
What the person tried to do, in one sentence. Then the exact command:
```sh
the command
```

### What happened
```
the exact output
```
Exit code: N

### What you expected
What the person expected to see.

### Runtime link or run id
The report link, the request ID or the workflow status. Write "none" if there is none.

### Smallest example
The smallest repo or file shape that shows the problem.

### OS
The OS and its version.

### Node version
The output of node -v.

### Agent
The agent and its version, or "none".

### Suspected cause
Only when you have a guess. Say why you think so.
~~~

Keep facts and guesses apart:

- Under "What happened", write only what the person or the agent saw.
- Put a guess under "Suspected cause", with the reason for it. Never write a guess as a fact.
- A cause that you found in the code of pdd is still a suspected cause. Name the file and the line.

## 7. File the issue

Show the person the title and the body. File the issue only when the person says yes. The issue is public, and it shows the GitHub account of the person.

Write the body to a file outside the repo. Then run:

```sh
gh issue create -R promptdriven/pdd --title "[alpha] <the title>" --body-file /tmp/pdd-issue.md
```

Give the person the issue link that `gh` prints. A person without `gh` can use the [issue form](https://github.com/promptdriven/pdd/issues/new?template=bug.yml).

## A good example

Title: `[alpha] pdd check --lint waits 90 seconds, then says "The lint result is unknown"`

~~~markdown
### pdd version
0.1.9

### What you did
I signed up at promptdriven.ai and tried to lint my first Story.
```sh
pdd check --lint
```

### What happened
```
Checking 3 files (29 KB) on the PDD runtime (lint, 0 AI calls)…
Still checking the files: waiting for an answer · 16 s
…
The lint result is unknown. Run pdd check --lint again; a lint uses no AI calls.
```
Exit code: 3, after 90 seconds. I waited 1 minute and ran it again, as the README says. The result was the same.

### What you expected
A lint result, or a message that tells me why pdd cannot lint.

### Runtime link or run id
None. pdd printed no link.

### Smallest example
A new repo with one prompt, one Story with 2 criteria and its test file.

### OS
macOS 15.3

### Node version
v22.20.0

### Agent
None. I typed the command in a terminal.

### Suspected cause
My GitHub account may not have PDD Cloud approval yet. I signed up 10 minutes before the command.
~~~

## A bad example

Title: `pdd check broken, retry bug in runtime-client.mjs`

```
pdd does not work. The retry code in runtime-client is wrong. Also pdd try is slow,
and the README has a typo. My token is ghp_… if you need it.
```

What is wrong:

- The title gives a guess as a fact. It does not say what the person saw.
- The body has no version, no command, no output and no expected result.
- The issue has three problems.
- The body has a token. Never paste a token. If a token is in an issue, revoke the token at once.
