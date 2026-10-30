# Report a problem with pdd

Use this guide to report a problem with pdd itself: the `pdd` command, the PDD skills, the PDD interpreter (`pdd test` and `pdd simulate`) or these docs. The guide is for people and for their coding agents. Most issues come from agents, so each step is an instruction that an agent can follow.

For a bug in your own project, use the `pdd-bug` skill. For access to the interpreter, see [Access](../README.md#access).

**Agent:** do the steps in order. Get each fact from a command or from the person. Never invent a fact. When you do not know a fact, ask the person.

## 1. Check the pdd version

```sh
pdd --version
```

| It prints | What to do |
|---|---|
| `0.1.` and a number, for example `0.1.10` | Go to step 2. |
| `pdd, version 0.0.` and a number, for example `pdd, version 0.0.310` | This is the Python pdd (0.0.x). It is retired. Do not file an issue. Tell the person to install pdd with the steps in [Install](../README.md#install). |
| `command not found` | pdd is not installed. Tell the person to install pdd with the steps in [Install](../README.md#install). |

If the person installed pdd 0.1.10 or newer and `pdd --version` prints `pdd, version 0.0.` and a number, the Python pdd comes first on the PATH. See [USAGE §3](USAGE.md#3-if-you-have-the-old-python-pdd).

If the version is older than the version in [Install](../README.md#install), update pdd first with the steps in Install. Then run the failing command again. Report the problem only if it stays.

## 2. Look for the problem first

1. Read the tables in [When something goes wrong](../README.md#when-something-goes-wrong) and [USAGE §13](USAGE.md#13-troubleshooting), and the known limits in [USAGE §12](USAGE.md#12-known-limits) and [RUNBOOK §16](../RUNBOOK.md#16-known-limits-today). If a table tells what to do, do it.
2. Search the open issues with 2 or 3 words from the error message or the command:

   ```sh
   gh issue list -R promptdriven/pdd --state open --search "serve 404"
   ```

3. If an open issue has the same problem, add a comment to it. Do not open a second issue. A comment is public too, so do steps 3, 4 and 7 for it: collect only the facts that the issue does not have, remove secrets and private data, and show the comment to the person. Post it only when the person says yes. Write the comment to a file outside the repo:

   ```sh
   gh issue comment 123 -R promptdriven/pdd --body-file /tmp/pdd-comment.md
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
- **The link or ID.** The report link that `pdd test` printed (`https://…/r/…`), or a request ID that pdd printed. For a workflow run, the issue number and the output of `pdd workflow status N`, `git --version` and `herdr --version`.
- **The expected result.** What the person expected to see.
- **The smallest example.** The smallest repo or set of files that shows the problem. For example: one prompt, one Story with 2 criteria and its test file. `pdd test --files` lists the files that a check sends.
- **The agent.** The name and version of the agent that ran pdd. Write "none" when the person typed the command.

A report link shows the steps, the checks and the answers of the check, and anyone with the link can open it. Add it only when the person agrees. Never add a Simulator link (`…/s/…`). Anyone with a Simulator link can use it and spend its AI calls.

## 4. Remove secrets and private data

An issue or a comment stays public. Read all the text before you post it. Remove:

- tokens, passwords, keys and the output of `gh auth token`;
- Simulator links and private chat links;
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

Show the person the title and the body. File the issue only when the person says yes. The issue is public, and it shows the GitHub account of the person. Do the same for a comment on an existing issue (step 2).

Write the body to a file outside the repo. Then run:

```sh
gh issue create -R promptdriven/pdd --title "[alpha] <the title>" --body-file /tmp/pdd-issue.md
```

Give the person the issue link that `gh` prints. A person without `gh` can use the [issue form](https://github.com/promptdriven/pdd/issues/new?template=bug.yml).

## A good example

This example is not a real problem. It shows the shape of a good issue.

Title: `[alpha] pdd simulate --serve answers 404 for a route that my prompt declares`

~~~markdown
### pdd version
0.1.10

### What you did
I tried my HTTP API by hand, with the route that my prompt declares.
```sh
pdd simulate my-story --serve 8091
curl -i http://127.0.0.1:8091/api/items
```

### What happened
```
HTTP/1.1 404 Not Found
```
Exit code of curl: 0. The prompt entry has the input schema title `HTTP GET /api/items`. `pdd test my-story` passes.

### What you expected
The answer of the prompt for GET /api/items, the same as in the check.

### Runtime link or run id
None.

### Smallest example
A new repo with one prompt that has one entry, `HTTP GET /api/items`, one Story with 1 criterion and its test file.

### OS
macOS 15.3

### Node version
v22.20.0

### Agent
None. I typed the commands in a terminal.

### Suspected cause
Maybe pdd does not serve the routes of a prompt with only one entry. I did not test a prompt with two entries.
~~~

## A bad example

Title: `pdd test broken, retry bug in runtime-client.mjs`

```
pdd does not work. The retry code in runtime-client is wrong. Also pdd simulate is slow,
and the README has a typo. My token is ghp_… if you need it.
```

What is wrong:

- The title gives a guess as a fact. It does not say what the person saw.
- The body has no version, no command, no output and no expected result.
- The issue has three problems.
- The body has a token. Never paste a token. If a token is in an issue, revoke the token at once.
