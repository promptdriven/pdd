# Autopilot settings on GitHub

Own `src/autopilot-github.mjs`. Export `publishAutopilotSettings(input, ports)` and `checkAutopilotSettings(input, ports)`. Autopilot workers start from the default branch of the repository on GitHub and read `pdd.json` there. A mode, trust or untrust command saves the setting in this checkout ([Autopilot settings](autopilot.prompt.md)). Publish puts the same setting on GitHub. Check says when GitHub has another setting. Neither function changes the current branch, the index or the uncommitted files of the checkout: every GitHub change goes through the GitHub API.

## Input and result

- `publishAutopilotSettings({cwd, action, mode, retry}, ports)`: action is `mode`, `trust` or `untrust`. mode is the named mode of a mode action. retry is the command that the person can run again, for example `pdd autopilot auto`.
- `checkAutopilotSettings({cwd}, ports)`.

Both find the Git top-level folder of cwd and read the key `autopilot` of its `pdd.json` (the local value). Both return `{state, message}`. The message is one line or empty. Neither throws: an unexpected error is a result.

## Ports

- `github.repository()` returns `{repository, defaultBranch}`. The native port calls `resolveWorkflowRepository({cwd: root}, {execFile})` of [workflow GitHub](workflow-github.prompt.md): the `origin` remote and `gh repo view`, with the gh sign-in that pdd already uses. There are no new credentials.
- `github.request({method, path, body})` returns `{status, body}` for each HTTP answer of the GitHub REST API, also for an error status. It throws when there is no HTTP answer: gh is missing or not signed in, or GitHub cannot be reached. The native port runs `gh api --method METHOD PATH`. It sends a body as JSON on stdin (`--input -`), and it reads an error status from the `(HTTP NNN)` text of gh. A success is status 200.
- `execFile(file, args, {cwd, input})` runs `git` and `gh`. The native port gives each command 15 seconds.
- `shortId()` gives the branch suffix. Native: 8 random lowercase hex characters.

Tests inject `github`. They never call GitHub.

## Publish

1. Read the local value. When it is not an object (no file, invalid JSON, or a value that trust and untrust keep), return `skipped` with an empty message.
2. Get the repository and its default branch. GET `repos/R/contents/pdd.json?ref=BRANCH`. A 404 means that there is no file: the GitHub configuration is `{}` and there is no blob sha. A 200 must be a base64 file with a sha, and its text must be a JSON object.
3. When the GitHub `autopilot` value is the same JSON value as the local value (key order does not count), return `current` with `pdd.json on GitHub is already up to date.` Write nothing.
4. Else make the new text: the GitHub configuration with only its `autopilot` key set to the local value, as JSON with a 2-space indent and a final newline. Other keys stay as GitHub has them, and other local edits do not go to GitHub. PUT `repos/R/contents/pdd.json` with `{message, content, branch, sha}`: content in base64, branch the default branch, sha the blob sha from step 2 (leave it out when there was no file). This is one commit that changes only `pdd.json`. The commit message is `Set PDD Autopilot mode to MODE` for a mode action, else `Update PDD Autopilot trust list`. On success return `written` with `Updated pdd.json on GitHub (BRANCH): COMMIT_URL`.
5. When the default branch refuses the PUT with 403, 409 or 422 (a protected branch, a required PR, or a file that changed), read the head of the default branch (GET `repos/R/git/ref/heads/BRANCH`) and make the branch `pdd/autopilot-settings-ID` there (POST `repos/R/git/refs`). Read `pdd.json` on the new branch, make the new text in the same way and PUT it on the new branch with its blob sha. Open a PR from the new branch to the default branch (POST `repos/R/pulls`). Its title is `Turn on PDD Autopilot` when the local mode is `observe` or `auto` and the GitHub mode is `off` (a missing or invalid mode counts as `off`), else `Update PDD Autopilot settings`. Return `pull-request` with `BRANCH does not accept a direct change, so pdd opened PR_URL. Merge it before Autopilot workers use the new mode.` For trust and untrust, the end is `the new trust list`.
6. Each other failure returns `not-updated` with `pdd.json on GitHub was not updated: REASON. This checkout has the new setting. To retry, run RETRY.` REASON is short and has no token and no local path, for example `GitHub could not be reached or gh is not signed in`, `gh is missing or did not answer in time`, `this repository has no origin remote`, `origin is not a github.com repository` or `GitHub refused the change (HTTP 404)`. When the new branch has the change but the PR did not open, REASON names the branch.

The caller keeps the local write and exit code 0 in each case.

## Check

Check reads the local value (no file counts as `{}`) and the default-branch `pdd.json` as in Publish (a 404 counts as `{}`). It compares the effective mode (`off`, `observe` or `auto`; a missing or invalid mode is `off`) and the trust names (case and order do not count). When they are the same, return `same` with an empty message. When they differ, return `different` with one line: `Warning: pdd.json on GitHub (BRANCH) has other Autopilot settings (GitHub: MODE, trust NAMES; this checkout: MODE, trust NAMES). Autopilot workers use the GitHub copy. To update it, run pdd autopilot LOCAL_MODE.` NAMES is the names joined with `, `, or `(none)`. When a part cannot be read, return `unknown` with an empty message. Check never writes.

## Dependencies

- [Workflow GitHub](workflow-github.prompt.md): required generation context for `resolveWorkflowRepository` and its `execFile` port.
- [Autopilot settings](autopilot.prompt.md): owns the local `pdd.json` shape and its writes.
- The [CLI](pdd-cli.prompt.md) calls Publish after the mode, trust and untrust commands, and Check after `pdd autopilot start` and `pdd autopilot status`.
