# Autopilot alerts

`src/autopilot-alerts.mjs` lets Autopilot tell a person about an operational
incident or a real human decision. Each person sets their own destination once
per machine: a Discord or Slack incoming webhook, or a Discord bot that posts in
one channel. The coordinator sends one
message only for a concrete person ask that passes the quiet-send gates below. The answer goes
on the GitHub issue, so it stays with the original run.

Export module functions `runAutopilotAlerts(input, ports)` and
`alertStatusLine(input, ports)`. `runAutopilotAlerts` takes `action` `set`,
`test`, `clear`, `alert` or native-only `digest` and returns `{exitCode, message}` with a one-line
message. The [CLI](pdd-cli.prompt.md) owns streams and reads stdin into
`input.text`. The [launcher](autopilot-launcher.prompt.md) shows the status line.
Preserve destination setup, transport safety, local status and existing CLI forms; the rules below intentionally narrow chat delivery.

## The webhook URL is a secret

- Take the URL only from stdin (`set`). No command takes it as an argument.
- Never write the URL, or any part of it, to stdout, stderr, the alert record or
  an error. Delivery messages name only the service, the HTTP status and a short
  Slack error word such as `no_service`.
- Save it outside every repository, in
  `<XDG_CONFIG_HOME or HOME/.config>/pdd/autopilot-alerts.json` as
  `{"v":1,"service":"discord|slack","url":URL}`. Create the folder with mode
  0700. Write the file atomically with mode 0600. If a read finds wider file
  permissions, set them back to 0600.

## An absolute home folder

A relative path resolves in the current folder, which is often a checkout. So
use only absolute paths for the destination and the alert record:

- Use `XDG_CONFIG_HOME` only when it is absolute.
- Use `HOME` only when it is absolute. When it is empty or relative, use the
  account home folder from the operating system (`os.userInfo().homedir`).
  `os.homedir()` is not a fallback, because it returns the same bad `HOME`.
- When no absolute home folder exists, `set`, `test`, `clear` and `alert` exit 1
  with one line that asks for an absolute `HOME`, and read, save, record and send
  nothing. The `alert` line also says `Continue other work.`
  `alertStatusLine` returns the empty string.

## A Discord bot destination

`set` with `discordChannel` (from `--discord-channel ID`) saves a bot
destination instead of a webhook. The channel ID has 17 to 20 digits. The bot
token comes from one of two places:

- stdin (`text`), when `tokenCommand` is absent. Save
  `{"v":1,"service":"discord-bot","channel":ID,"token":TOKEN}` like the webhook,
  with mode 0600. A token is 20 to 256 characters of letters, digits, `.`, `_`
  and `-`.
- `tokenCommand` (from `--token-command CMD`), for example a cloud secret
  manager command. Save `{"v":1,"service":"discord-bot","channel":ID,"tokenCommand":CMD}`
  and no token. Run CMD with `/bin/sh -c` in `cwd` at each send and each test,
  with a 30-second limit. Its trimmed stdout is the token. A nonzero exit, a
  timeout or output that is not a token is the result `failed` with detail
  `token command failed (exit N)` or `token command gave no token`; nothing is
  sent. Never save, print or log the command output or its stderr.

The bot token is a secret under the same rules as the URL. `tokenCommand`
without `discordChannel`, or an invalid channel, token or command, exits 2 and
saves nothing. The CLI gives `--discord-channel` and `--token-command` only to
`set`.

Bot requests go to Discord REST v10, `https://discord.com/api/v10`, with headers
`Authorization: Bot TOKEN` and `User-Agent: PDD-Autopilot/VERSION`,
where VERSION is the package version.

- Send: `POST /channels/ID/messages` with
  `{"content":TEXT,"allowed_mentions":{"parse":[]},"flags":4}`. Flag 4 stops
  link embeds. A status that is not 2xx is `failed` (`HTTP 403`). A 2xx reply
  without a numeric message `id` is `unconfirmed` (`no message id`).
- Readback: `GET /channels/ID/messages/MESSAGE_ID`. It is `delivered` only when
  the reply has the same `id` and the [same content](#delivery-and-readback).
  Otherwise it is `unconfirmed`: `readback mismatch`, `readback HTTP N` or
  `readback no reply`.
- `test` first makes two read-only checks: `GET /users/@me` and
  `GET /channels/ID`. If one fails, exit 1 and send nothing. Otherwise send the
  test message with readback. Exit 0 only when it is delivered. The message names
  the bot `username` and the channel `name`.

## Destination commands

| Action | Result |
| --- | --- |
| `set` | Trim `text`. Save it when it is a supported webhook. Exit 0 and name the service. Otherwise exit 2 and save nothing. |
| `test` | Send one test message, `PDD Autopilot test alert (HOST).`, with the host name. Exit 0 only when it is delivered. Exit 1 when no destination is set, or delivery failed or is unconfirmed. A bot destination also makes the [read-only checks](#a-discord-bot-destination). When the test is delivered, add a log row (action `test`, result `delivered`, no issue) to each alert record that already exists on this machine. Otherwise record nothing. |
| `clear` | Remove the destination file. Exit 0, also when no file exists. |

Supported webhooks use `https`, no user name or password and no port:

- Discord: host `discord.com`, `discordapp.com`, `ptb.discord.com` or
  `canary.discord.com`; path `/api/webhooks/ID/TOKEN` or `/api/vN/webhooks/ID/TOKEN`.
- Slack: host `hooks.slack.com`; path `/services/` and more path parts.

## Delivery and readback

| Service | Request | Delivered when |
| --- | --- | --- |
| Discord | POST JSON `{"content":TEXT,"allowed_mentions":{"parse":[]}}` to the URL with query `wait=true` added | The status is 2xx and the reply is the created message: a string `id` and the same content |
| Slack | POST JSON `{"text":TEXT}`, with `&`, `<` and `>` escaped as `&amp;`, `&lt;`, `&gt;` | The status is 200 and the body is `ok` after trim |

The same content means equal text after this normalization of both sides: CRLF
and CR become LF, each line loses its trailing whitespace, and the whole text is
trimmed. A chat service can store the text in this form, so this change alone is
not a mismatch.

`allowed_mentions` and the Slack escapes stop issue text from paging a whole
channel. Each send is one request with a 10-second limit. The module does not
retry inside one call. Digest TEXT is limited to 1900 characters; alert and recovery TEXT to 480 (about 400). Never cut an issue link or the ask to fit; record an oversized ask instead.

Each send has one result:

- `delivered`: the readback above.
- `failed`: the status is not 2xx (`HTTP 404`), or the request did not reach the
  server (the HTTP port throws an error with code `unreached`).
- `unconfirmed`: any other error, such as a timeout, or a 2xx reply without
  readback. The message can exist, so a repeat call does not send it again.
- `not-configured`: no destination is set. The alert stays in the local record.

## Alerts: one real ask

`alert` still accepts `cwd`, `issue` (positive integer text), `kind`, `update`
and JSON `text` from stdin. Export `ALERT_KINDS` with usage-limit, resource,
interpreter, interpreter-access, access, decision, stuck, test-suite,
long-running and recovered. Invalid issue/kind/JSON or missing nonblank `cause`,
`tried`, `need` (only `cause` for recovery) exits 2 without effects.

The coordinator alone should call this module. `notifyAutopilotAsk(input, ports)`
is the small native hook for a future core caller: it takes the same inputs with
`fields` as the JSON object instead of `text`, forces action `alert`, and returns
the same `{exitCode, message}`. It does not wire itself into the core or authorize
workers. Existing CLI forms stay unchanged. The module cannot authenticate the
calling process; coordinator ownership is a caller obligation.

Additional JSON fields: `code` is a stable lowercase cause identifier (letters,
digits, hyphens, underscores, periods, colons and slashes; 1–160 characters),
`ifNoAnswer` explains what waits and what continues, `owner` optionally names who
answers, `details` optionally links an issue comment, and `issues` optionally
lists additional positive issue numbers known before sending. `paused` is a
Boolean for machine observations; optional `tick` (string or number) identifies
a coordinator tick. Missing tick uses the observation time in milliseconds.
No free-text cause is used as identity. Legacy payloads without code or a
consequence remain recorded and are not sent.

An eligible ask is a single line containing one question ending in `?`, or one
imperative sentence beginning Approve, Choose, Grant, Provide, Supply, Sign,
Release, Review, Restore, Renew, Increase, Allow or Run. Require substantive words in a question; punctuation alone is not an ask. Reject multiple action clauses separated by semicolons, commas, colons or dashes as well as conjunctions. Reject multiple questions,
multiple sentences or coordinated actions (including an ampersand, such as "approve & grant"), blank/generic needs (including "Identify the blocker" and
"No named blocker is saved"), and informational/no-action wording in any need.
This is structural validation; the coordinator owns whether only a person can
answer. A sendable message must retain its full ask and all issue links. There is no separate ask-length limit: measure the complete message.

| Kind | Chat eligibility |
| --- | --- |
| decision, access | One clear person ask, code, tried and ifNoAnswer |
| usage-limit, resource, interpreter, interpreter-access | The same fields, plus paused work on two distinct consecutive observations spanning at least 15 minutes; measure from the first paused observation to the latest distinct tick's observation time, never the current replay time. Paused false resets the observation window. Repeating one tick never advances it. |
| test-suite, long-running | Record only for the issue/daily report; never send, even with update |
| stuck | Record only; the core owns retry exhaustion and must express any actual person ask as decision/access |
| recovered | Close matching incidents, but notify only for a confirmed delivered alert that remained open at least 15 minutes from delivery and passes the message budgets |

Incident identity is lowercase repository + code, shared across issues and
checkouts. Machine kinds additionally use the saved stable machine name. Prefer a same-host cause over a person cause on another host. Reconcile the same code on the same host across person/machine classifications with the existing incident, retaining its kind and delivery route; a classification change cannot create a second send. Record-only observations cannot send or replace an existing person ask; an unsent record-only cause may acquire its first eligible ask. Distinct machine hosts remain separate. Missing
code falls back to issue/kind only for local record identity. Issues join an
open incident without another send. `--update` can resend only when need or owner
changes; changed cause/tried/issue lists cannot send. Even a changed ask obeys
the budgets. A failed delivery may be attempted on a later call subject to them;
an unconfirmed send is not repeated. A recovered payload may name `kind` and/or
`code`; without them it closes all incidents listing the issue on this machine.
Legacy incident keys and missing sent timestamps cannot authorize recovery chat.

Every automatic chat send, including recovery and digest, obeys at most six
attempts per rolling hour per machine across repos and destinations. Each issue
can appear in at most one attempted chat message in a rolling 24 hours, including
recoveries and digests. No new alert or digest sends within two hours after recovery of any
of its issues (even when the recovery was quiet). Boundaries are inclusive:
at exactly 15 minutes, 2 hours, 24 hours, or 1 hour the corresponding wait ends.
Failed/unconfirmed attempts consume budgets because an external outcome may be
uncertain. Unconfigured destinations consume none. Suppression never closes the
open ask, except an explicit recovery, and remains available to a later digest.

Messages have the form:

```text
PDD Autopilot needs you: decision
Issue: https://github.com/OWNER/REPO/issues/N
Ask: Approve one resend?
Tried: Read the saved verdict; none exists.
If no answer: This run waits; other work continues.
```

Use Issues for multiple sorted unique links. Append optional Owner and Details
lines when they fit. Keep tried/consequence on single lines, compact them to
80 characters apiece as needed; never cut the ask. A recovery instead names the
kind, issue links and what changed. Omit run identifiers, hashes and cause prose
from person asks. Defensively scrub secrets from fields before persistence, attention snapshots, chat and replies.

Resolve repo with `repository({cwd})` (native gh repo view, then origin remote).
Use the saved launcher machine for cwd first, then other matching repo state
files in filename order, else hostname. Retain the existing record path:
`<state root>/alerts/<first 20 hex SHA-256 of lowercase repo>.json`, private
atomic JSON `{v:1, repo, incidents, log}`. Retain the latest 200 log rows.
Incidents store kind, code, host, issues, listed, fields, openedAt, updatedAt,
result, optional detail/destination, firstPausedAt, lastPausedAt (the latest distinct paused tick's ISO observation time), ticks, lastTick, asked (the last attempted need/owner identity),
channel (destination hash) and sentAt
(the confirmed delivery time). `listed` means issues in the last attempted send.
Logs retain at, issue, kind, action, result, optional detail/destination.
`recorded` and `not-sent` are local outcomes, not transport failures.

Every recorded call exits 0 with a one-line outcome and work continues. Error
saving exits 1; unavailable home/repository retains existing exit 1 behavior.
No approval is recorded and no GitHub issue/comment is written here.

## Separate infrastructure destination

Destination actions accept optional `destination: "autopilot"|"infrastructure"`
(default `autopilot`), exposed as `--destination`. Validate it before any effect;
unknown values exit 2. Infrastructure uses a separate private file
`autopilot-infrastructure-alerts.json` beside `autopilot-alerts.json`, with the
same secret, path, validation and permissions rules. Set, test and clear affect
only the selected file. Their success and failure hints retain the selected
`--destination infrastructure`, so the next command addresses the same route. A delivered test clears only older send failures on its selected route;
open undelivered incidents still count. Log its route (`destination` is
`infrastructure`; absent means `autopilot` for legacy records). Alert and digest callers cannot choose a destination.

Route machine kinds (`usage-limit`, `resource`, `interpreter`,
`interpreter-access`) to the infrastructure destination when set, otherwise the
ordinary destination for compatibility. Route issue kinds and digests only to
Autopilot. Split a recovery that closes both classes into one message per
selected destination; never leak an infrastructure recovery into the issue
channel when an infrastructure destination is configured. PDD does not manage
external credential-maintenance or machine-health programs; configure their
senders separately. Status tests and hints must identify the failing route. Save `destination:
"infrastructure"` on an incident and log row delivered through that route;
absence means `autopilot`. Evaluate latest send failures independently per
route, so testing one cannot hide failures of the other. A digest has no issue;
show its kind without an issue number. A delivered destination test also takes
the shared record lock for each record update.

## Quiet digest and concurrent runs

Native `digest` takes cwd, env and optional attention rows `{number, category,
need}` (the workflow projection supplies need only for an actual open question). Keep only decision/access
rows with a concrete need. Save each repo/host attention snapshot so calls from
other checkouts can combine it with all locally visible open decision/access
incidents routed to the same destination. Do not show machine causes, suite
failures, age notices, generic parked/stuck rows or cause prose as asks.
Deduplicate and sort by lowercase repo, issue and ask. Each complete line is the
issue link and ask; never append an omission count. If the complete list exceeds
1900 characters, record only rather than omit asks.

Send at most once per rolling 24 hours per destination channel, across locally
visible repos and hosts, and only if this canonical open list differs from the
last attempted digest. A host change or changed cause text is not a list change.
No list means no send/time change. Failed/unconfirmed attempts count for the day;
no destination does not count. Use the same machine/issue message budgets.

Shared private `alerts/delivery.json` stores `v:1`, `sends` (rolling-hour entries
with numeric millisecond at, host, destination hash and issue identities),
`issueSentAt` and `recoveredAt` maps keyed by lowercase repo:number, `digests`
(destination hash to at/fingerprint/outcome), and `attention` (repo/host to rows).
Hash destination identity from service and webhook URL or bot channel; never
store credentials there. This aggregates only state visible in this state root;
cross-machine channel coordination requires shared state or a future broker.
When shared history is absent, seed known issue sends/recoveries and the current
channel digest time from legacy record logs, so an upgrade cannot bypass recent
message budgets. Unknown legacy transport outcomes cannot authorize recovery.
Corrupt/unreadable existing shared history fails closed without sending.
Reserve budgets atomically before the external send; interruption may suppress
a later send rather than double-post. This is not exactly-once transport.

Serialize alert/digest/readback/save and shared history under one state-root lock
`alerts/delivery.lock`, shared across processes and checkouts. Use acquireRunLock
with dead-owner recovery, at most 30 seconds of contention and 20 ms sleeps.
Retain injected recordLock and sleep ports and private atomic writes.

## Status line

`alertStatusLine({repo, env}, ports)` reads only local files: no network and no
GitHub. It returns the empty string when `repo` is absent, the record is absent
or unreadable, or there is no problem. A problem is an open incident whose latest
result is a delivery failure, unconfirmed or not-configured (record-only and
quietly deferred incidents are not delivery problems), or a newest send (of any action) that is `failed` or
`unconfirmed`. Then it returns one line, for example:

```text
Alerts: 1 open alert not delivered; last delivery failed (HTTP 404) for #12 usage-limit at 2026-11-06T10:00:00.000Z; check with pdd autopilot alerts test.
```

Without a destination the end is `; set one with pdd autopilot alerts set.`

A failed recovery is not sent again, because its incident is closed. A delivered
`test` adds the newest send to every record, so it ends the `last delivery` part
of an older failed or unconfirmed send, for example of that recovery. An open
incident that is not delivered still counts, and the next call for it sends it
again.

## Dependencies

- [Prompting guide](../../docs/prompting-guide.md): authoring.
- [CLI](pdd-cli.prompt.md): generation and testing of dispatch, stdin and streams.
- [Autopilot launcher](autopilot-launcher.prompt.md): status calls
  `alertStatusLine` with its saved repository and state root.
- [Workflow runner](workflow-runner.prompt.md): required native context for
  `automaticAttention` rows and `acquireRunLock` for shared record custody.
- Native runtime: Node `fs`, `crypto`, `os`, timers and `fetch`.
- Input `env` (default: the process environment) gives HOME and
  XDG_CONFIG_HOME; a relative or empty value is ignored, as
  [above](#an-absolute-home-folder).
- Ports, all optional: `http({method, url, headers, body})` returns
  `{status, text}` or throws (code `unreached` means the request did not reach
  the server); method defaults to POST, and a GET has no body;
  `tokenCommand(command, {cwd})` returns the command stdout or throws with an
  optional numeric `exitCode`; the default runs `/bin/sh -c`;
  `repository({cwd})` returns `{nameWithOwner}`; `now()`; `hostname()`;
  `userInfo()` returns `{homedir}` or throws (default `os.userInfo`);
  `stateRoot`; `recordLock(directory, filename)` returns a release callback or
  throws `run_busy` (default: workflow runner `acquireRunLock`); `sleep(ms)`
  waits between lock attempts (default: native timer). Tests inject `http`; no test sends a real webhook request.
