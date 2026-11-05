# Local command catalog


The public command catalog also includes `pdd autopilot off`, `pdd autopilot observe`, `pdd autopilot auto`, `pdd autopilot trust <name>...`, and `pdd autopilot untrust <name>`. Expose these forms in help and completion; reject missing or extra operands through the existing parser contract.

Own `src/command-catalog.mjs`; export only `PUBLIC_COMMAND_ROUTES`, `PUBLIC_COMMAND_IDS`, `PUBLIC_COMMAND_MANIFEST`, `NAMES` ([Names](#names)), `PUBLIC_HELP_TEXT` ([Help text](#help-text)) and `BUNDLED_WORKFLOW_NAMES` (feature, bug, small-change, product). Catalog the complete small alpha surface: root help, --version, completion bash|zsh, workflow list [--json] and setup (`pdd setup`, local `setup`, no operands or options; its help says that it installs the PDD skills for Codex and Claude if they are missing, adds the short PDD block to CLAUDE.md, else AGENTS.md, and that repeat setup keeps an existing Autopilot mode). Each route has stable id, exact prefix, local disposition, operand/option specs and plain help forms. Expose no excluded command, private schema/type, service flag or hosted execution operation. Help, parser and completion share this one authority.

## Authoring

Read the full [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow the [public alpha boundary](public-boundary.prompt.md) for native authoring/generation scope and shared local command policy. These authoring obligations do not add runtime facts: the complete catalog route declarations below own what the pure data module exposes.

## Names

`NAMES` is the one place for the words of five commands: the frozen object `{test: 'test', lint: 'lint', simulate: 'simulate', run: 'run', requestUptake: 'ack'}`. A later rename changes only `NAMES`. This prompt and the prompts that link here write these words as they are today: test, lint, simulate, run and ack. A rename changes `NAMES` and those words together.

The `check`, `try` and `workflow.run` routes keep their ids and local dispositions; `lint` is the route for the lint forms. Some routes also list quiet words or removed words:

| Route id | Prefix | Local | Quiet words | Removed words |
|---|---|---|---|---|
| `check` | `test` | `runtime-check` | | `check` (new command `pdd test`) |
| `lint` | `lint` | `runtime-check` | | `check` with the flag `--lint` (new command `pdd lint`) |
| `try` | `simulate` | `runtime-try` | `sim` | `try` (new command `pdd simulate`) |
| `workflow.run` | `workflow run` | `workflow-run` | `workflow start` | |

- A quiet word parses like the prefix of its route, with the same plan, and pdd prints no extra line for it. Completion never offers it. Help never names `workflow start`; it names `sim` once, in the description of the first `simulate` form.
- A removed word runs nothing. The [argument parser](argument-parser.prompt.md#removed-names) refuses it with one line that names the new command.
- `workflow start` stays a quiet word for now. A later change moves it to the removed words, with the new command `pdd workflow run`: one data edit.

Help forms and completion name only the `NAMES` words.

## Autopilot routes

Catalog four local routes before the product routes: `autopilot.start` (`autopilot start`, local `autopilot-start`, no operands, optional text --runs); `autopilot.stop` and `autopilot.status` (matching prefixes/dispositions, no operands/options); `autopilot.add` (`autopilot add`, local `autopilot-add`, required repeated issue operands). Forms and descriptions:

- `pdd autopilot start [--runs N]`: Start this repo in an interactive Herdr agent; check now and every 30 minutes without AI on empty ticks. --runs optionally caps concurrent runs.
- `pdd autopilot stop`: Stop this machine's timer; let the current agent step finish.
- `pdd autopilot status`: Show this machine's repo, agent and next tick.
- `pdd autopilot add N...`: Mark named old issues with pdd:autopilot so Autopilot may take them.

The [launcher](autopilot-launcher.prompt.md) owns behavior and --runs numeric interpretation. No fixed run cap, headless flag or additional setup question. Include routes in help and completion. Preserve all unrelated forms and ordering.

## Public routes

Catalog local routes `autopilot.off`, `autopilot.observe`, and `autopilot.auto` with prefixes `autopilot off`, `autopilot observe`, and `autopilot auto`, dispositions of the same names, no operands and no options. Catalog `autopilot.trust` with prefix `autopilot trust`, local `autopilot-trust`, one or more text name operands and no options; catalog `autopilot.untrust` with prefix `autopilot untrust`, local `autopilot-untrust`, exactly one text name operand and no options. The parser and completion consume these routes; dispatch uses their stable dispositions. Include all five in the manifest and help as below.

There is no `session` route and no `workflow feature|bug|small-change` chat route: people call the PDD skills in their own chat. No arbitrary path or workflow creation route.

Catalog the area-chat runner routes ([runner](workflow-runner.prompt.md)):
- workflow.run `workflow run NAME ISSUE [--agent codex|claude|gemini|agy] [--base BRANCH]`: NAME is a safe workflow name, ISSUE is a number, `owner/repo#number` or `https://github.com/owner/repo/issues/number`. Default agent codex. `--base` is a text option naming an existing origin branch; omitted means the actual repository default. Help describes that selection.

For `workflow.run`, accept optional `--adopt-corpus FILE`, a nonempty text path to an existing-approved-corpus declaration. Its help description says it adopts exact unchanged approved content for a fresh replay-evidence-enabled workflow; keep the existing help form unchanged. Example: `pdd workflow run feature 2640 --adopt-corpus approved-corpus.json`. The runner and replay owner define validation and trust, not the parser.

- workflow.done `workflow done STEP [--summary TEXT] [--skipped REASON]`: STEP is a safe step name; the summary and the reason are free text. Help says it records the step with pdd's own latest `pdd <NAMES.test>`, `pdd <NAMES.lint>` and prove results (the summary is an agent note), and that --skipped records that the step was skipped, and why. Build the two command words from `NAMES`, like every other form, so a rename changes this help too.
- `workflow.request-uptake` (local `workflow-request-uptake`): the public verb comes only from `NAMES.requestUptake`, used for both the `['workflow', verb]` prefix and help form `pdd workflow <verb> REQUEST_ID --summary TEXT`. Require one text operand and text option `--summary` (dispatch enforces its presence). Help describes an agent in a run worktree recording that it took up one delivered change request, with a short note. Keep all five existing exports, including `NAMES` with its existing keys and values plus the uptake key; consumers find this route by its stable id, never by duplicating the public verb.
- workflow.ask `workflow ask QUESTION…`: the question words join into one text; `--` ends options.
- workflow.approve `workflow approve [ISSUE] [--said WORDS]`, workflow.status `workflow status [ISSUE] [--all] [--cancelled] [--json]` (flags).
- workflow.changes `workflow changes ISSUE TEXT…`: the text words join into one request; `--` ends options.
- workflow.refresh-description `workflow refresh-description ISSUE PR` (local `workflow-refresh-description`): one required issue operand and one required text PR number operand, no options. The runner validates the recorded PR identity. Help says it retries only the existing PR description update, without advancing workflow progress.
- workflow.cancel `workflow cancel ISSUE`.
- workflow.open `workflow open ISSUE [AREA] [--new]`: optional AREA uses the existing `workflow-name` operand type (the parser's safe name validator); --new is a flag. Help distinguishes focusing/resuming a saved area from replacing the current area's native session, keeping the run and approvals. The runner owns area existence/history checks; the catalog does not inspect saved runs.
- workflow.view `workflow view ISSUE` (local `workflow-view`): one required issue operand, no options. Help says it shows a read-only review of gates, approvals, files, PRs and Simulator links without starting or resuming a chat.
- workflow.list `workflow list [--json]`.
- workflow.prove `workflow prove ISSUE --test COMMAND --expect TEXT [--timeout MIN]` (local `workflow-prove`): one required issue operand, two text options and an optional integer `--timeout` from 1 to 120 (minutes). Help says it runs committed changed tests on the merge-base of committed head with the fetched base branch and committed head, with a limit per phase (default 10 minutes; --timeout sets 1 to 120), and saves a non-gating report that pull requests show as pdd's own result. No native option passthrough. Both text options are required by CLI dispatch before effects; parser retains ordinary text/duplicate/blank validation. [Old-code proof](workflow-prove.prompt.md) owns execution, outcome and saved-result policy (required generation/runtime/verification context).
No resume, attach, run IDs, decisions flag or native argument passthrough. The areas module decides which workflow names exist.

Both routes support the exact `--said -` marker. It forwards unchanged to the approval owner, which reads all UTF-8 stdin as one payload after strict/configuration prechecks. Help shows the shared quoted-heredoc template, with a delimiter absent from person text. Keep help in short sentences: ask the person; relay their words; latest chat alone never approves. Both approval routes declare `--said` as optional nonblank text, preserve its exact argument (including option-like words), and show it in help/completion. Missing value, duplicate, empty and whitespace-only values refuse through ordinary parser rules. Workflow approval help reflects the [runner's approval authority](workflow-runner.prompt.md#approval-through-the-persons-words): one --said approves the gate and all its draft prompts using any nonblank words relayed from the person after the gate prompt in any chat, without grading them. Help says: "Ask the person, then relay their words with --said. Without --said, use a separate person terminal." It avoids terminal jargon; latest native chat alone never approves. Person-terminal y/N stays available; root pdd.json strict_approvals true permits only person-terminal y/N.

## Workflow runner help

Describe the runner routes in plain words without preview labels. workflow.run says that pdd starts a chat and exits, and that pdd later pushes the branch and opens a real PR. Keep route IDs, prefixes, local dispositions, operands/options/forms and parser/completion behavior consistent with their contracts. Place the uptake route help beside done and ask, after ask; preserve the earlier root-help commands and their order.

## Interpreter routes

Help calls the hosted service "the PDD interpreter" ([word rule](public-boundary.prompt.md#pdd-interpreter)). It keeps the words "runtime interface", the name of the block in a prompt file.

Catalog `approve` (local `prompt-approve`, [prompt approve](prompt-approve.prompt.md)) with the form `pdd approve PROMPT [--said WORDS]`: one required text operand and optional text option `--said`. Its help says that it shows the prompt's runtime interface and the text changes since the last approval, and that easy mode accepts the person's chat words through --said; no-said asks terminal y/N. Root pdd.json strict_approvals true requires a person terminal.

Catalog `check` (prefix `test`, local `runtime-check`) with the forms `pdd test [PATH|STORY...] [--lf] [--cache-clear] [--json] [--details] [--timeout MIN] [--max-calls N]` (help: it checks Stories on the PDD interpreter with the person's gh login, waits for every check, with no default limit in any shell, and prints a progress line every 30 s; `--timeout MIN` sets the limit), `pdd test --read [BATCH|CALL_ID] [--json] [--timeout MIN]`, `pdd test --fill-hash`, `pdd test --fill-hash --compact` and `pdd test --files [STORY...] [--app-map PATH]`. Catalog `lint` (prefix `lint`, local `runtime-check`) with the optional repeated text operand STORY, the options `--json`, `--timeout` and `--local`, and the form `pdd lint [STORY...] [--json] [--timeout MIN]` (help: it prints local SVG layout warnings, then runs only the PDD interpreter lint with 0 AI calls, and sends no checks). The `lint` plan always has the flag `--lint`, so the runtime client runs the same code as for `pdd test --lint`. On `check`, `--lint` and `--local` stay as hidden flags: `pdd test --lint` works like `pdd lint`, with the same options. Catalog `try` (prefix `simulate`, local `runtime-try`) with the forms `pdd simulate [STORY] [--max-calls N] [--tab call|screen|terminal|world] [--app-map PATH] [--new] [--no-open] [--no-wait] [--agent NAME]` (`--app-map` is an option of kind `text`; help: it makes a Try link on the PDD interpreter with the person's gh login) and `pdd simulate --stop [STORY]`. `--app-map` on check is a text option accepted only with `--files`, to preview a Try map. STORY words are free text. `--timeout` is an option of kind `integer` from 1 to 120 and Check `--max-calls` from 1 to 1000. Try accepts `--max-calls` as a positive integer up to 1000, the server cap. Help states that a new Try defaults to400calls and both Check and Try accept --max-calls1..1000. `--request` (kind `uuid`) is hidden. No help form and no completion show a hidden option. These three routes are the one exception to the no-hosted-operation rule above: they call the PDD interpreter through the [runtime client](runtime-client.prompt.md).

Check also catalogs `--screen` (text URL) and `--drawing` (text PATH), with the form `pdd test --screen URL --drawing PATH [--json]`, and lint has the form `pdd lint --local [STORY...] [--json]`. The local lint form checks linked SVG layout parts locally with warning diagnostics and 0 AI/network calls; the screen form compares the real page in installed headless Chrome/Chromium at the drawing viewport, with no AI or interpreter call. [Runtime client](runtime-client.prompt.md#local-drawing-checks) owns combinations, selection, output and exit codes; ordinary remote lint keeps its existing behavior.

Check also catalogs visible flag `--compact`. Its help form `pdd test --fill-hash --compact` says it fills draft hashes and removes interface JSON formatting whitespace, preserving values and prose, with no network. [Runtime client](runtime-client.prompt.md#hash-filling) owns allowed combinations and output; [preflight](runtime-preflight.prompt.md#draft-interface-compaction) owns the transform.

Check also catalogs `--retry` as a text option with form `pdd test --retry BATCH [--json] [--details] [--timeout MIN]`. Help says it retries only proven unstarted checks for the saved identical source, preserving completed/running results.

Try also catalogs flags --cli, --shell and --save-last and optional-integer --serve (1..65535, default 8080).
Help forms: `pdd simulate [STORY] --cli [--shell] [--max-calls N] [--new]`, `pdd simulate [STORY] --serve [PORT] [--max-calls N] [--new]`,
`pdd simulate --save-last`. Describe real terminal commands, localhost HTTP requests and saving the last command
into its original test. --shell compatibility and mode conflicts belong to runtime-client.

`pdd workflow evidence ISSUE --summary FILE` records newer source-verified saved check JSON without rerunning workflow steps or publication; require ISSUE and --summary, no extra operands/options.
Try catalogs --agent as nonempty text NAME: accept quoted custom display names as one argument as well as the default codex, claude and gemini names. Agent discovery and unknown-name errors belong to the local agent bridge; parsing does not read configuration or execute a launcher. Workflow --agent keeps its codex|claude|gemini|agy value choices. Completion must not present a fixed provider-only list for Try agent names. Its help says pdd stays running to connect the person’s own agent when stdout is a terminal or --agent is explicit; ordinary non-terminal Try returns after collecting saved cases once. --agent selects a configured name and --no-wait skips the bridge. Runtime-client owns conflicts/lifecycle.

Catalog `mcp` (local `mcp`) with the form `pdd mcp`, no operands or options. Help describes a stdio MCP server for the current repository's Try tools. Setup help says "show exact config changes", without a preview-status label, and states that it offers detected Codex, Claude Code and Gemini registrations after showing exact config changes and asking once with y/N.

Remote lint uses --timeout when explicit; otherwise it retains its 90-second agent default and unlimited interactive wait. Preliminary lint uses its owning Check's unlimited default wait. Neither has a separate120second cap. Read help explains that a saved normal Check held for lint may safely continue its original checks; other reads remain GET-only. Runtime-client owns the continuation safeguards: saved-batch reads wait without a default limit in every shell; --timeout sets a limit, while explicit retry retains its finite default.

Catalog `jobs` (stable id `jobs`, local disposition `runtime-jobs`) with the sole form `pdd jobs`, no operands or options. Help says it lists active and waiting interpreter jobs on this machine without contacting the interpreter. Root help and shell completion include jobs. The [slots helper](runtime-slots.prompt.md) owns listing; this route does not authenticate or import the runtime client.

## Shared contract routes

Catalog `contracts` (stable id `contracts`, local `contracts`) with form
`pdd contracts`, no operands/options: list shared records, users and Stories made
stale since their last check. Catalog `contracts.sync` (local `contracts-sync`)
with form `pdd contracts sync [--write]`, no operands and only flag `--write`.
Help says preview moving copies to references, and apply only with --write.
Both routes are local, use working files and make no runtime call. Include them
in root help and completion; do not import the runtime client for parsing/help.

## Product routes

Catalog `product.status` (`product status`, local `product-status`, optional flag
`--json`), `product.next` (`product next`, local `product-next`, no operands or
options), and `product.start` (`product start`, local `product-start`, required
text operand RUN, flags `--no-run` and value `--agent` with codex|claude|gemini|agy). Forms:
`pdd product status [--json]`, `pdd product next`, and
`pdd product start RUN [--no-run] [--agent codex|claude|gemini|agy]`. Help says status counts
Stories by part and slice, next shows ready runs, and start creates or reuses one
issue then starts a normal feature run unless `--no-run`. All three make zero
interpreter calls, and their help says "no interpreter calls". [Product](product.prompt.md) owns their behavior.

## Help forms

`PUBLIC_COMMAND_MANIFEST` owns the forms, descriptions and order below. Each route owns entries whose form starts with its prefix. A help entry may include multiline example text. After each approval entry, include the shared policy's quoted-heredoc example with that route's command (`pdd approve PATH` or `pdd workflow approve N`). The example preserves person text without shell interpolation. Tell the caller to choose a delimiter absent from the text. Both approval descriptions state that --said - reads all UTF-8 stdin, including trailing newlines; simple literal --said text remains supported. A person terminal uses y/N; workflow y/N covers the ready gate and all selected drafts in one call.

The ordered help-form list consists of the lines below in their displayed order, inserting the canonical form and description for catalog route `workflow.request-uptake` immediately after the ask line. That inserted entry uses that route's prefix followed by `REQUEST_ID --summary TEXT` and its catalog-owned agent uptake description; resolve it by stable id rather than a copied public verb. Each line is two spaces, the form, two spaces and its description. The [catalog](command-catalog.prompt.md) routes own them; the first words after `pdd` are the route prefix. This complete list, including the catalog-derived inserted entry, defines the manifest and root help.


```text
  pdd product status [--json]  Count Stories by part and slice from the product plan; no interpreter calls.
  pdd product next  Show ready planned runs and their start commands; no interpreter calls.
  pdd product start RUN [--no-run] [--agent codex|claude|gemini|agy]  Create or reuse the run issue and start a normal feature run; --no-run only prepares the issue. No interpreter calls.
  pdd workflow run NAME ISSUE [--agent codex|claude|gemini|agy] [--base BRANCH]  Start the first area chat for a GitHub issue in Herdr and exit; --base selects an existing origin branch (default: repository default); --adopt-corpus FILE adopts exact unchanged approved content for a fresh replay-evidence-enabled workflow; pdd later pushes the issue branch and opens a real PR.
  pdd workflow prove ISSUE --test COMMAND --expect TEXT [--timeout MIN]  Run committed changed tests on the fetched base branch merge-base and committed head with a limit per phase (default 10 minutes; --timeout sets 1 to 120); save a non-gating report that pull requests show as pdd's own result.
  pdd workflow done STEP [--summary TEXT] [--skipped REASON]  For the agent in a run worktree: record a step with pdd's own latest pdd test, pdd lint and prove results (the summary is an agent note) and print what to do next; --skipped records that the step was skipped, and why.
  pdd workflow evidence ISSUE --summary FILE  Record source-verified saved check JSON without rerunning steps, gates or publication.
  pdd workflow ask QUESTION  For the agent in a run worktree: show the person that the chat waits for their answer.
  pdd workflow refresh-description ISSUE PR  Retry the existing PR description update without advancing workflow progress.
  pdd workflow approve [ISSUE] [--said WORDS]  Use --said - with the shared quoted-heredoc template to record chat words for the gate and all its drafts, or use terminal y/N; strict mode requires a person terminal.
  pdd workflow changes ISSUE TEXT  Send a change request to the same area chat; the gate stays open.
  pdd workflow cancel ISSUE  Cancel the run and close its Herdr tabs; keep the worktree and branch.
  pdd workflow status [ISSUE] [--all] [--cancelled] [--json]  Show this repo's runs, or one run with its area, gate, chat and PRs. --all (or outside a repo): every run on this machine, people-waiting first.
  pdd workflow view ISSUE  Read-only review of gates, approvals, files, PRs and Simulator links; never start or resume a chat.
  pdd workflow open ISSUE [AREA] [--new]  Focus or resume a saved area chat; --new replaces the current session while keeping the run and approvals.
  pdd  Show local commands.
  pdd --help  Show local commands.
  pdd -h  Show local commands.
  pdd help  Show local commands.
  pdd help prompting  Show how to write prompts, Stories and tests, and where the guide is.
  pdd --version  Show this package version.
  pdd completion bash|zsh  Print local shell completion.
  pdd workflow list [--json]  List the bundled workflows with their areas and gates.
  pdd test [PATH|STORY...] [--lf] [--cache-clear] [--json] [--details] [--timeout MIN] [--max-calls N]  Check stories on the PDD interpreter with your gh login: reuses unchanged passing Stories from .pdd/cache/test/; --lf selects previous failures in scope or uses the normal selection when none match, --cache-clear clears the cache and sends the selected Stories again (the interpreter may reuse saved answers); sends selected PATH or STORY dependencies (every Story when you name none), waits for every check (no default limit in any shell; --timeout MIN sets the limit) with a progress line every 30 s, then prints one table with report links. Defaults to 12 calls per step, at least 18 and at most 1000; --max-calls accepts 1 to 1000.
  pdd test --read [BATCH|CALL_ID] [--json] [--timeout MIN]  Read saved results; a normal Check held for lint may continue its original checks. Other reads send no work.
  pdd test --retry BATCH [--json] [--details] [--timeout MIN]  Retry only confirmed unstarted checks from a saved batch, with the same source and call caps; preserve completed and uncertain runs.
  pdd test --fill-hash  Fill prose_sha256 of draft runtime interfaces; no network.
  pdd test --fill-hash --compact  Fill draft hashes and remove interface JSON formatting whitespace; preserve values and prose, no network.
  pdd test --files [STORY...] [--app-map PATH]  List the exact selected upload files and byte sizes; no network. --app-map selects the Simulator's app map.
  pdd test --screen URL --drawing PATH [--json]  Compare a real page with its drawing at the drawing viewport in installed headless Chrome/Chromium; no AI or interpreter calls.
  pdd lint [STORY...] [--json] [--timeout MIN]  Print local SVG layout warnings, then the PDD interpreter lint (0 AI calls) on selected Stories and their dependencies; sends no checks.
  pdd lint --local [STORY...] [--json]  Check linked SVG layout parts locally with warning diagnostics and 0 AI/network calls.
  pdd approve PROMPT [--said WORDS]  Approve one prompt with the person's chat words in easy mode, or show its interface/text changes and ask terminal y/N; strict mode requires a person terminal.
  pdd simulate [STORY] [--max-calls N] [--tab call|screen|terminal|world] [--app-map PATH] [--new] [--no-open] [--no-wait] [--agent NAME]  Open the Story in the PDD Simulator: make a link on the PDD interpreter with your gh login and open it in your browser; it ends in 24 hours. Short form: pdd sim. A new simulation defaults to 400 calls; --max-calls accepts 1 to 1000. With terminal stdout or explicit --agent, it stays running to connect your own agent; otherwise it reads saved cases once and returns. --agent selects a configured name or a default Codex, Claude or Gemini; --no-wait skips the bridge. In a terminal it adds each test saved in the Simulator to the story's test file.
  pdd simulate [STORY] --cli [--shell] [--max-calls N] [--new]  Run your program in your terminal through a Simulator session; prints a PATH line, or opens a shell with --shell.
  pdd simulate [STORY] --serve [PORT] [--max-calls N] [--new]  Serve real HTTP requests through your Simulator session on localhost (default port 8080).
  pdd simulate --save-last  Save the last terminal command and its output in the original Story test file.
  pdd simulate --stop [STORY]  Stop the open Simulator link of a story.
  pdd jobs  List active and waiting interpreter jobs on this machine without contacting the interpreter.
  pdd contracts  List shared records, their users and Stories stale since their last check; local working files only.
  pdd contracts sync [--write]  Show proposed changes for moving schema copies to references; apply only with --write. No interpreter calls.
  pdd mcp  Serve the current repository’s Try tools over stdio MCP.
  pdd autopilot off  Set the repository Autopilot mode to off.
  pdd autopilot observe  Set the repository Autopilot mode to observe.
  pdd autopilot auto  Set the repository Autopilot mode to auto.
  pdd autopilot trust NAME...  Add explicitly trusted GitHub names.
  pdd autopilot untrust NAME  Remove an explicitly trusted GitHub name.
  pdd setup  Install the PDD skills for Codex and Claude if they are missing, and add the short PDD block to CLAUDE.md, else AGENTS.md. Offer detected Codex, Claude Code and Gemini MCP registrations after showing exact config changes and one y/N question. Offer Autopilot settings in a Git repository with a terminal; keep an existing mode on repeat setup.
```



The `help` route owns the forms `pdd`, `pdd --help`, `pdd -h`, `pdd help` and `pdd help prompting`, and lists one help topic: `prompting`. A topic is no route prefix, so `prompting` alone is no command. The [Learn PDD](#learn-pdd) section owns the topic's text; the [parser](argument-parser.prompt.md#help-topics) owns its syntax.

## Help text

Export the frozen `PUBLIC_HELP_TEXT` object with `heading`, `closingLines`, `learnLines` and `promptingLines`. The heading is exactly `PDD: prompt-driven development for your coding agent.` The three line arrays contain the exact ordered lines in the closing block below, the Learn PDD block and the prompting topic block respectively. Keep `PACKAGE_ROOT` as a template marker in `learnLines`; the CLI substitutes its absolute package root. The topic uses the last two learn lines after its prompting lines. This catalog owns every help text template; the dispatcher owns composition and path substitution.

The closing lines are exactly:

```text
Open Codex or Claude as usual and call a PDD skill: $pdd-feature in Codex, /pdd-feature in Claude Code (also pdd-bug, pdd-small-change, pdd-prompting).
workflow run opens the first area chat in Herdr session pdd and exits. The person approves each area; after the last step pdd pushes the branch and opens a real PR.
pdd never merges.
```

(`run` is the [NAMES](#names) word. Codex calls a skill with `$name`, Claude Code with `/name`.)

## Learn PDD

The catalog owns these help text templates; the CLI substitutes its package root without reading files.

Help tells a person or an agent with no PDD skills where to learn PDD. PACKAGE_ROOT is the absolute path of the folder that holds the package.json of this pdd: the `packageRoot` of the CLI dispatcher's `runPdd`, by default the parent folder of `src/`. It is never the cwd or the person's repo. Both files ship in the package (`files` in package.json), so both paths exist in every install. Help reads no file to print them. The learn line and the two path lines are exactly:

```text
Learn PDD: run pdd help prompting, or read the Prompting guide and the RUNBOOK.
Prompting guide: PACKAGE_ROOT/docs/prompting-guide.md
RUNBOOK: PACKAGE_ROOT/RUNBOOK.md
```

`pdd help prompting` is a help topic, not a command ([help topics](argument-parser.prompt.md#help-topics)). It prints the first help line, one empty line, the lines below, one empty line, then the two path lines. It exits 0, writes nothing to stderr and is local, as all help is.

```text
In PDD, prompts are the source. Code follows the prompts.
1. Prompt: prompts/NAME.prompt.md. Write what the program does in plain English, then ## Dependencies, then one Runtime interface block.
2. Story: user_stories/STORY.md. Write one thing that a person can do, then a numbered ## Acceptance criteria list.
3. Test: tests/STORY.json. When the repo keeps its own tests in tests/ or test/, use tests/runtime/ or test/runtime/. Write steps with an exact check for each criterion.
4. Check: run pdd test --fill-hash, then pdd lint (0 AI calls), then pdd test STORY on the PDD interpreter.
5. Approve: a person reads each prompt and runs pdd approve PROMPT. An agent never approves.
```


## Dependencies

No outside values or callback replies are required for this data-only module. All runtime route IDs, prefixes, dispositions, operand/option types, forms and help facts are owned here. Native authoring/generation uses the repository contracts linked above to identify the receiving modules and public boundary; links in route descriptions are native integration/ownership navigation, not a request to load their unrelated implementation/runtime policies when parsing catalog data.

## Test cache options

The check route accepts Boolean flags `--lf` and `--cache-clear`. PATH operands
select files or directories as defined by preflight. Ordinary tests reuse
unchanged successful Stories; `--lf` selects prior failed Stories, and
`--cache-clear` clears `.pdd/cache/test/` and sends the named selected scope again (all Stories when no operands are given); it takes precedence over `--lf`. With no failed Story in the selected scope, `--lf` uses the normal selection. The test help retains the caveat `the interpreter may reuse saved answers`. The runtime client
owns precedence, eligibility and persistence. The exact test help description is:

```text
Check stories on the PDD interpreter with your gh login: reuses unchanged passing Stories from .pdd/cache/test/; --lf selects previous failures in scope or uses the normal selection when none match, --cache-clear clears the cache and sends the selected Stories again (the interpreter may reuse saved answers); sends selected PATH or STORY dependencies (every Story when you name none), waits for every check (no default limit in any shell; --timeout MIN sets the limit) with a progress line every 30 s, then prints one table with report links. Defaults to 12 calls per step, at least 18 and at most 1000; --max-calls accepts 1 to 1000.
```

Preserve every unrelated help form.
