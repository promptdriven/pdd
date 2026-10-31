# Local command catalog

Own `src/command-catalog.mjs`; export only `PUBLIC_COMMAND_ROUTES`, `PUBLIC_COMMAND_IDS`, `PUBLIC_COMMAND_MANIFEST`, `NAMES` ([Names](#names)) and `BUNDLED_WORKFLOW_NAMES` (feature, bug, small-change, product). Catalog the complete small alpha surface: root help, --version, completion bash|zsh, workflow list [--json] and setup (`pdd setup`, local `setup`, no operands or options; its help says that it installs the PDD skills for Codex and Claude if they are missing, adds the short PDD block to CLAUDE.md, else AGENTS.md, and that a second run changes nothing). Each route has stable id, exact prefix, local disposition, operand/option specs and plain help forms. Expose no excluded command, private schema/type, service flag or hosted execution operation. Help, parser and completion share this one authority.

## Authoring

Read the full [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow the [public alpha boundary](public-boundary.prompt.md) for native authoring/generation scope and shared local command policy. These authoring obligations do not add runtime facts: the complete catalog route declarations below own what the pure data module exposes.

## Names

`NAMES` is the one place for the words of four commands: the frozen object `{test: 'test', lint: 'lint', simulate: 'simulate', start: 'run'}`. A later rename changes only `NAMES`. This prompt and the prompts that link here write these words as they are today: test, lint, simulate and run. A rename changes `NAMES` and those words together.

The Interpreter routes below list `formerly`, the words that people typed before; workflow.run keeps former start compatibility. The `check`, `try` and `workflow.run` routes keep their ids and local dispositions; `lint` is the route for the lint forms:

| Route id | Prefix | Local | `formerly` |
|---|---|---|---|
| `check` | `test` | `runtime-check` | `check` |
| `lint` | `lint` | `runtime-check` | `check` with the flag `--lint` |
| `try` | `simulate` | `runtime-try` | `try` |
| `workflow.run` | `workflow run` | `workflow-run` | `workflow start` |

The `try` route also has the short form `sim`: it parses like `simulate` and never gets a notice. Help names it once, in the description of the first `simulate` form; completion does not offer it. Help forms, help text and completion show only the new words. The [argument parser](argument-parser.prompt.md#former-names) owns how the former words still parse and the one-line notice that they get.

## Public routes

There is no `session` route and no `workflow feature|bug|small-change` chat route: people call the PDD skills in their own chat. No arbitrary path or workflow creation route.

Catalog the area-chat runner routes ([runner](workflow-runner.prompt.md)):
- workflow.run `workflow run NAME ISSUE [--agent codex|claude] [--base BRANCH]`: NAME is a safe workflow name, ISSUE is a number, `owner/repo#number` or `https://github.com/owner/repo/issues/number`. Default agent codex. `--base` is a text option naming an existing origin branch; omitted means the actual repository default. Help describes that selection.
- workflow.done `workflow done STEP [--summary TEXT]`: STEP is a safe step name; the summary is free text.
- workflow.ask `workflow ask QUESTION…`: the question words join into one text; `--` ends options.
- workflow.approve `workflow approve [ISSUE] [--said WORDS]`, workflow.status `workflow status [ISSUE] [--all] [--cancelled] [--json]` (flags).
- workflow.changes `workflow changes ISSUE TEXT…`: the text words join into one request; `--` ends options.
- workflow.cancel `workflow cancel ISSUE`, workflow.open `workflow open ISSUE`.
- workflow.view `workflow view ISSUE` (local `workflow-view`): one required issue operand, no options. Help says it shows a read-only review of gates, approvals, files, PRs and Try links without starting or resuming a chat.
- workflow.list `workflow list [--json]`.
- workflow.prove `workflow prove ISSUE --test COMMAND --expect TEXT` (local `workflow-prove`): one required issue operand and two text options. Help says it runs committed changed tests on the merge-base of committed head with the fetched base branch and committed head, with a 120-second limit per phase, and saves a non-gating report. No timeout override or native option passthrough. Both text options are required by CLI dispatch before effects; parser retains ordinary text/duplicate/blank validation. [Old-code proof](workflow-prove.prompt.md) owns execution, outcome and saved-result policy (required generation/runtime/verification context).
No resume, attach, run IDs, decisions flag or native argument passthrough. The areas module decides which workflow names exist.

Both routes support the exact `--said -` marker. It forwards unchanged to the approval owner, which reads all UTF-8 stdin as one payload after strict/configuration prechecks. Help shows the shared quoted-heredoc template, with a delimiter absent from person text. Keep help in short sentences: ask the person; relay their words; latest chat alone never approves. Both approval routes declare `--said` as optional nonblank text, preserve its exact argument (including option-like words), and show it in help/completion. Missing value, duplicate, empty and whitespace-only values refuse through ordinary parser rules. Workflow approval help reflects the [runner's approval authority](workflow-runner.prompt.md#approval-through-the-persons-words): one --said approves the gate and all its draft prompts using any nonblank words relayed from the person after the gate prompt in any chat, without grading them. Help tells an agent, non-TTY caller or caller in the current area pane without --said to ask the person then relay their words with --said; latest native chat alone never approves. Person-terminal y/N stays available; root pdd.json strict_approvals true permits only person-terminal y/N. The start route is `workflow run`, without a former-name notice for run; the already-supported `workflow start` spelling remains a former-name alias with the parser-owned notice. Other 0.1.12 names stay unchanged.

## Workflow runner help

Describe the runner routes in plain words without preview labels. workflow.run says that pdd starts a chat and exits, and that pdd later pushes the branch and opens a real PR. Keep route IDs, prefixes, local dispositions, operands/options/forms and parser/completion behavior consistent with their contracts.

## Interpreter routes

Help calls the hosted service "the PDD interpreter" ([word rule](public-boundary.prompt.md#pdd-interpreter)). It keeps the words "runtime interface", the name of the block in a prompt file.

Catalog `approve` (local `prompt-approve`, [prompt approve](prompt-approve.prompt.md)) with the form `pdd approve PROMPT [--said WORDS]`: one required text operand and optional text option `--said`. Its help says that it shows the prompt's runtime interface and the text changes since the last approval, and that easy mode accepts the person's chat words through --said; no-said asks terminal y/N. Root pdd.json strict_approvals true requires a person terminal.

Catalog `check` (prefix `test`, local `runtime-check`) with the forms `pdd test [STORY...] [--json] [--details] [--timeout MIN] [--max-calls N]` (help: it checks Stories on the PDD interpreter with the person's gh login, waits for every check, with no limit in a terminal and at most 90 s for an agent, and prints a progress line every 30 s; `--timeout MIN` sets the limit), `pdd test --read [BATCH|CALL_ID] [--json] [--timeout MIN]`, `pdd test --fill-hash` and `pdd test --files [STORY...] [--app-map PATH]`. Catalog `lint` (prefix `lint`, local `runtime-check`) with the optional repeated text operand STORY, the options `--json`, `--timeout` and `--local`, and the form `pdd lint [STORY...] [--json] [--timeout MIN]` (help: it prints local SVG layout warnings, then runs only the PDD interpreter lint with 0 AI calls, and sends no checks). The `lint` plan always has the flag `--lint`, so the runtime client runs the same code as for `pdd test --lint`. On `check`, `--lint` and `--local` stay as hidden flags: `pdd test --lint` works like `pdd lint`, and the former `check --lint` keeps all its options. Catalog `try` (prefix `simulate`, local `runtime-try`) with the forms `pdd simulate [STORY] [--max-calls N] [--tab call|screen|terminal|world] [--app-map PATH] [--new] [--no-open] [--no-wait] [--agent NAME]` (`--app-map` is an option of kind `text`; help: it makes a Try link on the PDD interpreter with the person's gh login) and `pdd simulate --stop [STORY]`. `--app-map` on check is a text option accepted only with `--files`, to preview a Try map. STORY words are free text. `--timeout` is an option of kind `integer` from 1 to 120 and Check `--max-calls` from 1 to 1000. Try accepts `--max-calls` as a positive integer up to 1000, the server cap. Help states that a new Try defaults to400calls and both Check and Try accept --max-calls1..1000. `--request` (kind `uuid`) is hidden. No help form and no completion show a hidden option. These three routes are the one exception to the no-hosted-operation rule above: they call the PDD interpreter through the [runtime client](runtime-client.prompt.md).

Check also catalogs `--screen` (text URL) and `--drawing` (text PATH), with the form `pdd test --screen URL --drawing PATH [--json]`, and lint has the form `pdd lint --local [STORY...] [--json]`. The local lint form checks linked SVG layout parts locally with warning diagnostics and 0 AI/network calls; the screen form compares the real page in installed headless Chrome/Chromium at the drawing viewport, with no AI or interpreter call. [Runtime client](runtime-client.prompt.md#local-drawing-checks) owns combinations, selection, output and exit codes; ordinary remote lint keeps its existing behavior.

Check also catalogs `--retry` as a text option with form `pdd test --retry BATCH [--json] [--details] [--timeout MIN]`. Help says it retries only proven unstarted checks for the saved identical source, preserving completed/running results.

Try also catalogs flags --cli, --shell and --save-last and optional-integer --serve (1..65535, default 8080).
Help forms: `pdd simulate [STORY] --cli [--shell] [--max-calls N] [--new]`, `pdd simulate [STORY] --serve [PORT] [--max-calls N] [--new]`,
`pdd simulate --save-last`. Describe real terminal commands, localhost HTTP requests and saving the last command
into its original test. --shell compatibility and mode conflicts belong to runtime-client.

`pdd workflow evidence ISSUE --summary FILE` records newer source-verified saved check JSON without rerunning workflow steps or publication; require ISSUE and --summary, no extra operands/options.
Try catalogs --agent as nonempty text NAME: accept quoted custom display names as one argument as well as the default codex, claude and gemini names. Agent discovery and unknown-name errors belong to the local agent bridge; parsing does not read configuration or execute a launcher. Workflow --agent keeps its codex|claude value choices. Completion must not present a fixed provider-only list for Try agent names. Its help says pdd stays running to connect the person’s own agent when stdout is a terminal or --agent is explicit; ordinary non-terminal Try returns after collecting saved cases once. --agent selects a configured name and --no-wait skips the bridge. Runtime-client owns conflicts/lifecycle.

Catalog `mcp` (local `mcp`) with the form `pdd mcp`, no operands or options. Help describes a stdio MCP server for the current repository's Try tools. Setup help says "show exact config changes", without a preview-status label, and states that it offers detected Codex, Claude Code and Gemini registrations after showing exact config changes and asking once with y/N.

Remote lint uses the Check caller wait, including --timeout; no separate120second cap. Read help explains that a saved normal Check held for lint may safely continue its original checks; other reads remain GET-only. Runtime-client owns the continuation safeguards and finite recovery wait.

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
text operand RUN, flags `--no-run` and value `--agent` with codex|claude). Forms:
`pdd product status [--json]`, `pdd product next`, and
`pdd product start RUN [--no-run] [--agent codex|claude]`. Help says status counts
Stories by part and slice, next shows ready runs, and start creates or reuses one
issue then starts a normal feature run unless `--no-run`. All three make zero
interpreter calls, and their help says "no interpreter calls". [Product](product.prompt.md) owns their behavior.

## Help forms

`PUBLIC_COMMAND_MANIFEST` owns the forms, descriptions and order below. Each route owns entries whose form starts with its prefix. A help entry may include multiline example text. After each approval entry, include the shared policy's quoted-heredoc example with that route's command (`pdd approve PATH` or `pdd workflow approve N`). The example preserves person text without shell interpolation. Tell the caller to choose a delimiter absent from the text. Both approval descriptions state that --said - reads all UTF-8 stdin, including trailing newlines; simple literal --said text remains supported. A person terminal uses y/N; workflow y/N covers the ready gate and all selected drafts in one call.

```text
  pdd product status [--json]  Count Stories by part and slice from the product plan; no interpreter calls.
  pdd product next  Show ready planned runs and their start commands; no interpreter calls.
  pdd product start RUN [--no-run] [--agent codex|claude]  Create or reuse the run issue and start a normal feature run; --no-run only prepares the issue. No interpreter calls.
  pdd workflow run NAME ISSUE [--agent codex|claude] [--base BRANCH]  Start the first area chat for a GitHub issue in Herdr and exit; --base selects an existing origin branch (default: repository default); pdd later pushes the issue branch and opens a real PR.
  pdd workflow prove ISSUE --test COMMAND --expect TEXT  Run committed changed tests on the fetched base branch merge-base and committed head with a 120-second limit per phase; save a non-gating report.
  pdd workflow done STEP [--summary TEXT]  For the agent in a run worktree: record a step and print what to do next.
  pdd workflow evidence ISSUE --summary FILE  Record source-verified saved check JSON without rerunning steps, gates or publication.
  pdd workflow ask QUESTION  For the agent in a run worktree: show the person that the chat waits for their answer.
  pdd workflow approve [ISSUE] [--said WORDS]  Use --said - with the shared quoted-heredoc template to record chat words for the gate and all its drafts, or use terminal y/N; strict mode requires a person terminal.
  pdd workflow changes ISSUE TEXT  Send a change request to the same area chat; the gate stays open.
  pdd workflow cancel ISSUE  Cancel the run and close its Herdr tabs; keep the worktree and branch.
  pdd workflow status [ISSUE] [--all] [--cancelled] [--json]  Show this repo's runs, or one run with its area, gate, chat and PRs. --all (or outside a repo): every run on this machine, people-waiting first.
  pdd workflow view ISSUE  Read-only review of gates, approvals, files, PRs and Simulator links; never start or resume a chat.
  pdd workflow open ISSUE  Focus or attach the current area chat; resume it if its session ended.
  pdd  Show local commands.
  pdd --help  Show local commands.
  pdd -h  Show local commands.
  pdd help  Show local commands.
  pdd --version  Show this package version.
  pdd completion bash|zsh  Print local shell completion.
  pdd workflow list [--json]  List the bundled workflows with their areas and gates.
  pdd test [STORY...] [--json] [--details] [--timeout MIN] [--max-calls N]  Check stories on the PDD interpreter with your gh login: sends the named Stories (every Story when you name none) and their dependencies, waits for every check (no limit in a terminal, at most 90 s for an agent; --timeout MIN sets the limit) with a progress line every 30 s, then prints one table with report links. Defaults to 12 calls per step, at least 18 and at most 1000; --max-calls accepts 1 to 1000.
  pdd test --read [BATCH|CALL_ID] [--json] [--timeout MIN]  Read saved results; a normal Check held for lint may continue its original checks. Other reads send no work.
  pdd test --retry BATCH [--json] [--details] [--timeout MIN]  Retry only confirmed unstarted checks from a saved batch, with the same source and call caps; preserve completed and uncertain runs.
  pdd test --fill-hash  Fill prose_sha256 of draft runtime interfaces; no network.
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
  pdd setup  Install the PDD skills for Codex and Claude if they are missing, and add the short PDD block to CLAUDE.md, else AGENTS.md. Offer detected Codex, Claude Code and Gemini MCP registrations after showing exact config changes and one y/N question. A second run changes nothing.
```



## Dependencies

No outside values or callback replies are required for this data-only module. All runtime route IDs, prefixes, dispositions, operand/option types, forms and help facts are owned here. Native authoring/generation uses the repository contracts linked above to identify the receiving modules and public boundary; links in route descriptions are native integration/ownership navigation, not a request to load their unrelated implementation/runtime policies when parsing catalog data.
