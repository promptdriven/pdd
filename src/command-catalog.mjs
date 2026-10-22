const flag = (name) => Object.freeze({ name, kind: 'flag' });
const value = (name, type = 'text', { repeat = false } = {}) => Object.freeze({ name, kind: 'value', type, repeat });
const operand = (name, type = 'text', { optional = false, repeat = false } = {}) => Object.freeze({ name, type, optional, repeat });
const form = (form, description) => Object.freeze({ form, description });

const routes = [
  {
    id: 'help', prefix: ['help'], local: 'help', operands: [], options: [],
    forms: [
      form('pdd', 'Show every supported PDD command.'),
      form('pdd --help', 'Show every supported PDD command.'),
      form('pdd -h', 'Show every supported PDD command.'),
      form('pdd help', 'Show every supported PDD command.'),
    ],
  },
  {
    id: 'version', prefix: ['--version'], local: 'version', operands: [], options: [],
    forms: [],
  },
  {
    id: 'skill', prefix: ['--skill'], local: 'skill', operands: [], options: [],
    forms: [form('pdd --skill', 'Print the PDD skill for an AI coding assistant.')],
  },
  {
    id: 'completion', prefix: ['completion'], local: 'completion', operands: [operand('shell', 'choice:bash,zsh')], options: [],
    forms: [form('pdd completion bash|zsh', 'Print shell completion for supported PDD commands.')],
  },
  {
    id: 'session.open', prefix: ['session'], operands: [], options: [
      value('--agent', 'choice:codex,claude'), value('--request', 'id'), flag('--json'),
    ], validate: 'session-open', host: true,
    forms: [form('pdd session [--agent codex|claude] [--request id] [--json]', 'Open a PDD prompt session in this folder.')],
  },
  {
    id: 'session.make-it', prefix: ['session', 'make-it'], operands: [], options: [
      value('--request', 'absolute-path'), value('--resume', 'id'), flag('--json'),
    ], validate: 'session-make-it', host: true,
    forms: [form('pdd session make-it --request file|--resume operation [--json]', 'Start a workflow from a saved session request.')],
  },
  {
    id: 'doctor', prefix: ['doctor'], operands: [], options: [
      flag('--fix'), value('--action', 'choice:conversation,workflow,publication,simulation'), flag('--details'), flag('--json'),
    ], host: true,
    forms: [form('pdd doctor [--fix] [--action conversation|workflow|publication|simulation] [--details|--json]', 'Check this machine and show how to fix issues.')],
  },
  {
    id: 'init', prefix: ['init'], operands: [], options: [
      flag('--initial-commit'), value('--preparation', 'choice:background,on-demand'), value('--codex-home', 'path'), value('--codex-bin', 'path'), flag('--json'),
    ], host: true,
    forms: [form('pdd init [--codex-home path] [--codex-bin path] [--initial-commit] [--preparation background|on-demand] [--json]', 'Connect this checkout to PDD.')],
  },
  {
    id: 'bootstrap-repo', prefix: ['bootstrap-repo'], operands: [], options: [flag('--json')], host: true,
    forms: [form('pdd bootstrap-repo [--json]', 'Prepare an existing repository for prompt space.')],
  },
  {
    id: 'repo.add', prefix: ['repo', 'add'], operands: [operand('folder-or-repository', 'project', { optional: true })], options: [
      value('--preparation', 'choice:background,on-demand'), value('--host', 'label'), flag('--json'),
    ], host: true,
    forms: [form('pdd repo add [folder|owner/name] [--preparation background|on-demand] [--host machine] [--json]', 'Add a project to PDD.')],
  },
  {
    id: 'repo.list', prefix: ['repo', 'list'], operands: [], options: [
      value('--host', 'label'), value('--query', 'text'), value('--page', 'positive-int'), flag('--json'),
    ], host: true,
    forms: [form('pdd repo list [--host machine] [--query text] [--page number] [--json]', 'List projects available to PDD.')],
  },
  {
    id: 'repo.browse', prefix: ['repo', 'browse'], operands: [operand('repository', 'repository')], options: [value('--host', 'label'), flag('--json')], host: true,
    forms: [form('pdd repo browse owner/name [--host machine] [--json]', 'Read project issues without cloning the repository.')],
  },
  {
    id: 'repo.disconnect', prefix: ['repo', 'disconnect'], operands: [operand('repository', 'repository')], options: [flag('--json')], host: true,
    forms: [form('pdd repo disconnect owner/name [--json]', 'Disconnect a project registration while keeping its files and work.')],
  },
  {
    id: 'repo.remove', prefix: ['repo', 'remove'], operands: [operand('repository', 'repository')], options: [flag('--json')], host: true,
    forms: [form('pdd repo remove owner/name [--json]', 'Remove a project registration across machines while keeping its files.')],
  },
  {
    id: 'issues', prefix: ['issues'], operands: [operand('issue-reference', 'issue-ref', { optional: true })], options: [
      flag('--all'), value('--repo', 'repository'), flag('--json'), flag('--brief'), value('--limit', 'positive-int'),
    ], host: true,
    forms: [form('pdd issues [number|repo#number] [--repo owner/name] [--all] [--json|--brief] [--limit number]', 'List open issues or read one issue.')],
  },
  {
    id: 'run.start', prefix: ['run', 'start'], operands: [operand('issue', 'issue-ref')], options: [
      flag('--wait'), value('--base', 'branch'), value('--checkout', 'path'), value('--repo', 'repository'), value('--host', 'label'),
      value('--workflow', 'slug'), flag('--dry-run'), value('--from', 'stage'), value('--skip', 'stages'), flag('--ignore-blockers'),
      flag('--ignore-flag'), flag('--ignore-closing-pr'), value('--reason', 'text'), flag('--json'),
    ], host: true,
    forms: [form('pdd run start <issue> [--workflow name] [--base branch] [--checkout folder] [--repo owner/name] [--host machine] [--dry-run] [--from stage] [--skip stage,stage] [--ignore-blockers] [--ignore-flag] [--ignore-closing-pr] [--reason text] [--wait] [--json]', 'Start a workflow for an issue.')],
  },
  {
    id: 'run.list', prefix: ['run', 'list'], operands: [], options: [flag('--json'), flag('--brief'), value('--limit', 'positive-int')], host: true,
    forms: [form('pdd run list [--json|--brief] [--limit number]', 'List recent runs and retained history.')],
  },
  {
    id: 'run.status', prefix: ['run', 'status'], operands: [operand('run-or-issue', 'issue-ref')], options: [flag('--json'), flag('--brief')], host: true,
    forms: [form('pdd run status <run|issue> [--json|--brief]', 'Show one run.')],
  },
  {
    id: 'run.checkout-status', prefix: ['run', 'checkout-status'], operands: [operand('request-id', 'id')], options: [flag('--json')], host: true,
    forms: [form('pdd run checkout-status <request-id> [--json]', 'Read the status of a checkout request.')],
  },
  {
    id: 'run.open', prefix: ['run', 'open'], operands: [operand('run-or-issue', 'issue-ref')], options: [flag('--json')], host: true,
    forms: [form('pdd run open <run|issue> [--json]', 'Open the current session for a run.')],
  },
  {
    id: 'run.answer', prefix: ['run', 'answer'], operands: [operand('run-or-issue', 'issue-ref'), operand('text', 'text', { optional: true, repeat: true })], options: [
      value('--option', 'text'), flag('--json'),
    ], host: true,
    forms: [form('pdd run answer <run|issue> [text] [--option number|choice] [--json]', 'Answer a question in a run.')],
  },
  {
    id: 'run.message', prefix: ['run', 'message'], operands: [operand('run-or-issue', 'issue-ref'), operand('text', 'text', { repeat: true })], options: [flag('--json')], host: true,
    forms: [form('pdd run message <run|issue> <text> [--json]', 'Message the current agent for a run.')],
  },
  {
    id: 'run.changes', prefix: ['run', 'changes'], operands: [operand('run-or-issue', 'issue-ref'), operand('note', 'text', { repeat: true })], options: [
      value('--kind', 'choice:solution,story,pr1,pr2'), flag('--json'),
    ], host: true,
    forms: [form('pdd run changes <run|issue> <note> [--kind solution|story|pr1|pr2] [--json]', 'Ask for changes to a run.')],
  },
  {
    id: 'run.merge', prefix: ['run', 'merge'], operands: [operand('run-or-issue', 'issue-ref'), operand('pull-request', 'choice:pr1,pr2')], options: [flag('--json')], host: true,
    forms: [form('pdd run merge <run|issue> pr1|pr2 [--json]', 'Merge the current pull request through PDD.')],
  },
  {
    id: 'run.approve', prefix: ['run', 'approve'], operands: [operand('run-or-issue', 'issue-ref'), operand('revision', 'choice:solution,story', { optional: true })], options: [
      value('--option', 'positive-int'), value('--note', 'text'), flag('--json'),
    ], host: true,
    forms: [form('pdd run approve <run|issue> [solution|story] [--option number] [--note text] [--json]', 'Approve the current revision of a run.')],
  },
  {
    id: 'run.stop', prefix: ['run', 'stop'], operands: [operand('run-or-issue', 'issue-ref')], options: [flag('--acknowledge-unknown-writer'), flag('--json')], host: true,
    forms: [form('pdd run stop <run|issue> [--acknowledge-unknown-writer] [--json]', 'Stop the current run.')],
  },
  {
    id: 'run.free-up', prefix: ['run', 'free-up'], operands: [operand('run-or-issue', 'issue-ref')], options: [flag('--json')], host: true,
    forms: [form('pdd run free-up <run|issue> [--json]', 'Free the run files while keeping sessions and history.')],
  },
  {
    id: 'run.free-space', prefix: ['run', 'free-space'], operands: [operand('run-or-issue', 'issue-ref')], options: [flag('--json')], host: true,
    forms: [form('pdd run free-space <run|issue> [--json]', 'Free the run files while keeping sessions and history.')],
  },
  {
    id: 'run.remove', prefix: ['run', 'remove'], operands: [operand('run-or-issue', 'issue-ref')], options: [flag('--delete-anyway'), flag('--json')], host: true,
    forms: [form('pdd run remove <run|issue> [--delete-anyway] [--json]', 'Remove run files and sessions after the existing confirmation.')],
  },
  {
    id: 'now', prefix: ['now'], operands: [], options: [flag('--json'), flag('--brief'), value('--limit', 'positive-int')], host: true,
    forms: [form('pdd now [--json|--brief] [--limit number]', 'Show what needs your attention.')],
  },
  {
    id: 'status', prefix: ['status'], operands: [], options: [flag('--json'), flag('--brief'), value('--limit', 'positive-int')], host: true,
    forms: [form('pdd status [--json|--brief] [--limit number]', 'Show what needs your attention.')],
  },
  {
    id: 'watch', prefix: ['watch'], operands: [], options: [], host: true,
    forms: [form('pdd watch', 'Stay open for questions and approvals on this machine.')],
  },
  {
    id: 'wait', prefix: ['wait'], operands: [operand('run-or-issue', 'issue-ref')], options: [
      value('--until', 'wait-state'), value('--timeout', 'positive-int'), flag('--json'),
    ], host: true,
    forms: [form('pdd wait <run|issue> [--until needs-you|question|solution|story|merge|ended|stage:id] [--timeout ms] [--json]', 'Wait for a step or a person.')],
  },
  {
    id: 'agents.list', prefix: ['agents'], operands: [], options: [flag('--json'), flag('--brief'), value('--limit', 'positive-int')], host: true,
    forms: [form('pdd agents [--json|--brief] [--limit number]', 'List ordinary Codex sessions and retained history.')],
  },
  {
    id: 'agents.start', prefix: ['agents', 'start'], operands: [operand('text', 'text', { optional: true, repeat: true })], options: [
      value('--project', 'repository'), value('--model', 'slug'), value('--effort', 'slug'), flag('--list-models'), value('--host', 'label'), flag('--json'),
    ], validate: 'agent-list-models', host: true,
    forms: [
      form('pdd agents start [text] [--project owner/name] [--model name] [--effort name] [--host machine] [--json]', 'Start an ordinary conversation.'),
      form('pdd agents start --list-models [--host machine] [--json]', 'Show model and effort choices on a machine.'),
    ],
  },
  {
    id: 'agents.open', prefix: ['agents', 'open'], operands: [operand('session-id-or-exact-name', 'text')], options: [flag('--json')], host: true,
    forms: [form('pdd agents open <session-id|exact-name> [--json]', 'Read or message an existing ordinary conversation.')],
  },
  {
    id: 'agents.message', prefix: ['agents', 'message'], operands: [operand('session', 'id'), operand('text', 'text', { optional: true, repeat: true })], options: [
      value('--file', 'path', { repeat: true }), flag('--json'),
    ], host: true,
    forms: [form('pdd agents message <session> [text] [--file path ...] [--json]', 'Send text and files in one step.')],
  },
  {
    id: 'agents.file-status', prefix: ['agents', 'file-status'], operands: [operand('attachment-id', 'id')], options: [flag('--json')], host: true,
    forms: [form('pdd agents file-status <attachment-id> [--json]', 'Read one file attachment status.')],
  },
  {
    id: 'agents.message-status', prefix: ['agents', 'message-status'], operands: [operand('request-id', 'id')], options: [flag('--json')], host: true,
    forms: [form('pdd agents message-status <request-id> [--json]', 'Read one message delivery status.')],
  },
  {
    id: 'agents.end', prefix: ['agents', 'end'], operands: [operand('session', 'id')], options: [value('--host', 'label'), flag('--json')], host: true,
    forms: [form('pdd agents end <session> [--host machine] [--json]', 'End an agent session while keeping its files and history.')],
  },
  {
    id: 'agents.resume', prefix: ['agents', 'resume'], operands: [operand('session', 'id')], options: [value('--host', 'label'), flag('--json')], host: true,
    forms: [form('pdd agents resume <session> [--host machine] [--json]', 'Resume the same retained conversation.')],
  },
  {
    id: 'agents.interrupt', prefix: ['agents', 'interrupt'], operands: [operand('session', 'id')], options: [
      value('--generation', 'positive-int'), value('--turn', 'id'), flag('--json'),
    ], validate: 'agent-interrupt', host: true,
    forms: [form('pdd agents interrupt <session> --generation number --turn id [--json]', 'Stop the observed turn of an ordinary conversation.')],
  },
  {
    id: 'agents.answer', prefix: ['agents', 'answer'], operands: [operand('session', 'id'), operand('text', 'text', { repeat: true })], options: [
      value('--request', 'id'), value('--generation', 'positive-int'), flag('--json'),
    ], validate: 'agent-request-action', host: true,
    forms: [form('pdd agents answer <session> <text> --request id --generation number [--json]', 'Answer a pending question in an ordinary conversation.')],
  },
  {
    id: 'agents.approve', prefix: ['agents', 'approve'], operands: [operand('session', 'id'), operand('decision', 'choice:accept,accept-session,decline')], options: [
      value('--request', 'id'), value('--generation', 'positive-int'), flag('--json'),
    ], validate: 'agent-request-action', host: true,
    forms: [form('pdd agents approve <session> accept|accept-session|decline --request id --generation number [--json]', 'Answer a pending tool approval.')],
  },
  {
    id: 'workflow.list', prefix: ['workflow', 'list'], local: 'workflow-list', operands: [], options: [flag('--json')],
    forms: [form('pdd workflow list [--json]', 'List workflows from the current project.')],
  },
  {
    id: 'workflow.new', prefix: ['workflow', 'new'], operands: [operand('name', 'slug')], options: [
      value('--from', 'slug'), value('--describe', 'text'), flag('--json'),
    ], validate: 'workflow-new', host: true,
    forms: [form('pdd workflow new <name> [--from template|--describe text] [--json]', 'Create a workflow for you to review and edit.')],
  },
  {
    id: 'workflow.edit', prefix: ['workflow', 'edit'], operands: [operand('name', 'slug', { optional: true })], options: [flag('--json')], host: true,
    forms: [form('pdd workflow edit [name] [--json]', 'Open a workflow for editing.')],
  },
  {
    id: 'phone', prefix: ['phone'], operands: [], options: [flag('--json')], host: true,
    forms: [form('pdd phone [--json]', 'Show the web app link and QR code to open PDD on your phone.')],
  },
  {
    id: 'approve', prefix: ['approve'], operands: [operand('code', 'id')], options: [flag('--json')], host: true,
    forms: [form('pdd approve <code> [--json]', 'Review a request to connect another computer.')],
  },
  {
    id: 'machine.approve', prefix: ['machine', 'approve'], operands: [operand('code', 'id')], options: [flag('--json')], host: true,
    forms: [form('pdd machine approve <code> [--json]', 'Review a request to connect another computer.')],
  },
  {
    id: 'machine.sign-in', prefix: ['machine', 'sign-in'], operands: [], options: [flag('--check')], host: true,
    forms: [form('pdd machine sign-in [--check]', 'Show identity or sign in on this enrolled machine.')],
  },
  {
    id: 'machine.invite', prefix: ['machine', 'invite'], operands: [], options: [
      value('--purpose', 'choice:personal,testing,preparation'), flag('--primary'), value('--os', 'choice:darwin,linux'), value('--kind', 'choice:personal,shared'), flag('--json'),
    ], host: true,
    forms: [form('pdd machine invite [--purpose personal|testing|preparation] [--primary] [--os darwin|linux] [--kind personal|shared] [--json]', 'Make a one-use code for another computer.')],
  },
  {
    id: 'machine.list', prefix: ['machine', 'list'], operands: [], options: [flag('--json')], host: true,
    forms: [form('pdd machine list [--json]', 'List computers connected to your account.')],
  },
  {
    id: 'machine.disconnect', prefix: ['machine', 'disconnect'], operands: [operand('machine', 'label')], options: [flag('--json')], host: true,
    forms: [form('pdd machine disconnect <name|id> [--json]', 'Disconnect a computer while keeping its work running.')],
  },
  {
    id: 'machine.reconnect', prefix: ['machine', 'reconnect'], operands: [operand('machine', 'label')], options: [flag('--json')], host: true,
    forms: [form('pdd machine reconnect <name|id> [--json]', 'Reconnect a computer to your account.')],
  },
  {
    id: 'machine.rename', prefix: ['machine', 'rename'], operands: [operand('machine', 'label'), operand('name', 'text')], options: [flag('--json')], host: true,
    forms: [form('pdd machine rename <name|id> <new name> [--json]', 'Rename a computer in your account.')],
  },
  {
    id: 'machine.remove', prefix: ['machine', 'remove'], operands: [operand('machine', 'label')], options: [flag('--json')], host: true,
    forms: [form('pdd machine remove <name|id> [--json]', 'Remove a computer from your account after the existing checks.')],
  },
  {
    id: 'verify', prefix: ['verify'], operands: [operand('scenario', 'path', { optional: true })], options: [flag('--live'), value('--request', 'id'), flag('--json')],
    validate: 'runtime-request', host: true,
    forms: [form('pdd verify [scenario.json] [--live] [--json]', 'Check a prompt scenario with a supported runtime.'), form('pdd verify --request id [--json]', 'Read the result of an existing prompt check.')],
  },
  {
    id: 'try', prefix: ['try'], operands: [operand('prompt', 'path', { optional: true })], options: [
      flag('--json'), flag('--terminal'), value('--session', 'id'), value('--command', 'text'), value('--request', 'id'), value('--run', 'issue-ref'),
      value('--input', 'json-or-path'), value('--repeat', 'positive-int'),
    ], validate: 'try', host: true,
    forms: [
      form('pdd try [--json]', 'Open the current prompts with the local Try settings.'),
      form('pdd try <prompt> --input <file|json> [--repeat number] [--json]', 'Try a prompt with the supplied input.'),
      form('pdd try --request id [--json]', 'Read an existing Try request without sending it again.'),
      form('pdd try --run <issue> [--terminal] [--json]', 'Open the guided Try page and show its link and phone QR.'),
      form('pdd try --terminal [--session id] [--command text] [--json]', 'Type commands in a hosted session.'),
      form('pdd try --session id [--command text|--request id] [--json]', 'Send a line to or read a hosted session.'),
    ],
  },
  {
    id: 'call', prefix: ['call'], operands: [operand('prompt', 'path', { optional: true }), operand('operation', 'slug', { optional: true })], options: [
      value('--input', 'json'), value('--session', 'id'), value('--request', 'id'), flag('--json'),
    ], validate: 'call', host: true,
    forms: [form('pdd call <prompt> <operation> --input JSON [--session id] [--json]', 'Invoke a prompt entry and print its view.'), form('pdd call --request id [--json]', 'Read the result of an existing prompt call.')],
  },
  {
    id: 'tests', prefix: ['tests'], operands: [operand('action', 'choice:draft', { optional: true })], options: [value('--story', 'text'), value('--request', 'id'), flag('--json')],
    validate: 'tests', host: true,
    forms: [form('pdd tests draft --story text [--json]', 'Draft tests from a story.'), form('pdd tests --request id [--json]', 'Read the result of an existing test draft.')],
  },
  {
    id: 'lint', prefix: ['lint'], operands: [operand('path', 'path', { optional: true, repeat: true })], options: [value('--request', 'id'), flag('--json')],
    validate: 'runtime-request', host: true,
    forms: [form('pdd lint [paths...] [--json]', 'Check prompt rules for free.'), form('pdd lint --request id [--json]', 'Read the result of an existing prompt check.')],
  },
  {
    id: 'replay', prefix: ['replay'], operands: [operand('saved-check', 'path', { optional: true })], options: [value('--request', 'id'), flag('--json')],
    validate: 'runtime-request', host: true,
    forms: [form('pdd replay <saved-check> [--json]', 'Read a saved prompt check or Try.'), form('pdd replay --request id [--json]', 'Read the result of an existing replay request.')],
  },
  {
    id: 'runtime', prefix: ['runtime'], operands: [operand('operation', 'choice:discover,lint,draft-scenario,merge-scenario,report,debug,recover,replay-session', { optional: true })], options: [value('--request', 'id'), flag('--json')], validate: 'runtime', host: true,
    forms: [
      form('pdd runtime --request id [--json]', 'Read the result of an existing Runtime operation.'),
      form('pdd runtime discover [--json]', 'Run the Runtime discovery operation.'),
      form('pdd runtime lint [--json]', 'Run the Runtime lint operation.'),
      form('pdd runtime draft-scenario [--json]', 'Run the Runtime scenario drafting operation.'),
      form('pdd runtime merge-scenario [--json]', 'Run the Runtime scenario merge operation.'),
      form('pdd runtime report [--json]', 'Run the Runtime report operation.'),
      form('pdd runtime debug [--json]', 'Run the Runtime debugging operation.'),
      form('pdd runtime recover [--json]', 'Run the Runtime recovery operation.'),
      form('pdd runtime replay-session [--json]', 'Run the Runtime session replay operation.'),
    ],
  },
];

export const PUBLIC_COMMAND_ROUTES = Object.freeze(routes.map((route) => Object.freeze({
  ...route,
  prefix: Object.freeze([...route.prefix]),
  operands: Object.freeze([...route.operands]),
  options: Object.freeze([...route.options]),
  forms: Object.freeze([...route.forms]),
})));

export const PUBLIC_COMMAND_IDS = Object.freeze(PUBLIC_COMMAND_ROUTES.map((route) => route.id));

export const PUBLIC_COMMAND_MANIFEST = Object.freeze([
  form('pdd --version', 'Show the installed PDD CLI version.'),
  ...PUBLIC_COMMAND_ROUTES.flatMap((route) => route.forms),
].map((entry) => Object.freeze({ form: entry.form, description: entry.description })));

export const RUNTIME_OPERATIONS = Object.freeze(['discover', 'lint', 'draft-scenario', 'merge-scenario', 'report', 'debug', 'recover', 'replay-session']);
