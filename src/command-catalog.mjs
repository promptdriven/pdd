// Generated from prompts/cli/command-catalog.prompt.md (sha256: a2156835acacfeae7930c601b97ee99e8eb205afb781094a132c337b010aa826).
const form = (form, description) => Object.freeze({ form, description });
export const BUNDLED_WORKFLOW_NAMES = Object.freeze(['feature', 'bug', 'small-change']);
const routes = [
  { id: 'workflow.run', prefix: ['workflow', 'run'], local: 'workflow-run',
    operands: [{name:'name',type:'workflow-name'},{name:'issue',type:'issue'}],
    options:[{name:'--agent',kind:'value',choices:['codex','claude']}],
    forms:[form('pdd workflow run NAME ISSUE [--agent codex|claude]', 'Run a validated project or bundled workflow for a GitHub issue; may push branches and create real PRs.')] },
  { id: 'workflow.resume', prefix: ['workflow', 'resume'], local: 'workflow-resume',
    operands:[{name:'run-id',type:'uuid'}],options:[{name:'--decision',kind:'value',choices:['approve','skip']}],
    forms:[form('pdd workflow resume RUN_ID [--decision approve|skip]', 'Inspect or continue a saved workflow; omitted decision only reads/reconciles.')] },
  { id: 'workflow.attach', prefix: ['workflow', 'attach'], local: 'workflow-attach',
    operands:[{name:'run-id',type:'uuid'}],options:[],
    forms:[form('pdd workflow attach RUN_ID','Attach to the saved active background stage; archived stages return information.')] },
  ...BUNDLED_WORKFLOW_NAMES.map(name => ({ id: `workflow.${name}`, prefix: ['workflow', name], local: 'session', workflowName: name,
    operands: [{ name: 'request', type: 'text', optional: true, repeat: true }],
    options: [{ name: '--agent', kind: 'value', choices: ['codex', 'claude'] }],
    forms: [form(`pdd workflow ${name} [--agent codex|claude] [request text]`, `Open your coding agent with the short PDD intro and the pdd-${name} skill; default codex.`)] })),
  { id: 'session', prefix: ['session'], local: 'session', operands: [{ name: 'request', type: 'text', optional: true, repeat: true }],
    options: [{ name: '--agent', kind: 'value', choices: ['codex', 'claude'] }],
    forms: [form('pdd session [--agent codex|claude] [request text]', 'Open your coding agent with the short PDD intro; it loads the PDD skills when needed. Default codex.')] },
  { id: 'help', prefix: ['help'], local: 'help', operands: [], options: [], forms: [
    form('pdd', 'Show local alpha commands.'), form('pdd --help', 'Show local alpha commands.'),
    form('pdd -h', 'Show local alpha commands.'), form('pdd help', 'Show local alpha commands.') ] },
  { id: 'version', prefix: ['--version'], local: 'version', operands: [], options: [],
    forms: [form('pdd --version', 'Show this package version.')] },
  { id: 'completion', prefix: ['completion'], local: 'completion', operands: [{ name: 'shell', type: 'choice:bash,zsh' }], options: [],
    forms: [form('pdd completion bash|zsh', 'Print local shell completion.')] },
  { id: 'workflow.list', prefix: ['workflow', 'list'], local: 'workflow-list', operands: [], options: [{ name: '--json', kind: 'flag' }],
    forms: [form('pdd workflow list [--json]', 'List validated project and bundled workflow definitions.')] },
  { id: 'check', prefix: ['check'], local: 'runtime-check', operands: [{ name: 'story', type: 'text', optional: true, repeat: true }],
    options: [{ name: '--json', kind: 'flag' }, { name: '--details', kind: 'flag' }, { name: '--timeout', kind: 'integer', min: 1, max: 120 },
      { name: '--max-calls', kind: 'integer', min: 1, max: 100 }, { name: '--read', kind: 'flag' }, { name: '--fill-hash', kind: 'flag' },
      { name: '--files', kind: 'flag' }, { name: '--request', kind: 'uuid', hidden: true }],
    forms: [form('pdd check [STORY...] [--json] [--details] [--timeout MIN] [--max-calls N]', 'Check stories on the PDD runtime with your gh login: sends your Git files, then prints one table with report links.'),
      form('pdd check --read [BATCH] [--json]', 'Show saved check results again; sends no check.'),
      form('pdd check --fill-hash', 'Fill prose_sha256 of draft runtime interfaces; no network.'),
      form('pdd check --files', 'List the files a check would send; no network.')] },
  { id: 'try', prefix: ['try'], local: 'runtime-try', operands: [{ name: 'story', type: 'text', optional: true }],
    options: [{ name: '--tab', kind: 'value', choices: ['call', 'screen', 'terminal', 'world'] }, { name: '--new', kind: 'flag' },
      { name: '--no-open', kind: 'flag' }, { name: '--stop', kind: 'flag' }, { name: '--app-map', kind: 'text' }],
    forms: [form('pdd try [STORY] [--tab call|screen|terminal|world] [--app-map PATH] [--new] [--no-open]', 'Make a Try link on the PDD runtime with your gh login and open it in your browser; it ends in 24 hours.'),
      form('pdd try --stop [STORY]', 'Stop the open Try link of a story.')] },
];
export const PUBLIC_COMMAND_ROUTES = Object.freeze(routes.map(route => Object.freeze({ ...route,
  prefix: Object.freeze(route.prefix), operands: Object.freeze(route.operands.map(Object.freeze)),
  options: Object.freeze(route.options.map(Object.freeze)), forms: Object.freeze(route.forms) })));
export const PUBLIC_COMMAND_IDS = Object.freeze(PUBLIC_COMMAND_ROUTES.map(route => route.id));
export const PUBLIC_COMMAND_MANIFEST = Object.freeze(PUBLIC_COMMAND_ROUTES.flatMap(route => route.forms));
