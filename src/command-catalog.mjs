// Generated from prompts/cli/command-catalog.prompt.md (sha256: c1a15906d43ed6f57c65823488bbe0fe38dd260b2d5c91c09fbd8af764d8f09f).
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
    operands:[{name:'issue',type:'run-ref'}],options:[],
    forms:[form('pdd workflow attach ISSUE','Attach to the saved active background stage; archived stages return information.')] },
  { id: 'workflow.runs', prefix: ['workflow', 'runs'], local: 'workflow-runs',
    operands:[{name:'issue',type:'run-ref',optional:true}],options:[{name:'--json',kind:'flag'}],
    forms:[form('pdd workflow runs [ISSUE] [--json]','List saved workflow runs or inspect one run and its finished stages.')] },
  { id: 'workflow.open', prefix: ['workflow', 'open'], local: 'workflow-open',
    operands:[{name:'issue',type:'run-ref'},{name:'stage',type:'workflow-name'}],options:[],
    forms:[form('pdd workflow open ISSUE STAGE','Inspect a finished native session read-only after a y/N warning; use attach for live stages.')] },
  ...BUNDLED_WORKFLOW_NAMES.map(name => ({ id: `workflow.${name}`, prefix: ['workflow', name], local: 'session', workflowName: name,
    operands: [{ name: 'request', type: 'text', optional: true, repeat: true }],
    options: [{ name: '--agent', kind: 'value', choices: ['codex', 'claude'] }],
    forms: [form(`pdd workflow ${name} [--agent codex|claude] [request text]`, `Open a native conversation following the bundled ${name} recipe; default codex.`)] })),
  { id: 'session', prefix: ['session'], local: 'session', operands: [{ name: 'request', type: 'text', optional: true, repeat: true }],
    options: [{ name: '--agent', kind: 'value', choices: ['codex', 'claude'] }],
    forms: [form('pdd session [--agent codex|claude] [request text]', 'Open an installed native agent with the full guide and manual recipes; default codex.')] },
  { id: 'help', prefix: ['help'], local: 'help', operands: [], options: [], forms: [
    form('pdd', 'Show local alpha commands.'), form('pdd --help', 'Show local alpha commands.'),
    form('pdd -h', 'Show local alpha commands.'), form('pdd help', 'Show local alpha commands.') ] },
  { id: 'version', prefix: ['--version'], local: 'version', operands: [], options: [],
    forms: [form('pdd --version', 'Show this package version.')] },
  { id: 'skill', prefix: ['--skill'], local: 'skill', operands: [], options: [],
    forms: [form('pdd --skill', 'Print the full Prompting guide, then the skill and its references.')] },
  { id: 'completion', prefix: ['completion'], local: 'completion', operands: [{ name: 'shell', type: 'choice:bash,zsh' }], options: [],
    forms: [form('pdd completion bash|zsh', 'Print local shell completion.')] },
  { id: 'workflow.list', prefix: ['workflow', 'list'], local: 'workflow-list', operands: [], options: [{ name: '--json', kind: 'flag' }],
    forms: [form('pdd workflow list [--json]', 'List validated project and bundled workflow definitions.')] },
];
export const PUBLIC_COMMAND_ROUTES = Object.freeze(routes.map(route => Object.freeze({ ...route,
  prefix: Object.freeze(route.prefix), operands: Object.freeze(route.operands.map(Object.freeze)),
  options: Object.freeze(route.options.map(Object.freeze)), forms: Object.freeze(route.forms) })));
export const PUBLIC_COMMAND_IDS = Object.freeze(PUBLIC_COMMAND_ROUTES.map(route => route.id));
export const PUBLIC_COMMAND_MANIFEST = Object.freeze(PUBLIC_COMMAND_ROUTES.flatMap(route => route.forms));
