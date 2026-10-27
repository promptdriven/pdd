// Generated from prompts/cli/command-catalog.prompt.md (sha256: c9fc4197c58379215291391cfff6d7b1d1220b2e65c52b0923cd78e6ba06a0ec).
const form = (form, description) => Object.freeze({ form, description });
export const BUNDLED_WORKFLOW_NAMES = Object.freeze(['feature', 'bug', 'small-change']);
const routes = [
  { id: 'workflow.decide', prefix: ['workflow', 'decide'], local: 'workflow-decide',
    operands:[{name:'run-id',type:'uuid'}], options:[{name:'--decision',kind:'value',choices:['approve','changes','skip']},
      {name:'--via',kind:'value',choices:['phone']},
      ...['--text','--id','--expect-stage','--expect-seq','--phone','--approval'].map(name=>({name,kind:'value'})),
      {name:'--yes',kind:'flag'},{name:'--json',kind:'flag'}],
    forms:[form('pdd workflow decide RUN_ID --decision approve|changes|skip [--text TEXT] --id UUID --expect-stage STAGE --expect-seq N [--yes] [--via phone --phone PHONE_ID --approval TOKEN] [--json]', 'Apply one bound person decision and continue the saved workflow.')] },
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
