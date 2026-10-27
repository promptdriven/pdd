// Generated from prompts/cli/command-catalog.prompt.md (sha256: 310fcd1767f1a259ea53fd3c11ea15b3210daaa22ecdc0c1b4ea372b4c56857b).
const form = (form, description) => Object.freeze({ form, description });
export const BUNDLED_WORKFLOW_NAMES = Object.freeze(['feature', 'bug', 'small-change']);
const routes = [
  { id: 'workflow.run', prefix: ['workflow', 'run'], local: 'workflow-run',
    operands: [{name:'name',type:'workflow-name'},{name:'issue',type:'issue'}],
    options:[{name:'--agent',kind:'value',choices:['codex','claude']}],
    forms:[form('pdd workflow run NAME ISSUE [--agent codex|claude]', 'Start the first area chat for a GitHub issue in Herdr and exit; pdd later pushes the branch and opens a real PR.')] },
  { id: 'workflow.done', prefix: ['workflow', 'done'], local: 'workflow-done',
    operands: [{name:'step',type:'workflow-name'}], options: [{name:'--summary',kind:'text'}],
    forms: [form('pdd workflow done STEP [--summary TEXT]', 'For the agent in a run worktree: record a step and print what to do next.')] },
  { id: 'workflow.approve', prefix: ['workflow', 'approve'], local: 'workflow-approve',
    operands: [{name:'issue',type:'issue',optional:true}], options: [],
    forms: [form('pdd workflow approve [ISSUE]', 'Approve the area at its gate and start the next area in a new chat. Only a person approves.')] },
  { id: 'workflow.changes', prefix: ['workflow', 'changes'], local: 'workflow-changes',
    operands: [{name:'issue',type:'issue'},{name:'request',type:'text',repeat:true}], options: [],
    forms: [form('pdd workflow changes ISSUE TEXT', 'Send a change request to the same area chat; the gate stays open.')] },
  { id: 'workflow.cancel', prefix: ['workflow', 'cancel'], local: 'workflow-cancel',
    operands: [{name:'issue',type:'issue'}], options: [],
    forms: [form('pdd workflow cancel ISSUE', 'Cancel the run and close its Herdr tabs; keep the worktree and branch.')] },
  { id: 'workflow.status', prefix: ['workflow', 'status'], local: 'workflow-status',
    operands: [{name:'issue',type:'issue',optional:true}], options: [],
    forms: [form('pdd workflow status [ISSUE]', 'Show runs, or one run with its area, gate, chat and PR with CI state.')] },
  { id: 'workflow.open', prefix: ['workflow', 'open'], local: 'workflow-open',
    operands: [{name:'issue',type:'issue'}], options: [],
    forms: [form('pdd workflow open ISSUE', 'Focus or attach the current area chat; resume it if its session ended.')] },
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
    forms: [form('pdd workflow list [--json]', 'List the bundled workflows with their areas and gates.')] },
];
export const PUBLIC_COMMAND_ROUTES = Object.freeze(routes.map(route => Object.freeze({ ...route,
  prefix: Object.freeze(route.prefix), operands: Object.freeze(route.operands.map(Object.freeze)),
  options: Object.freeze(route.options.map(Object.freeze)), forms: Object.freeze(route.forms) })));
export const PUBLIC_COMMAND_IDS = Object.freeze(PUBLIC_COMMAND_ROUTES.map(route => route.id));
export const PUBLIC_COMMAND_MANIFEST = Object.freeze(PUBLIC_COMMAND_ROUTES.flatMap(route => route.forms));
