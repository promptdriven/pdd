// Generated from prompts/cli/command-catalog.prompt.md (sha256: 77480f8f0bde4c142761947a3c385fd023573a5b232a70ae333b229506c58a69).
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
  { id: 'phone', prefix: ['phone'], local: 'phone', operands: [], options: [
    {name:'--relay',kind:'value'},{name:'--name',kind:'value'},{name:'--codex',kind:'value'},{name:'--claude',kind:'value'},{name:'--no-integrations',kind:'flag'}],
    forms:[form('pdd phone [--relay URL] [--name NAME] [--codex PATH] [--claude PATH] [--no-integrations]','Set up the local PDD phone Link.')] },
  { id: 'link.status', prefix: ['link','status'], local: 'link-status', operands: [], options:[{name:'--json',kind:'flag'}], forms:[form('pdd link status [--json]','Show local Link status.')] },
  { id: 'link.restart', prefix: ['link','restart'], local: 'link-restart', operands: [], options: [], forms:[form('pdd link restart','Restart local Link.')] },
  { id: 'link.stop', prefix: ['link','stop'], local: 'link-stop', operands: [], options: [], forms:[form('pdd link stop','Stop local Link.')] },
  { id: 'link.logs', prefix: ['link','logs'], local: 'link-logs', operands: [], options: [], forms:[form('pdd link logs','Show local Link logs.')] },
  { id: 'link.devices', prefix: ['link','devices'], local: 'link-devices', operands: [], options: [], forms:[form('pdd link devices','List paired Link devices.')] },
  { id: 'link.revoke', prefix: ['link','revoke'], local: 'link-revoke', operands:[{name:'id-or-name',type:'text'}], options: [], forms:[form('pdd link revoke ID_OR_NAME','Revoke a paired Link device.')] },
  { id: 'link.uninstall', prefix: ['link','uninstall'], local: 'link-uninstall', operands: [], options:[{name:'--forget',kind:'flag'}], forms:[form('pdd link uninstall [--forget]','Remove the local Link service.')] },
  { id: 'link.reset-identity', prefix: ['link','reset-identity'], local: 'link-reset-identity', operands: [], options: [], forms:[form('pdd link reset-identity','Reset local Link identity.')] },
  { id: 'link.run', prefix: ['link','run'], local: 'link-run', operands: [], options: [], forms:[] },
];
const value = (name, choices) => ({name,kind:'value',...(choices?{choices}: {})});
const flag = name => ({name,kind:'flag'});
const operand = (name,type='text',optional=false,repeat=false) => ({name,type,optional,repeat});
function route(id,prefix,operands=[],options=[],syntax='',description='') {
  routes.push({id,prefix:prefix.split(' '),local:id.replaceAll('.','-'),operands,options,
    forms:[form(`pdd ${prefix}${syntax?' '+syntax:''}`,description)]});
}
route('agents','agents',[],[value('--search')],'[--search TEXT]','List fleet agents.');
route('open','open',[operand('agent')],[],'AGENT','Open an agent in Herdr.');
route('agent.show','agent show',[operand('agent')],[flag('--terminal')],'AGENT [--terminal]','Show an agent.');
route('agent.send','agent send',[operand('agent'),operand('text')],[value('--id')],'AGENT TEXT --id ACTION_ID','Send text once with an action id.');
route('agent.keys','agent keys',[operand('agent'),operand('key','text',false,true)],[value('--id')],'AGENT KEY [KEY ...] --id ACTION_ID','Send keys once.');
route('agent.resume','agent resume',[operand('agent')],[value('--id')],'AGENT --id ACTION_ID','Resume a managed agent.');
route('agent.stop','agent stop',[operand('agent')],[value('--how',['interrupt','exit','close']),value('--id')],'AGENT --how interrupt|exit|close --id ACTION_ID','Stop the selected agent.');
route('agent.dismiss','agent dismiss',[operand('agent')],[],'AGENT','Dismiss an agent.');
route('setup','setup',[],[flag('--no-phone')],'[--no-phone]','Set up this machine through the optional client.');
route('join','join',[],[],'','Join a fleet through the optional client.');
for (const [cmd,ops,opts,syntax] of [
 ['status',[],[],''],['approve',[operand('code')],[],'CODE'],['remove',[operand('member')],[],'MEMBER'],
 ['admissions',[operand('member')],[],'MEMBER'],['tag',[operand('machine'),operand('tag','choice:always-on,laptop')],[],'MACHINE always-on|laptop'],
 ['rename',[operand('machine'),operand('name')],[],'MACHINE NAME'],
 ['set-endpoints',[],['--relay','--keeper','--app'].map(n=>value(n)),'[--relay URL] [--keeper URL] [--app URL]']])
 route(`fleet.${cmd}`,`fleet ${cmd}`,ops,opts,syntax,'Use the optional fleet client.');
route('accounts','accounts',[],[],'','List machine/tool accounts through the optional client.');
for (const [cmd,ops,opts,syntax] of [
 ['add',[operand('tool','choice:codex,claude,anthropic-key'),operand('name')],[flag('--from-pool'),flag('--replace')],'codex|claude|anthropic-key NAME [options]'],
 ...['remove','resign'].map(c=>[c,[operand('account')],[],'ACCOUNT']),['delete-all',[],[],''],
 ['mode',[operand('tool','choice:codex,claude'),operand('setting','text',true)],[value('--machine')],'[--machine MACHINE] TOOL [auto|ACCOUNT]'],
 ['when-out',[operand('tool','choice:codex,claude'),operand('setting','choice:ask,continue,wait',true)],[value('--machine')],'[--machine MACHINE] TOOL [ask|continue|wait]'],
 ['quota-decide',[operand('question-id','uuid')],[value('--decision',['continue','wait']),value('--rev')],'QUESTION_ID --decision continue|wait --rev N'],
 ['migrate-sessions',[],[],''],['rotate',[operand('kind','choice:github')],[],'github'],
 ['policy',[operand('tool','choice:codex,claude')],[value('--machine'),value('--pinned'),value('--then',['auto','wait']),value('--exclude')],'[--machine MACHINE] TOOL [--pinned ACCOUNTS --then auto|wait] [--exclude ACCOUNTS]'],
 ['allow',[operand('account'),operand('allowed','choice:on,off')],[value('--machine')],'ACCOUNT --machine MACHINE on|off']])
 route(`accounts.${cmd}`,`accounts ${cmd}`,ops,opts,syntax,'Use the optional accounts client.');
for (const entry of routes) {
  if (['phone','link','fleet','agents','agent','open','accounts','setup','join'].includes(entry.prefix[0])) {
    entry.optionalClient = true;
    entry.forms = entry.forms.map(({form: syntax, description}) => form(syntax,
      description.includes('optional') ? description : `${description} Needs the optional client.`));
  }
}
export const PUBLIC_COMMAND_ROUTES = Object.freeze(routes.map(route => Object.freeze({ ...route,
  prefix: Object.freeze(route.prefix), operands: Object.freeze(route.operands.map(Object.freeze)),
  options: Object.freeze(route.options.map(option => Object.freeze({...option,
    ...(option.choices ? {choices: Object.freeze([...option.choices])} : {})}))), forms: Object.freeze(route.forms) })));
export const PUBLIC_COMMAND_IDS = Object.freeze(PUBLIC_COMMAND_ROUTES.map(route => route.id));
export const PUBLIC_COMMAND_MANIFEST = Object.freeze(PUBLIC_COMMAND_ROUTES.flatMap(route => route.forms));
