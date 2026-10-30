// Generated from prompts/cli/workflow-agents.prompt.md (sha256: 7153c686a2e93da49e223c1fab5c93785763687fbe5f8dc3accbe62809b0bd67).
import { runAgentProcess, parseAgentAuthStatus } from './agent-adapters.mjs';

const agents = ['codex', 'claude'];
const names = { codex: 'Codex', claude: 'Claude Code' };
const install = {
  codex: 'https://developers.openai.com/codex/cli',
  claude: 'https://code.claude.com/docs/en/setup',
};
const statusArgs = { codex: ['login', 'status'], claude: ['auth', 'status'] };
const states = new Set(['ready', 'missing', 'signed_out', 'unavailable']);
const normalize = value => states.has(value) ? value : 'unavailable';
const refuse = message => ({ ok: false, agent: null, message });
function guidance(agent, state) {
  if (state === 'missing') return `${names[agent]} is not installed. Install: ${install[agent]}`;
  if (state === 'signed_out') return `${names[agent]} is not signed in. Run: ${agent === 'codex' ? 'codex login' : 'claude auth login'}`;
  return `${names[agent]} sign-in could not be checked. Run: ${agent} ${statusArgs[agent].join(' ')}`;
}
export function chooseWorkflowAgent({ codex, claude, requested } = {}) {
  if (requested !== undefined && !agents.includes(requested)) return refuse('Choose --agent codex or --agent claude.');
  const observed = { codex: normalize(codex), claude: normalize(claude) };
  const candidates = requested === undefined ? agents : [requested];
  const agent = candidates.find(name => observed[name] === 'ready');
  if (agent) return { ok: true, agent, message: '' };
  if (requested === undefined && agents.every(name => observed[name] === 'missing')) {
    return refuse(`Install Codex or Claude Code first.\nCodex: ${install.codex}\nClaude Code: ${install.claude}`);
  }
  return refuse(candidates.map(name => guidance(name, observed[name])).join('\n'));
}
export async function checkWorkflowAgents({ cwd = process.cwd(), env = process.env, requested } = {}, { run = runAgentProcess } = {}) {
  if (requested !== undefined && !agents.includes(requested)) return chooseWorkflowAgent({ requested });
  const observed = { codex: 'unavailable', claude: 'unavailable' };
  await Promise.all((requested === undefined ? agents : [requested]).map(async agent => {
    try {
      observed[agent] = parseAgentAuthStatus({agent,result:await run(agent, [...statusArgs[agent]], { cwd, env, input: '', timeoutMs: 10000, maxBytes: 16384 })});
    } catch (error) { observed[agent] = error?.code === 'ENOENT' && error.executableMissing === true ? 'missing' : 'unavailable'; }
  }));
  return chooseWorkflowAgent({ ...observed, requested });
}
