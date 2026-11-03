// Generated from prompts/cli/workflow-agents.prompt.md (sha256: 9aac7f1b3cadbc84d2416d6cbf32c1227b9d9ae9c8603586ac119efa44bb57de).
import { runAgentProcess, parseAgentAuthStatus } from './agent-adapters.mjs';

const agents = ['codex', 'claude', 'gemini'];
const names = { codex: 'Codex', claude: 'Claude Code', gemini: 'Gemini CLI' };
const install = {
  codex: 'https://developers.openai.com/codex/cli',
  claude: 'https://code.claude.com/docs/en/setup',
  gemini: 'https://geminicli.com/docs/get-started/installation/',
};
const statusArgs = { codex: ['login', 'status'], claude: ['auth', 'status'], gemini: ['--version'] };
const states = new Set(['ready', 'missing', 'signed_out', 'unavailable']);
const normalize = value => states.has(value) ? value : 'unavailable';
const refuse = message => ({ ok: false, agent: null, message });
function guidance(agent, state) {
  if (state === 'missing') return `${names[agent]} is not installed. Install: ${install[agent]}`;
  if (state === 'signed_out') return `${names[agent]} is not signed in. Run: ${agent === 'codex' ? 'codex login' : agent === 'claude' ? 'claude auth login' : 'gemini'}`;
  return `${names[agent]} sign-in could not be checked. Run: ${agent} ${statusArgs[agent].join(' ')}`;
}
export function chooseWorkflowAgent({ codex, claude, gemini, requested } = {}) {
  if (requested !== undefined && !agents.includes(requested)) return refuse('Choose --agent codex, --agent claude or --agent gemini.');
  const observed = { codex: normalize(codex), claude: normalize(claude), gemini: normalize(gemini) };
  const available = gemini === undefined ? agents.slice(0, 2) : agents;
  const candidates = requested === undefined ? available : [requested];
  const agent = candidates.find(name => observed[name] === 'ready');
  if (agent) return { ok: true, agent, message: '' };
  if (requested === undefined && candidates.every(name => observed[name] === 'missing')) {
    if (gemini === undefined) return refuse(`Install Codex or Claude Code first.\nCodex: ${install.codex}\nClaude Code: ${install.claude}`);
    return refuse(`Install Codex, Claude Code or Gemini CLI first.\nCodex: ${install.codex}\nClaude Code: ${install.claude}\nGemini CLI: ${install.gemini}`);
  }
  return refuse(candidates.map(name => guidance(name, observed[name])).join('\n'));
}
export async function checkWorkflowAgents({ cwd = process.cwd(), env = process.env, requested } = {}, { run = runAgentProcess } = {}) {
  if (requested !== undefined && !agents.includes(requested)) return chooseWorkflowAgent({ requested });
  const observed = { codex: 'unavailable', claude: 'unavailable', gemini: 'unavailable' };
  await Promise.all((requested === undefined ? agents : [requested]).map(async agent => {
    try {
      const result = await run(agent, [...statusArgs[agent]], { cwd, env, input: '', timeoutMs: 10000, maxBytes: 16384 });
      observed[agent] = agent === 'gemini' ? (result?.code === 0 && typeof result.stdout === 'string' && result.stdout.trim() ? 'ready' : 'unavailable') : parseAgentAuthStatus({agent,result});
    } catch (error) { observed[agent] = error?.code === 'ENOENT' && error.executableMissing === true ? 'missing' : 'unavailable'; }
  }));
  return chooseWorkflowAgent({ ...observed, requested });
}
