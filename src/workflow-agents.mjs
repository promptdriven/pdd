// Generated from prompts/cli/workflow-agents.prompt.md (sha256: 89752e2b49583cc7b857ab463fdfa2d9f42396cb2781a26d440720bf16117265).
import { runAgentProcess } from './agent-adapters.mjs';

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
function authState(agent, result) {
  if (!result || !Number.isInteger(result.code) || typeof result.stdout !== 'string' || typeof result.stderr !== 'string') return 'unavailable';
  if (agent === 'claude') {
    try {
      const value = JSON.parse(result.stdout);
      if (value?.loggedIn === true && result.code === 0) return 'ready';
      if (value?.loggedIn === false && [0, 1].includes(result.code)) return 'signed_out';
    } catch { /* An untyped response is not sign-in evidence. */ }
    return 'unavailable';
  }
  const text = `${result.stdout}\n${result.stderr}`.replace(/\x1b\[[0-?]*[ -/]*[@-~]/g, '');
  const negative = /\bnot\s+(?:logged|signed)\s+in\b|\b(?:login|sign[ -]?in)\s+required\b/i.test(text);
  if ([0, 1].includes(result.code) && negative) return 'signed_out';
  return result.code === 0 && /\blogged in\b/i.test(text) ? 'ready' : 'unavailable';
}
export async function checkWorkflowAgents({ cwd = process.cwd(), env = process.env, requested } = {}, { run = runAgentProcess } = {}) {
  if (requested !== undefined && !agents.includes(requested)) return chooseWorkflowAgent({ requested });
  const observed = { codex: 'unavailable', claude: 'unavailable' };
  for (const agent of requested === undefined ? agents : [requested]) {
    try {
      observed[agent] = authState(agent, await run(agent, [...statusArgs[agent]], { cwd, env, input: '', timeoutMs: 10000, maxBytes: 16384 }));
    } catch (error) { observed[agent] = error?.code === 'ENOENT' ? 'missing' : 'unavailable'; }
  }
  return chooseWorkflowAgent({ ...observed, requested });
}
