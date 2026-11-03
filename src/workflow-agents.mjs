// Generated from prompts/cli/workflow-agents.prompt.md (sha256: 4688f5ace9bee53f3b062992c70e0e679113f2d0b34b9f48cdd978652509538f).
import { runAgentProcess, parseAgentAuthStatus } from './agent-adapters.mjs';

const agents = ['codex', 'claude', 'gemini', 'agy'];
const names = { codex: 'Codex', claude: 'Claude Code', gemini: 'Gemini CLI', agy: 'Antigravity CLI' };
const install = {
  codex: 'https://developers.openai.com/codex/cli',
  claude: 'https://code.claude.com/docs/en/setup',
  gemini: 'https://geminicli.com/docs/get-started/installation/',
  agy: 'https://antigravity.google/docs/cli/',
};
const statusArgs = { codex: ['login', 'status'], claude: ['auth', 'status'], gemini: ['--version'], agy: ['models'] };
const signIn = { codex: 'codex login', claude: 'claude auth login', gemini: 'gemini', agy: 'agy' };
// Gemini CLI serves only a paid API key, Vertex AI or Code Assist; free and Google One accounts use Antigravity CLI.
const paidGemini = ['GEMINI_API_KEY', 'GOOGLE_API_KEY', 'GOOGLE_GENAI_USE_VERTEXAI', 'GOOGLE_GENAI_USE_GCA'];
export const GEMINI_FREE_HINT = 'With a free or Google One account, Gemini CLI does not run; use Antigravity CLI: --agent agy.';
const states = new Set(['ready', 'missing', 'signed_out', 'unavailable']);
const normalize = value => states.has(value) ? value : 'unavailable';
const refuse = message => ({ ok: false, agent: null, message });
function guidance(agent, state) {
  if (state === 'missing') return `${names[agent]} is not installed. Install: ${install[agent]}`;
  if (state === 'signed_out') return `${names[agent]} is not signed in. Run: ${signIn[agent]}`;
  return `${names[agent]} sign-in could not be checked. Run: ${agent} ${statusArgs[agent].join(' ')}`;
}
export function chooseWorkflowAgent({ codex, claude, gemini, agy, requested } = {}) {
  if (requested !== undefined && !agents.includes(requested)) return refuse('Choose --agent codex, --agent claude, --agent gemini or --agent agy.');
  const observed = { codex: normalize(codex), claude: normalize(claude), gemini: normalize(gemini), agy: normalize(agy) };
  // An omitted optional state keeps the older candidate set and its guidance.
  const given = { gemini, agy }, available = agents.filter(name => !(name in given) || given[name] !== undefined);
  const candidates = requested === undefined ? available : [requested];
  const agent = candidates.find(name => observed[name] === 'ready');
  if (agent) return { ok: true, agent, message: '' };
  if (requested === undefined && candidates.every(name => observed[name] === 'missing')) {
    const listed = candidates.map(name => names[name]);
    return refuse(`Install ${listed.slice(0, -1).join(', ')} or ${listed.at(-1)} first.\n${candidates.map(name => `${names[name]}: ${install[name]}`).join('\n')}`);
  }
  return refuse(candidates.map(name => guidance(name, observed[name])).join('\n'));
}
export async function checkWorkflowAgents({ cwd = process.cwd(), env = process.env, requested } = {}, { run = runAgentProcess } = {}) {
  if (requested !== undefined && !agents.includes(requested)) return chooseWorkflowAgent({ requested });
  const observed = { codex: 'unavailable', claude: 'unavailable', gemini: 'unavailable', agy: 'unavailable' };
  await Promise.all((requested === undefined ? agents : [requested]).map(async agent => {
    try {
      const result = await run(agent, [...statusArgs[agent]], { cwd, env, input: '', timeoutMs: 10000, maxBytes: 16384 });
      observed[agent] = agent === 'gemini' ? (result?.code === 0 && typeof result.stdout === 'string' && result.stdout.trim() ? 'ready' : 'unavailable')
        : agent === 'agy' ? agyStatus(result) : parseAgentAuthStatus({agent,result});
    } catch (error) { observed[agent] = error?.code === 'ENOENT' && error.executableMissing === true ? 'missing' : 'unavailable'; }
  }));
  const chosen = chooseWorkflowAgent({ ...observed, requested });
  return chosen.agent === 'gemini' && !paidGemini.some(name => env?.[name]) ? { ...chosen, hint: GEMINI_FREE_HINT } : chosen;
}
// `agy models` lists models only for a signed-in person (no model query); signed out it exits 1 with a sign-in line.
function agyStatus(result) {
  if (!result || !Number.isInteger(result.code) || typeof result.stdout !== 'string' || typeof result.stderr !== 'string') return 'unavailable';
  if (result.code === 0 && result.stdout.trim()) return 'ready';
  return result.code === 1 && /\bsign in\b/i.test(result.stdout + result.stderr) ? 'signed_out' : 'unavailable';
}
