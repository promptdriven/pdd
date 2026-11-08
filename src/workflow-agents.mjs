// Generated from prompts/cli/workflow-agents.prompt.md (sha256: 3cd75468a0c40badcdcb79fdc2f5c94dc1e46ac32fac7480277f708d237a9eda).
import { runAgentProcess, parseAgentAuthStatus } from './agent-adapters.mjs';
import { loadAgentDefinitions } from './agent-config.mjs';

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
// The one list, per agent kind, of the variables that choose an agent's login or account. Every chat launch carries the
// caller's values for them and unsets the rest, so the Herdr server's old copy never decides the login. The config-folder
// variable is apart: the run saves it as configDir.
export const LOGIN_VARIABLES = Object.freeze({
  claude: Object.freeze(['ANTHROPIC_API_KEY', 'ANTHROPIC_AUTH_TOKEN', 'CLAUDE_CODE_OAUTH_TOKEN', 'ANTHROPIC_BASE_URL', 'CLAUDE_CODE_USE_BEDROCK', 'CLAUDE_CODE_USE_VERTEX']),
  codex: Object.freeze(['OPENAI_API_KEY', 'CODEX_API_KEY', 'CODEX_ACCESS_TOKEN', 'OPENAI_FEDERATION_RULE_ID', 'OPENAI_IDENTITY_TOKEN_FILE', 'OPENAI_WORKLOAD_IDENTITY_CONTEXT', 'OPENAI_BASE_URL']),
  gemini: Object.freeze(['GEMINI_API_KEY', 'GOOGLE_API_KEY', 'GOOGLE_GENAI_USE_VERTEXAI', 'GOOGLE_GENAI_USE_GCA', 'GOOGLE_APPLICATION_CREDENTIALS', 'GOOGLE_CLOUD_PROJECT']),
  agy: Object.freeze([]),
});
// Names that the shell owns when the chat's child sh runs `export NAME=value`: it refuses them (the agent then does not
// start) or sets its own value. Found with bash, dash, BusyBox ash, zsh and ksh as sh, on macOS and Linux.
export const SHELL_RESERVED_NAMES = Object.freeze(['BASHOPTS', 'BASHPID', 'BASH_ALIASES', 'BASH_ARGC', 'BASH_ARGV', 'BASH_CMDS', 'BASH_COMMAND',
  'BASH_LINENO', 'BASH_SOURCE', 'BASH_SUBSHELL', 'BASH_VERSINFO', 'DIRSTACK', 'EGID', 'EPOCHREALTIME', 'EPOCHSECONDS', 'EUID', 'FUNCNAME', 'GID',
  'GROUPS', 'HISTCMD', 'KSH_VERSION', 'LINENO', 'OPTIND', 'PIPESTATUS', 'PPID', 'RANDOM', 'SECONDS', 'SHELLOPTS', 'SHLVL', 'SRANDOM', 'TTYIDLE',
  'UID', 'ZSH_EVAL_CONTEXT', 'ZSH_SUBSHELL', '_', 'signals']);
// One line that names the entry's shell-reserved env names, or null. It never shows a command or an env value.
export function reservedEnvMessage({ name, env = {} }) {
  const reserved = Object.keys(env).filter(key => SHELL_RESERVED_NAMES.includes(key));
  return reserved.length ? `The agents.json entry ${JSON.stringify(String(name))} sets names in env that the shell controls: ${reserved.join(', ')}. pdd cannot give them to the chat. Remove them from that entry's env, then run the command again.` : null;
}
const CHOICES = '--agent codex, --agent claude, --agent gemini or --agent agy';
// --agent is a built-in agent or the name of a ~/.config/pdd/agents.json entry. A built-in name never reads the file.
export function workflowAgentEntry(requested, { cwd, env = process.env } = {}, load = loadAgentDefinitions) {
  if (requested === undefined || agents.includes(requested)) return { ok: true, agent: requested, definition: null };
  let definitions;
  try { definitions = load({ cwd, env }); }
  catch (error) { return refuse(`${error.message} Fix ~/.config/pdd/agents.json, or choose ${CHOICES}.`); }
  const found = definitions.find(item => item.name === requested);
  // An enabled default entry (Codex, Claude, Gemini) is the built-in agent.
  if (found && agents.includes(found.id)) return { ok: true, agent: found.kind, definition: null };
  // The chat's child sh could not set a shell-reserved name, so such an entry refuses before any effect.
  if (found) return reservedEnvMessage(found) ? refuse(reservedEnvMessage(found)) : { ok: true, agent: found.kind, definition: found };
  const names = definitions.filter(item => !agents.includes(item.id)).map(item => JSON.stringify(item.name));
  return refuse(`Unknown agent ${JSON.stringify(String(requested))}. Choose ${CHOICES}${names.length ? `, or a name from ~/.config/pdd/agents.json: ${names.join(', ')}.` : '. ~/.config/pdd/agents.json has no agent with that name.'}`);
}
const states = new Set(['ready', 'missing', 'signed_out', 'unavailable']);
const normalize = value => states.has(value) ? value : 'unavailable';
const refuse = message => ({ ok: false, agent: null, message });
function guidance(agent, state) {
  if (state === 'missing') return `${names[agent]} is not installed. Install: ${install[agent]}`;
  if (state === 'signed_out') return `${names[agent]} is not signed in. Run: ${signIn[agent]}`;
  return `${names[agent]} sign-in could not be checked. Run: ${agent} ${statusArgs[agent].join(' ')}`;
}
// Guidance for a not-ready agents.json entry; it never shows the entry's command text.
function entryGuidance(definition, state) {
  const who = `${names[definition.kind]} (agents.json entry ${JSON.stringify(definition.name)})`;
  if (state === 'missing') return `${who} is not installed or its command was not found. Fix the command in ~/.config/pdd/agents.json.`;
  if (state === 'signed_out') return `${who} is not signed in. Sign in with that entry's command, then run the command again.`;
  return `${who} sign-in could not be checked. Run that entry's command with ${statusArgs[definition.kind].join(' ')}.`;
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
export async function checkWorkflowAgents({ cwd = process.cwd(), env = process.env, requested } = {}, { run = runAgentProcess, load } = {}) {
  const entry = workflowAgentEntry(requested, { cwd, env }, load);
  if (!entry.ok) return entry;
  // From here on the request is the agent kind; a named entry keeps its own program and env.
  const definition = entry.definition;
  requested = entry.agent;
  const observed = { codex: 'unavailable', claude: 'unavailable', gemini: 'unavailable', agy: 'unavailable' };
  await Promise.all((requested === undefined ? agents : [requested]).map(async agent => {
    try {
      // A named entry is checked with the same program and environment that its chat starts.
      const result = await run(definition ? definition.command : agent, [...statusArgs[agent]], { cwd, env: definition ? { ...env, ...definition.env } : env, input: '', timeoutMs: 10000, maxBytes: 16384 });
      observed[agent] = agent === 'gemini' ? (result?.code === 0 && typeof result.stdout === 'string' && result.stdout.trim() ? 'ready' : 'unavailable')
        : agent === 'agy' ? agyStatus(result) : parseAgentAuthStatus({agent,result});
    } catch (error) { observed[agent] = error?.code === 'ENOENT' && error.executableMissing === true ? 'missing' : 'unavailable'; }
  }));
  let chosen = chooseWorkflowAgent({ ...observed, requested });
  if (definition) chosen = chosen.ok ? { ...chosen, name: definition.name } : refuse(entryGuidance(definition, observed[definition.kind]));
  const geminiEnv = definition ? { ...env, ...definition.env } : env;
  return chosen.agent === 'gemini' && !paidGemini.some(name => geminiEnv?.[name]) ? { ...chosen, hint: GEMINI_FREE_HINT } : chosen;
}
// `agy models` lists models only for a signed-in person (no model query); signed out it exits 1 with a sign-in line.
function agyStatus(result) {
  if (!result || !Number.isInteger(result.code) || typeof result.stdout !== 'string' || typeof result.stderr !== 'string') return 'unavailable';
  if (result.code === 0 && result.stdout.trim()) return 'ready';
  return result.code === 1 && /\bsign in\b/i.test(result.stdout + result.stderr) ? 'signed_out' : 'unavailable';
}
