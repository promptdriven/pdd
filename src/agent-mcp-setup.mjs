// Generated from prompts/cli/agent-mcp-setup.prompt.md (sha256: d500ed09a2bd77ffa58681b233bf1ab062df7a3e5e071899389712a1798b6dfb).
import { accessSync, constants, existsSync, lstatSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname, delimiter, join, resolve } from 'node:path';
import { homedir } from 'node:os';
import { fileURLToPath } from 'node:url';
import { createInterface } from 'node:readline';
import { parse } from './vendor/smol-toml/parse.js';

const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const same = (actual, wanted) => object(actual) && Object.entries(wanted).every(([key, value]) => JSON.stringify(actual[key]) === JSON.stringify(value));
function safePath(file) {
  let current = resolve(file);
  while (true) {
    try {
      const stat = lstatSync(current);
      if (stat.isSymbolicLink()) throw Error(`${current} is a symlink; register PDD manually or use a regular config path.`);
      if (current === resolve(file) && !stat.isFile()) throw Error(`${file} is not a regular file.`);
    } catch (error) { if (error.code !== 'ENOENT') throw error; }
    const parent = dirname(current); if (parent === current) break; current = parent;
  }
}
function executable(name, env) {
  return (env.PATH ?? '').split(delimiter).filter(Boolean).some(folder => {
    try { accessSync(join(folder, name), constants.X_OK); return lstatSync(join(folder, name)).isFile() || lstatSync(join(folder, name)).isSymbolicLink(); } catch { return false; }
  });
}
const read = file => { try { return readFileSync(file, 'utf8'); } catch (error) { if (error.code === 'ENOENT') return null; throw error; } };
function planConfig({ name, file, wanted, toml }) {
  safePath(file);
  const before = read(file);
  let data;
  try { data = toml ? parse(before ?? '') : JSON.parse(before ?? '{}'); }
  catch { throw Error(`${file} contains malformed ${toml ? 'TOML' : 'JSON'}; fix it before running pdd setup again.`); }
  if (!object(data)) throw Error(`${file} must contain an object.`);
  const key = toml ? 'mcp_servers' : 'mcpServers';
  if (data[key] !== undefined && !object(data[key])) throw Error(`${file}: ${key} must be an object.`);
  if (data[key]?.pdd !== undefined) {
    if (same(data[key].pdd, wanted)) return null;
    throw Error(`${file} already has a different pdd MCP server; resolve that entry manually before running pdd setup again.`);
  }
  let after, preview;
  if (toml) {
    const addition = `[mcp_servers.pdd]\ncommand = ${JSON.stringify(wanted.command)}\nargs = ${JSON.stringify(wanted.args)}\ndefault_tools_approval_mode = "approve"\ntool_timeout_sec = 600\n`;
    const separator = before ? (before.endsWith('\n') ? '\n' : '\n\n') : '';
    after = `${before ?? ''}${separator}${addition}`;
    try { const result = parse(after); if (!same(result.mcp_servers?.pdd, wanted)) throw Error(); }
    catch { throw Error(`${file}: cannot safely append the pdd table to this TOML layout; register it manually.`); }
    preview = `Append exactly:\n${separator}${addition}`;
  } else {
    data[key] ??= {}; data[key].pdd = wanted;
    after = `${JSON.stringify(data, null, 2)}\n`;
    preview = `Add /mcpServers/pdd = ${JSON.stringify(wanted, null, 2)}\nPreserve other values; format this JSON file with two-space indentation and a final newline.`;
  }
  return { name, file, before, after, preview };
}
export async function setupAgentMcp({ env = process.env, packageRoot = fileURLToPath(new URL('..', import.meta.url)) } = {}, { stdin = process.stdin, stdout = process.stdout, stderr = process.stderr, confirm } = {}) {
  const say = value => stdout.write(`${value}\n`);
  try {
    const home = env.HOME || homedir();
    const command = process.execPath, args = [resolve(packageRoot, 'bin/pdd.mjs'), 'mcp'];
    const codex = env.CODEX_HOME ? resolve(env.CODEX_HOME) : join(home, '.codex');
    const claude = env.CLAUDE_CONFIG_DIR ? resolve(env.CLAUDE_CONFIG_DIR) : join(home, '.claude');
    const candidates = [
      { name: 'Codex', detect: 'codex', home: codex, file: join(codex, 'config.toml'), toml: true,
        wanted: { command, args, default_tools_approval_mode: 'approve', tool_timeout_sec: 600 } },
      { name: 'Claude Code', detect: 'claude', home: claude, file: env.CLAUDE_CONFIG_DIR ? join(claude, '.claude.json') : join(home, '.claude.json'),
        wanted: { type: 'stdio', command, args } },
      { name: 'Gemini', detect: 'gemini', home: join(home, '.gemini'), file: join(home, '.gemini/settings.json'),
        wanted: { command, args, trust: true, timeout: 600000 } },
    ].filter(item => existsSync(item.home) || existsSync(item.file) || executable(item.detect, env));
    const changes = candidates.map(planConfig).filter(Boolean);
    if (!changes.length) { say(candidates.length ? 'PDD Try tools already registered. No config change.' : 'No Codex, Claude Code or Gemini installation found. No config change.'); return 0; }
    for (const change of changes) say(`${change.name}: ${change.file}\n${change.preview}`);
    say('Only the PDD server is approved to run on your intent. Runs use the Try call budget and appear on its page. Claude Code keeps its normal tool approval controls.');
    const question = 'Register these PDD Try tools? [y/N] ';
    let answer;
    if (confirm) { stdout.write(question); answer = await confirm(question); }
    else if (stdin.isTTY && stdout.isTTY) {
      const rl = createInterface({ input: stdin, output: stdout });
      try {
        answer = await new Promise(resolveAnswer => {
          rl.once('close', () => resolveAnswer(undefined));
          rl.question(question, resolveAnswer);
        });
      } finally { rl.close(); }
    }
    if (typeof answer !== 'string' || answer.trim().toLowerCase() !== 'y') { say('PDD MCP registration skipped. No config change.'); return 0; }
    for (const change of changes) {
      safePath(change.file);
      if (read(change.file) !== change.before) throw Error(`${change.file} changed after the preview; run pdd setup again. No config changes applied.`);
    }
    for (const change of changes) {
      mkdirSync(dirname(change.file), { recursive: true, mode: 0o700 });
      safePath(change.file);
      writeFileSync(change.file, change.after, { mode: 0o600, flag: change.before === null ? 'wx' : 'w' });
      say(`Registered PDD Try tools for ${change.name} in ${change.file}.`);
    }
    return 0;
  } catch (error) { stderr.write(`pdd setup: ${String(error.message).split(/[\r\n]/)[0]}\n`); return 1; }
}
