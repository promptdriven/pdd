// Prompt: prompts/cli/agent-mcp-setup.prompt.md
import { accessSync, constants, existsSync, lstatSync, readFileSync } from 'node:fs';
import { dirname, delimiter, join, resolve } from 'node:path';
import { homedir } from 'node:os';
import { fileURLToPath } from 'node:url';
import { createInterface } from 'node:readline';
import { writeAtomicPrivate } from './shared/atomic-fs.mjs';
import { parse } from './shared/toml/parse.js';

const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const same = (actual, wanted) => object(actual) && Object.entries(wanted).every(([key, value]) => JSON.stringify(actual[key]) === JSON.stringify(value));

function displayPath(filePath, home) {
  if (!home || !filePath) return filePath;
  const normHome = resolve(home).replace(/[\\/]+$/, '');
  if (!normHome) return filePath;
  const normFile = resolve(filePath);
  if (normFile === normHome) return '~';
  if (normFile.startsWith(`${normHome}/`) || normFile.startsWith(`${normHome}\\`)) {
    return `~${normFile.slice(normHome.length)}`;
  }
  return filePath;
}

// Recognize a previously registered PDD MCP server (e.g. pointing to an older Node or package path)
// so setup updates stale entries cleanly instead of failing on upgrades.
function isStalePddEntry(entry) {
  if (!object(entry)) return false;
  const cmd = typeof entry.command === 'string' ? entry.command : '';
  const args = Array.isArray(entry.args) ? entry.args.map(String) : [];
  if (/(?:^|[\\/])pdd(?:\.mjs)?$/i.test(cmd) && args.includes('mcp')) return true;
  return args.includes('mcp') && args.some(arg => /(?:^|[\\/])pdd(?:\.mjs)?$/i.test(arg));
}

// Scope symlink checks strictly to the target config file and its agent config directory
// (stopping before $HOME / OS mount ancestors like macOS /var).
function safePath(file, boundaryDir) {
  const target = resolve(file);
  const stopAt = resolve(boundaryDir);
  let current = target;
  while (true) {
    try {
      const stat = lstatSync(current);
      if (stat.isSymbolicLink()) {
        throw Object.assign(
          new Error(`${current} is a symlink; register PDD manually or use a regular config path.`),
          { code: 'PDD_MCP_SYMLINK' },
        );
      }
      if (current === target && !stat.isFile()) {
        throw new Error(`${file} is not a regular file.`);
      }
    } catch (error) {
      if (error.code !== 'ENOENT') throw error;
    }
    if (current === stopAt) break;
    const parent = dirname(current);
    if (parent === current) break;
    current = parent;
  }
}

function executable(name, env) {
  return (env.PATH ?? '').split(delimiter).filter(Boolean).some(folder => {
    try {
      const full = join(folder, name);
      accessSync(full, constants.X_OK);
      const st = lstatSync(full);
      return st.isFile() || st.isSymbolicLink();
    } catch { return false; }
  });
}

const read = file => {
  try { return readFileSync(file, 'utf8'); }
  catch (error) { if (error.code === 'ENOENT') return null; throw error; }
};

function existingMode(file) {
  try {
    const mode = lstatSync(file).mode & 0o777;
    return mode || 0o600;
  } catch { return 0o600; }
}

const PDD_TOML_KEYS = /^\s*(?:command|args|default_tools_approval_mode|tool_timeout_sec)\s*=/;

function replaceTomlPddSection(before, wantedBlock) {
  const lines = before.split(/\r?\n/);
  const start = lines.findIndex(line => /^\s*\[mcp_servers\.pdd\]\s*(?:#.*)?$/.test(line));
  if (start < 0) return null;
  let end = lines.length;
  for (let i = start + 1; i < lines.length; i++) {
    if (/^\s*\[/.test(lines[i])) { end = i; break; }
  }
  const beforePart = lines.slice(0, start);
  const afterPart = lines.slice(end);
  const preservedExtras = lines.slice(start + 1, end).filter(line => line.trim() && !PDD_TOML_KEYS.test(line));
  const blockLines = [...wantedBlock.trimEnd().split('\n'), ...preservedExtras];
  const merged = [
    ...beforePart,
    ...blockLines,
    ...(afterPart.length && afterPart[0] !== '' ? [''] : []),
    ...afterPart,
  ].join('\n');
  return merged.endsWith('\n') ? merged : `${merged}\n`;
}

function planConfig({ name, file, boundary, wanted, toml, upgradeOnly = false }) {
  if (upgradeOnly) {
    let st;
    try { st = lstatSync(file); }
    catch (error) { if (error.code === 'ENOENT' || error.code === 'ENOTDIR') return null; throw error; }
    if (st.isSymbolicLink() || !st.isFile()) return null;
  }
  safePath(file, boundary);
  const before = read(file);
  let data;
  const jsonText = before ? before.replace(/^\uFEFF/, '') : '';
  try { data = toml ? parse(before ?? '') : (jsonText.trim() ? JSON.parse(jsonText) : {}); }
  catch {
    if (upgradeOnly && !/\bpdd\b/i.test(before ?? '')) return null;
    throw new Error(`${file} contains malformed ${toml ? 'TOML' : 'JSON'}; fix it before running pdd setup again.`);
  }
  if (!object(data)) {
    if (upgradeOnly) return null;
    throw new Error(`${file} must contain an object.`);
  }
  const key = toml ? 'mcp_servers' : 'mcpServers';
  if (data[key] !== undefined && !object(data[key])) {
    if (upgradeOnly) return null;
    throw new Error(`${file}: ${key} must be an object.`);
  }
  const existing = data[key]?.pdd;
  let updating = false;
  if (existing !== undefined) {
    if (same(existing, wanted)) return null;
    if (!isStalePddEntry(existing)) {
      if (upgradeOnly) return null;
      throw new Error(`${file} already has a different pdd MCP server; resolve that entry manually before running pdd setup again.`);
    }
    updating = true;
  } else if (upgradeOnly) {
    return null;
  }

  let after, preview;
  if (toml) {
    const addition = `[mcp_servers.pdd]\ncommand = ${JSON.stringify(wanted.command)}\nargs = ${JSON.stringify(wanted.args)}\ndefault_tools_approval_mode = "approve"\ntool_timeout_sec = 600\n`;
    if (updating) {
      after = replaceTomlPddSection(before ?? '', addition);
      if (!after) {
        throw new Error(`${file}: cannot safely update inline [mcp_servers.pdd] in this TOML layout; update it manually.`);
      }
      preview = `Update [mcp_servers.pdd] to:\n${addition}`;
    } else {
      const separator = before ? (before.endsWith('\n') ? '\n' : '\n\n') : '';
      after = `${before ?? ''}${separator}${addition}`;
      preview = `Append exactly:\n${separator}${addition}`;
    }
    try {
      const result = parse(after);
      if (!same(result.mcp_servers?.pdd, wanted)) throw new Error('mismatch');
    } catch {
      throw new Error(`${file}: cannot safely ${updating ? 'update' : 'append'} the pdd table in this TOML layout; register it manually.`);
    }
  } else {
    data[key] ??= {};
    const mergedEntry = updating ? { ...existing, ...wanted } : wanted;
    data[key].pdd = mergedEntry;
    after = `${JSON.stringify(data, null, 2)}\n`;
    preview = `${updating ? 'Update' : 'Add'} /mcpServers/pdd = ${JSON.stringify(mergedEntry, null, 2)}\nPreserve other values; format this JSON file with two-space indentation and a final newline.`;
  }
  return { name, file, boundary, before, after, preview, updating };
}

export async function setupAgentMcp(
  { env = process.env, packageRoot = fileURLToPath(new URL('..', import.meta.url)) } = {},
  {
    stdin = process.stdin,
    stdout = process.stdout,
    stderr = process.stderr,
    confirm,
    interactive = Boolean(confirm) || Boolean(stdin.isTTY && stdout.isTTY),
    yes = false,
    upgradeOnly = false,
  } = {},
) {
  const say = value => stdout.write(`${value}\n`);
  const home = env.HOME || homedir();
  const command = process.execPath;
  const args = [resolve(packageRoot, 'bin/pdd.mjs'), 'mcp'];
  const codex = env.CODEX_HOME ? resolve(env.CODEX_HOME) : join(home, '.codex');
  const claudeDir = env.CLAUDE_CONFIG_DIR ? resolve(env.CLAUDE_CONFIG_DIR) : join(home, '.claude');
  const claudeFile = env.CLAUDE_CONFIG_DIR ? join(claudeDir, '.claude.json') : join(home, '.claude.json');
  const geminiFile = join(home, '.gemini/settings.json');
  const agyDir = join(home, '.gemini/config');
  const agyFile = join(agyDir, 'mcp_config.json');

  const candidates = [
    {
      name: 'Codex',
      file: join(codex, 'config.toml'),
      boundary: codex,
      toml: true,
      detected: existsSync(codex) || existsSync(join(codex, 'config.toml')) || executable('codex', env),
      wanted: { command, args, default_tools_approval_mode: 'approve', tool_timeout_sec: 600 },
    },
    {
      name: 'Claude Code',
      file: claudeFile,
      boundary: env.CLAUDE_CONFIG_DIR ? claudeDir : claudeFile,
      detected: existsSync(claudeDir) || existsSync(claudeFile) || executable('claude', env),
      wanted: { type: 'stdio', command, args },
    },
    {
      name: 'Gemini',
      file: geminiFile,
      boundary: join(home, '.gemini'),
      // Bare ~/.gemini/ is also created by Antigravity; require Gemini CLI's own settings.json or binary.
      detected: existsSync(geminiFile) || executable('gemini', env),
      wanted: { command, args, trust: true, timeout: 600000 },
    },
    {
      name: 'Antigravity',
      file: agyFile,
      boundary: agyDir,
      // Never detect Antigravity solely from ~/.gemini/config (which skills or other Gemini tools may create).
      detected: existsSync(agyFile) || existsSync(join(home, '.gemini/antigravity-cli')) || executable('agy', env),
      wanted: { command, args },
    },
  ].filter(item => item.detected);

  // Isolate per-agent planning errors and symlinks so one broken agent config never blocks healthy agents.
  const changes = [];
  let hadError = false;
  for (const candidate of candidates) {
    try {
      const planned = planConfig({ ...candidate, upgradeOnly });
      if (planned) changes.push(planned);
    } catch (error) {
      const warning = error.code === 'PDD_MCP_SYMLINK';
      stderr.write(`pdd setup: ${warning ? 'warning: ' : ''}${String(error.message).split(/[\r\n]/)[0]}\n`);
      if (!warning) hadError = true;
    }
  }

  if (!changes.length) {
    if (!hadError && !upgradeOnly) {
      say(candidates.length
        ? 'PDD MCP tools already registered. No config change.'
        : 'No Codex, Claude Code, Gemini or Antigravity installation found. No config change.');
    }
    return hadError ? 1 : 0;
  }

  if (!upgradeOnly) {
    const padWidth = Math.max(14, ...changes.map(change => change.name.length + 2));
    say('MCP tools to register (pdd mcp):');
    for (const change of changes) {
      const suffix = change.updating ? ' (update)' : '';
      say(`  • ${change.name.padEnd(padWidth)}${displayPath(change.file, home)}${suffix}`);
    }

    if (!yes) {
      if (!interactive) {
        say('PDD MCP registration skipped. No config change.');
        return hadError ? 1 : 0;
      }
      const targetLabel = changes.length === 1 ? 'this 1 config' : `these ${changes.length} configs`;
      const showDetails = () => {
        stdout.write('\n');
        for (const change of changes) say(`${change.name}: ${change.file}\n${change.preview}`);
        say('Only the PDD server is approved to run on your intent. Claude Code keeps its normal tool approval controls.');
      };
      let consented = false;
      let detailsShown = false;
      const rl = !confirm && stdin.isTTY && stdout.isTTY ? createInterface({ input: stdin, output: stdout }) : null;
      const queuedLines = [];
      let pendingResolve = null;
      let rlClosed = false;
      if (rl) {
        rl.on('line', value => {
          if (pendingResolve) {
            const done = pendingResolve;
            pendingResolve = null;
            done(value);
          } else {
            queuedLines.push(value);
          }
        });
        rl.once('SIGINT', () => rl.close());
        rl.once('close', () => {
          rlClosed = true;
          if (pendingResolve) {
            const done = pendingResolve;
            pendingResolve = null;
            done(undefined);
          }
        });
      }
      const ask = async question => {
        if (confirm) {
          stdout.write(question);
          return confirm(question);
        }
        if (!rl) return undefined;
        stdout.write(question);
        if (queuedLines.length > 0) return queuedLines.shift();
        if (rlClosed) return undefined;
        return new Promise(resolveAnswer => {
          pendingResolve = resolveAnswer;
        });
      };
      try {
        stdout.write('\n');
        for (let turn = 0; turn < 16; turn++) {
          const question = detailsShown
            ? `Register PDD MCP tools in ${targetLabel}? [y/N] `
            : `Register PDD MCP tools in ${targetLabel}? [y/N/d] `;
          const answer = await ask(question);
          const normalized = typeof answer === 'string' ? answer.trim().toLowerCase() : '';
          if (normalized === 'd' || normalized === 'details') {
            showDetails();
            detailsShown = true;
            stdout.write('\n');
            continue;
          }
          consented = normalized === 'y';
          break;
        }
      } finally {
        rl?.close();
      }
      if (!consented) {
        say('PDD MCP registration skipped. No config change.');
        return hadError ? 1 : 0;
      }
    }
  }

  for (const change of changes) {
    try {
      safePath(change.file, change.boundary);
      if (read(change.file) !== change.before) {
        throw new Error(`${change.file} changed after the preview; run pdd setup again. No config changes applied.`);
      }
    } catch (error) {
      const warning = error.code === 'PDD_MCP_SYMLINK';
      stderr.write(`pdd setup: ${warning ? 'warning: ' : ''}${String(error.message).split(/[\r\n]/)[0]}\n`);
      if (!warning) return 1;
      return hadError ? 1 : 0;
    }
  }

  for (const change of changes) {
    try {
      safePath(change.file, change.boundary);
      const mode = change.before === null ? 0o600 : existingMode(change.file);
      writeAtomicPrivate(null, change.file, change.after, 0o700, mode);
      say(`${change.updating ? 'Updated' : 'Registered'} PDD MCP tools for ${change.name} in ${displayPath(change.file, home)}.`);
    } catch (error) {
      const warning = error.code === 'PDD_MCP_SYMLINK';
      stderr.write(`pdd setup: ${warning ? 'warning: ' : ''}${String(error.message).split(/[\r\n]/)[0]}\n`);
      if (!warning) hadError = true;
    }
  }

  return hadError ? 1 : 0;
}
