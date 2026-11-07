// Generated from prompts/cli/autopilot.prompt.md (sha256: bb35ea905a8eaf2490d580b696039fa41730a1fb7c4188a2ca24debc355e6a5e).
import * as nativeFs from 'node:fs';
import { join } from 'node:path';
import { randomUUID } from 'node:crypto';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { createInterface } from 'node:readline/promises';

const execute = promisify(execFile);
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const modes = ['off', 'observe', 'auto'];
const named = value => typeof value === 'string' && value.trim().length > 0;
const unique = names => {
  const seen = new Set();
  return names.filter(name => named(name) && !seen.has(name.toLowerCase()) && seen.add(name.toLowerCase()));
};
const notice = 'The trusted list may be incomplete.';
const describe = ({ owner, writers }) => `Trusted owner: ${owner || '(unavailable)'}. Trusted write-access people: ${writers.join(', ') || '(none available)'}.`;

// All filesystem, terminal and process effects stay behind the caller's ports.
function nativeConfig(root, fs) {
  const file = join(root, 'pdd.json');
  const read = () => {
    let text;
    try { text = fs.readFileSync(file, 'utf8'); }
    catch (error) { if (error.code === 'ENOENT') return {}; throw Error('Cannot read pdd.json.'); }
    let config;
    try { config = JSON.parse(text); } catch { throw Error('Invalid JSON in pdd.json.'); }
    if (!object(config)) throw Error('pdd.json must be an object.');
    return config;
  };
  return {
    read: async () => { const config = read(); return { raw: Object.hasOwn(config, 'autopilot') ? JSON.stringify(config.autopilot) : null }; },
    save: async ({ raw }) => {
      const config = read(), temporary = join(root, `.pdd.json.${randomUUID()}.tmp`);
      config.autopilot = JSON.parse(raw);
      try {
        fs.writeFileSync(temporary, JSON.stringify(config, null, 2) + '\n', { flag: 'wx' });
        fs.renameSync(temporary, file);
      } catch { throw Error('Cannot write pdd.json; the original file is unchanged.'); }
      finally { try { fs.unlinkSync(temporary); } catch {} }
      return { raw };
    },
  };
}
function nativeTerminal(stdin, stdout) {
  const rl = createInterface({ input: stdin, output: stdout });
  const answers = rl[Symbol.asyncIterator]();
  const ask = async text => {
    rl.setPrompt(text);
    rl.prompt();
    return (await answers.next()).value ?? '';
  };
  return {
    close: () => rl.close(),
    mode: async () => ({ answer: await ask('Autopilot for this repo (off/observe/auto) [off]: ') }),
    names: async info => {
      stdout.write(`${describe(info)}${info.complete ? '' : ` ${notice}`}\n`);
      const answer = await ask('Add anyone else? GitHub names, separated by spaces (optional): ');
      return { names: answer.trim().split(/[\s,]+/).filter(Boolean) };
    },
  };
}
function nativeGithub(root, exec) {
  return { lookup: async () => {
    let owner = '', writers = [], expired = false, complete = false, child;
    const stop = () => {
      if (!child) return;
      const owned = child;
      try { owned.kill('SIGTERM'); } catch {}
      const escalation = setTimeout(() => { try { owned.kill('SIGKILL'); } catch {} }, 250);
      escalation.unref();
      owned.once('exit', () => clearTimeout(escalation));
    };
    const command = async args => {
      if (expired) throw Error('GitHub lookup timed out');
      const pending = exec('gh', args, { cwd: root, encoding: 'utf8' });
      child = pending.child;
      try { return await pending; } finally { child = undefined; }
    };
    let timer;
    const deadline = new Promise(resolve => {
      timer = setTimeout(() => { expired = true; stop(); resolve(); }, 5000);
    });
    const work = (async () => {
      try {
        const repo = JSON.parse((await command(['repo', 'view', '--json', 'nameWithOwner,owner'])).stdout);
        if (expired) return;
        owner = repo.owner?.login ?? '';
        const pages = JSON.parse((await command(['api', `repos/${repo.nameWithOwner}/collaborators`, '--paginate', '--slurp'])).stdout);
        if (expired) return;
        writers = unique(pages.flat().filter(person => person.permissions?.push || person.permissions?.maintain || person.permissions?.admin).map(person => person.login));
        complete = !!owner;
      } catch { /* Keep the people confirmed before the failure. */ }
    })();
    await Promise.race([work, deadline]);
    clearTimeout(timer);
    return { owner, writers, complete: !expired && complete };
  } };
}

export async function runAutopilot(input, ports = {}) {
  let mode = 'off', trust = [], warnings = [];
  const result = (exitCode, message, trusted = false) => ({ mode, trust, trusted, message: [...warnings, message].filter(Boolean).join('\n'), exitCode });
  const { action, names, author } = input;
  if (!['setup', 'mode', 'trust', 'untrust', 'isTrusted'].includes(action)
    || action === 'mode' && !modes.includes(input.mode)
    || ['trust', 'untrust'].includes(action) && (!Array.isArray(names) || !names.length || names.some(name => !named(name)) || action === 'untrust' && names.length !== 1)
    || action === 'isTrusted' && !named(author)) return result(2, 'Invalid Autopilot arguments. Use pdd autopilot --help.');
  if (action === 'setup' && !input.inRepo) return result(0, '');
  try {
    const cwd = ports.cwd ?? process.cwd(), exec = ports.execFile ?? execute;
    let root = cwd;
    if (!ports.config) {
      // Git translates its messages; read the "not a git repository" text in the C locale.
      try { root = String((await exec('git', ['rev-parse', '--show-toplevel'], { cwd, encoding: 'utf8', env: { ...process.env, LC_ALL: 'C', LANG: 'C' } })).stdout).trim(); }
      catch (error) {
        if (action === 'setup') return result(0, '');
        return result(1, /not a git repository/i.test(String(error?.stderr ?? ''))
          ? 'This folder is not a Git repository. cd into the repo you want Autopilot to work on, then run the command again.'
          : 'Autopilot settings could not read the Git repository; retry.');
      }
    }
    const config = ports.config ?? nativeConfig(root, ports.fs ?? nativeFs);
    const { raw } = await config.read({ key: 'autopilot' });
    const saved = raw === null ? undefined : JSON.parse(raw), setting = object(saved) ? saved : {};
    mode = modes.includes(setting.mode) ? setting.mode : 'off';
    trust = unique(Array.isArray(setting.trust) ? setting.trust : []);
    const invalid = raw !== null && (!object(saved) || Object.hasOwn(setting, 'mode') && !modes.includes(setting.mode));
    if (invalid) warnings.push(`Saved Autopilot mode ${JSON.stringify(object(saved) ? setting.mode : saved)} is invalid; ${action === 'mode' ? 'treating it as off.' : 'using off and leaving it unchanged.'}`);
    if (['trust', 'untrust'].includes(action) && raw !== null && !object(saved)) {
      return result(0, 'Autopilot saved value is unchanged; use pdd autopilot off, observe or auto to replace it.');
    }
    const save = async value => config.save({ key: 'autopilot', raw: JSON.stringify(value) });
    const lookup = async () => {
      try { return await (ports.github ?? nativeGithub(root, exec)).lookup({}); }
      catch { return { owner: '', writers: [], complete: false }; }
    };
    if (action === 'setup') {
      if (!input.interactive || !input.inRepo) return result(0, `Autopilot: ${mode}.`);
      const terminal = ports.terminal ?? nativeTerminal(ports.stdin ?? process.stdin, ports.stdout ?? process.stdout);
      try {
        if (raw === null) {
          const { answer } = await terminal.mode({});
          mode = answer.trim() || 'off';
          if (!modes.includes(mode)) return result(2, 'Invalid Autopilot mode. Choose off, observe or auto.');
        }
        const info = await lookup();
        if (!info.complete || !info.owner && !info.writers.length) warnings.push(notice);
        const additions = (await terminal.names(info)).names;
        const nextTrust = unique([...trust, ...additions]);
        if (raw === null || additions.length) {
          // Preserve an existing invalid mode verbatim until a mode command replaces it.
          const next = raw === null ? { mode, trust: nextTrust } : { ...setting, trust: nextTrust };
          if (!object(saved) && raw !== null) return result(0, `${describe(info)} Autopilot: ${mode}; saved value unchanged.`);
          await save(next); trust = nextTrust;
        }
        return result(0, `${describe(info)} Autopilot: ${mode}. Explicit trust: ${trust.join(', ') || '(none)'}.`);
      } finally { if (!ports.terminal) terminal.close(); }
    }
    if (action === 'isTrusted') {
      const info = await lookup();
      if (!info.complete || !info.owner && !info.writers.length) warnings.push(notice);
      const trusted = [info.owner, ...info.writers, ...trust].filter(named).some(name => name.toLowerCase() === author.toLowerCase());
      return result(0, `${author} is ${trusted ? 'trusted' : 'not trusted'}.`, trusted);
    }
    const next = { ...setting, mode: Object.hasOwn(setting, 'mode') ? setting.mode : mode, trust };
    if (action === 'mode') next.mode = input.mode;
    else if (action === 'trust') next.trust = unique([...trust, ...names]);
    else next.trust = trust.filter(name => name.toLowerCase() !== names[0].toLowerCase());
    await save(next);
    mode = modes.includes(next.mode) ? next.mode : 'off'; trust = next.trust;
    return result(0, `Autopilot: ${mode}. Explicit trust: ${trust.join(', ') || '(none)'}.`);
  } catch (error) {
    return result(1, `Autopilot settings failed: ${error.message}`);
  }
}
