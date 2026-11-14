// Generated from prompts/cli/path-diagnostic.prompt.md (sha256: a0a45ff8363d4d399c28859d7d3ae0efb8f37c5296fc281b31ff2a3f9ffa1e8a).
import { spawnSync } from 'node:child_process';
import { accessSync, constants, readFileSync, realpathSync, statSync } from 'node:fs';
import { basename, delimiter, dirname, join, resolve } from 'node:path';

const quote = text => `'${text.replace(/'/g, "'\\''")}'`;
const clean = text => String(text).replace(/\x1b\[[0-?]*[ -/]*[@-~]/g, '').replace(/[\x00-\x1f\x7f]/g, ' ').replace(/\s+/g, ' ').trim().slice(0, 240);
const identity = path => { try { return realpathSync(path); } catch { return null; } };
function executable(path) {
  try { accessSync(path, constants.X_OK); return statSync(path).isFile(); } catch { return false; }
}
function candidates(cwd, env) {
  let listed;
  try {
    const reply = spawnSync('which', ['-a', 'pdd'], { cwd, env, encoding: 'utf8', timeout: 2000, maxBuffer: 65536 });
    if (!reply.error && reply.status === 0) listed = reply.stdout.split(/\r?\n/).filter(Boolean).map(path => resolve(cwd, path));
  } catch { /* A missing which still permits local PATH discovery. */ }
  listed ??= env.PATH === undefined ? [] : env.PATH.split(delimiter).map(dir => resolve(cwd, dir || '.', 'pdd'));
  return [...new Set(listed)].filter(executable);
}
function unrelatedNpmPdd(cwd, env, paths) {
  const dirs = new Set();
  for (const dir of env.PATH === undefined ? [] : env.PATH.split(delimiter)) {
    dirs.add(resolve(cwd, dir || '.', '../lib/node_modules/pdd'));
    dirs.add(resolve(cwd, dir || '.', 'node_modules/pdd'));
  }
  for (const path of paths) {
    const real = identity(path) ?? path;
    const match = /^(.*\/node_modules\/pdd)(?:\/|$)/.exec(real);
    if (match) dirs.add(match[1]);
  }
  for (const pkgDir of dirs) {
    try {
      const metadata = JSON.parse(readFileSync(join(pkgDir, 'package.json'), 'utf8'));
      if (metadata?.name === 'pdd' && !executable(join(pkgDir, 'bin/pdd.mjs'))) return pkgDir;
    } catch { /* Missing or unreadable candidate folder. */ }
  }
  return null;
}

// Only --version probes another executable; the guard prevents another copy of this pdd from probing back.
export function pathDiagnostic({ packageRoot, cwd, env, mode }) {
  if (env.PDD_PATH_PROBE === '1') return [];
  let version, running;
  try {
    version = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8')).version;
    running = resolve(packageRoot, 'bin/pdd.mjs');
    if (typeof version !== 'string' || !version || !executable(running)) return [];
  } catch { return []; }
  const paths = candidates(cwd, env), current = identity(running), selected = paths[0];
  const isAlpha = path => current !== null && identity(path) === current;
  const shadowed = selected && !isAlpha(selected);
  const foreignNpm = unrelatedNpmPdd(cwd, env, paths);
  const conflict = shadowed || paths.some(path => !isAlpha(path)) || Boolean(foreignNpm);
  if (mode === 'version' && !conflict || mode === 'workflow' && !shadowed) return [];
  let selectedVersion = `pdd ${version}`;
  if (shadowed) {
    selectedVersion = 'version unavailable';
    try {
      const reply = spawnSync(selected, ['--version'], { cwd, env: { ...env, PDD_PATH_PROBE: '1' },
        encoding: 'utf8', timeout: 2000, maxBuffer: 65536 });
      if (!reply.error && reply.status === 0 && clean(reply.stdout)) selectedVersion = clean(reply.stdout);
    } catch { /* Keep the selected path visible when its version cannot be read. */ }
  }
  const absolute = `${quote(process.execPath)} ${quote(running)}`;
  const selection = selected ? `PATH selects: ${clean(selected)} (${selectedVersion}).` : 'PATH has no executable named pdd.';
  if (mode === 'workflow') return [`${selection} Running pdd ${version}: ${clean(running)}. In workflow chats use "$PDD_BIN"; activate environments before correcting PATH.`];
  const lines = [`Running pdd ${version}: ${clean(running)}.`, ...paths.map((path, i) => `  PATH ${i + 1}: ${clean(path)}`), selection];
  if (conflict || !selected) {
    lines.push('Later environment activation (for example conda) can reorder PATH and shadow this pdd again.', `Use this pdd directly: ${absolute}`);
    const alpha = paths.find(path => basename(path) === 'pdd' && isAlpha(path));
    if (alpha) lines.push(`After environment activation, run: export PATH=${quote(dirname(alpha))}:"$PATH"; hash -r`);
  }
  if (foreignNpm) lines.push(`Found the unrelated npm package "pdd" at ${clean(foreignNpm)}. Run: npm uninstall -g pdd && npm install -g github:promptdriven/pdd`);
  return lines;
}
