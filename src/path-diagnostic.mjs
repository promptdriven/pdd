// Generated from prompts/cli/path-diagnostic.prompt.md (sha256: 51b668d5f529984645e99c672f8a925283c8919c866aa256d7b1a8279b8e19df).
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

// npm does not reliably keep GitHub provenance; show distribution advice by package identity.
export function packageInstallDiagnostic({ packageRoot }, ports = {}) {
  const read = path => {
    try { return JSON.parse((ports.files?.readFileSync ?? readFileSync)(path, 'utf8')); }
    catch { return null; }
  };
  const name = read(join(packageRoot, 'package.json'))?.name;
  const scoped = name === '@promptdriven/pdd';
  const installedScope = basename(packageRoot) === 'pdd' && basename(dirname(packageRoot)) === '@promptdriven'
    && basename(dirname(dirname(packageRoot))) === 'node_modules';
  const legacy = name === 'pdd' || scoped && installedScope
    && read(join(dirname(dirname(packageRoot)), 'pdd', 'package.json'))?.name === 'pdd';
  if (legacy) return {
    kind: 'legacy',
    detail: 'The old npm package name pdd can be replaced by an unrelated package with npm update -g. Both package names can compete for the pdd command. Remove the old name before installing the scoped package.',
    fix: 'npm uninstall -g pdd && npm install -g github:promptdriven/pdd'
  };
  if (scoped) return {
    kind: 'github',
    detail: 'pdd is distributed from GitHub. Until @promptdriven/pdd is published, do not use npm update -g for pdd.',
    fix: 'npm install -g github:promptdriven/pdd'
  };
  return { kind: 'none', detail: '', fix: '' };
}

// Only --version probes another executable; the guard prevents another copy of this pdd from probing back.
export function pathDiagnostic({ packageRoot, cwd, env, mode }) {
  if (env.PDD_PATH_PROBE === '1') return [];
  const update = mode === 'setup' ? packageInstallDiagnostic({ packageRoot }) : null;
  const updateLines = update && update.kind !== 'none' ? [`${update.detail} Update with: ${update.fix}`] : [];
  let version, running;
  try {
    version = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8')).version;
    running = resolve(packageRoot, 'bin/pdd.mjs');
    if (typeof version !== 'string' || !version || !executable(running)) return updateLines;
  } catch { return updateLines; }
  const paths = candidates(cwd, env), current = identity(running), selected = paths[0];
  const isAlpha = path => current !== null && identity(path) === current;
  const shadowed = selected && !isAlpha(selected);
  const conflict = shadowed || paths.some(path => !isAlpha(path));
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
  return [...lines, ...updateLines];
}
