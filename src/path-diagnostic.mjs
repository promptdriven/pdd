// Generated from prompts/cli/path-diagnostic.prompt.md (sha256: 68313e4b676ff838b09af1845d07ee14048108cf2a9a1d3ca347eb546cff23f1).
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

// Only --version probes another executable; the guard prevents another Alpha from probing back.
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
  const conflict = shadowed || paths.some(path => !isAlpha(path));
  if (mode === 'version' && !conflict || mode === 'workflow' && !shadowed) return [];
  let selectedVersion = `PDD Alpha ${version}`;
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
  if (mode === 'workflow') return [`${selection} Running PDD Alpha ${version}: ${clean(running)}. Use ${absolute}; activate environments before correcting PATH.`];
  const lines = [`Running PDD Alpha ${version}: ${clean(running)}.`, ...paths.map((path, i) => `  PATH ${i + 1}: ${clean(path)}`), selection];
  if (conflict || !selected) {
    lines.push('Later environment activation (for example conda) can reorder PATH and shadow Alpha again.', `Use Alpha directly: ${absolute}`);
    const alpha = paths.find(path => basename(path) === 'pdd' && isAlpha(path));
    if (alpha) lines.push(`After environment activation, run: export PATH=${quote(dirname(alpha))}:"$PATH"; hash -r`);
  }
  return lines;
}
