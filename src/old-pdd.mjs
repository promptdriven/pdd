// Generated from prompts/cli/old-pdd.prompt.md (sha256: e75a67f2c50afd35185afecd25769afc394aebcdc123d3e731d47fc3c11201e1).
// Shared detection and replacement guidance for an older `pdd` earlier on PATH.
// This module deliberately never removes a path itself: supported Python installs
// are retired only through their owning package manager.
import {accessSync, constants, existsSync, readFileSync, realpathSync, statSync} from 'node:fs';
import {join, delimiter, dirname, relative, sep} from 'node:path';
import {execFileSync} from 'node:child_process';

const PYTHON_VERSION = /^pdd,\s+version\s+0\.0\./i;

function clean(value) { return typeof value === 'string' ? value.replace(/[\x00-\x1f\x7f-\x9f]/g, '') : ''; }
function pathIsInside(file, directory) {
  if (!file || !directory) return false;
  const rel = relative(directory, file);
  return rel === '' || (rel && rel !== '..' && !rel.startsWith(`..${sep}`) && !rel.startsWith(sep));
}
function realpath(path, fs) {
  try { return fs.realpathSync(path); } catch { return null; }
}
function executable(path, fs) {
  try { fs.accessSync(path, fs.constants.X_OK); return true; } catch { return false; }
}
function sourceForPath(path, {home, env}) {
  const lower = path.toLowerCase();
  if (lower.includes('/.local/share/uv/tools/') || lower.includes('/uv/tools/')) return 'uv';
  if (lower.includes('/pipx/venvs/') || lower.includes('/.local/pipx/')) return 'pipx';
  if (lower.includes('/conda/') || lower.includes('/miniconda') || lower.includes('/anaconda')
      || (env.CONDA_PREFIX && pathIsInside(path, realpath(env.CONDA_PREFIX, fsDefault()))) ) return 'conda';
  if (home && path === join(home, '.local', 'bin', 'pdd')) return 'r-line';
  return 'pip';
}
function fsDefault() { return {realpathSync, accessSync, constants}; }
function pythonExecutable(candidate, source, env) {
  const path = candidate.replace(/\\/g, '/');
  if (source === 'uv' || source === 'pipx' || source === 'conda') {
    const bin = dirname(candidate);
    const python = join(bin, 'python');
    if (existsSync(python)) return python;
    const python3 = join(bin, 'python3');
    if (existsSync(python3)) return python3;
  }
  if (path.includes('/bin/')) {
    const python = join(dirname(candidate), 'python');
    if (existsSync(python)) return python;
    const python3 = join(dirname(candidate), 'python3');
    if (existsSync(python3)) return python3;
  }
  return env.PYTHON ?? 'python';
}
function classify(candidate, real, {home, env, fs, runVersion}) {
  let version = '';
  try { version = String(runVersion(candidate) ?? ''); } catch { /* a script may not be runnable */ }
  let body = '';
  try { body = fs.readFileSync(real, 'utf8').slice(0, 8192); } catch { /* classification stays unknown */ }
  const python = PYTHON_VERSION.test(version) || /^#!.*\bpython(?:3)?\b/m.test(body)
    || /python.*pdd[_-]?cli|from\s+pdd[_-]?cli|pdd[_-]?cli/.test(body);
  const rLine = home && real === realpath(join(home, '.local', 'bin', 'pdd'), fs) && !python;
  if (rLine) return {kind: 'r-line', source: 'r-line', path: candidate, realpath: real, label: 'the old R-line wrapper'};
  if (python) {
    const source = sourceForPath(real, {home, env});
    const pythonPath = pythonExecutable(real, source, env);
    return {kind: 'python', source, path: candidate, realpath: real, package: 'pdd-cli', python: pythonPath,
      label: `Python pdd-cli (${source})`};
  }
  return {kind: 'unknown', source: 'unknown', path: candidate, realpath: real, label: 'an unknown pdd executable'};
}

/** Walk PATH in order and return the first pdd that precedes Alpha. */
export function findEarlierPdd(options = {}) {
  const env = options.env ?? process.env;
  const cwd = options.cwd ?? process.cwd();
  const fs = options.fs ?? {accessSync, constants, realpathSync, readFileSync};
  const home = options.home ?? env.HOME;
  const pathValue = options.path ?? env.PATH ?? '';
  const alphaPath = options.alphaPath ?? (options.packageRoot ? join(options.packageRoot, 'bin', 'pdd.mjs') : null);
  const alphaReal = alphaPath ? realpath(alphaPath, fs) : null;
  const seen = new Set();
  const runVersion = options.runVersion ?? (candidate => execFileSync(candidate, ['--version'], {
    cwd, env, encoding: 'utf8', timeout: 1500, stdio: ['ignore', 'pipe', 'ignore']
  }));
  for (const entry of pathValue.split(delimiter)) {
    const directory = entry || cwd;
    const candidate = join(directory, 'pdd');
    if (seen.has(candidate)) continue;
    seen.add(candidate);
    if (!executable(candidate, fs)) continue;
    const real = realpath(candidate, fs);
    if (!real) continue;
    if (alphaReal && real === alphaReal) return null;
    return classify(candidate, real, {home, env, fs, runVersion});
  }
  return null;
}

export function uninstallPlan(found) {
  if (!found || found.kind !== 'python') return null;
  if (found.source === 'uv') return {executable: 'uv', args: ['tool', 'uninstall', 'pdd-cli'], display: 'uv tool uninstall pdd-cli'};
  if (found.source === 'pipx') return {executable: 'pipx', args: ['uninstall', 'pdd-cli'], display: 'pipx uninstall pdd-cli'};
  return {executable: found.python || 'python', args: ['-m', 'pip', 'uninstall', '-y', 'pdd-cli'], display: `${found.python || 'python'} -m pip uninstall -y pdd-cli`};
}

export function formatConflict(found) {
  if (!found) return '';
  return `${found.label} found first on PATH: ${found.path}`;
}

/**
 * Handle setup's one possible replacement conversation. `ask` and `run` are
 * injectable so tests can prove effects without replacing package-manager rules.
 */
export async function handlePddConflict(options = {}) {
  const {stdout = process.stdout, stderr = process.stderr, alphaPath, packageRoot, env = process.env,
    home = env.HOME, cwd = process.cwd(), fs, path, isInteractive = Boolean(process.stdin?.isTTY),
    ask, run, detector = findEarlierPdd} = options;
  const found = detector({env, home, cwd, fs, path, alphaPath, packageRoot});
  if (!found) return {state: 'clear'};
  const write = (stream, message) => stream.write(`${message}\n`);
  const alpha = alphaPath ?? join(packageRoot ?? '', 'bin', 'pdd.mjs');
  if (!isInteractive) {
    write(stderr, `Another pdd is first on PATH: ${found.path}`);
    write(stderr, `To use PDD Alpha in this shell: alias pdd='${alpha}'`);
    return {state: 'kept', found};
  }
  write(stderr, formatConflict(found));
  const answer = ask ? await ask('Replace it with PDD Alpha? [y/N] ') : await askFromTTY('Replace it with PDD Alpha? [y/N] ', stdout);
  if (String(answer ?? '').trim().toLowerCase() !== 'y') {
    write(stderr, `Keeping ${found.path}. To use PDD Alpha in this shell: alias pdd='${alpha}'`);
    return {state: 'kept', found};
  }
  const plan = uninstallPlan(found);
  if (!plan) {
    write(stderr, `Cannot replace ${found.path} automatically. Do not delete it by hand.`);
    write(stderr, found.kind === 'r-line'
      ? `Run the old R-line move script for ${found.path}, then rerun pdd setup.`
      : `Identify the owner of ${found.path}, uninstall it through that owner, then rerun pdd setup.`);
    return {state: 'manual', found};
  }
  try {
    if (run) {
      const result = await run(plan.executable, plan.args, {stdio: 'inherit'});
      if (result !== undefined && result !== null && ((typeof result === 'number' && result !== 0)
        || (typeof result === 'object' && Number.isInteger(result.code) && result.code !== 0)
        || (typeof result === 'object' && Number.isInteger(result.status) && result.status !== 0))) throw Error('uninstall_failed');
    } else execFileSync(plan.executable, plan.args, {stdio: 'inherit', env});
  } catch {
    write(stderr, `Could not run ${plan.display}; no file was deleted.`);
    write(stderr, `Run ${plan.display} yourself, then rerun pdd setup.`);
    return {state: 'failed', found, plan};
  }
  const after = detector({env, home, cwd, fs, path, alphaPath, packageRoot});
  if (after) {
    write(stderr, `The earlier pdd is still first on PATH at ${after.path}; no file was deleted.`);
    return {state: 'remaining', found, after, plan};
  }
  write(stdout, 'PDD Alpha now wins on PATH.');
  return {state: 'replaced', found, plan};
}

async function askFromTTY(prompt, stdout) {
  const {createInterface} = await import('node:readline/promises');
  const terminal = createInterface({input: process.stdin, output: stdout});
  try { return await terminal.question(prompt); } finally { terminal.close(); }
}
