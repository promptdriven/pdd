// Prompt: prompts/cli/status.prompt.md
import { spawnSync } from 'node:child_process';
import { existsSync, lstatSync, realpathSync, statSync } from 'node:fs';
import { dirname, isAbsolute, join, relative, resolve, sep } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { findOwners } from '../file-owner.mjs';
import { runtimePreflightSlice } from '../runtime-seam.mjs';
import { gitFiles, resolveRepoRoot } from '../shared/git-context.mjs';
import { readBoundedUtf8 } from '../shared/safe-read.mjs';

const HERE = dirname(fileURLToPath(import.meta.url));
const START = '<!-- pdd:start -->';
const END = '<!-- pdd:end -->';

const canonicalPath = value => typeof value === 'string' && value.trim().length > 0 && value.length <= 1000 && !isAbsolute(value)
  && !/[\\\x00-\x1f\x7f]/.test(value) && !value.split('/').some(part => !part || part === '.' || part === '..' || part.toLowerCase() === '.git');

function globToRegExp(pattern) {
  let re = '^';
  const text = String(pattern ?? '').replace(/\\/g, '/');
  for (let i = 0; i < text.length; i++) {
    const ch = text[i];
    if (ch === '*' && text[i + 1] === '*') {
      if (text[i + 2] === '/') { re += '(?:.*/)?'; i += 2; }
      else { re += '.*'; i += 1; }
    } else if (ch === '*') re += '[^/]*';
    else if (ch === '?') re += '[^/]';
    else if (/[.+^${}()|[\]\\]/.test(ch)) re += `\\${ch}`;
    else re += ch;
  }
  return new RegExp(`${re}$`);
}

function matchVerifyPaths(paths, verifyPaths) {
  if (!paths.length || !verifyPaths.length) return [];
  return verifyPaths.filter(entry => {
    const globs = Array.isArray(entry.when) ? entry.when : [];
    return globs.some(glob => {
      const re = globToRegExp(glob);
      return paths.some(file => re.test(file));
    });
  });
}

function readInstructionBlockState(root) {
  const realRoot = (() => { try { return realpathSync(root); } catch { return resolve(root); } })();
  for (const name of ['CLAUDE.md', 'AGENTS.md']) {
    const full = join(root, name);
    let st;
    try { st = lstatSync(full); } catch { continue; }
    let target = full;
    if (st.isSymbolicLink()) {
      try {
        const resolved = realpathSync(full);
        const rel = relative(realRoot, resolved);
        if (!rel || rel.startsWith('..') || isAbsolute(rel) || !statSync(resolved).isFile()) return { instruction_file: name, has_pdd_block: false };
        target = resolved;
      } catch { return { instruction_file: name, has_pdd_block: false }; }
    }
    try {
      const lines = readBoundedUtf8(target, { maxBytes: 256 * 1024, noFollow: true }).split(/\r?\n/);
      return { instruction_file: name, has_pdd_block: lines.includes(START) && lines.includes(END) };
    } catch { return { instruction_file: name, has_pdd_block: false }; }
  }
  return { instruction_file: null, has_pdd_block: false };
}

function readFeatureMap(root) {
  const file = join(root, 'pdd.json');
  if (!existsSync(file)) return { test: null, paths: [] };
  try {
    const cfg = JSON.parse(readBoundedUtf8(file, { maxBytes: 256 * 1024, noFollow: true }));
    const verify = cfg && typeof cfg === 'object' && !Array.isArray(cfg) ? cfg.verify : null;
    if (!verify || typeof verify !== 'object' || Array.isArray(verify)) return { test: null, paths: [] };
    const test = typeof verify.test === 'string' && verify.test.trim() ? verify.test.trim() : null;
    const rawPaths = Array.isArray(verify.paths) ? verify.paths : [];
    const paths = rawPaths
      .filter(item => item && typeof item === 'object' && typeof item.id === 'string' && item.id.trim())
      .map(item => ({
        id: item.id.trim(),
        name: typeof item.name === 'string' && item.name.trim() ? item.name.trim() : item.id.trim(),
        when: Array.isArray(item.when) ? item.when.filter(w => typeof w === 'string' && w.trim()) : [],
        run: typeof item.run === 'string' ? item.run.trim() : '',
        needs: Array.isArray(item.needs) ? item.needs.filter(n => typeof n === 'string' && n.trim()) : [],
      }));
    return { test, paths };
  } catch {
    return { test: null, paths: [] };
  }
}

async function detectChangedFiles(root, ports = {}) {
  const changedMapPath = join(HERE, 'changed-map.mjs');
  if (existsSync(changedMapPath)) {
    try {
      const mod = await import(pathToFileURL(changedMapPath).href);
      if (typeof mod.analyzeChangedMap === 'function') {
        const res = mod.analyzeChangedMap({ cwd: root }, ports);
        if (res?.ok && res.report) {
          const scoped = (res.report.scope?.files ?? []).filter(canonicalPath);
          if (scoped.length) return [...new Set(scoped)].sort();
        }
      }
      const fn = mod.mapChangedFiles ?? mod.inspectChangedMap ?? mod.default;
      if (typeof fn === 'function') {
        const res = await fn({ root }, ports);
        if (Array.isArray(res?.changed)) return [...new Set(res.changed.filter(canonicalPath))].sort();
        if (Array.isArray(res?.files)) return [...new Set(res.files.map(f => (typeof f === 'string' ? f : f?.path)).filter(canonicalPath))].sort();
      }
    } catch { /* Fall back cleanly to git status when optional changed-map fails. */ }
  }
  const found = new Set();
  const status = spawnSync('git', ['status', '--porcelain', '-z', '--untracked-files=all'], { cwd: root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] });
  if (status.status === 0 && status.stdout) {
    const tokens = status.stdout.split('\0').filter(Boolean);
    for (let i = 0; i < tokens.length; i++) {
      const entry = tokens[i];
      if (entry.length < 4) continue;
      const code = entry.slice(0, 2);
      const path = entry.slice(3);
      if (canonicalPath(path)) found.add(path);
      if ((code[0] === 'R' || code[0] === 'C') && tokens[i + 1]) i++;
    }
  }
  const diff = spawnSync('git', ['diff', '--name-only', '-z', 'HEAD'], { cwd: root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] });
  if (diff.status === 0 && diff.stdout) {
    for (const path of diff.stdout.split('\0').filter(Boolean)) if (canonicalPath(path)) found.add(path);
  }
  return [...found].sort();
}

export async function inspectStatus({ cwd = process.cwd(), paths = [], changed = false } = {}, ports = {}) {
  const root = await (ports.resolveRepoRoot ?? resolveRepoRoot)(cwd, ports);
  if (!root) {
    const err = new Error('pdd status works inside a Git repository.');
    err.exitCode = 2;
    throw err;
  }
  const base = realpathSync(cwd);
  const explicitPaths = [];
  for (const typed of paths) {
    const rel = relative(root, resolve(base, typed)).split(sep).join('/');
    if (!canonicalPath(rel)) {
      const err = new Error(`${typed} is not a file path inside this repository.`);
      err.exitCode = 2;
      throw err;
    }
    explicitPaths.push(rel);
  }

  const changedFiles = changed ? await detectChangedFiles(root, ports) : [];
  const targetPaths = [...new Set([...explicitPaths, ...changedFiles])].sort();

  const { findTests } = ports.preflightSlice ?? runtimePreflightSlice();
  const discovered = findTests({ root, excludeFixtureProjects: true });
  const promptPaths = [...discovered.discoveryVisible].filter(path => path.endsWith('.prompt.md')).sort();
  const ownership = targetPaths.length
    ? findOwners({ root, paths: targetPaths }, { ...(ports.files ? { files: ports.files } : { files: () => gitFiles(root) }), ...(ports.read ? { read: ports.read } : {}) }).files
    : [];

  const { instruction_file, has_pdd_block } = readInstructionBlockState(root);
  const featureMap = readFeatureMap(root);
  const matchedVerify = matchVerifyPaths(targetPaths, featureMap.paths);

  return {
    schema_version: 'pdd.status.v1',
    root,
    instruction_file,
    has_pdd_block,
    counts: {
      prompts: promptPaths.length,
      stories: discovered.stories.length,
      tests: discovered.tests.length,
      orphans: discovered.orphans.length,
      warnings: discovered.warnings.length,
      verify_paths: featureMap.paths.length,
    },
    prompts: promptPaths,
    stories: discovered.stories.map(s => s.path),
    tests: discovered.tests.map(t => t.path),
    orphans: discovered.orphans.map(o => o.path),
    verify: {
      test: featureMap.test,
      paths: featureMap.paths.map(({ id, name, when, needs }) => ({ id, name, when, needs })),
      matched: matchedVerify.map(p => p.id),
    },
    ...(changed ? { changed: changedFiles } : {}),
    files: ownership.map(({ path, owner, owners, source, certain, note }) => ({ path, owner, owners, source, certain, note })),
  };
}

function formatStatusText(view) {
  const c = view.counts;
  const lines = [
    `PDD status: ${c.prompts} prompt${c.prompts === 1 ? '' : 's'}, ${c.stories} Stor${c.stories === 1 ? 'y' : 'ies'}, ${c.tests} test${c.tests === 1 ? '' : 's'}${c.orphans ? `, ${c.orphans} orphan${c.orphans === 1 ? '' : 's'}` : ''}`,
    `Repo init: ${view.has_pdd_block ? `ready (${view.instruction_file})` : 'not initialized (run `pdd init` to add the 4-line PDD block)'}`,
    `Feature Map: ${c.verify_paths} path${c.verify_paths === 1 ? '' : 's'}${view.verify.test ? ` · test: ${view.verify.test}` : ''}`,
  ];
  if (view.verify.paths.length) {
    const shown = view.verify.paths.slice(0, 4).map(p => `${p.id} (${p.name})`).join(', ');
    const more = view.verify.paths.length > 4 ? ` +${view.verify.paths.length - 4} more` : '';
    lines.push(`  paths: ${shown}${more}`);
  }
  if (view.changed) {
    lines.push(`Changed files (${view.changed.length}):${view.changed.length === 0 ? ' none' : ''}`);
  }
  for (const row of view.files) {
    const label = row.owner ? `${row.owner} (${row.source})` : 'unowned';
    lines.push(`  ${row.path}: ${label}${row.note ? ` — ${row.note}` : ''}`);
  }
  if (view.verify.matched.length) {
    lines.push(`Touched verify paths: ${view.verify.matched.join(', ')}`);
  }
  return `${lines.join('\n')}\n`;
}

const epipeGuards = new WeakMap();
function guardEpipe(stream) {
  if (!stream || typeof stream.on !== 'function') return { closed: false };
  let state = epipeGuards.get(stream);
  if (!state) {
    state = { closed: false };
    epipeGuards.set(stream, state);
    stream.on('error', err => { if (err?.code === 'EPIPE') { state.closed = true; return; } throw err; });
  }
  state.closed = false;
  return state;
}

export async function runStatus({ cwd = process.cwd(), paths = [], changed = false, json = false } = {}, ports = {}) {
  const stdout = ports.stdout ?? process.stdout, stderr = ports.stderr ?? process.stderr;
  const pipeState = guardEpipe(stdout);
  try {
    const view = await inspectStatus({ cwd, paths, changed }, ports);
    const out = json ? `${JSON.stringify(view)}\n` : formatStatusText(view);
    if (!pipeState.closed) { try { stdout.write(out); } catch (err) { if (err?.code !== 'EPIPE') throw err; } }
    return 0;
  } catch (error) {
    if (error?.code === 'EPIPE') return 0;
    stderr.write(`${error.message}\n`);
    return error.exitCode ?? 1;
  }
}
