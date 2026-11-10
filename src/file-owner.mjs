// Generated from prompts/cli/file-owner.prompt.md (sha256: 8355b570b5c57dbcd24f71f255749f344198e0d1f7f830a275fb04f5fbdb482a).
import { execFileSync } from 'node:child_process';
import { closeSync, openSync, readSync, realpathSync } from 'node:fs';
import { isAbsolute, posix, relative, resolve, sep } from 'node:path';
import { gitFiles } from './runtime-preflight.mjs';

const HEAD = 4096, PROMPT = 65536, LINE = 1100;
const HEADER = /^\s*(?:\/\/+|#+|--|;+|\/\*+|\*+|<!--|"""|''')?\s*Generated from (\S+\.prompt\.md)(?: \(sha256: [a-f0-9]{64}\))?\.?\s*(?:\*\/|-->|"""|''')?\s*$/;
const unique = values => [...new Set(values)];
const bytesOf = content => typeof content === 'string' ? Buffer.from(content, 'utf8') : content;
const decode = (content, limit) => content ? new TextDecoder().decode(bytesOf(content).subarray(0, limit)) : '';
const canonicalPath = value => typeof value === 'string' && value.trim().length > 0 && value.length <= 1000 && !isAbsolute(value)
  && !/[\\\x00-\x1f\x7f]/.test(value) && !value.split('/').some(part => !part || part === '.' || part === '..' || part.toLowerCase() === '.git');

export function headerPrompts(content) {
  if (!content) return [];
  const bytes = bytesOf(content), lines = decode(bytes, HEAD).split(/\r?\n/);
  if (bytes.length > HEAD) lines.pop();
  return unique(lines.filter(line => line.length <= LINE).map(line => HEADER.exec(line)?.[1]).filter(canonicalPath));
}

function openingSentence(text) {
  const lines = text.split(/\r?\n/);
  let at = 0;
  const blanks = () => { while (at < lines.length && !lines[at].trim()) at++; };
  blanks();
  if (/^# /.test(lines[at] ?? '')) { at++; blanks(); }
  const stop = line => !line.trim() || /^\s*#/.test(line) || /^\s*(?:```|~~~)/.test(line);
  const paragraph = [];
  while (at < lines.length && !stop(lines[at])) paragraph.push(lines[at++].trim());
  const joined = paragraph.join(' ');
  let code = false;
  for (let i = 0; i < joined.length; i++) {
    if (joined[i] === '`') code = !code;
    else if (!code && '.!?'.includes(joined[i]) && (i + 1 === joined.length || /\s/.test(joined[i + 1]))) return joined.slice(0, i + 1);
  }
  return joined;
}

export function promptClaims(promptPath, content) {
  if (!content) return [];
  const folder = posix.dirname(promptPath), near = target => posix.normalize(posix.join(folder, target));
  let sentence = openingSentence(decode(content, PROMPT));
  const claims = [];
  sentence = sentence.replace(/\]\(([^)\s]+)\)/g, (_, target) => {
    const file = target.split('#')[0];
    if (file && !/^[a-z][a-z0-9+.-]*:/i.test(file)) claims.push(near(file));
    return ']';
  });
  for (let [run] of sentence.matchAll(/[A-Za-z0-9_@+~./-]+/g)) {
    run = run.replace(/\.+$/, '');
    if (run.includes('/') || run.includes('.')) claims.push(/^\.\.?\//.test(run) ? near(run) : run);
  }
  return unique(claims.filter(path => canonicalPath(path) && !path.endsWith('.prompt.md'))).sort();
}

function bindingTable(text) {
  if (text === null || text === undefined) return new Map();
  try {
    const doc = JSON.parse(text);
    if (!doc || typeof doc !== 'object' || doc.schema_version !== 'pdd.bindings.v1' || !Array.isArray(doc.modules)) return null;
    const table = new Map();
    for (const item of doc.modules) {
      if (!item || typeof item !== 'object' || typeof item.module !== 'string') continue;
      table.set(item.module, [...(table.get(item.module) ?? []), ...(typeof item.prompt === 'string' ? [item.prompt] : [])]);
    }
    return table;
  } catch { return null; }
}

export function resolveOwners({ paths = [], bindings = null, heads = [], prompts = [] } = {}) {
  const table = bindings === false ? null : bindingTable(bindings);
  const content = new Map(heads.map(row => [row.path, row.content]));
  const visible = new Set(prompts.map(row => row.path));
  const claims = prompts.map(row => [row.path, new Set(promptClaims(row.path, row.content))]);
  const files = unique(paths).map(path => {
    const bound = table?.get(path), head = content.get(path);
    const recorded = unique([...(bound ?? []), ...headerPrompts(head || null)]);
    const owners = recorded.length ? recorded : claims.filter(([, set]) => set.has(path)).map(([prompt]) => prompt).sort();
    const notes = [], missing = recorded.filter(prompt => !visible.has(prompt));
    if (!recorded.length && owners.length) notes.push(`named only in the opening sentence of ${owners.join(', ')}; add a Generated from header or a pdd-bindings.json entry`);
    for (const prompt of missing) notes.push(`names ${prompt}, which is not a Git-visible prompt`);
    if (!owners.length && table === null) notes.push('pdd-bindings.json could not be read, so a binding may be missing');
    if (!bound?.length && head === false) notes.push('the file could not be read, so a header may be missing');
    if (bound && !bound.length) notes.push('pdd-bindings.json declares it with no prompt');
    const certain = recorded.length ? !missing.length : !owners.length && table !== null && head !== false;
    const source = owners.length ? (bound?.includes(owners[0]) ? 'binding' : recorded.length ? 'header' : 'prose') : bound ? 'binding' : null;
    return { path, owner: owners[0] ?? null, owners, source, certain, note: notes.join('; ') };
  });
  return { schema_version: 'pdd.owner.v1', files };
}

function readHead(root, path, limit) {
  let fd;
  try { fd = openSync(resolve(root, path), 'r'); }
  catch (error) { if (error.code === 'ENOENT' || error.code === 'ENOTDIR') return null; throw error; }
  try { const buffer = Buffer.alloc(limit); return buffer.subarray(0, readSync(fd, buffer, 0, limit, 0)); }
  finally { closeSync(fd); }
}

export function findOwners({ root, paths = [] }, ports = {}) {
  const files = ports.files ?? (() => gitFiles(root)), read = ports.read ?? ((path, limit) => readHead(root, path, limit));
  const attempt = (path, limit) => { try { return read(path, limit); } catch { return false; } };
  const raw = attempt('pdd-bindings.json', PROMPT);
  const bindings = raw ? decode(raw, PROMPT) : raw;
  const prompts = files().filter(path => path.endsWith('.prompt.md')).map(path => ({ path, content: attempt(path, PROMPT) || null }));
  const heads = unique(paths).map(path => ({ path, content: attempt(path, HEAD) }));
  return resolveOwners({ paths, bindings, heads, prompts });
}

export function runOwner({ cwd = process.cwd(), paths = [], json = false } = {}, { stdout = process.stdout, stderr = process.stderr, files, read } = {}) {
  let root;
  try { root = execFileSync('git', ['rev-parse', '--show-toplevel'], { cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] }).trim(); }
  catch { stderr.write('pdd owner works inside a Git repository.\n'); return 2; }
  const base = realpathSync(cwd), named = [];
  for (const typed of paths) {
    const path = relative(root, resolve(base, typed)).split(sep).join('/');
    if (!canonicalPath(path)) { stderr.write(`${typed} is not a file path inside this repository.\n`); return 2; }
    named.push(path);
  }
  const result = findOwners({ root, paths: named }, { ...(files ? { files } : {}), ...(read ? { read } : {}) });
  if (json) { stdout.write(`${JSON.stringify(result)}\n`); return 0; }
  for (const row of result.files) {
    const doubt = row.certain ? '' : 'not certain: treat as owned';
    const line = row.owners.length ? `${row.path}: ${row.owners.join(', ')} (${[row.source, doubt].filter(Boolean).join(', ')})`
      : `${row.path}: no owner${doubt ? ` (${doubt})` : ''}`;
    stdout.write(`${line}\n${row.note ? `  ${row.note}\n` : ''}`);
  }
  return 0;
}
