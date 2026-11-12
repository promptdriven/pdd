// Generated from prompts/cli/file-owner.prompt.md (sha256: 4263fd21a5218625f98dbbd847dd4845b858747ac9d0be3952793fb17015ab3e).
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { closeSync, fstatSync, openSync, readSync, realpathSync } from 'node:fs';
import { isAbsolute, posix, relative, resolve, sep } from 'node:path';
import { runtimePreflightSlice } from './runtime-seam.mjs';

const { gitFiles, interfaceBlocks } = runtimePreflightSlice();

const HEAD = 4096, PROMPT = 65536, LINE = 1100, WHOLE = 10 * 1024 * 1024;
const HEADER = /^\s*(?:\/\/+|#+|--|;+|\/\*+|\*+|<!--|"""|''')?\s*Generated from (\S+\.prompt\.md)(?: \(sha256: ([a-f0-9]{64})\))?\.?\s*(?:\*\/|-->|"""|''')?\s*$/;
const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
const unique = values => [...new Set(values)];
const bytesOf = content => typeof content === 'string' ? Buffer.from(content, 'utf8') : content;
const decode = (content, limit) => content ? new TextDecoder().decode(bytesOf(content).subarray(0, limit)) : '';
const canonicalPath = value => typeof value === 'string' && value.trim().length > 0 && value.length <= 1000 && !isAbsolute(value)
  && !/[\\\x00-\x1f\x7f]/.test(value) && !value.split('/').some(part => !part || part === '.' || part === '..' || part.toLowerCase() === '.git');

export function headerEntries(content) {
  if (!content) return [];
  const bytes = bytesOf(content), lines = decode(bytes, HEAD).split(/\r?\n/), rows = new Map();
  if (bytes.length > HEAD) lines.pop();
  for (const line of lines.filter(line => line.length <= LINE)) {
    const match = HEADER.exec(line);
    if (match && canonicalPath(match[1]) && !rows.has(match[1])) rows.set(match[1], { prompt: match[1], sha256: match[2] ?? null });
  }
  return [...rows.values()];
}
export const headerPrompts = content => headerEntries(content).map(row => row.prompt);

// The behavior text: each Runtime interface JSON object loses its approval metadata (status, prose_sha256).
export function promptHeaderHash(content) {
  const text = typeof content === 'string' ? content : new TextDecoder('utf-8', { ignoreBOM: true }).decode(content);
  let behavior = '', at = 0;
  for (const match of interfaceBlocks(text)) {
    const [start, end] = match.indices[1];
    let value; try { value = JSON.parse(text.slice(start, end)); } catch { continue; }
    if (!value || typeof value !== 'object' || Array.isArray(value)) continue;
    const { status, prose_sha256, ...declarations } = value;
    behavior += text.slice(at, start) + JSON.stringify(declarations); at = end;
  }
  return sha256(Buffer.from(behavior + text.slice(at), 'utf8'));
}

// The whole-file form remains accepted for compatibility and reports legacy: true.
export function headerHashState(hash, promptContent) {
  if (promptContent === null || promptContent === undefined || promptContent === false) return { expected: null, state: 'unknown', legacy: false };
  const expected = promptHeaderHash(promptContent);
  if (hash === null || hash === undefined) return { expected, state: 'none', legacy: false };
  if (hash === expected) return { expected, state: 'current', legacy: false };
  return hash === sha256(bytesOf(promptContent)) ? { expected, state: 'current', legacy: true } : { expected, state: 'stale', legacy: false };
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
  const visible = new Set(prompts.map(row => row.path)), whole = new Map(prompts.map(row => [row.path, row.content]));
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
    const headers = headerEntries(head || null).map(({ prompt, sha256: hash }) => ({ prompt, sha256: hash, ...headerHashState(hash, whole.get(prompt) ?? null) }));
    return { path, owner: owners[0] ?? null, owners, source, certain, note: notes.join('; '), headers };
  });
  return { schema_version: 'pdd.owner.v1', files };
}

function readHead(root, path, limit) {
  let fd;
  try { fd = openSync(resolve(root, path), 'r'); }
  catch (error) { if (error.code === 'ENOENT' || error.code === 'ENOTDIR') return null; throw error; }
  try {
    const buffer = Buffer.alloc(Math.min(limit, fstatSync(fd).size + 1));
    let total = 0;
    while (total < buffer.length) { const count = readSync(fd, buffer, total, buffer.length - total, total); if (!count) break; total += count; }
    return buffer.subarray(0, total);
  } finally { closeSync(fd); }
}

export function findOwners({ root, paths = [] }, ports = {}) {
  const files = ports.files ?? (() => gitFiles(root)), read = ports.read ?? ((path, limit) => readHead(root, path, limit));
  const attempt = (path, limit) => { try { return read(path, limit); } catch { return false; } };
  const raw = attempt('pdd-bindings.json', PROMPT);
  const bindings = raw ? decode(raw, PROMPT) : raw;
  // A whole prompt for its header hash; one byte more shows a prompt that is too large.
  const prompts = files().filter(path => path.endsWith('.prompt.md')).map(path => {
    const content = attempt(path, WHOLE + 1);
    return { path, content: content && content.length > WHOLE ? false : content };
  });
  // One byte more than the window, so headerPrompts can see that its last line is cut.
  const heads = unique(paths).map(path => ({ path, content: attempt(path, HEAD + 1) }));
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
    const hashes = row.headers.map(({ prompt, sha256: hash, expected, state, legacy }) => state === 'stale' ? `${prompt} header hash is stale (${hash}); current is ${expected}`
      : state === 'none' ? `${prompt} header has no hash; current is ${expected}` : legacy ? `${prompt} header uses the whole-file hash; current is ${expected}` : '');
    stdout.write([line, row.note, ...hashes].filter(Boolean).map((text, index) => `${index ? '  ' : ''}${text}\n`).join(''));
  }
  return 0;
}
