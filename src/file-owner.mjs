// Prompt: prompts/cli/file-owner.prompt.md
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { closeSync, fstatSync, lstatSync, openSync, readSync, realpathSync } from 'node:fs';
import { isAbsolute, join, posix, relative, resolve, sep } from 'node:path';
import { gitFiles } from './shared/git-context.mjs';
import { interfaceBlocks } from './shared/workspace-policy.mjs';

const HEAD = 4096, PROMPT = 65536, LINE = 1100, WHOLE = 10 * 1024 * 1024;
const HEADER_PARTS = /^(\s*(?:Generated from |(?:\/\/+|#+|--|;+|\/\*+|\*+|<!--|\{\/\*|"""|''')\s*(?:Generated from |Prompt: )))(\S+\.prompt\.md)(?:( \(sha256: )([a-f0-9]{64})(\))|( sha256=)([a-f0-9]{64}))?(\.?\s*(?:(?:\*\/\}|\*\/|-->|"""|''')\s*)?)$/;
const HEX64 = /^[a-f0-9]{64}$/;
const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');
const unique = values => [...new Set(values)];
const bytesOf = content => typeof content === 'string' ? Buffer.from(content, 'utf8') : content;
const decode = (content, limit) => content ? new TextDecoder().decode(bytesOf(content).subarray(0, limit)) : '';
const canonicalPath = value => typeof value === 'string' && value.trim().length > 0 && value.length <= 1000 && !isAbsolute(value)
  && !/[\\\x00-\x1f\x7f]/.test(value) && !value.split('/').some(part => !part || part === '.' || part === '..' || part.toLowerCase() === '.git');

function splitLinesWithEol(text) {
  const out = [];
  let start = 0;
  for (let i = 0; i < text.length; i++) {
    const ch = text[i];
    if (ch === '\r' || ch === '\n') {
      const eol = ch === '\r' && text[i + 1] === '\n' ? '\r\n' : ch;
      out.push({ line: text.slice(start, i), eol });
      if (eol.length === 2) i++;
      start = i + 1;
    }
  }
  if (start < text.length) out.push({ line: text.slice(start), eol: '' });
  return out;
}

export function headerEntries(content) {
  if (!content) return [];
  const bytes = bytesOf(content), lines = decode(bytes, HEAD).split(/\r?\n/), rows = new Map();
  if (bytes.length > HEAD) lines.pop();
  if (lines[0] === '---') {
    for (let i = 1; i < lines.length && lines[i] !== '---'; i++) {
      if (lines[i].length > LINE) continue;
      const fm = /^prompt:\s*(\S+\.prompt\.md)\s*$/.exec(lines[i]);
      if (fm && canonicalPath(fm[1]) && !rows.has(fm[1])) rows.set(fm[1], { prompt: fm[1], sha256: null });
    }
  }
  for (const line of lines.filter(line => line.length <= LINE)) {
    const match = HEADER_PARTS.exec(line);
    if (match && canonicalPath(match[2]) && !rows.has(match[2])) rows.set(match[2], { prompt: match[2], sha256: match[4] ?? match[7] ?? null });
  }
  return [...rows.values()];
}
export const headerPrompts = content => headerEntries(content).map(row => row.prompt);

export function moduleContentHash(content) {
  const raw = typeof content === 'string' ? content : new TextDecoder('utf-8').decode(content);
  const normalized = raw.replace(/^\uFEFF/, '').replace(/\r\n?/g, '\n');
  const totalBytes = Buffer.byteLength(normalized, 'utf8');
  const rows = splitLinesWithEol(normalized);
  let byteOffset = 0, out = '';
  for (let i = 0; i < rows.length; i++) {
    const { line, eol } = rows[i];
    const stepBytes = Buffer.byteLength(line, 'utf8') + eol.length;
    const withinWindow = totalBytes <= HEAD || byteOffset + stepBytes <= HEAD;
    if (withinWindow && line.length <= LINE) {
      const match = HEADER_PARTS.exec(line);
      if (match && canonicalPath(match[2])) {
        out += `${match[1]}${match[2]}${match[8]}${eol}`;
        byteOffset += stepBytes;
        continue;
      }
    }
    out += line + eol;
    byteOffset += stepBytes;
  }
  return sha256(Buffer.from(out, 'utf8'));
}

export function updateHeaderHash(codeText, promptPath, hash) {
  if (typeof codeText !== 'string' || !canonicalPath(promptPath) || !HEX64.test(hash ?? '')) return { content: codeText, changed: false };
  const totalBytes = Buffer.byteLength(codeText, 'utf8');
  const rows = splitLinesWithEol(codeText);
  let byteOffset = 0, out = '', changed = false;
  for (let i = 0; i < rows.length; i++) {
    const { line, eol } = rows[i];
    const stepBytes = Buffer.byteLength(line, 'utf8') + Buffer.byteLength(eol, 'utf8');
    const cutByWindow = totalBytes > HEAD && byteOffset + stepBytes > HEAD;
    if (byteOffset < HEAD && !cutByWindow && line.length <= LINE) {
      const match = HEADER_PARTS.exec(line);
      if (match && canonicalPath(match[2]) && match[2] === promptPath) {
        const nextLine = match[6] ? `${match[1]}${match[2]}${match[6]}${hash}${match[8]}` : `${match[1]}${match[2]} (sha256: ${hash})${match[8]}`;
        if (nextLine !== line) changed = true;
        out += nextLine + eol;
        byteOffset += stepBytes;
        continue;
      }
    }
    out += line + eol;
    byteOffset += stepBytes;
  }
  return { content: out, changed };
}

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

export function headerHashState(hash, promptContent) {
  if (promptContent === null || promptContent === undefined || promptContent === false) return { expected: null, state: 'unknown', legacy: false };
  const expected = promptHeaderHash(promptContent);
  if (hash === null || hash === undefined) return { expected, state: 'none', legacy: false };
  if (hash === expected) return { expected, state: 'current', legacy: false };
  return hash === sha256(bytesOf(promptContent)) ? { expected, state: 'current', legacy: true } : { expected, state: 'stale', legacy: false };
}

function openingSentence(text) {
  const lines = text.replace(/^---\r?\n[\s\S]*?\r?\n---(?:\r?\n|$)/, '').split(/\r?\n/);
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

export const isTestOwnedPath = path => canonicalPath(path) && !path.endsWith('.prompt.md')
  && /(?:^|\/)(?:tests?|__tests__)\/|(?:^|\/)(?:[^/]+\.(?:test|spec)\.[^/]+|test_[^/]+\.[^/]+|[^/]+_test\.[^/]+)$/i.test(path);

export const isTestPromptPath = path => canonicalPath(path) && path.endsWith('.prompt.md')
  && (/(?:^|\/)prompts\/(?:tests?|__tests__)\/|(?:^|\/)[^/]+\.(?:test|spec)\.prompt\.md$/i.test(path)
    || (/(?:^|\/)(?:tests?|__tests__)\//i.test(path) && !/(?:^|\/)(?:tests?|__tests__)\/fixtures\//i.test(path)));

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

const NON_CODE_DIR = /^(?:user_stories|docs?|\.github)\//i;
const FIXTURE_EXAMPLE_DIR = /(?:^|\/)(?:fixtures|examples)\//i;
const DOTFILE = /(?:^|\/)\.[^/]+$/;
const CONFIG_FILE = /(?:^|\/)(?:package(?:-lock)?\.json|pdd(?:-bindings)?\.json|tsconfig[^/]*\.json|jsconfig\.json|Makefile|GNUmakefile|Dockerfile|Containerfile|Procfile|Justfile|Vagrantfile|Rakefile|Gemfile)$/i;
const NON_CODE_EXT = /\.(?:mdx?|rst|txt|json|jsonl|ndjson|ya?ml|toml|ini|cfg|conf|lock|csv|tsv|xml|svg|png|jpe?g|gif|webp|ico|pdf|woff2?)$/i;
const isExcludedPath = path => !canonicalPath(path) || isTestOwnedPath(path) || FIXTURE_EXAMPLE_DIR.test(path) || /\.prompt\.md$/i.test(path)
  || NON_CODE_DIR.test(path) || DOTFILE.test(path) || CONFIG_FILE.test(path) || NON_CODE_EXT.test(path);
const fileExt = path => { const ext = posix.extname(posix.basename(path)); return ext.length > 1 ? ext : ''; };
const isEligibleCodePath = path => !isExcludedPath(path) && Boolean(fileExt(path));
const isEligiblePromptPath = path => {
  if (!canonicalPath(path) || !path.endsWith('.prompt.md') || FIXTURE_EXAMPLE_DIR.test(path)) return false;
  const p = path.slice(0, -'.prompt.md'.length);
  return canonicalPath(p) && !isTestOwnedPath(p);
};
const parentDir = path => { const dir = posix.dirname(path); return dir === '.' ? '' : posix.basename(dir); };

function buildAdvisoryPathMatcher(promptPaths, poolPaths) {
  const validPrompts = unique(promptPaths.filter(isEligiblePromptPath)).sort();
  const allCanonical = new Set(poolPaths.filter(canonicalPath));
  const codeFiles = unique(poolPaths.filter(isEligibleCodePath)).sort();
  const add = (map, key, value) => { let list = map.get(key); if (!list) map.set(key, list = []); list.push(value); };

  const codeByNoExt = new Map(), codeByBase = new Map(), codeByParentBase = new Map(), codeByStem = new Map(), codeByParentStem = new Map();
  for (const file of codeFiles) {
    const base = posix.basename(file), ext = fileExt(file), stem = base.slice(0, -ext.length), parent = parentDir(file);
    add(codeByNoExt, file.slice(0, -ext.length), file);
    add(codeByBase, base, file);
    add(codeByStem, stem, file);
    if (parent) { add(codeByParentBase, `${parent}/${base}`, file); add(codeByParentStem, `${parent}/${stem}`, file); }
  }

  const promptByExactRel = new Map(), promptByExtlessRel = new Map(), promptByBase = new Map(), promptByParentBase = new Map(), promptByStem = new Map(), promptByParentStem = new Map();
  for (const prompt of validPrompts) {
    const rel = prompt.slice(0, -'.prompt.md'.length).replace(/^prompts\/(?:modules\/)?/, '');
    const base = posix.basename(rel), ext = fileExt(rel), parent = parentDir(rel);
    if (ext || rel.includes('/')) add(promptByExactRel, rel, prompt);
    if (!ext) add(promptByExtlessRel, rel, prompt);
    else { add(promptByBase, base, prompt); if (parent) add(promptByParentBase, `${parent}/${base}`, prompt); }
    add(promptByStem, base, prompt);
    if (parent) add(promptByParentStem, `${parent}/${base}`, prompt);
  }

  return path => {
    if (isExcludedPath(path)) return null;
    const exact = promptByExactRel.get(path);
    if (exact?.length) return { owners: exact, kind: 'path' };
    const ext = fileExt(path);
    if (!ext) return null;
    const noExt = path.slice(0, -ext.length), extless = promptByExtlessRel.get(noExt);
    if (extless?.length && !allCanonical.has(noExt) && codeByNoExt.get(noExt)?.length === 1) return { owners: extless, kind: 'path' };
    const base = posix.basename(path), stem = base.slice(0, -ext.length), parent = parentDir(path);
    const byBase = promptByBase.get(base);
    if (byBase?.length) {
      if (codeByBase.get(base)?.length === 1 && byBase.length === 1) return { owners: byBase, kind: 'name' };
      const key = `${parent}/${base}`;
      if (parent && codeByParentBase.get(key)?.length === 1 && promptByParentBase.get(key)?.length === 1) return { owners: promptByParentBase.get(key), kind: 'name' };
    }
    const byStem = promptByStem.get(stem);
    if (byStem?.length) {
      if (codeByStem.get(stem)?.length === 1 && byStem.length === 1) return { owners: byStem, kind: 'name' };
      const key = `${parent}/${stem}`;
      if (parent && codeByParentStem.get(key)?.length === 1 && promptByParentStem.get(key)?.length === 1) return { owners: promptByParentStem.get(key), kind: 'name' };
    }
    return null;
  };
}

export function resolveOwners({ paths = [], allPaths = paths, bindings = null, heads = [], prompts = [] } = {}) {
  const table = bindings === false ? null : bindingTable(bindings);
  const content = new Map(heads.map(row => [row.path, row.content]));
  const visible = new Set(prompts.map(row => row.path)), whole = new Map(prompts.map(row => [row.path, row.content]));
  const claims = prompts.map(row => [row.path, new Set(promptClaims(row.path, row.content))]);
  const matchAdvisoryPath = table === null ? () => null : buildAdvisoryPathMatcher(prompts.map(row => row.path), [...(allPaths ?? paths), ...paths]);

  const files = unique(paths).map(path => {
    const bound = table?.get(path), head = content.get(path);
    const owners = unique([...(bound ?? []), ...headerPrompts(head || null)]);
    const notes = [], missing = owners.filter(prompt => !visible.has(prompt));
    // Honest ownership: prose mentions and filename stems are advisory hints only — never ownership claims.
    if (!owners.length && !bound && head !== false && table !== null) {
      const prose = claims.filter(([, set]) => set.has(path)).map(([prompt]) => prompt).sort();
      if (prose.length) notes.push(`named only in the opening sentence of ${prose.join(', ')}; add a // Prompt: header or a pdd-bindings.json entry`);
      else {
        const matched = matchAdvisoryPath(path);
        if (matched) notes.push(`matched by ${matched.kind === 'path' ? 'path' : 'file name'} to ${matched.owners.join(', ')}; add a // Prompt: header or a pdd-bindings.json entry`);
      }
    }
    for (const prompt of missing) notes.push(`names ${prompt}, which is not a Git-visible prompt`);
    if (!owners.length && table === null) notes.push('pdd-bindings.json could not be read, so a binding may be missing');
    if (!bound?.length && head === false) notes.push('the file could not be read, so a header may be missing');
    if (bound && !bound.length) notes.push('pdd-bindings.json declares it with no prompt');
    const certain = owners.length ? !missing.length : table !== null && head !== false;
    const source = owners.length ? (bound?.includes(owners[0]) ? 'binding' : 'header') : bound ? 'binding' : null;
    const headers = headerEntries(head || null).map(({ prompt, sha256: hash }) => ({ prompt, sha256: hash, ...headerHashState(hash, whole.get(prompt) ?? null) }));
    return { path, owner: owners[0] ?? null, owners, source, certain, note: notes.join('; '), headers };
  });
  return { schema_version: 'pdd.owner.v1', files };
}

function checkRegularPath(root, path) {
  const parts = path.split('/');
  let cur = root;
  for (let i = 0; i < parts.length; i++) {
    cur = join(cur, parts[i]);
    let st;
    try { st = lstatSync(cur); }
    catch (error) { if (error.code === 'ENOENT' || error.code === 'ENOTDIR') return null; throw error; }
    if (st.isSymbolicLink() || (i === parts.length - 1 ? !st.isFile() : !st.isDirectory())) {
      throw Object.assign(new Error('not a regular file'), { code: 'ELOOP' });
    }
  }
  return cur;
}

function readHead(root, path, limit) {
  const full = checkRegularPath(root, path);
  if (full === null) return null;
  let fd;
  try { fd = openSync(full, 'r'); }
  catch (error) { if (error.code === 'ENOENT' || error.code === 'ENOTDIR') return null; throw error; }
  try {
    const buffer = Buffer.alloc(Math.min(limit, fstatSync(fd).size + 1));
    let total = 0;
    while (total < buffer.length) { const count = readSync(fd, buffer, total, buffer.length - total, total); if (!count) break; total += count; }
    return buffer.subarray(0, total);
  } finally { closeSync(fd); }
}

// Shared single-scan repository loader used by findOwners, findTestPromptViolations, and runOwner.
function loadOwnerContext({ root }, ports = {}) {
  const listFiles = ports.files ?? (() => gitFiles(root));
  const readPort = ports.read ?? ((path, limit) => readHead(root, path, limit));
  const visible = listFiles();
  const visibleSet = new Set(visible);
  const isRegularVisible = path => {
    if (!visibleSet.has(path)) return false;
    if (ports.read) return true;
    try { return checkRegularPath(root, path) !== null; } catch { return false; }
  };
  const attempt = (path, limit) => { try { return readPort(path, limit); } catch { return false; } };
  const attemptVisible = (path, limit) => (!isRegularVisible(path) ? null : attempt(path, limit));

  // Bug 2 + Bug 3 fix: check Git visibility consistently and read PROMPT + 1 bytes to detect >64 KiB truncation.
  const rawBindings = attemptVisible('pdd-bindings.json', PROMPT + 1);
  const bindings = rawBindings === false || (rawBindings && bytesOf(rawBindings).length > PROMPT)
    ? false
    : rawBindings ? decode(rawBindings, PROMPT) : rawBindings;
  const table = bindings === false ? null : bindingTable(bindings);
  const prompts = visible.filter(path => path.endsWith('.prompt.md')).map(path => {
    const content = attemptVisible(path, WHOLE + 1);
    return { path, content: content && bytesOf(content).length > WHOLE ? false : content };
  });
  const promptMap = new Map(prompts.map(row => [row.path, row.content]));
  return { visible, visibleSet, isRegularVisible, attempt, attemptVisible, bindings, table, prompts, promptMap };
}

function collectPromptTestClaims(ctx, queriedPrompts, skipTargets, { includeProse = false } = {}) {
  const claimsByPrompt = new Map();
  if (!queriedPrompts.length) return claimsByPrompt;
  const extra = new Set();
  const proseByPrompt = new Map();
  if (includeProse) {
    for (const promptPath of queriedPrompts) {
      const proseSet = new Set();
      for (const claim of promptClaims(promptPath, ctx.promptMap.get(promptPath) || null)) {
        if (isTestOwnedPath(claim)) { extra.add(claim); proseSet.add(claim); }
      }
      proseByPrompt.set(promptPath, proseSet);
    }
  }
  if (ctx.table) {
    for (const [mod, owners] of ctx.table.entries()) {
      if (isTestOwnedPath(mod) && owners.some(owner => queriedPrompts.includes(owner))) extra.add(mod);
    }
  }
  const testCandidates = unique([...ctx.visible.filter(isTestOwnedPath), ...extra]).filter(p => !skipTargets.has(p)).sort();
  if (!testCandidates.length) return claimsByPrompt;
  const heads = testCandidates.map(path => ({ path, content: ctx.isRegularVisible(path) ? ctx.attemptVisible(path, HEAD + 1) : null }));
  const checked = resolveOwners({ paths: testCandidates, allPaths: ctx.visible, bindings: ctx.bindings, heads, prompts: ctx.prompts });
  for (const promptPath of queriedPrompts) {
    const proseSet = proseByPrompt.get(promptPath) ?? new Set();
    const claimed = checked.files
      .filter(row => row.owners.includes(promptPath) || (includeProse && proseSet.has(row.path)))
      .map(row => row.path)
      .sort();
    if (claimed.length) claimsByPrompt.set(promptPath, claimed);
  }
  return claimsByPrompt;
}

export function findOwners({ root, paths = [] }, ports = {}) {
  const ctx = loadOwnerContext({ root }, ports);
  const heads = unique(paths).map(path => ({ path, content: ctx.attempt(path, HEAD + 1) }));
  return resolveOwners({ paths, allPaths: ctx.visible, bindings: ctx.bindings, heads, prompts: ctx.prompts });
}

export function findTestPromptViolations({ root, promptPaths = [], checkPaths = [], includeProse = false } = {}, ports = {}) {
  const checkedPrompts = unique(promptPaths.filter(path => canonicalPath(path) && path.endsWith('.prompt.md')));
  const checkedTests = unique(checkPaths.filter(path => canonicalPath(path) && isTestOwnedPath(path)));
  const violations = [], reportedTargets = new Set();
  for (const prompt of checkedPrompts) {
    if (isTestPromptPath(prompt)) violations.push({
      kind: 'test-prompt-path', prompt, targets: [],
      message: `Error: misplaced test prompt: ${prompt}. Prompts own production modules, not test files; delete ${prompt} and keep tests in test/.`,
    });
  }
  const ordinaryPrompts = checkedPrompts.filter(path => !isTestPromptPath(path));
  if (!ordinaryPrompts.length && !checkedTests.length) return { ok: violations.length === 0, violations };

  const ctx = loadOwnerContext({ root }, ports);
  if (checkedTests.length) {
    const heads = checkedTests.map(path => ({ path, content: ctx.isRegularVisible(path) ? ctx.attemptVisible(path, HEAD + 1) : null }));
    const resolved = resolveOwners({ paths: checkedTests, allPaths: ctx.visible, bindings: ctx.bindings, heads, prompts: ctx.prompts });
    for (const row of resolved.files) {
      if (!row.owners.length || (row.source !== 'binding' && row.source !== 'header')) continue;
      reportedTargets.add(row.path);
      const testOwners = row.owners.filter(isTestPromptPath);
      const prodOwners = row.owners.filter(owner => !isTestPromptPath(owner));
      // Bug 1 fix: emit BOTH test-prompt-path and ordinary misplaced-owner diagnostics when a test file has mixed owners.
      for (const owner of testOwners) {
        violations.push({
          kind: 'test-file-owned', prompt: owner, targets: [row.path],
          message: `Error: misplaced test prompt: ${row.path} is claimed by ${owner} (${row.source}). Prompts own production modules, not test files; delete ${owner} and keep tests in test/.`,
        });
      }
      if (prodOwners.length) {
        violations.push({
          kind: 'test-file-owned', prompt: prodOwners[0], targets: [row.path],
          message: `Error: misplaced prompt owner: ${row.path} is claimed by ${prodOwners.join(', ')} (${row.source}). Prompts own production modules, not test files; remove test ownership before continuing.`,
        });
      }
    }
  }
  for (const [promptPath, claimed] of collectPromptTestClaims(ctx, ordinaryPrompts, reportedTargets, { includeProse })) {
    violations.push({
      kind: 'test-file-claim', prompt: promptPath, targets: claimed,
      message: `Error: misplaced prompt owner: ${promptPath} claims ${claimed.join(', ')}. Prompts own production modules, not test files; remove test ownership before continuing.`,
    });
  }
  return { ok: violations.length === 0, violations };
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
  const ports = { ...(files ? { files } : {}), ...(read ? { read } : {}) };
  const ctx = loadOwnerContext({ root }, ports);
  const heads = unique(named).map(path => ({ path, content: ctx.attempt(path, HEAD + 1) }));
  const result = resolveOwners({ paths: named, allPaths: ctx.visible, bindings: ctx.bindings, heads, prompts: ctx.prompts });

  const errors = [], warnings = [], warnedTargets = new Set(), reportedTestPrompts = new Set();
  for (const path of unique(named)) {
    if (isTestPromptPath(path)) {
      reportedTestPrompts.add(path);
      errors.push(`Error: misplaced test prompt: ${path}. Prompts own production modules, not test files; delete ${path} and keep tests in test/.`);
    }
  }
  for (const row of result.files) {
    const testOwners = row.owners.filter(isTestPromptPath);
    const prodOwners = row.owners.filter(owner => !isTestPromptPath(owner));
    if (testOwners.length) {
      warnedTargets.add(row.path);
      for (const owner of testOwners) {
        if (!reportedTestPrompts.has(owner)) errors.push(`Error: misplaced test prompt: ${row.path} is claimed by ${owner} (${row.source}). Prompts own production modules, not test files; delete ${owner} and keep tests in test/.`);
      }
    }
    if (prodOwners.length && isTestOwnedPath(row.path)) {
      warnedTargets.add(row.path);
      warnings.push(`Warning: misplaced prompt owner: ${row.path} is claimed by ${prodOwners.join(', ')} (${row.source}). Prompts own production modules, not test files.`);
    }
  }
  const queriedPrompts = unique(named.filter(path => path.endsWith('.prompt.md') && !isTestPromptPath(path)));
  for (const [promptPath, claimed] of collectPromptTestClaims(ctx, queriedPrompts, warnedTargets, { includeProse: true })) {
    warnings.push(`Warning: misplaced prompt owner: ${promptPath} claims ${claimed.join(', ')}. Prompts own production modules, not test files.`);
  }
  for (const error of errors) stderr.write(`${error}\n`);
  for (const warning of warnings) stderr.write(`${warning}\n`);
  const exitCode = errors.length ? 1 : 0;
  if (json) { stdout.write(`${JSON.stringify(result)}\n`); return exitCode; }
  for (const row of result.files) {
    const doubt = row.certain ? '' : 'not certain: treat as owned';
    const line = row.owners.length ? `${row.path}: ${row.owners.join(', ')} (${[row.source, doubt].filter(Boolean).join(', ')})`
      : `${row.path}: no owner${doubt ? ` (${doubt})` : ''}`;
    const hashes = row.headers.map(({ prompt, sha256: hash, expected, state, legacy }) => state === 'stale' ? `${prompt} header hash is stale (${hash}); current is ${expected}`
      : legacy ? `${prompt} header uses the whole-file hash; current is ${expected}` : '');
    stdout.write([line, row.note, ...hashes].filter(Boolean).map((text, index) => `${index ? '  ' : ''}${text}\n`).join(''));
  }
  return exitCode;
}
