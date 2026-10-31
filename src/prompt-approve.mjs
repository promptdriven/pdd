// Generated from prompts/cli/prompt-approve.prompt.md (sha256: 92a2560cd9405ca039278254ecb94f71c6792edd7f8980b3f6f5e47e955944ec).
import { approvalActor, readApprovalPolicy, readPromptApprovals, recordPromptApproval } from './approval-policy.mjs';
import { randomUUID } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { lstatSync, readFileSync, realpathSync, writeFileSync } from 'node:fs';
import { relative, resolve, sep, join } from 'node:path';
import { createInterface } from 'node:readline';
import { isDeepStrictEqual } from 'node:util';
import { gitFiles, interfaceBlocks, interfaceSchemaProblems, proseSha256 } from './runtime-preflight.mjs';

class Stop extends Error { constructor(exitCode, message) { super(message); this.exitCode = exitCode; } }
const line = (stream, text) => stream.write(`${text}\n`);
const isObject = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const show = value => JSON.stringify(value);
const either = items => items.length > 1 ? `${items.slice(0, -1).join(', ')} or ${items.at(-1)}` : items[0];
const plural = (count, word) => `${count} ${word}${count === 1 ? '' : 's'}`;
function range(min, max, unit) {
  const word = count => unit ? ` ${plural(count, unit).split(' ').slice(1).join(' ')}` : '';
  if (min !== undefined && max !== undefined) return `${min} to ${max}${word(max)}`;
  return min !== undefined ? `at least ${min}${word(min)}` : `at most ${max}${word(max)}`;
}

// One schema as short words: "string (at least 1 character)", "integer, 1 to 20", "\"S\", \"M\" or \"L\"".
function short(schema) {
  if (!isObject(schema)) return 'any value';
  if (Array.isArray(schema.oneOf)) return either(schema.oneOf.map(short));
  if (Array.isArray(schema.enum)) return either(schema.enum.map(show));
  if (Object.hasOwn(schema, 'const')) return show(schema.const);
  const type = schema.type;
  if (type === 'string') {
    const length = schema.minLength !== undefined || schema.maxLength !== undefined ? ` (${range(schema.minLength, schema.maxLength, 'character')})` : '';
    return `string${length}${typeof schema.pattern === 'string' ? ` matching ${schema.pattern}` : ''}`;
  }
  if (type === 'integer' || type === 'number') {
    const bounds = schema.minimum !== undefined || schema.maximum !== undefined ? `, ${range(schema.minimum, schema.maximum)}` : '';
    return `${type}${bounds}${schema.exclusiveMinimum !== undefined ? `, more than ${schema.exclusiveMinimum}` : ''}${schema.exclusiveMaximum !== undefined ? `, less than ${schema.exclusiveMaximum}` : ''}`;
  }
  if (type === 'array') {
    const count = schema.minItems !== undefined || schema.maxItems !== undefined ? ` (${range(schema.minItems, schema.maxItems, 'item')})` : '';
    if (schema.maxItems === 0) return 'an empty list';
    return isObject(schema.items) && schema.items.type === 'object' ? `a list${count} of:` : `a list${count} of ${short(schema.items)}`;
  }
  if (type === 'object') return 'an object:';
  return typeof type === 'string' ? type : 'any value';
}

// The lines that describe a schema, one field per line, nested fields indented.
function describe(schema, indent) {
  if (isObject(schema) && schema.type === 'object' && isObject(schema.properties)) {
    const required = new Set(Array.isArray(schema.required) ? schema.required : []);
    const fields = Object.entries(schema.properties);
    if (!fields.length) return [`${indent}(nothing)`];
    return fields.flatMap(([name, child]) => [`${indent}${name}${required.has(name) ? '' : ' (optional)'}: ${short(child)}`, ...nested(child, `${indent}  `)]);
  }
  return [`${indent}${short(schema)}`, ...nested(schema, `${indent}  `)];
}
function nested(schema, indent) {
  if (!isObject(schema)) return [];
  if (schema.type === 'object') return describe(schema, indent);
  if (schema.type === 'array' && schema.maxItems !== 0 && isObject(schema.items) && schema.items.type === 'object') return describe(schema.items, indent);
  return [];
}

// The interface in plain words, for the person who approves it.
export function describeInterface(path, iface) {
  const out = [`${path} (${iface.status})`];
  for (const entry of Array.isArray(iface.entries) ? iface.entries : []) {
    out.push(`Operation ${entry?.operation}`, 'Input:', ...describe(entry?.input_schema, '  '), 'Result:', ...describe(entry?.result_schema, '  '),
      `Errors: ${Array.isArray(entry?.errors) && entry.errors.length ? entry.errors.join(', ') : 'none'}`);
  }
  const calls = Array.isArray(iface.calls) ? iface.calls : [];
  if (calls.length) out.push(`Calls: ${calls.map(call => `${call?.target} ${call?.target_operation} (at most ${call?.max_calls})`).join('; ')}`);
  const resources = Array.isArray(iface.resources) ? iface.resources : [];
  if (resources.length) out.push(`Resources: ${resources.map(resource => `${resource?.name} (${resource?.kind}, ${resource?.access})`).join('; ')}`);
  return out;
}

// ---- The prose that the person approves (round-2 tester: the screen showed only the interface) ----
const PROSE_LINES = 40, HISTORY = 200;
// No control characters, so that terminal codes cannot hide words; spaces stay.
const plain = text => text.replace(/\x1b\[[0-9;?]*[ -/]*[@-~]/g, '').replace(/[\x00-\x08\x0b-\x1f\x7f-\x9f]/g, ' ').trimEnd();
// The text without its Runtime interface block (what prose_sha256 hashes).
function proseOf(text) {
  let out = '', at = 0;
  for (const block of interfaceBlocks(text)) { out += text.slice(at, block.index); at = block.index + block[0].length; }
  return out + text.slice(at);
}

// The newest version in Git that was approved with its own prose hash: {commit, text}, or null.
function lastApproved(root, path) {
  const log = spawnSync('git', ['log', '--format=%H', '-n', String(HISTORY), '--', path], { cwd: root, encoding: 'utf8' });
  for (const commit of log.status === 0 ? log.stdout.split('\n').filter(Boolean) : []) {
    const shown = spawnSync('git', ['show', `${commit}:${path}`], { cwd: root, encoding: 'utf8', maxBuffer: 16 * 1024 * 1024 });
    const blocks = shown.status === 0 ? interfaceBlocks(shown.stdout) : [];
    let value = null;
    try { value = blocks.length === 1 ? JSON.parse(blocks[0][1]) : null; } catch { value = null; }
    if (value?.status === 'approved' && value.prose_sha256 === proseSha256(shown.stdout)) return { commit, text: shown.stdout };
  }
  return null;
}

// A line diff (longest common subsequence) as [mark, line] with mark ' ', '-' or '+'.
function lineDiff(before, after) {
  const a = before.split('\n'), b = after.split('\n');
  let head = 0, tailA = a.length, tailB = b.length;
  while (head < tailA && head < tailB && a[head] === b[head]) head += 1;
  while (tailA > head && tailB > head && a[tailA - 1] === b[tailB - 1]) { tailA -= 1; tailB -= 1; }
  const x = a.slice(head, tailA), y = b.slice(head, tailB), middle = [];
  if (x.length * y.length > 4_000_000) middle.push(...x.map(text => ['-', text]), ...y.map(text => ['+', text]));
  else {
    const common = Array.from({ length: x.length + 1 }, () => new Uint32Array(y.length + 1));
    for (let i = x.length - 1; i >= 0; i -= 1) for (let j = y.length - 1; j >= 0; j -= 1) common[i][j] = x[i] === y[j] ? common[i + 1][j + 1] + 1 : Math.max(common[i + 1][j], common[i][j + 1]);
    for (let i = 0, j = 0; i < x.length || j < y.length;) {
      if (i < x.length && j < y.length && x[i] === y[j]) { middle.push([' ', x[i]]); i += 1; j += 1; }
      else if (i < x.length && (j >= y.length || common[i + 1][j] >= common[i][j + 1])) { middle.push(['-', x[i]]); i += 1; }
      else { middle.push(['+', y[j]]); j += 1; }
    }
  }
  return [...a.slice(0, head).map(text => [' ', text]), ...middle, ...a.slice(tailA).map(text => [' ', text])];
}

// The changed lines with 1 unchanged line around each change, and "…" between parts.
function changedRows(before, after) {
  const diff = lineDiff(before, after), keep = new Set();
  diff.forEach(([mark], index) => { if (mark !== ' ') for (const near of [index - 1, index, index + 1]) keep.add(near); });
  const rows = [];
  diff.forEach(([mark, text], index) => {
    if (!keep.has(index)) return;
    if (rows.length && !keep.has(index - 1)) rows.push('  …');
    rows.push(plain(`${mark === ' ' ? '    ' : `  ${mark} `}${text}`));
  });
  return rows;
}

const capped = (title, rows, more) => rows.length <= PROSE_LINES ? [title, ...rows]
  : [title, ...rows.slice(0, PROSE_LINES), `… ${rows.length - PROSE_LINES} more lines not shown. ${more}`];

// What the person approves in words: the prose changes since the last approved version, else all of the prose.
function proseView(root, path, text) {
  const before = lastApproved(root, path), prose = proseOf(text);
  if (!before) {
    const rows = prose.split('\n').map(text => plain(`  ${text}`));
    while (rows.length && !rows.at(-1)) rows.pop();
    return capped('Text (no approved version in Git, so all of it):', rows, `Read the whole file: ${path}`);
  }
  const commit = before.commit.slice(0, 12), rows = changedRows(proseOf(before.text), prose);
  if (!rows.length) return [`Text: the same as the last approved version (${commit}).`];
  return capped(`Text changes since the last approved version (${commit}):`, rows, `See all of them with: git diff ${commit} -- ${path}`);
}

// The [start, end) of the string value of a top-level key in a JSON object text, or null.
function topLevelString(text, key) {
  const skip = at => { let index = at + 1; while (index < text.length && text[index] !== '"') index += text[index] === '\\' ? 2 : 1; return index + 1; };
  let depth = 0;
  for (let index = 0; index < text.length;) {
    const char = text[index];
    if (char === '"') {
      const end = skip(index), after = /^\s*:\s*/.exec(text.slice(end, end + 64));
      if (depth === 1 && after && JSON.parse(text.slice(index, end)) === key) {
        const start = end + after[0].length;
        return text[start] === '"' ? [start, skip(start)] : null;
      }
      index = end; continue;
    }
    if (char === '{' || char === '[') depth += 1;
    if (char === '}' || char === ']') depth -= 1;
    index += 1;
  }
  return null;
}

// Set the top-level status to approved and fill prose_sha256; keep every other byte. Null when that is not safe.
export function approvePromptText(text) {
  const blocks = interfaceBlocks(text);
  if (blocks.length !== 1) return null;
  const [start, end] = blocks[0].indices[1], body = blocks[0][1], hash = proseSha256(text);
  let value;
  try { value = JSON.parse(body); } catch { return null; }
  const status = topLevelString(body, 'status'), digest = topLevelString(body, 'prose_sha256');
  if (!isObject(value) || !status || !digest) return null;
  const edits = [[...status, '"approved"'], [...digest, `"${hash}"`]].sort((a, b) => b[0] - a[0]);
  const changed = edits.reduce((textSoFar, [from, to, put]) => textSoFar.slice(0, from) + put + textSoFar.slice(to), body);
  const next = text.slice(0, start) + changed + text.slice(end);
  try {
    return isDeepStrictEqual(JSON.parse(changed), { ...value, status: 'approved', prose_sha256: hash }) && proseSha256(next) === hash ? next : null;
  } catch { return null; }
}

// One reader for the whole command, so answers typed for several questions are all kept.
export function lineReader(stdin) {
  const reader = createInterface({ input: stdin }), lines = [], waiting = [];
  let closed = false;
  reader.on('line', text => { const next = waiting.shift(); if (next) next(text); else lines.push(text); });
  reader.on('close', () => { closed = true; for (const next of waiting.splice(0)) next(''); });
  return { ask: () => lines.length ? Promise.resolve(lines.shift()) : closed ? Promise.resolve('') : new Promise(done => waiting.push(done)), close: () => reader.close() };
}

// Show one prompt, ask the person, and approve on y. expectedHash (from the Try page) must equal the local prose hash.
// Returns {state: 'done' | 'declined', exitCode, message}; prints the view and the question to stdout.
export async function askApproval({ root, path, stdout, answers, expectedHash, said, commit }) {
  const text = readFileSync(join(root, path), 'utf8'), blocks = interfaceBlocks(text);
  if (blocks.length !== 1) return { state: 'declined', exitCode: 4, message: `${path} has ${blocks.length ? 'more than one' : 'no'} Runtime interface block.` };
  let iface;
  try { iface = JSON.parse(blocks[0][1]); } catch { iface = null; }
  if (!isObject(iface)) return { state: 'declined', exitCode: 4, message: `The Runtime interface of ${path} is not a JSON object.` };
  const hash = proseSha256(text), current = iface.prose_sha256 === hash;
  if (expectedHash !== undefined && expectedHash !== hash) {
    return { state: 'declined', exitCode: 4, message: `${path}: the prompt changed since you clicked Approve. Not approved; look at the new text, then click Approve again.` };
  }
  if (iface.status === 'approved' && current) return { state: 'done', exitCode: 0, message: `${path} is already approved and current.` };
  const problems = interfaceSchemaProblems(iface);
  if (problems.length) {
    for (const problem of problems) line(stdout, `  ${problem.code}  ${problem.pointer}  ${problem.rule}`);
    return { state: 'declined', exitCode: 4, message: `Fix these in ${path} before you approve.` };
  }
  for (const row of [...describeInterface(path, iface), ...proseView(root, path, text)]) line(stdout, row);
  if (iface.status === 'approved') line(stdout, 'The text changed after it was approved. Read the prompt again before you answer.');
  if (said === undefined) stdout.write(`Approve ${path}? y/n `);
  const answer = said === undefined ? await answers.ask() : "yes";
  if (!/^(?:y|yes)$/i.test(answer.trim())) { line(stdout, ''); return { state: 'declined', exitCode: 1, message: `Not approved: ${path}. Nothing changed.` }; }
  const next = approvePromptText(text);
  if (!next) return { state: 'declined', exitCode: 4, message: `pdd could not set approved in ${path}. Add "prose_sha256": "" to the Runtime interface, then approve again.` };
  if (commit) await commit({ text, next, hash });
  else writeFileSync(join(root, path), next);
  return { state: 'done', exitCode: 0, message: `Approved ${path}.` };
}

// A path that pdd approve may touch: a Git-visible regular *.prompt.md file inside the repo, or null.
export function promptPath(root, cwd, word) {
  const path = relative(root, resolve(realpathSync(cwd), word)).split(sep).join('/');
  let regular = false;
  try { regular = lstatSync(join(root, path)).isFile() && realpathSync(join(root, path)) === join(root, path); } catch { regular = false; }
  return path.endsWith('.prompt.md') && !path.startsWith('..') && regular && gitFiles(root).includes(path) ? path : null;
}

// pdd approve PROMPT. Returns the exit code.
export async function runApprove({ words = [], cwd = process.cwd(), said } = {}, ports = {}) {
  const stdout = ports.stdout ?? process.stdout, stderr = ports.stderr ?? process.stderr, stdin = ports.stdin ?? process.stdin;
  const interactive = ports.interactive ?? (!!process.stdin.isTTY && !!process.stdout.isTTY);
  try {
    if (words.length !== 1) throw new Stop(2, 'Name one prompt: pdd approve prompts/<name>.prompt.md');
    const gitRun = async (args, cwd) => ports.execFile ? ports.execFile('git', args, {cwd,encoding:'utf8'}).then(result => ({...result,status:result.code ?? 0})) : (ports.spawnSync ?? spawnSync)('git', args, {cwd,encoding:'utf8'});
    const top = await gitRun(['rev-parse', '--show-toplevel'], cwd);
    if (top.status !== 0) throw new Stop(2, 'pdd approve works in a Git repository.');
    const root = realpathSync(top.stdout.trim()), path = promptPath(root, cwd, words[0]);
    if (!path) throw new Stop(2, `${relative(root, resolve(realpathSync(cwd), words[0])).split(sep).join('/')} is not a Git-visible *.prompt.md file in this repository.`);
    const { strictApprovals } = readApprovalPolicy({ root }, ports);
    if (said !== undefined && (typeof said !== 'string' || !said.trim())) throw new Stop(2, '--said requires nonblank words.');
    const env = ports.env ?? process.env;
    const agent = approvalActor(env).kind === 'agent';
    // A saved current workflow pane is also an agent environment in strict mode.
    let pane = false;
    if (strictApprovals && env.HERDR_PANE_ID) {
      const { runForWorktree } = await import('./workflow-runs.mjs');
      const run = await runForWorktree(cwd, ports);
      pane = Boolean(run?.chats?.some(chat => chat.paneId === env.HERDR_PANE_ID));
    }
    if (strictApprovals ? said !== undefined || !interactive || agent || pane : said === undefined && !interactive) throw new Stop(2, `pdd approve is for a person at a terminal. Ask the person to run: pdd approve ${path}`);
    const common = await gitRun(['rev-parse', '--path-format=absolute', '--git-common-dir'], root);
    if (common.status !== 0) throw new Stop(4, 'Cannot resolve Git common directory.');
    const commonDir = common.stdout.trim();
    readPromptApprovals({ commonDir }, ports);
    const answers = said === undefined ? lineReader(stdin) : { close() {} };
    const commit = async ({ text, next, hash }) => {
      const fs = ports.fs ?? { writeFileSync };
      const evidence = { id: (ports.randomUUID ?? randomUUID)(), route: said === undefined ? 'terminal' : 'said', actor: approvalActor(env), at: (ports.now ?? Date.now)(), words: said ?? null, prompts: [{ path, proseSha256: hash }] };
      try {
        fs.writeFileSync(join(root, path), next);
        await recordPromptApproval({ commonDir, evidence }, ports);
      } catch (error) {
        try { fs.writeFileSync(join(root, path), text); } catch { throw new Stop(4, `Approval evidence failed; rollback failed for ${path}.`); }
        throw error;
      }
      line(stdout, `${path} ${hash}`);
      line(stdout, `Approval route: ${evidence.route}; actor: ${evidence.actor.kind} ${evidence.actor.id}; at: ${evidence.at}`);
    };
    try {
      const result = await askApproval({ root, path, stdout, answers, said, commit });
      if (result.exitCode === 1) line(stdout, 'Not approved. Nothing changed.');
      else if (result.exitCode === 4 && result.message.startsWith('Fix these')) line(stdout, 'Fix these before you approve.');
      else line(result.exitCode === 4 ? stderr : stdout, result.message);
      return result.exitCode;
    } finally { answers.close(); }
  } catch (error) {
    if (error instanceof Stop) { line(stderr, error.message); return error.exitCode; }
    line(stderr, error.message || 'Approval failed.'); return 4;
  }
}
