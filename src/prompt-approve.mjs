// Generated from prompts/cli/prompt-approve.prompt.md (sha256: 95717c7bdc02fe786a618fd5557ed4994cc9d24fda730cfd92e48c8df78e6872).
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
export async function askApproval({ root, path, stdout, answers, expectedHash }) {
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
  for (const row of describeInterface(path, iface)) line(stdout, row);
  if (iface.status === 'approved') line(stdout, 'The text changed after it was approved. Read the prompt again before you answer.');
  stdout.write(`Approve ${path}? y/n `);
  const answer = await answers.ask();
  if (!/^(?:y|yes)$/i.test(answer.trim())) { line(stdout, ''); return { state: 'declined', exitCode: 1, message: `Not approved: ${path}. Nothing changed.` }; }
  const next = approvePromptText(text);
  if (!next) return { state: 'declined', exitCode: 4, message: `pdd could not set approved in ${path}. Add "prose_sha256": "" to the Runtime interface, then approve again.` };
  writeFileSync(join(root, path), next);
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
export async function runApprove({ words = [], cwd = process.cwd() } = {}, ports = {}) {
  const stdout = ports.stdout ?? process.stdout, stderr = ports.stderr ?? process.stderr, stdin = ports.stdin ?? process.stdin;
  const interactive = ports.interactive ?? (!!process.stdin.isTTY && !!process.stdout.isTTY);
  try {
    if (words.length !== 1) throw new Stop(2, 'Name one prompt: pdd approve prompts/<name>.prompt.md');
    const top = spawnSync('git', ['rev-parse', '--show-toplevel'], { cwd, encoding: 'utf8' });
    if (top.status !== 0) throw new Stop(2, 'pdd approve works in a Git repository.');
    const root = realpathSync(top.stdout.trim()), path = promptPath(root, cwd, words[0]);
    if (!path) throw new Stop(2, `${relative(root, resolve(realpathSync(cwd), words[0])).split(sep).join('/')} is not a Git-visible *.prompt.md file in this repository.`);
    if (!interactive) throw new Stop(2, `pdd approve is for a person at a terminal. Ask the person to run: pdd approve ${path}`);
    const answers = lineReader(stdin);
    try {
      const result = await askApproval({ root, path, stdout, answers });
      if (result.exitCode === 1) line(stdout, 'Not approved. Nothing changed.');
      else if (result.exitCode === 4 && result.message.startsWith('Fix these')) line(stdout, 'Fix these before you approve.');
      else line(result.exitCode === 4 ? stderr : stdout, result.message);
      return result.exitCode;
    } finally { answers.close(); }
  } catch (error) {
    if (error instanceof Stop) { line(stderr, error.message); return error.exitCode; }
    throw error;
  }
}
