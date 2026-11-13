import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { DEFAULT_RUNTIME_URL, runtimeOrigin } from '../../src/runtime/runtime-client.mjs';
import { TEST_SCHEMA, interfaceBlocks } from '../../src/runtime/runtime-preflight.mjs';
import { runCheck } from '../../src/runtime-seam.mjs';
import { harbor, portsFor, root } from './runtime-fake.mjs';

const FORBIDDEN = [/\bPDD runtime\b/i, /\bthe runtime\b(?!\s+(?:interfaces?|check)\b)/i];
const SERVER_TEXTS = new Set(['The runtime opens soon.']);

// Split a source into tokens: comments, regex literals, quoted strings and the static parts of template literals.
function tokens(source) {
  const out = [], stack = []; let i = 0, prev = '';
  const end = (from, char) => { const at = source.indexOf(char, from); if (at < 0) throw new Error(`unterminated at ${from}`); return at; };
  const regexOk = () => !prev || /^[(,=:[!&|?{};+\-*%<>~^]$/.test(prev) || /^(return|typeof|case|in|of|delete|void|throw|new|else|do|yield|await)$/.test(prev);
  const quoted = (from, close) => {
    let j = from;
    while (source[j] !== close && !(close === '`' && source[j] === '$' && source[j + 1] === '{')) {
      if (j >= source.length) throw new Error(`unterminated string at ${from}`);
      j += source[j] === '\\' ? 2 : 1;
    }
    return j;
  };
  while (i < source.length) {
    const c = source[i], d = source[i + 1];
    if (c === '/' && d === '/') { const j = source.indexOf('\n', i); const stop = j < 0 ? source.length : j; out.push({ kind: 'comment', start: i, end: stop }); i = stop; continue; }
    if (c === '/' && d === '*') { const j = end(i + 2, '*/') + 2; out.push({ kind: 'comment', start: i, end: j }); i = j; continue; }
    if (c === '\'' || c === '"') { const j = quoted(i + 1, c); out.push({ kind: 'string', start: i + 1, end: j }); i = j + 1; prev = 'string'; continue; }
    if (c === '`' || (c === '}' && stack.at(-1) === 0)) {
      if (c === '}') stack.pop();
      const j = quoted(i + 1, '`'); out.push({ kind: 'string', start: i + 1, end: j });
      if (source[j] === '`') { i = j + 1; prev = 'string'; } else { stack.push(0); i = j + 2; prev = '('; }
      continue;
    }
    if (c === '{' || c === '}') { if (stack.length) stack[stack.length - 1] += c === '{' ? 1 : -1; i++; prev = c; continue; }
    if (c === '/' && regexOk()) {
      let j = i + 1, inClass = false;
      while (inClass || source[j] !== '/') {
        if (j >= source.length || source[j] === '\n') throw new Error(`unterminated regex at ${i}`);
        if (source[j] === '\\') j++; else if (source[j] === '[') inClass = true; else if (source[j] === ']') inClass = false;
        j++;
      }
      j++; while (/[a-z]/.test(source[j] ?? '')) j++;
      out.push({ kind: 'regex', start: i, end: j }); i = j; prev = 'regex'; continue;
    }
    if (/\s/.test(c)) { i++; continue; }
    if (/[A-Za-z0-9_$]/.test(c)) { let j = i; while (/[A-Za-z0-9_$]/.test(source[j] ?? '')) j++; prev = source.slice(i, j); i = j; continue; }
    prev = c; i++;
  }
  assert.equal(stack.length, 0, 'every template literal closes');
  return out;
}
const sourceFiles = () => readdirSync(join(root, 'src/runtime'))
  .filter(name => name.endsWith('.mjs'))
  .map(name => join('src/runtime', name));

test('runtime strings: no string literal in src/runtime calls the service "PDD runtime" or "the runtime"', t => {
  let strings = 0, found = 0, files = 0;
  for (const file of sourceFiles()) {
    const source = readFileSync(join(root, file), 'utf8'), list = tokens(source); files++;
    strings += list.filter(token => token.kind === 'string').length;
    for (const pattern of FORBIDDEN) for (const match of source.matchAll(new RegExp(pattern.source, 'gi'))) {
      found++;
      const token = list.find(item => item.start <= match.index && match.index < item.end);
      const where = `${file}:${source.slice(0, match.index).split('\n').length}`;
      assert.ok(token, `${where}: "${match[0]}" outside any token`);
      if (token.kind === 'string') assert.ok(SERVER_TEXTS.has(source.slice(token.start, token.end)), `${where}: "${source.slice(token.start, token.end)}"`);
    }
  }
  const all = sourceFiles().flatMap(file => { const source = readFileSync(join(root, file), 'utf8'); return tokens(source).filter(token => token.kind === 'string').map(token => source.slice(token.start, token.end)); });
  assert.ok(all.some(text => text.includes('PDD interpreter')), 'the scan sees the interpreter strings');
  assert.ok(strings > 5000, 'the scan reads the string literals');
  t.diagnostic(`bounds: ${files} files, ${strings} string literals; ${found} forbidden-word places`);
});

const sourceOf = file => readFileSync(join(root, 'src/runtime', file), 'utf8');
test('keep-list (runtime): schema ids, host, setting, folder, block label and gate text stay', async t => {
  assert.equal(TEST_SCHEMA, 'prompt-runtime.program-scenario.v1');
  assert.ok(sourceOf('runtime-client.mjs').includes('\'prompt-runtime.app-map.v1\''), 'runtime-client.mjs');
  const host = new URL(DEFAULT_RUNTIME_URL);
  assert.equal(host.protocol, 'https:');
  assert.equal(host.hostname.split('.')[0], 'runtime');
  assert.ok(host.hostname.endsWith('.promptdriven.ai'), host.hostname);
  assert.equal(runtimeOrigin({}), DEFAULT_RUNTIME_URL);
  assert.equal(runtimeOrigin({ PDD_RUNTIME_URL: 'https://other.example' }), 'https://other.example');
  for (const [file, words] of [['runtime-client.mjs', '\'.pdd\', \'runtime\''], ['runtime-slots.mjs', '\'.pdd\', \'runtime\''],
    ['agent-project.mjs', '\'.pdd/runtime\''], ['agent-ask.mjs', '\'.pdd\',\'runtime\'']]) assert.ok(sourceOf(file).includes(words), file);
  const block = label => `# A prompt\n\n<details><summary>${label}</summary>\n\n\`\`\`json\n{"status": "draft"}\n\`\`\`\n</details>\n`;
  assert.equal(interfaceBlocks(block('Runtime interface')).length, 1);
  assert.equal(interfaceBlocks(block('Interpreter interface')).length, 0);
  assert.ok(tokens(sourceOf('runtime-preflight.mjs')).some(token => token.kind === 'string'
    && sourceOf('runtime-preflight.mjs').slice(token.start, token.end).includes('Runtime interface')), 'runtime-preflight.mjs');
  const said = [];
  for (const [status, text, json] of [[503, 'The runtime opens soon.'], [429, null, { error: { code: 'other', message: 'The runtime is busy. Try again later.' } }], [503, 'Other text.']]) {
    const run = harbor(t); let requests = 0;
    const fetch = async () => { requests++; return json ? Response.json(json, { status }) : new Response(text, { status, headers: { 'content-type': 'text/plain' } }); };
    const { ports } = portsFor({ HOME: run.home, PDD_STATE_DIR: run.state, PDD_RUNTIME_URL: 'http://127.0.0.1:9' }, { fetch });
    const code = await runCheck({ words: ['place-order'], cwd: run.repo, options: status === 503 && text === 'Other text.' ? { '--timeout': 1 } : {} }, ports);
    said.push({ code, requests, out: ports.stdout.text + ports.stderr.text });
  }
  assert.equal(said[0].code, 5, said[0].out); assert.equal(said[0].requests, 1, said[0].out); assert.ok(said[0].out.includes('The runtime opens soon.'), said[0].out);
  assert.equal(said[1].code, 5, said[1].out); assert.ok(said[1].out.includes('The runtime is busy. Try again later.'), said[1].out);
  assert.notEqual(said[2].code, 5, said[2].out); assert.ok(said[2].requests > 1, said[2].out);
});
