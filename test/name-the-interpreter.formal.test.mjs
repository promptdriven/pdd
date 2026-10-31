import test from 'node:test';
import assert from 'node:assert/strict';
import { readdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { PUBLIC_COMMAND_ROUTES } from '../src/command-catalog.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { DEFAULT_RUNTIME_URL, runCheck, runtimeOrigin } from '../src/runtime-client.mjs';
import { summaryLine } from '../src/runtime-output.mjs';
import { TEST_SCHEMA, interfaceBlocks } from '../src/runtime-preflight.mjs';
import { runtimeLines } from '../src/workflow-runner.mjs';
import { harbor, portsFor, root, sink } from './runtime-fake.mjs';

// Bounded check of user_stories/name-the-interpreter.md, Rules to check (RUNBOOK §17).
// Oracle from the Story: pdd's own lines never call the hosted service "PDD runtime" or "the runtime";
// the machine-read words of the keep-list stay where code reads them. "the Runtime interface" (the block) and
// "the Runtime check line" (the summary line) are keep-list names, not the service.
const FORBIDDEN = [/\bPDD runtime\b/i, /\bthe runtime\b(?!\s+(?:interfaces?|check)\b)/i];
// The keep-list server text that pdd detects and prints as the server sent it.
const SERVER_TEXTS = new Set(['The runtime opens soon.']);
const label = argv => JSON.stringify(argv);

function helpArgvs() {
  const prefixes = new Map();
  for (const route of PUBLIC_COMMAND_ROUTES) for (let length = 1; length <= route.prefix.length; length++) {
    const prefix = route.prefix.slice(0, length);
    if (!['help', '--version'].includes(prefix[0])) prefixes.set(prefix.join(' '), prefix);
  }
  const list = [[], ['--help'], ['-h'], ['help']];
  // `sim` is the short form of `simulate`: its help is the same help.
  for (const prefix of [...prefixes.values(), ['sim']]) list.push(['help', ...prefix], [...prefix, '--help'], [...prefix, '-h']);
  return list;
}

test('help: every help argv names the interpreter and keeps "runtime" only for the Runtime interface block', async t => {
  const list = helpArgvs();
  let lines = 0;
  for (const argv of list) {
    const stdout = sink(), stderr = sink();
    assert.equal(await runPdd(argv, { stdout, stderr }), 0, label(argv));
    assert.equal(stderr.text, '', label(argv));
    for (const pattern of [...FORBIDDEN, /\bruntime calls?\b/i]) assert.doesNotMatch(stdout.text, pattern, label(argv));
    for (const match of stdout.text.matchAll(/runtime/gi)) {
      assert.match(stdout.text.slice(match.index), /^runtime\s+interfaces?\b/i, `${label(argv)}: "${stdout.text.slice(match.index - 40, match.index + 40)}"`);
    }
    if (argv.includes('product')) assert.doesNotMatch(stdout.text, /runtime/i, label(argv));
    lines += stdout.text.split('\n').length;
  }
  const rootHelp = sink(); await runPdd(['--help'], { stdout: rootHelp, stderr: sink() });
  assert.match(rootHelp.text, /PDD interpreter/, 'the root help names the interpreter');
  const simulateHelp = sink(); await runPdd(['simulate', '--help'], { stdout: simulateHelp, stderr: sink() });
  assert.match(simulateHelp.text, /PDD Simulator/, 'the simulate help names the Simulator');
  t.diagnostic(`bounds: ${list.length} help argv, ${lines} help lines`);
});

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
const sourceFiles = () => [
  ...readdirSync(join(root, 'src')).filter(name => name.endsWith('.mjs')).map(name => join('src', name)),
  ...readdirSync(join(root, 'bin')).filter(name => name.endsWith('.mjs')).map(name => join('bin', name))];

test('pdd\'s own strings: no string literal in src or bin calls the service "PDD runtime" or "the runtime"', t => {
  let strings = 0, found = 0, files = 0;
  for (const file of sourceFiles()) {
    const source = readFileSync(join(root, file), 'utf8'), list = tokens(source); files++;
    strings += list.filter(token => token.kind === 'string').length;
    // Each place where a forbidden word stands in the file must be a comment, a regex or a keep-list server text.
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
  t.diagnostic(`bounds: ${files} files, ${strings} string literals; ${found} forbidden-word places, all in comments, regexes or the keep-list server text`);
});

// The keep-list: each machine-read word, checked where code reads it.
const sourceOf = file => readFileSync(join(root, 'src', file), 'utf8');
test('keep-list: schema ids, host, setting, folder, block label and gate text stay; the Prompt tests line reads old lines', async t => {
  // Schema ids `prompt-runtime.*`: tests are still found by their schema id; the app map id stays where it is read.
  assert.equal(TEST_SCHEMA, 'prompt-runtime.program-scenario.v1');
  for (const file of ['runtime-client.mjs', 'workflow-view.mjs']) assert.ok(sourceOf(file).includes('\'prompt-runtime.app-map.v1\''), file);
  const setup = harbor(t), files = sink();
  assert.equal(await runPdd(['test', '--files'], { stdout: files, stderr: sink(), cwd: setup.repo, env: { HOME: setup.home, PDD_STATE_DIR: setup.state, PATH: '/usr/bin:/bin' } }), 0);
  assert.match(files.text, /tests\/place-order\.json/);
  // The default host and the setting name. Only src/runtime-client.mjs writes the host (RUNTIME-ADDRESS1),
  // so this check reads it from there: the host still starts with the word "runtime".
  const host = new URL(DEFAULT_RUNTIME_URL);
  assert.equal(host.protocol, 'https:');
  assert.equal(host.hostname.split('.')[0], 'runtime');
  assert.ok(host.hostname.endsWith('.promptdriven.ai'), host.hostname);
  assert.equal(runtimeOrigin({}), DEFAULT_RUNTIME_URL);
  assert.equal(runtimeOrigin({ PDD_RUNTIME_URL: 'https://other.example' }), 'https://other.example');
  // The folder ~/.pdd/runtime, in each module that builds it.
  for (const [file, words] of [['runtime-client.mjs', '\'.pdd\', \'runtime\''], ['runtime-slots.mjs', '\'.pdd\', \'runtime\''],
    ['agent-project.mjs', '\'.pdd/runtime\''], ['agent-adapters.mjs', '\'.pdd\',\'runtime\'']]) assert.ok(sourceOf(file).includes(words), file);
  // The block label: pdd finds a `Runtime interface` block, and its messages name the block.
  const block = label => `# A prompt\n\n<details><summary>${label}</summary>\n\n\`\`\`json\n{"status": "draft"}\n\`\`\`\n</details>\n`;
  assert.equal(interfaceBlocks(block('Runtime interface')).length, 1);
  assert.equal(interfaceBlocks(block('Interpreter interface')).length, 0);
  for (const file of ['runtime-preflight.mjs', 'prompt-approve.mjs']) assert.ok(tokens(sourceOf(file)).some(token => token.kind === 'string'
    && sourceOf(file).slice(token.start, token.end).includes('Runtime interface')), file);
  // The `Prompt tests (story): ...` line that pdd writes is the line that the PR reader reads; an older `Runtime check` line reads the same way.
  const line = summaryLine([{ story: 'place-order', state: 'passed', criteria: { passed: 1, total: 1 }, checks: { passed: 1, total: 1 }, calls: 1 }], 'place-order');
  assert.match(line, /^Prompt tests \(place-order\): /);
  for (const text of [line, line.replace('Prompt tests', 'Runtime check')]) assert.deepEqual(runtimeLines(text).map(item => [item.story, item.pass]), [['place-order', true]]);
  assert.match(sourceOf('workflow-view.mjs'), /PROMPT_TESTS_WORDS/);
  // The gate answer "The runtime opens soon." is still detected, and a server text is printed as the server sent it.
  const said = [];
  for (const [status, text, json] of [[503, 'The runtime opens soon.'], [429, null, { error: { code: 'other', message: 'The runtime is busy. Try again later.' } }], [503, 'Other text.']]) {
    const run = harbor(t); let requests = 0;
    const fetch = async () => { requests++; return json ? Response.json(json, { status }) : new Response(text, { status, headers: { 'content-type': 'text/plain' } }); };
    const { ports } = portsFor({ HOME: run.home, PDD_STATE_DIR: run.state, PDD_RUNTIME_URL: 'http://127.0.0.1:9' }, { fetch });
    const code = await runCheck({ words: ['place-order'], cwd: run.repo, options: {} }, ports);
    said.push({ code, requests, out: ports.stdout.text + ports.stderr.text });
  }
  // The gate stops at the first answer; another 503 text is not the gate.
  assert.equal(said[0].code, 5, said[0].out); assert.equal(said[0].requests, 1, said[0].out); assert.ok(said[0].out.includes('The runtime opens soon.'), said[0].out);
  assert.equal(said[1].code, 5, said[1].out); assert.ok(said[1].out.includes('The runtime is busy. Try again later.'), said[1].out);
  assert.notEqual(said[2].code, 5, said[2].out); assert.ok(said[2].requests > 1, said[2].out);
  t.diagnostic('bounds: 6 keep-list words (schema ids: 2, host, setting, folder: 4 readers, block label, gate text), the Prompt tests line with both labels and 1 server text');
});
