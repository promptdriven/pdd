import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readdirSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { PUBLIC_COMMAND_ROUTES } from '../src/command-catalog.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { summaryLine } from '../src/runtime-seam.mjs';
import { runtimeLines } from '../src/workflow-runner.mjs';
import { harbor, root, sink } from './helpers/runtime-fake.mjs';

// Bounded check of user_stories/name-the-interpreter.md, Rules to check (RUNBOOK §17).
const FORBIDDEN = [/\bPDD runtime\b/i, /\bthe runtime\b(?!\s+(?:interfaces?|check)\b)/i];
const SERVER_TEXTS = new Set(['The runtime opens soon.']);
const label = argv => JSON.stringify(argv);

function helpArgvs() {
  const prefixes = new Map();
  for (const route of PUBLIC_COMMAND_ROUTES) for (let length = 1; length <= route.prefix.length; length++) {
    const prefix = route.prefix.slice(0, length);
    if (!['help', '--version'].includes(prefix[0])) prefixes.set(prefix.join(' '), prefix);
  }
  const list = [[], ['--help'], ['-h'], ['help']];
  for (const prefix of [...prefixes.values(), ['sim']]) list.push(['help', ...prefix], [...prefix, '--help'], [...prefix, '-h']);
  return list;
}

test('help: every help argv names the interpreter and keeps "runtime" only for the Runtime interface block', async t => {
  const packageRoot = '/pdd-test-package';
  const list = helpArgvs();
  let lines = 0;
  for (const argv of list) {
    const stdout = sink(), stderr = sink();
    assert.equal(await runPdd(argv, { stdout, stderr, packageRoot }), 0, label(argv));
    assert.equal(stderr.text, '', label(argv));
    for (const pattern of [...FORBIDDEN, /\bruntime calls?\b/i]) assert.doesNotMatch(stdout.text, pattern, label(argv));
    for (const match of stdout.text.matchAll(/runtime/gi)) {
      assert.match(stdout.text.slice(match.index), /^runtime\s+interfaces?\b/i, `${label(argv)}: "${stdout.text.slice(match.index - 40, match.index + 40)}"`);
    }
    if (argv.includes('product')) assert.doesNotMatch(stdout.text, /runtime/i, label(argv));
    lines += stdout.text.split('\n').length;
  }
  const rootHelp = sink(); await runPdd(['--help'], { stdout: rootHelp, stderr: sink(), packageRoot });
  assert.match(rootHelp.text, /PDD interpreter/, 'the root help names the interpreter');
  const simulateHelp = sink(); await runPdd(['simulate', '--help'], { stdout: simulateHelp, stderr: sink(), packageRoot });
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

test('pdd\'s own strings: no string literal in host src or bin calls the service "PDD runtime" or "the runtime"', t => {
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
  t.diagnostic(`bounds: ${files} files, ${strings} string literals; ${found} forbidden-word places, all in comments, regexes or the keep-list server text`);
});

const sourceOf = file => readFileSync(join(root, 'src', file), 'utf8');
test('keep-list (host): workflow schema id, CLI test --files, approval block label and Prompt tests line stay', async t => {
  assert.ok(sourceOf('workflow-view.mjs').includes('\'prompt-runtime.app-map.v1\''), 'workflow-view.mjs');
  const setup = harbor(t), files = sink();
  assert.equal(await runPdd(['test', '--files'], { stdout: files, stderr: sink(), cwd: setup.repo, env: { HOME: setup.home, PDD_STATE_DIR: setup.state, PATH: '/usr/bin:/bin' } }), 0);
  assert.match(files.text, /tests\/place-order\.json/);
  assert.ok(tokens(sourceOf('prompt-approve.mjs')).some(token => token.kind === 'string'
    && sourceOf('prompt-approve.mjs').slice(token.start, token.end).includes('Runtime interface')), 'prompt-approve.mjs');
  const line = summaryLine([{ story: 'place-order', state: 'passed', criteria: { passed: 1, total: 1 }, checks: { passed: 1, total: 1 }, calls: 1 }], 'place-order');
  assert.match(line, /^Prompt tests \(place-order\): /);
  for (const text of [line, line.replace('Prompt tests', 'Runtime check')]) assert.deepEqual(runtimeLines(text).map(item => [item.story, item.pass]), [['place-order', true]]);
  assert.match(sourceOf('workflow-view.mjs'), /PROMPT_TESTS_WORDS/);
});
