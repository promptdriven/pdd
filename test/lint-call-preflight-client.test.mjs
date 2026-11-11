import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, mkdirSync, writeFileSync } from 'node:fs';
import { spawn } from 'node:child_process';
import { join } from 'node:path';
import { parseArgv } from '../src/argument-parser.mjs';
import { renderHelp, runPdd } from '../src/pdd-cli.mjs';
import { runCheck } from '../src/runtime-client.mjs';
import { client } from './runtime-compatibility/replay.mjs';
import { harbor, portsFor, root, TOKEN } from './runtime-fake.mjs';

const scenario = JSON.parse(readFileSync(new URL('./runtime/lint-call-preflight.json', import.meta.url)));
const features = ['lint-tests', 'lint-call-preflight'];
const capacity = featureList => ({ status: 200, json: { maintenance: null, features: featureList } });

test('issue820: modern lint accepts cap 25 and advertises zero-AI preflight', () => {
  let plan;
  assert.doesNotThrow(() => { plan = parseArgv(['lint', 'place-order', '--max-calls', '25']); }, 'issue820: lint must accept a selected call cap before paid work');
  assert.deepEqual(plan.options, { '--lint': true, '--max-calls': '25' });
  assert.match(renderHelp(['lint']), /--max-calls N/);
  assert.equal(parseArgv(['test', '--lint', '--max-calls', '25']).options['--max-calls'], '25');
});

test('issue820: cap validation and forbidden mixes fail before capture or network', async t => {
  const h = harbor(t), p = portsFor({ HOME: h.home, PDD_STATE_DIR: h.state }, {
    captureSource() { assert.fail('invalid cap or combination must not capture'); },
    gh() { assert.fail('invalid cap or combination must not authenticate'); },
    fetch() { assert.fail('invalid cap or combination must not contact Runtime'); },
  });
  for (const value of [0, 1001, -1, 1.5, NaN, null, '', '01', '1e2', true]) {
    assert.equal(await runCheck({ cwd: h.repo, words: ['place-order'], options: { '--lint': true, '--max-calls': value } }, p.ports), 2, String(value));
  }
  for (const mode of ['--local', '--files', '--fill-hash', '--read', '--explain-bindings']) {
    assert.equal(await runCheck({ cwd: h.repo, options: { '--lint': true, '--max-calls': 25, [mode]: true } }, p.ports), 2, mode);
  }
  for (const value of ['0', '1001', '-1', '1.5', '01', '1e2']) assert.throws(() => parseArgv(['lint', '--max-calls', value]));
  for (const value of ['1', '1000']) assert.equal(parseArgv(['lint', '--max-calls', value]).options['--max-calls'], value);
  const out = { write() {} }, err = { text: '', write(value) { this.text += value; } };
  assert.equal(await runPdd(['check', '--max-calls', '25'], { stdout: out, stderr: err }), 2);
  assert.match(err.text, /was removed/);
});

for (const mode of ['warning', 'within', 'unknown', 'mismatch']) test(`issue820: lint forwards selected cap and preserves ${mode} server facts`, async t => {
  const vector = scenario.steps.find(step => step.step_id === mode);
  const raw = structuredClone(vector.input.preflight);
  raw.future_server_fact = { retained: true };
  let context;
  const c = await client(t, { lintEdit(answer) {
    const post = c.f.posts.find(post => post.request.requestId === answer.requestId);
    context = { ...vector.input.context, source_sha256: mode === 'mismatch' ? 'd'.repeat(64) : post.request.source_sha256 };
    answer.max_calls = 0; answer.selected_max_calls = 25;
    answer.result.call_preflight_context = context;
    answer.result.report.lint.call_preflight_context = structuredClone(context);
    answer.result.report.lint.tests[0].call_preflight = structuredClone(raw);
    answer.result.tests = structuredClone(answer.result.report.lint.tests);
  } });
  c.f.capacity = () => capacity(features);
  const result = await c.run('lint', { '--max-calls': '25' });
  assert.equal(result.code, 0, result.err + result.out);
  assert.equal(c.f.posts.length, 1); assert.equal(c.f.posts[0].command, 'lint');
  assert.equal(c.f.posts[0].request.max_calls, 25, 'cap must reach the zero-AI lint request unchanged');
  assert.deepEqual(result.json.rows[0].call_preflight, raw, 'JSON must retain exact server facts and future keys');
  assert.deepEqual(result.json.call_preflight_context, context);
  assert.equal(result.json.call_preflight_requested_cap, 25);
  assert.equal(c.saved(result).answer.max_calls, 0, 'selected analysis cap does not become an execution budget');
  assert.equal(c.saved(result).answer.selected_max_calls, 25);
  assert.equal(c.saved(result).batch.intent, 'lint-only');
  assert.equal(c.saved(result).batch.rows[0].max_calls, undefined, 'lint cap cannot establish paid intent');
  for (const json of [false, true]) {
    const read = await c.run('check', { '--read': result.json.batch, '--json': json }, []);
    assert.equal(read.code, 0, read.err + read.out);
    if (json) {
      assert.deepEqual(read.json.rows[0].call_preflight, raw);
      assert.deepEqual(read.json.call_preflight_context, context);
      assert.equal(read.json.call_preflight_requested_cap, 25);
    } else {
      assert.match(read.out, /no guarantee of actual calls or completion/);
      assert.match(read.out, /resource continuations are not included/);
      assert.ok(read.out.includes(context.source_sha256)); assert.ok(read.out.includes(context.engine_build));
      if (mode === 'warning') assert.match(read.out, /Warning:.*exceeds.*cap is unchanged/);
      if (mode === 'within') assert.match(read.out, /within-estimate; structural catalog estimate 20 calls/);
      if (mode === 'unknown') assert.match(read.out, /unknown; structural catalog estimate unknown calls/);
      if (mode === 'mismatch') assert.match(read.out, /unavailable; no estimate or cap-fit claim/);
    }
  }
  assert.equal(c.f.posts.length, 1, 'saved standalone lint reads never start paid work or repeat lint');
});

test('issue820: existing test --lint alias forwards the selected cap without paid intent', async t => {
  const plan = parseArgv(['test', 'place-order', '--lint', '--max-calls', '5', '--json']);
  const modern = parseArgv(['lint', 'place-order', '--max-calls', '5', '--json']);
  assert.deepEqual(plan.options, modern.options);
  assert.deepEqual(plan.operands, modern.operands);
  const c = await client(t);
  c.f.capacity = () => capacity(features);
  const result = await c.run('check', plan.options, plan.operands);
  assert.equal(result.code, 0, result.err + result.out);
  assert.deepEqual(c.f.posts.map(post => [post.command, post.request.max_calls]), [['lint', 5]]);
  assert.equal(result.json.call_preflight_requested_cap, 5);
  assert.equal(c.saved(result).batch.intent, 'lint-only');
  assert.equal(c.saved(result).batch.rows[0].max_calls, undefined, 'the alias cannot establish paid intent');
});

for (const argv of [['lint'], ['test', '--lint']]) test(`issue820: old server refuses a selected cap for ${argv.join(' ')} before lint and ordinary lint still works`, async t => {
  const c = await client(t);
  c.f.capacity = () => capacity(['lint-tests']);
  const plan = parseArgv([...argv, 'place-order', '--max-calls', '25']);
  const selected = await c.run('check', plan.options, plan.operands);
  assert.equal(selected.code, 4, selected.err + selected.out);
  assert.match(selected.out, /lint-call-preflight-unsupported/);
  assert.match(selected.out, /does not support selected-cap call preflight/);
  assert.equal(c.f.posts.length, 0, 'unsupported preflight cannot silently discard the cap');
  const ordinary = await c.run('lint');
  assert.equal(ordinary.code, 0, ordinary.err + ordinary.out);
  assert.equal(Object.hasOwn(c.f.posts[0].request, 'max_calls'), false);
  assert.equal(ordinary.json.rows[0].call_preflight, null);
});

// Run the actual candidate bin in a child process. Only gh and HTTP are controlled.
test('issue820: actual candidate CLI sends cap-aware lint without a paid request', async t => {
  const c = await client(t, { lintEdit(answer) {
    const post = c.f.posts.find(post => post.request.requestId === answer.requestId);
    answer.result.call_preflight_context = { ...scenario.steps[0].input.context, source_sha256: post.request.source_sha256 };
    answer.result.report.lint.tests[0].call_preflight = structuredClone(scenario.steps[0].input.preflight);
  } });
  c.f.capacity = () => capacity(features);
  const fakeBin = join(c.h.sandbox, 'bin'); mkdirSync(fakeBin);
  writeFileSync(join(fakeBin, 'gh'), '#!/bin/sh\ncase "$1" in\n  auth) printf "%s\\n" "' + TOKEN + '" ;;\n  api) printf "%s\\n" "tester 123" ;;\n  *) exit 1 ;;\nesac\n', { mode: 0o700 });
  const env = { ...process.env, HOME: c.h.home, XDG_CONFIG_HOME: join(c.h.home, '.config'),
    PATH: fakeBin + ':' + process.env.PATH, PDD_STATE_DIR: c.h.state, PDD_RUNTIME_URL: c.f.origin };
  for (const key of ['GH_TOKEN', 'GITHUB_TOKEN', 'GH_CONFIG_DIR', 'CLAUDE_CONFIG_DIR', 'PDD_VM_SUITE_LOCK']) delete env[key];
  const result = await new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [join(root, 'bin/pdd.mjs'), 'lint', 'place-order', '--max-calls', '25', '--json'], { cwd: c.h.repo, env });
    let out = '', err = ''; child.stdout.on('data', chunk => { out += chunk; }); child.stderr.on('data', chunk => { err += chunk; });
    child.on('error', reject); child.on('close', (code, signal) => resolve({ code, signal, out, err }));
    const timer = setTimeout(() => child.kill(), 15000); child.on('close', () => clearTimeout(timer));
  });
  assert.equal(result.signal, null); assert.equal(result.code, 0, result.err + result.out);
  const report = JSON.parse(result.out);
  assert.equal(report.rows[0].call_preflight.status, 'warning');
  assert.equal(report.call_preflight_requested_cap, 25);
  assert.deepEqual(c.f.posts.map(post => [post.command, post.request.max_calls]), [['lint', 25]]);
  assert.ok(!(result.out + result.err).includes(TOKEN));
});
