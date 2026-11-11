import test from 'node:test';
import assert from 'node:assert/strict';
import { spawn } from 'node:child_process';
import { mkdirSync, readFileSync, unlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { outcomeFor, outcomeExitCode } from '../src/runtime/runtime-outcome.mjs';
import { projectAnswer } from '../src/runtime/runtime-output.mjs';
import { harbor, fakeRuntime, TOKEN, PLACE } from './runtime-fake.mjs';
import { client, pure, TEST } from './runtime-compatibility/replay.mjs';

// Native regressions for approved malformed-hold, bounded display and saved-source
// rules. Synthetic loopback reports exercise the real CLI, never a live engine.
const CLI = fileURLToPath(new URL('../bin/pdd.mjs', import.meta.url));
const HOST_PATH = '/srv/private/coverage-source';
const BODY = 'synthetic private coverage fixture body';
const MARKER = 'NESTED_MALFORMED_REPORT';
const paid = f => f.posts.filter(post => ['check', 'try'].includes(post.command));

async function cliFixture(t, edit) {
  const h = harbor(t), bin = join(h.sandbox, 'bin'); mkdirSync(bin);
  writeFileSync(join(bin, 'gh'), `#!/bin/sh\nif [ "$1" = auth ]; then echo ${TOKEN}; else echo "octo 4242"; fi\n`, { mode: 0o700 });
  const f = await fakeRuntime(t, (entry, fake) => {
    assert.equal(entry.command, 'lint', 'held selected work cannot dispatch a paid POST');
    const answer = fake.lint(entry.request.requestId);
    const wire = edit(answer);
    return wire ? { status: 200, text: wire } : { status: 200, json: answer };
  });
  async function run(args) {
    const proc = spawn(process.execPath, [CLI, ...args], { cwd: h.repo,
      env: { ...process.env, HOME: h.home, PDD_STATE_DIR: h.state, PDD_RUNTIME_URL: f.origin, PATH: bin + ':' + process.env.PATH },
      stdio: ['ignore', 'pipe', 'pipe'] });
    t.after(() => { if (proc.exitCode === null) proc.kill(); });
    let out = '', err = '';
    proc.stdout.on('data', chunk => out += chunk); proc.stderr.on('data', chunk => err += chunk);
    const code = await new Promise((resolve, reject) => { proc.on('error', reject); proc.on('close', resolve); });
    return { code, out, err };
  }
  return { h, f, run };
}

for (const [delivery, value] of [['top', true], ['top', false], ['legacy', false], ['top', { secret: TOKEN, path: HOST_PATH, fixture_body: BODY }],
  ['legacy', { secret: TOKEN, path: HOST_PATH, fixture_body: BODY }]]) {
  test(`COMPAT real lint CLI exposes only Boolean inventory coverage (${delivery}/${typeof value === 'boolean' ? value : 'malformed'})`, { timeout: 30000 }, async t => {
    const c = await cliFixture(t, answer => {
      delete answer.result.capabilities_complete;
      if (delivery === 'top') answer.result.capabilities_complete = value;
      else answer.result.report.lint.capabilities_complete = value;
    });
    for (const json of [true, false]) {
      const r = await c.run(['lint', 'place-order', ...(json ? ['--json'] : [])]);
      assert.equal(r.code, 0, r.err);
      for (const privateValue of [TOKEN, HOST_PATH, BODY]) assert.ok(!(r.out + r.err).includes(privateValue), 'COMPAT coverage must not publish arbitrary wire content');
      if (json) {
        const view = JSON.parse(r.out);
        assert.equal(view.capabilities_complete, typeof value === 'boolean' ? value : null);
        assert.equal(view.rows[0].state, 'passed');
        assert.equal(view.rows[0].compatibility.association, 'matched', 'envelope coverage cannot replace selected support');
      } else if (typeof value === 'boolean') assert.match(r.out, new RegExp(`Capability inventory complete: ${value}\\.`));
      else assert.doesNotMatch(r.out, /Capability inventory complete:/);
    }
    assert.equal(c.f.posts.length, 2); assert.equal(paid(c.f).length, 0);
  });
}

const malformedPlaces = {
  extra: report => { report.extra = MARKER; },
  identity: report => { report.operations[0].selection.node_id = MARKER; },
  reason: report => { report.operations[0].reason_code = MARKER; },
};
for (const [place, edit] of Object.entries(malformedPlaces)) {
  test(`COMPAT deep malformed ${place} ends held through outcome and projection`, t => {
    const p = pure(t);
    // Mutate transport data, retaining the original independent expected outcome.
    edit(p.report);
    const wire = JSON.stringify(p.answer).split(JSON.stringify(MARKER)).join('['.repeat(5000) + '0' + ']'.repeat(5000));
    const answer = JSON.parse(wire), outcome = outcomeFor(answer, p.options);
    assert.equal(outcome.state, 'not_run', 'COMPAT malformed selected evidence is held, never a crash or support');
    assert.equal(outcomeExitCode([outcome]), 5);
    assert.equal(outcome.compatibility.issue, 'capability-report-unavailable');
    assert.equal(outcome.compatibility.reported.complete, true, 'independently valid coverage metadata is retained');
    assert.equal(outcome.compatibility.reported.engine_build, p.report.engine_build);
    assert.deepEqual(outcome.compatibility.reported.source, p.report.source, 'safe closed source facts survive malformed rows');
    assert.ok(!Object.hasOwn(outcome.compatibility.reported, 'operations'));
    const view = projectAnswer(answer, p.options);
    assert.equal(view.state, 'not_run'); assert.equal(view.compatibility.state, 'unknown');
    assert.doesNotThrow(() => JSON.stringify(view));
  });
  for (const command of ['lint', 'test']) test(`COMPAT real ${command} CLI holds deep malformed ${place} with valid JSON and no paid work`, { timeout: 30000 }, async t => {
    const c = await cliFixture(t, answer => {
      // Deliver only one report too: even a self-comparison must not traverse
      // arbitrary nesting before checking the closed wire shape.
      delete answer.result.report.lint.tests[0].capabilities;
      edit(answer.result.capabilities[0].report);
      return JSON.stringify(answer).replace(JSON.stringify(MARKER), '['.repeat(3000) + '0' + ']'.repeat(3000));
    });
    const r = await c.run([command, 'place-order', '--json']);
    assert.equal(r.code, 5, r.err);
    const view = JSON.parse(r.out);
    assert.equal(view.exit_code, 5); assert.equal(view.rows[0].state, 'not run');
    assert.equal(view.rows[0].compatibility.state, 'unknown');
    assert.equal(view.rows[0].compatibility.issue, 'capability-report-unavailable');
    assert.equal(view.rows[0].compatibility.reported.complete, true);
    assert.doesNotMatch(r.err, /internal error|Maximum call stack|Still running/);
    assert.equal(c.f.posts.length, 1); assert.equal(paid(c.f).length, 0);
    if (command === 'test') {
      assert.equal(view.rows[0].request_id, null); assert.equal(view.rows[0].calls, 0);
      const saved = JSON.parse(readFileSync(join(c.h.state, 'batches', view.batch, 'batch.json')));
      assert.deepEqual(saved.rows[0].request_ids, []);
    }
  });
}

test('COMPAT duplicate deliveries ignore object key order and preserve valid conflict semantics', t => {
  const p = pure(t), copy = JSON.parse(JSON.stringify(p.report));
  p.answer.result.report.lint.tests[0].capabilities = Object.fromEntries(Object.entries(copy).reverse());
  assert.equal(outcomeFor(p.answer, p.options).state, 'passed');
  p.answer.result.report.lint.tests[0].capabilities.complete = false;
  assert.equal(outcomeFor(p.answer, p.options).compatibility.issue, 'capability-report-conflict');
});

for (const change of ['missing', 'changed']) test(`COMPAT repeated saved reads retain ${change} source explanation and unsent proof`, async t => {
  const c = await client(t, { pending: true });
  const first = await c.run('check', { '--timeout': 0.01 }); assert.equal(first.code, 3);
  c.state.pending = false;
  const path = join(c.h.repo, change === 'missing' ? TEST : PLACE), original = readFileSync(path);
  if (change === 'missing') unlinkSync(path);
  else writeFileSync(path, Buffer.concat([original, Buffer.from('\nChanged source.\n')]));
  for (let read = 0; read < 3; read++) {
    const r = await c.run('check', { '--read': first.json.batch }, []);
    assert.equal(r.code, 5); assert.equal(r.json.rows[0].state, 'not run');
    assert.match(r.err, change === 'missing' ? /No checks were sent.*saved source cannot be verified/ : /No checks were sent.*source changed/);
    assert.equal(r.clock.uuids, 0); assert.equal(paid(c.f).length, 0);
    assert.equal(r.json.rows[0].request_id, null); assert.equal(r.json.rows[0].calls, 0);
    assert.equal(r.json.rows[0].compatibility.association, 'unknown');
    assert.deepEqual(c.saved(r).batch.rows[0].request_ids, []);
  }
  writeFileSync(path, original);
  const restored = await c.run('check', { '--read': first.json.batch }, []);
  assert.equal(restored.code, 0, restored.err);
  assert.equal(paid(c.f).length, 1, 'only restored exact saved source and matched selected support can dispatch');
  const again = await c.run('check', { '--read': first.json.batch }, []);
  assert.equal(again.code, 0); assert.equal(again.clock.uuids, 0); assert.equal(paid(c.f).length, 1);
});
