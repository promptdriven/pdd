import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { runCheck } from '../src/runtime-client.mjs';
import { PLACE, fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

async function run(setup, fake, options = {}) {
  const { ports } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  const code = await runCheck({ words: ['place-order'], options, cwd: setup.repo }, ports);
  return { code, out: ports.stdout.text, err: ports.stderr.text };
}

for (const lint of [true, false]) test(`interface refusal preserves server pointer and rule in ${lint ? 'lint' : 'check'} output`, async t => {
  const setup = harbor(t);
  const pointer = '/entries/0/input_schema/properties/amount/type';
  const rule = 'type must be a single supported type';
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'POST' && entry.command === 'lint'
    ? { status: 200, json: f.lint(entry.request.requestId, [{ path: PLACE, state: 'refused', admission_state: 'refused', interface: null }],
      [{ code: 'invalid-interface', path: PLACE, pointer, rule, message: 'invalid-interface' }]) } : f.normal(entry));
  const options = lint ? { '--lint': true } : {};
  const result = await run(setup, fake, options);
  assert.equal(result.code, 4);
  assert.ok((result.out + result.err).includes(pointer), result.out + result.err);
  assert.ok((result.out + result.err).includes(rule));
});

test('generic interface refusal identifies missing diagnostic without guessing a field', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'POST' && entry.command === 'lint'
    ? { status: 200, json: f.lint(entry.request.requestId, [{ path: PLACE, state: 'refused', admission_state: 'refused', interface: null }],
      [{ code: 'invalid-interface', path: PLACE, message: 'invalid-interface' }]) } : f.normal(entry));
  const result = await run(setup, fake, { '--lint': true, '--json': true });
  assert.equal(result.code, 4);
  const problem = JSON.parse(result.out).problems[0];
  assert.equal(problem.field ?? null, null);
  assert.match(problem.hint, /Runtime.*field/i);
});

test('generic canonical section does not identify a field', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method !== 'POST' || entry.command !== 'lint') return f.normal(entry);
    const answer = f.lint(entry.request.requestId, [{ path: PLACE, state: 'refused', admission_state: 'refused', interface: null }]);
    answer.result.problems = [{ code: 'invalid-interface', path: PLACE, at: 'Runtime interface', section: 'Runtime interface', pointer: null, message: 'invalid-interface' }];
    return { status: 200, json: answer };
  });
  const result = await run(setup, fake, { '--lint': true, '--json': true });
  assert.equal(result.code, 4);
  const problem = JSON.parse(result.out).problems[0];
  assert.equal(problem.field ?? null, null);
  assert.match(problem.hint, /Runtime.*field/i);
});
