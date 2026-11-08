import test from 'node:test';
import assert from 'node:assert/strict';
import { writeFileSync, mkdirSync, copyFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { harbor, fakeRuntime, portsFor, PLACE } from './runtime-fake.mjs';

function project(t, modules) {
  return harbor(t, root => {
    mkdirSync(join(root, 'src'));
    for (const name of ['order', 'printer', 'other']) writeFileSync(join(root, `src/${name}.mjs`), 'export const value = 1;\n');
    if (modules) writeFileSync(join(root, 'pdd-bindings.json'), JSON.stringify({ schema_version: 'pdd.bindings.v1', modules }));
  });
}
const bound = { module: 'src/order.mjs', stories: ['user_stories/place-order.md'], prompt: PLACE };
const unbound = { module: 'src/printer.mjs', stories: ['user_stories/place-order.md'], reason: 'Physical acknowledgement has no accepted contract.', port_attempt: 'Tried fixed printer answers; physical acknowledgement remains unspecified.' };
async function check(t, setup, options = { '--lint': true }, words = ['place-order']) {
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const { ports } = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin });
  const code = await runCheck({ cwd: setup.repo, words, options }, ports);
  return { code, out: ports.stdout.text, err: ports.stderr.text, fake };
}

test('bindings: selected Story count and each unbound explanation remain visible beside passing lint', async t => {
  const setup = project(t, [bound, unbound, { module: 'src/other.mjs', stories: ['user_stories/unknown-item.md'], reason: 'Other Story only.', port_attempt: 'Tried another port.' }]);
  const run = await check(t, setup);
  assert.equal(run.code, 0, run.err);
  assert.match(run.out, /1 of 2 modules bound/);
  for (const text of [unbound.module, unbound.reason, unbound.port_attempt]) assert.ok(run.out.includes(text), run.out);
  assert.doesNotMatch(run.out, /src\/other\.mjs/);
  assert.equal(run.fake.posts.filter(p => p.command === 'check').length, 0);
});

test('bindings: blank unbound reason is a lint refusal, not a passing omission', async t => {
  const run = await check(t, project(t, [bound, { ...unbound, reason: '  ' }]));
  assert.equal(run.code, 4, run.out + run.err);
  assert.match(run.out + run.err, /src\/printer\.mjs/);
  assert.match(run.out + run.err, /reason/i);
  assert.equal(run.fake.posts.filter(p => p.command === 'check').length, 0);
});

test('bindings: no attempted port is a lint refusal', async t => {
  const { port_attempt, ...missing } = unbound;
  const run = await check(t, project(t, [missing]));
  assert.equal(run.code, 4, run.out + run.err);
  assert.match(run.out + run.err, /port/i);
});

test('bindings: an unreferenced prompt cannot claim a selected module is bound', async t => {
  const setup = harbor(t, root => {
    mkdirSync(join(root, 'src')); writeFileSync(join(root, 'src/order.mjs'), '');
    copyFileSync(join(root, PLACE), join(root, 'prompts/unreached.prompt.md'));
    writeFileSync(join(root, 'pdd-bindings.json'), JSON.stringify({ schema_version: 'pdd.bindings.v1', modules: [{ ...bound, prompt: 'prompts/unreached.prompt.md' }] }));
  });
  const run = await check(t, setup);
  assert.equal(run.code, 4, run.out + run.err);
  assert.match(run.out + run.err, /reach|bound/i);
});

test('bindings: absent inventory is unavailable, not a claim of complete coverage', async t => {
  const run = await check(t, project(t), { '--lint': true, '--json': true });
  assert.equal(run.code, 0, run.err);
  assert.deepEqual(JSON.parse(run.out).coverage, { available: false, bound: null, total: null, modules: [] });
});
