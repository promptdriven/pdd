import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { runCheck } from '../src/runtime-client.mjs';
import { findTests, preflight, scenarioShapeRefusal, captureSource, interfaceBlocks, proseSha256 } from '../src/runtime-preflight.mjs';
import { harbor, fakeRuntime, portsFor, PLACE } from './runtime-fake.mjs';

const TEST = 'tests/place-order.json';
const readJson = (repo, path) => JSON.parse(readFileSync(join(repo, path), 'utf8'));
const writeJson = (repo, path, value) => writeFileSync(join(repo, path), JSON.stringify(value, null, 2) + '\n');

function editPrompt(repo, path, mutate) {
  let text = readFileSync(join(repo, path), 'utf8');
  const block = interfaceBlocks(text)[0];
  const iface = JSON.parse(block[1]);
  mutate(iface);
  iface.status = 'draft';
  text = text.slice(0, block.indices[1][0]) + JSON.stringify(iface) + text.slice(block.indices[1][1]);
  text = text.replace(/"prose_sha256"\s*:\s*"[^"]*"/, `"prose_sha256":"${proseSha256(text)}"`);
  writeFileSync(join(repo, path), text);
}

const schema = { type: 'object', properties: {}, required: [], additionalProperties: false };
const portResource = (name, operation) => ({
  name,
  kind: 'port',
  access: 'write',
  operations: [{ name: operation, access: 'write', arguments_schema: schema, result_schema: schema }]
});

test('3273: invalid-step names unknown, missing, non-object and blank-string step defects across preflight and shape refusal', t => {
  const f = harbor(t);
  const base = readJson(f.repo, TEST);
  const cases = [
    {
      name: 'unknown key',
      mutate: doc => { doc.steps[0].simulation = {}; },
      expect: [/unknown key "simulation"/, /Required step keys: step_id, entry_path, operation, input, checks/, /optional step keys: expected_error, simulation_overrides, model/]
    },
    {
      name: 'missing required key',
      mutate: doc => { delete doc.steps[0].operation; },
      expect: [/missing required key "operation"/, /Required step keys:/, /optional step keys:/]
    },
    {
      name: 'missing and unknown keys together',
      mutate: doc => { delete doc.steps[0].input; delete doc.steps[0].checks; doc.steps[0].simulation = {}; doc.steps[0].extra = 1; },
      expect: [/missing required keys "input", "checks"/, /unknown keys "simulation", "extra"/]
    },
    {
      name: 'non-object step',
      mutate: doc => { doc.steps[0] = null; },
      expect: [/A step must be a JSON object\./, /Required step keys:/]
    },
    {
      name: 'blank string step fields',
      mutate: doc => { doc.steps[0].step_id = ''; doc.steps[0].operation = 42; },
      expect: [/Step "step_id", "operation" must be nonblank strings\./]
    }
  ];

  for (const item of cases) {
    const doc = structuredClone(base);
    item.mutate(doc);
    const shape = scenarioShapeRefusal(doc, TEST);
    assert.ok(shape, `${item.name}: scenarioShapeRefusal`);
    assert.equal(shape.code, 'invalid-step');
    assert.equal(shape.section, 'steps[0]');

    writeJson(f.repo, TEST, doc);
    const found = findTests({ root: f.repo });
    const row = preflight({ root: f.repo, found, selected: found.tests.filter(item => item.path === TEST) }).rows[0];
    const refusal = row.refusals.find(entry => entry.code === 'invalid-step');
    assert.ok(refusal, `${item.name}: preflight refusal`);
    assert.equal(refusal.message, shape.message);
    for (const pattern of item.expect) {
      assert.match(refusal.message, pattern, `${item.name}: ${pattern}`);
    }
  }
});

test('3273: list-shaped step.simulation_overrides binds the target operation without array-index candidates', async t => {
  const f = harbor(t);
  editPrompt(f.repo, PLACE, iface => { iface.resources = [portResource('dispatch', 'changeRun')]; });
  const doc = readJson(f.repo, TEST);
  doc.simulation = {};
  doc.steps = [
    { ...doc.steps[0], step_id: 'peer-up' },
    {
      ...doc.steps[0],
      step_id: 'peer-down',
      simulation_overrides: [{
        operation: 'dispatch.changeRun',
        criterion_id: doc.criteria[0].id,
        failure_quote: doc.criteria[0].text.slice(0, 12),
        reason: 'Force peer lookup failure on step 2.',
        binding: { action: 'fixture.lookup', cases: [{ args: {}, result: { ok: false } }] }
      }]
    }
  ];
  writeJson(f.repo, TEST, doc);

  const plan = captureSource(f.repo, { tests: [TEST] }).bindingPlans?.[0];
  assert.ok(plan);
  assert.deepEqual(plan.edges.map(edge => [edge.step_id, edge.state]), [['peer-up', 'missing'], ['peer-down', 'bound']]);
  const boundEdge = plan.edges.find(edge => edge.step_id === 'peer-down');
  assert.deepEqual(boundEdge.candidates, [{ kind: 'simulation', name: 'dispatch.changeRun', cause: 'selected' }]);
  assert.equal(boundEdge.candidates.some(candidate => candidate.name === '0'), false);

  const { ports } = portsFor(
    { HOME: f.home, XDG_CONFIG_HOME: join(f.home, 'config'), PDD_STATE_DIR: f.state },
    { gh: () => { throw Error('must not authenticate'); }, fetch: () => { throw Error('must not send'); } }
  );
  const code = await runPdd(['test', '--explain-bindings', 'place-order'], {
    cwd: f.repo,
    env: ports.env,
    stdout: ports.stdout,
    stderr: ports.stderr
  });
  assert.equal(code, 4);
  assert.match(ports.stdout.text, /peer-down: prompts\/place_order\.prompt\.md: dispatch\.changeRun: bound; considered: simulation dispatch\.changeRun \(selected\)/);
  assert.doesNotMatch(ports.stdout.text, /simulation 0/);
});

test('3273: test cache handles list-shaped step.simulation_overrides without reporting array index 0', async t => {
  const f = harbor(t, repo => {
    editPrompt(repo, PLACE, iface => { iface.resources = [portResource('gcloud', 'call')]; });
  });
  const fake = await fakeRuntime(t, entry => {
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    if (entry.command === 'lint') {
      return { status: 200, json: fake.lint(id, [{ path: PLACE, state: 'approved', admission_state: 'approved', interface: { calls: [] } }]) };
    }
    const job = fake.check(id);
    job.engine_sha = 'a'.repeat(40);
    job.usage.requested_model = 'synthetic-model-A';
    job.result.report.evaluation.requested_model = 'synthetic-model-A';
    return { status: 200, json: job };
  });
  const { ports, clock } = portsFor({ HOME: f.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: f.state });
  const run = async () => {
    ports.stdout.text = '';
    ports.stderr.text = '';
    const before = fake.posts.filter(post => post.command === 'check').length;
    const code = await runCheck({ words: ['place-order'], options: { '--json': true }, cwd: f.repo, cache: true }, ports);
    clock.now += 1;
    assert.equal(code, 0, ports.stderr.text);
    return { sent: fake.posts.filter(post => post.command === 'check').length - before, json: JSON.parse(ports.stdout.text) };
  };

  // 1. Single-step deterministic list override is eligible for cache reuse.
  const single = readJson(f.repo, TEST);
  single.simulation = {};
  single.steps[0].simulation_overrides = [{
    operation: 'gcloud.call',
    criterion_id: single.criteria[0].id,
    failure_quote: single.criteria[0].text.slice(0, 12),
    reason: 'Deterministic fixture override.',
    binding: { action: 'fixture.lookup', cases: [{ args: {}, result: { ok: true } }] }
  }];
  writeJson(f.repo, TEST, single);
  assert.equal((await run()).sent, 1);
  assert.equal((await run()).sent, 0, 'deterministic list override reuses cached pass');

  // 2. Two-step partial list override names the declared resource (gcloud), never array index 0.
  const partial = structuredClone(single);
  partial.steps = [
    { ...single.steps[0], step_id: 'step-1', simulation_overrides: undefined },
    { ...single.steps[0], step_id: 'step-2' }
  ];
  delete partial.steps[0].simulation_overrides;
  writeJson(f.repo, TEST, partial);
  assert.equal((await run()).sent, 1);
  const secondPartial = await run();
  assert.equal(secondPartial.sent, 1);
  assert.equal(secondPartial.json.rows[0].cache_reason, 'runs every time: uses an AI-played fake (gcloud)');

  // 3. Nondeterministic .prompt list override names gcloud, never array index 0.
  const promptOverride = structuredClone(single);
  promptOverride.steps[0].simulation_overrides[0].binding = { action: 'http.prompt', target: PLACE };
  writeJson(f.repo, TEST, promptOverride);
  assert.equal((await run()).sent, 1);
  const secondPrompt = await run();
  assert.equal(secondPrompt.sent, 1);
  assert.equal(secondPrompt.json.rows[0].cache_reason, 'runs every time: uses an AI-played fake (gcloud)');
});
