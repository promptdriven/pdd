import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { harbor, portsFor } from './runtime-fake.mjs';
import { runCheck } from '../../src/runtime-seam.mjs';
import { parseArgv } from '../../src/argument-parser.mjs';
import { latestCheckVerdict, readRunResults } from '../../src/workflow-results.mjs';

test('repeatable step selection is parsed without consuming a Story', () => {
  const plan = parseArgv(['test', 'place-order', '--step', 'a', '--step', 'b']);
  assert.deepEqual(plan.operands, ['place-order']);
  assert.deepEqual(plan.options['--step'], ['a', 'b']);
});

test('an unknown selected step is refused locally and leaves source unchanged', async t => {
  const setup = harbor(t), file = join(setup.repo, 'tests/place-order.json');
  const before = readFileSync(file);
  const scenario = JSON.parse(before);
  const ports = portsFor({ HOME: setup.home, PDD_STATE_DIR: setup.state }, {fetch: () => assert.fail('no upload')}).ports;
  const code = await runCheck({cwd: setup.repo, words:['place-order'], options:{'--step':['absent'],'--json':true}}, ports);
  assert.equal(code, 4, ports.stderr.text);
  const row = JSON.parse(ports.stdout.text).rows[0];
  assert.equal(row.refusals[0].code, 'unknown-step');
  assert.match(row.refusals[0].message, new RegExp(scenario.steps[0].step_id));
  assert.deepEqual(readFileSync(file), before);
});

test('selected step is uploaded as a diagnostic projection without changing the source', async t => {
  const setup = harbor(t), path = join(setup.repo, 'tests/place-order.json');
  const doc = JSON.parse(readFileSync(path));
  const selected = doc.steps[0].step_id;
  const extra = structuredClone(doc.steps[0]); extra.step_id = 'unused'; extra.input = {invalid:'input'}; extra.operation = 'missing'; extra.entry_path = 'prompts/missing.prompt.md';
  extra.checks = extra.checks.filter(check => check.criterion_id !== 'AC1');
  doc.steps[0].checks = doc.steps[0].checks.filter(check => check.criterion_id === 'AC1');
  doc.steps.push(extra); writeFileSync(path, JSON.stringify(doc));
  const original = readFileSync(path);
  const cachePath = join(setup.repo,'.pdd/cache/test/stories.json');
  mkdirSync(join(setup.repo,'.pdd/cache/test'),{recursive:true});
  writeFileSync(cachePath,JSON.stringify({schema_version:1,generation:7,epoch:'sentinel',stories:{'user_stories/place-order.md':{outcome:'passed'}}}));
  const originalCache = existsSync(cachePath) ? readFileSync(cachePath) : null;
  const {fakeRuntime} = await import('./runtime-fake.mjs');
  const fake = await fakeRuntime(t, entry => {
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    return {status:200,json:entry.command === 'lint' ? fake.lint(id, [{path:'prompts/place_order.prompt.md',state:'approved',admission_state:'approved',interface:{calls:[]}}]) : fake.check(id)};
  });
  const ports = portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin}).ports;
  const code = await runCheck({cwd:setup.repo,words:['place-order'],cache:true,options:{'--step':[selected],'--json':true}}, ports);
  assert.equal(code,0,ports.stderr.text || ports.stdout.text);
  const result = JSON.parse(ports.stdout.text);
  assert.equal(result.rows[0].diagnostic_subset,true);
  assert.deepEqual(result.rows[0].selected_steps,[selected]);
  assert.deepEqual(readFileSync(path),original);
  const uploaded = fake.posts.find(post => post.command === 'check');
  const extracted = spawnSync('tar', ['-xOf', '-', 'tests/place-order.json'], {input:uploaded.tar, encoding:'utf8'});
  assert.equal(extracted.status,0,extracted.stderr);
  assert.deepEqual(JSON.parse(extracted.stdout).steps.map(step => step.step_id),[selected]);
  assert.deepEqual(JSON.parse(extracted.stdout).criteria.map(item => item.id),['AC1']);
  const story = spawnSync('tar', ['-xOf', '-', 'user_stories/place-order.md'], {input:uploaded.tar, encoding:'utf8'});
  assert.equal(story.status,0,story.stderr);
  assert.match(story.stdout,/An order of 2 Espresso/);
  assert.doesNotMatch(story.stdout,/The order keeps the name/);
  assert.deepEqual(existsSync(cachePath) ? readFileSync(cachePath) : null,originalCache);
  ports.stdout.text = ''; ports.stderr.text = '';
  assert.equal(await runCheck({cwd:setup.repo,cache:true,options:{'--read':result.batch,'--json':true}},ports),0,ports.stderr.text);
  assert.deepEqual(JSON.parse(ports.stdout.text).rows[0].selected_steps,[selected]);
  assert.deepEqual(existsSync(cachePath) ? readFileSync(cachePath) : null,originalCache);
  const env = {HOME:setup.home,PDD_STATE_DIR:setup.state};
  assert.equal(latestCheckVerdict({root:setup.repo,since:0},{env}),null);
  assert.equal(readRunResults({root:setup.repo},{env}).some(item => item.kind === 'pdd test'),false);
});

test('a step with an omitted stateful prefix refuses before upload', async t => {
  const setup = harbor(t), path = join(setup.repo,'tests/place-order.json');
  const doc = JSON.parse(readFileSync(path));
  const late = structuredClone(doc.steps[0]); late.step_id = 'late'; doc.steps.push(late);
  doc.initial_world = {saved:true}; writeFileSync(path,JSON.stringify(doc));
  const ports = portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state},{fetch:() => assert.fail('no upload')}).ports;
  assert.equal(await runCheck({cwd:setup.repo,words:['place-order'],options:{'--step':['late'],'--json':true}},ports),4);
  assert.equal(JSON.parse(ports.stdout.text).rows[0].refusals[0].code,'step-prerequisite');
});
