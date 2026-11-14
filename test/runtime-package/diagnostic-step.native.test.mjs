import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { harbor, portsFor } from './runtime-fake.mjs';
import { runCheck, readContractHistory } from '../../src/runtime-seam.mjs';
import { parseArgv } from '../../src/argument-parser.mjs';
import { savedStoryEvidence, resendableStoryChecks } from '../../src/runtime/runtime-client.mjs';
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
  assert.deepEqual(row.selected_steps, ['absent']);
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
  assert.deepEqual((await savedStoryEvidence({root:setup.repo},{env})).stories, []);
  assert.ok(readContractHistory({root:setup.repo,env}).stories.every(item => item.baseline === 'not-checked'));
  assert.deepEqual((await resendableStoryChecks({root:setup.repo},{env})).stories, []);
  const id = uploaded.request.requestId;
  ports.stdout.text = ''; ports.stderr.text = '';
  assert.equal(await runCheck({cwd:setup.repo,cache:true,options:{'--read':id,'--json':true}},ports),0,ports.stderr.text);
  assert.equal(JSON.parse(ports.stdout.text).rows[0].diagnostic_subset,true);
  assert.deepEqual(readFileSync(cachePath),originalCache);
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


test('malformed selected checks and null steps return structured refusals', async t => {
  for (const malformed of [null, 'bad']) {
    const setup = harbor(t), path = join(setup.repo, 'tests/place-order.json');
    const doc = JSON.parse(readFileSync(path));
    if (malformed === null) doc.steps.push(null); else doc.steps[0].checks = malformed;
    writeFileSync(path, JSON.stringify(doc));
    const selected = malformed === null ? ['missing'] : [doc.steps[0].step_id];
    const ports = portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state},{fetch:() => assert.fail('no upload')}).ports;
    assert.equal(await runCheck({cwd:setup.repo,words:['place-order'],options:{'--step':selected,'--json':true}},ports),4);
    const row = JSON.parse(ports.stdout.text).rows[0];
    assert.deepEqual(row.selected_steps,selected);
    assert.equal(row.refusals[0].code,malformed === null ? 'unknown-step' : 'invalid-check');
  }
});

test('late criteria and selected dependencies project in authored order', async t => {
  const setup = harbor(t), path = join(setup.repo,'tests/place-order.json');
  const doc = JSON.parse(readFileSync(path));
  const first = doc.steps[0];
  const second = structuredClone(first), third = structuredClone(first);
  first.checks = first.checks.filter(c => c.criterion_id === 'AC1');
  second.step_id = 'second'; second.checks = second.checks.filter(c => c.criterion_id === 'AC2');
  third.step_id = 'third'; third.checks = third.checks.filter(c => c.criterion_id === 'AC3');
  second.input.customerName = 'literal $step_result';
  third.input.customerName = {$step_result:{step_id:'second',path:'/customerName'}};
  doc.steps = [first,second,third]; writeFileSync(path,JSON.stringify(doc));
  const {fakeRuntime} = await import('./runtime-fake.mjs');
  const fake = await fakeRuntime(t, entry => { const id = entry.request?.requestId ?? entry.url.split('/').at(-1); return {status:200,json:entry.command === 'lint' ? fake.lint(id,[{path:'prompts/place_order.prompt.md',state:'approved',admission_state:'approved',interface:{calls:[]}}]) : fake.check(id)}; });
  const ports = portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin}).ports;
  assert.equal(await runCheck({cwd:setup.repo,words:['place-order'],options:{'--step':['third','second','third'],'--json':true}},ports),0,ports.stderr.text + ports.stdout.text);
  const sent = fake.posts.find(post => post.command === 'check');
  const extract = name => spawnSync('tar',['-xOf','-',name],{input:sent.tar,encoding:'utf8'}).stdout;
  const wire = JSON.parse(extract('tests/place-order.json'));
  assert.deepEqual(wire.steps.map(s => s.step_id),['second','third']);
  assert.deepEqual(wire.criteria.map(c => c.id),['AC2','AC3']);
  assert.ok((wire.check_exemptions ?? []).every(e => ['AC2','AC3'].includes(e.criterion_id)));
  const story = extract('user_stories/place-order.md');
  assert.ok(wire.criteria.every(c => story.includes(c.text)));
  assert.ok(!story.includes(doc.criteria.find(c => c.id === 'AC1').text));
});

test('selected references permit selected prerequisites and refuse omitted ones', async t => {
  const setup = harbor(t), path = join(setup.repo,'tests/place-order.json');
  const doc = JSON.parse(readFileSync(path));
  const prior = doc.steps[0], late = structuredClone(prior); late.step_id = 'late';
  late.input = { ...late.input, quantity: {$step_result:{step_id:prior.step_id,path:'/quantity'}} };
  doc.steps.push(late); writeFileSync(path,JSON.stringify(doc));
  const ports = portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state},{fetch:() => assert.fail('no upload')}).ports;
  assert.equal(await runCheck({cwd:setup.repo,words:['place-order'],options:{'--step':['late'],'--json':true}},ports),4);
  assert.equal(JSON.parse(ports.stdout.text).rows[0].refusals[0].code,'step-prerequisite');
});


test('authored exemptions remain refused for diagnostic selection', async t => {
  const setup = harbor(t), path = join(setup.repo,'tests/place-order.json');
  const doc = JSON.parse(readFileSync(path));
  doc.check_exemptions = [{criterion_id:'AC2',reason:'out-of-scope',detail:'authored'}];
  writeFileSync(path,JSON.stringify(doc));
  const ports = portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state},{fetch:() => assert.fail('no upload')}).ports;
  assert.equal(await runCheck({cwd:setup.repo,words:['place-order'],options:{'--step':[doc.steps[0].step_id],'--json':true}},ports),4);
  assert.equal(JSON.parse(ports.stdout.text).rows[0].refusals[0].code,'pdd-partial-test');
});
