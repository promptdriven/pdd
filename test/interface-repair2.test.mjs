import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { runCheck } from '../src/runtime-seam.mjs';
import { interfaceBlocks, proseSha256 } from '../src/runtime-seam.mjs';
import { readRunResults, resultLines } from '../src/workflow-results.mjs';
import { runStatus } from '../src/workflow-runner.mjs';
import { fixture as workflow } from './helpers/workflow-runner-fixture.mjs';
import { harbor, PLACE, storyTest, fakeRuntime, portsFor } from './runtime-fake.mjs';

const nativePath = 'prompts/kernel.prompt.md';
const nativeTest = 'tests/kernel.json';
const reason = 'cross-process filesystem locks';

function mixed(repo) {
  storyTest(repo, 'kernel');
  let prompt = '# Kernel\n\n<details><summary>Runtime interface</summary>\n\n```json\n'
    + JSON.stringify({ kind: 'native-only', reason, status: 'draft', prose_sha256: '' })
    + '\n```\n</details>\n';
  prompt = prompt.replace('"prose_sha256":""', `"prose_sha256":"${proseSha256(prompt)}"`);
  writeFileSync(join(repo, nativePath), prompt);
  const path = join(repo, nativeTest), doc = JSON.parse(readFileSync(path));
  doc.steps[0].entry_path = nativePath;
  writeFileSync(path, JSON.stringify(doc));
}

const batchFile = (setup, batch) => join(setup.state, 'batches', batch, 'batch.json');
const savedBatch = (setup, batch) => {
  const saved=JSON.parse(readFileSync(batchFile(setup,batch)));
  saved.rows=saved.rows.map(row=>({...row,state:row.recovery_state ?? row.state}));
  return saved;
};
const kernel = rows => rows.find(row => row.test === nativeTest);
function omission(row, state = 'not_run') {
  assert.equal(row.state, state, 'native-only outcome');
  assert.equal(row.request_ids?.length ?? 0, 0, 'native-only must have no Runtime request');
  if (row.calls !== undefined) assert.equal(row.calls, 0);
  assert.match(JSON.stringify(row), /cross-process filesystem locks/, 'native-only reason');
}

for (const lint of [false, true]) for (const json of [false, true]) {
  test(`2826 repair 2: delayed ${lint ? 'lint' : 'check'} preserves native omissions and refusals (${json ? 'JSON' : 'text'})`, async t => {
    const refusedTest = 'tests/invalid-kernel.json';
    const setup = harbor(t, repo => {
      mixed(repo);
      storyTest(repo, 'invalid-kernel');
      const path = join(repo, refusedTest), doc = JSON.parse(readFileSync(path));
      doc.steps[0].entry_path = nativePath; doc.criteria = [];
      writeFileSync(path, JSON.stringify(doc));
    });
    let reply = 'pending';
    const fake = await fakeRuntime(t, (entry, server) => {
      if (entry.command === 'lint') return { status: 202, json: server.job(entry.request.requestId, 'lint', 'queued') };
      const id = entry.url.split('/').at(-1);
      if (entry.method === 'GET' && !fake.posts.some(post => post.command === 'check' && post.request.requestId === id)) {
        if (reply === 'complete') return { status: 200, json: server.lint(id) };
        if (reply === 'unknown') return { status: 200, json: server.lint('00000000-0000-4000-8000-000000000000') };
        return { status: 200, json: server.job(id, 'lint', 'running') };
      }
      return server.normal(entry);
    });
    fake.capacity=()=>({status:200,json:{maintenance:null,features:['lint-tests']}});
    const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };
    const first = portsFor(env);
    assert.equal(await runCheck({ cwd: setup.repo, options: { '--json': true, '--timeout': 0.01, ...(lint ? { '--lint': true } : {}) } }, first.ports), 3);
    const result = JSON.parse(first.ports.stdout.text), initial = savedBatch(setup, result.batch);
    const original = kernel(initial.rows), refused = initial.rows.find(row => row.test === refusedTest);
    omission(original);
    omission(refused, 'refused');
    assert.equal(original.phase, 'local');
    assert.deepEqual(original.native_only, [{ path: nativePath, reason }]);
    assert.equal(original.refusals.length, 0);
    assert.ok(refused.refusals.length > 0);

    for (const stage of ['pending', 'unknown', 'complete']) {
      reply = stage;
      const next = portsFor(env);
      const code = await runCheck({ cwd: setup.repo, options: { '--read': result.batch, '--timeout': stage === 'complete' ? 1 : 0.01, ...(json ? { '--json': true } : {}) } }, next.ports);
      assert.equal(code, stage === 'complete' ? 5 : 3, next.ports.stderr.text);
      const saved = savedBatch(setup, result.batch);
      assert.deepEqual(kernel(saved.rows), original, `native-only saved fields after ${stage}`);
      assert.deepEqual(saved.rows.find(row => row.test === refusedTest), refused, `native-only refusal after ${stage}`);
      if (json) {
        const rows = JSON.parse(next.ports.stdout.text).rows;
        omission(kernel(rows),'not run');
        omission(rows.find(row => row.test === refusedTest), 'not run');
      }
      else {
        assert.match(next.ports.stdout.text, /cross-process filesystem locks/);
        assert.ok(next.ports.stdout.text.includes(nativePath));
      }
      if (stage === 'complete') {
        const executable = saved.rows.filter(row => !row.native_only?.length);
        assert.ok(executable.length > 0);
        assert.ok(executable.every(row => row.state === 'passed'), 'ordinary rows must complete');
        assert.equal(fake.posts.filter(post => post.command === 'check').length, lint ? 0 : executable.length);
      } else assert.equal(fake.posts.length, 1, 'unresolved lint sends no checks');
    }
    for (const post of fake.posts) {
      const listing = spawnSync('tar', ['-tf', '-'], { input: post.tar, encoding: 'utf8' });
      assert.equal(listing.status, 0);
      assert.doesNotMatch(listing.stdout, /kernel/, 'native-only files must not be uploaded');
      if(post.command==='lint') for(const path of post.request.tests) assert.ok(listing.stdout.split('\n').includes(path),'named lint path in upload');
    }
  });
}

for (const json of [false, true]) for (const list of [false, true]) {
  test(`2826 repair 2: local mixed lint saves refusals and omissions (${json ? 'JSON' : 'text'}, status ${list ? 'list' : 'detail'})`, async t => {
    const setup = harbor(t, repo => {
      mixed(repo);
      const path = join(repo, PLACE), text = readFileSync(path, 'utf8');
      writeFileSync(path, text.replace(interfaceBlocks(text)[0][0], ''));
    });
    const fake = await fakeRuntime(t, () => assert.fail('local lint must not contact Runtime'));
    fake.capacity=()=>({status:200,json:{maintenance:null,features:['lint-tests']}});
    const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin };
    const first = portsFor(env);
    first.ports.gh = () => assert.fail('local lint must not authenticate');
    assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order', 'kernel'], options: { '--lint': true, ...(json ? { '--json': true } : {}) } }, first.ports), 4);
    if (json) {
      const result = JSON.parse(first.ports.stdout.text);
      assert.ok(result.batch, 'local mixed lint must save a batch');
      assert.equal(result.lint_state, 'not run');
      omission(kernel(result.rows),'not run');
    } else assert.match(first.ports.stdout.text, /cross-process filesystem locks/);
    const results = readRunResults({ root: setup.repo }, { env }), evidence = results.find(row => row.kind === 'pdd lint');
    assert.ok(evidence, 'local mixed lint must save PR evidence');
    assert.deepEqual(evidence.coverage.runtime, { total: 2, checkable: 0, native_only: 1 });
    assert.equal(evidence.nativeOnly[0].state, 'not run');
    assert.deepEqual(evidence.nativeOnly[0].prompts, [{ path: nativePath, reason }]);
    assert.match(resultLines(results).join('\n'), /cross-process filesystem locks/);
    const saved = savedBatch(setup, evidence.batch);
    assert.equal(saved.local_only, true);
    assert.equal(saved.rows.length, 2);
    const refused = saved.rows.find(row => row.test === 'tests/place-order.json');
    assert.equal(refused.state, 'refused');
    assert.ok(refused.refusals.some(item => item.code === 'interface-missing'));
    omission(kernel(saved.rows));
    for (const readJson of [false, true]) {
      const next = portsFor(env); next.ports.gh = first.ports.gh;
      assert.equal(await runCheck({ cwd: setup.repo, options: { '--read': evidence.batch, ...(readJson ? { '--json': true } : {}) } }, next.ports), 4);
      if (readJson) {
        const read = JSON.parse(next.ports.stdout.text);
        assert.equal(read.lint_state, 'not run');
        assert.deepEqual(read.coverage.runtime, evidence.coverage.runtime);
        assert.equal(read.rows.find(row => row.test === refused.test).state, 'not run');
        omission(kernel(read.rows),'not run');
      } else assert.match(next.ports.stdout.text, /cross-process filesystem locks/);
    }
    const f = await workflow(t);
    assert.equal((await f.run()).exitCode, 0);
    const run = f.record(); run.state = 'completed';
    run.done.check = { at: f.clock, area: run.areas[0].name, pddResults: results };
    writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
    const status = await runStatus({ cwd: f.source, ...(list ? { all: true } : { ref: '17' }), json }, f.ports);
    assert.equal(status.exitCode, 0);
    if (json) {
      const row = JSON.parse(status.message).runs[0];
      assert.deepEqual(row.runtimeCoverage, evidence.coverage.runtime);
      assert.deepEqual(row.nativeOnly, evidence.nativeOnly);
    } else {
      assert.match(status.message, /Runtime coverage: 0 of 2 prompts checkable, 1 native-only/);
      assert.match(status.message, /cross-process filesystem locks/);
    }
    assert.equal(fake.posts.length, 0);
    assert.equal(fake.gets.length, 0);
  });
}
