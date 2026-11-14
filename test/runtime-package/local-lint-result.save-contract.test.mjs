import test from 'node:test';
import assert from 'node:assert/strict';
import {spawnSync} from 'node:child_process';
import {createHash} from 'node:crypto';
import {existsSync,lstatSync,mkdirSync,readFileSync,readdirSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {pathToFileURL} from 'node:url';
import {readRunResults,resultLines,usableResult} from '../../src/workflow-results.mjs';
import {harbor,PLACE,root as packageRoot} from './runtime-fake.mjs';

// AC5 and the approved shared safe-scope contract: an unrepresentable inspected
// path is a save failure, with no completed record or change to earlier evidence.
const unsafePath = 'prompts/with\\slash.prompt.md';
const digest = bytes => createHash('sha256').update(bytes).digest('hex');
const readJson = path => JSON.parse(readFileSync(path,'utf8'));
const cli = join(packageRoot,'bin/pdd.mjs');
const boundary = pathToFileURL(join(import.meta.dirname,'helpers/local-lint-boundary.mjs')).href;
function snapshot(root) {
  if (!existsSync(root)) return [];
  return ['',...readdirSync(root,{recursive:true}).sort()].map(path => {
    const file = join(root,path), stat = lstatSync(file,{bigint:true});
    return [path,String(stat.mode),String(stat.mtimeNs),stat.isFile() ? digest(readFileSync(file)) : 'directory'];
  });
}
function fixture(t,unsafe=false) {
  const h = harbor(t,repo => {
    if (unsafe) writeFileSync(join(repo,unsafePath),readFileSync(join(repo,PLACE)));
  });
  h.env = {...process.env,HOME:h.home,PDD_STATE_DIR:h.state,PDD_RUNTIME_URL:'invalid'};
  h.counts = join(h.sandbox,'offline-counts.json');
  h.preload = join(h.sandbox,'offline-counts.mjs');
  // Reuse the native offline boundary; counters also detect caught attempts.
  writeFileSync(h.preload,`
import ${JSON.stringify(boundary)};
import fs from 'node:fs';
import childProcess from 'node:child_process';
import {syncBuiltinESMExports} from 'node:module';
const counts = {authentication:0,network:0,model:0};
globalThis.fetch = (...args) => { counts.network++; if (/model/.test(String(args[0]))) counts.model++; throw Error('Offline transport attempted'); };
for (const name of ['spawn','spawnSync','execFileSync']) {
  const native = childProcess[name];
  childProcess[name] = function(command,...args) {
    if (/(^|\\/)gh$/.test(command)) { counts.authentication++; throw Error('Offline authentication attempted'); }
    return native.call(this,command,...args);
  };
}
syncBuiltinESMExports();
process.on('exit',() => fs.writeFileSync(process.env.PDD_TEST_LOCAL_COUNTS,JSON.stringify(counts)));
`);
  return h;
}
function command(h,argv) {
  const result = spawnSync(process.execPath,['--import',h.preload,cli,...argv],{
    cwd:h.repo,env:{...h.env,PDD_TEST_LOCAL_COUNTS:h.counts},encoding:'utf8'
  });
  assert.equal(result.error,undefined);
  assert.equal(result.signal,null);
  assert.deepEqual(readJson(h.counts),{authentication:0,network:0,model:0},'local persistence must remain offline');
  return result;
}
function seedHosted(h) {
  const batch = '20260101-000000-old1', folder = join(h.state,'batches',batch);
  mkdirSync(folder,{recursive:true});
  writeFileSync(join(folder,'batch.json'),JSON.stringify({version:1,batch,root:h.repo,created_at:'2026-01-01T00:00:00Z',
    intent:'lint-only',source_sha256:'a'.repeat(64),rows:[{test:'tests/place-order.json',state:'passed'}],lint:{state:'passed',request_ids:['hosted-control']}}));
  mkdirSync(join(h.state,'repos'));
  writeFileSync(join(h.state,'repos',`${digest(h.repo).slice(0,16)}.json`),JSON.stringify({root:h.repo,last_batch:batch,tries:{}}));
  return batch;
}
function evidence(h) {
  const before = snapshot(h.state);
  const results = readRunResults({root:h.repo,since:0},{env:h.env,capture:()=>({sha256:'a'.repeat(64)})});
  assert.deepEqual(snapshot(h.state),before,'the production reader must not change saved files');
  return results;
}

for (const prior of [false,true]) for (const json of [false,true]) {
  test(`local save rejects actual backslash scope (${prior ? 'hosted history' : 'no history'}, ${json ? 'JSON' : 'text'})`,t => {
    const h = fixture(t,true);
    const visible = spawnSync('git',['ls-files','-z'],{cwd:h.repo,encoding:'utf8'});
    assert.equal(visible.status,0,visible.stderr);
    assert.ok(visible.stdout.split('\0').includes(unsafePath),'the actual Linux filename must be Git-visible');
    assert.deepEqual(readFileSync(join(h.repo,unsafePath)),readFileSync(join(h.repo,PLACE)),'the extra prompt keeps its valid Harbor contract');
    const old = prior ? seedHosted(h) : null, before = snapshot(h.state), oldView = evidence(h);
    if (prior) { assert.equal(oldView[0].batch,old); assert.equal(usableResult(oldView[0]),true); }
    const result = command(h,['lint','--local',...(json ? ['--json'] : [])]);
    assert.equal(result.status,2,'unrepresentable local scope must fail the save instead of reporting success');
    assert.match(result.stderr,/Could not save local lint result.*PDD_STATE_DIR/i);
    assert.equal(result.stdout,'','save failure must not claim a completed saved result');
    assert.deepEqual(snapshot(h.state),before,'validation must publish no batch, summary, or repository pointer and preserve old bytes');
    assert.deepEqual(evidence(h),oldView,'failure must leave the existing evidence unchanged');
    if (!prior) assert.match(resultLines(evidence(h),{kinds:['pdd lint']}).join('\n'),/no pdd lint result/);
  });
}

test('valid local scope still saves a complete partial result through the source CLI',t => {
  const h = fixture(t), result = command(h,['lint','--local','--json']);
  assert.equal(result.status,0,result.stderr);
  assert.equal(result.stderr,'');
  const summary = JSON.parse(result.stdout), folder = join(h.state,'batches',summary.batch);
  assert.deepEqual(readJson(join(folder,'summary.json')),summary);
  const batch = readJson(join(folder,'batch.json'));
  assert.deepEqual(summary.local_scope,{tests:[],prompts:[PLACE]});
  assert.deepEqual(batch.local_scope,summary.local_scope);
  assert.equal(summary.state,'partial'); assert.equal(summary.lint_state,'partial'); assert.equal(summary.local_only,true);
  assert.equal(summary.exit_code,0); assert.equal(summary.reason.code,'local-only');
  assert.deepEqual(summary.rows,[]); assert.deepEqual(summary.warnings,[]); assert.deepEqual(summary.problems,[]);
  assert.equal(readJson(join(h.state,'repos',`${digest(h.repo).slice(0,16)}.json`)).last_batch,summary.batch);
  const view = evidence(h);
  assert.equal(view[0].batch,summary.batch); assert.equal(view[0].state,'partial'); assert.equal(usableResult(view[0]),false);
  assert.match(resultLines(view,{kinds:['pdd lint']}).join('\n'),/partial.*local-only/);
  const before = snapshot(h.state), read = command(h,['test','--read',summary.batch,'--json']);
  assert.equal(read.status,0,read.stderr); assert.deepEqual(JSON.parse(read.stdout),summary);
  assert.deepEqual(snapshot(h.state),before);
});

test('invalid authored entry paths produce static refusals for selected and default local lint', t => {
  const h = fixture(t), path = join(h.repo,'tests/place-order.json');
  const original = readJson(path);
  for (const entry of ['../outside.prompt.md','/outside.prompt.md','prompts/../outside.prompt.md']) {
    const doc = structuredClone(original);
    doc.steps[0].entry_path = entry;
    writeFileSync(path,JSON.stringify(doc));
    for (const selector of [[],['place-order'],['tests/place-order.json']]) {
      const result = command(h,['lint','--local','--json',...selector]);
      assert.equal(result.status,4,`${entry} ${selector}: ${result.stderr}`);
      const report = JSON.parse(result.stdout);
      assert.ok(report.problems.some(problem => problem.code === 'entry-missing'),JSON.stringify(report.problems));
      assert.ok(!report.local_scope.prompts.includes(entry));
    }
  }
});
