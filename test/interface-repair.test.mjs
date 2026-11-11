import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { runCheck } from '../src/runtime/runtime-client.mjs';
import { interfaceBlocks, proseSha256 } from '../src/runtime/runtime-preflight.mjs';
import { readRunResults, resultLines } from '../src/workflow-results.mjs';
import { runStatus, ownStoryCount } from '../src/workflow-runner.mjs';
import { fixture as workflow } from './helpers/workflow-runner-fixture.mjs';
import { harbor, PLACE, storyTest, fakeRuntime, portsFor } from './runtime-fake.mjs';

const reason = 'Real cross-process filesystem locks.';
function native(repo, path = PLACE) {
  const old = readFileSync(join(repo,path),'utf8'), block = interfaceBlocks(old)[0];
  let text = old.replace(block?.[0] ?? '', '') + '\n<details><summary>Runtime interface</summary>\n\n```json\n' + JSON.stringify({kind:'native-only',status:'draft',prose_sha256:'',reason}) + '\n```\n</details>\n';
  text = text.replace('"prose_sha256":""',`"prose_sha256":"${proseSha256(text)}"`);
  writeFileSync(join(repo,path),text);
}
function scenario(repo, edit, name = 'place-order') {
  const path = join(repo,`tests/${name}.json`), doc = JSON.parse(readFileSync(path,'utf8'));
  edit(doc); writeFileSync(path,JSON.stringify(doc));
}
function called(repo) {
  const path = join(repo,PLACE), text = readFileSync(path,'utf8'), block = interfaceBlocks(text)[0], iface = JSON.parse(block[1]);
  iface.calls = [{target:'prompts/kernel.prompt.md',target_operation:'lock',max_calls:1}];
  writeFileSync(path,text.replace(block[1],JSON.stringify(iface)));
  writeFileSync(join(repo,'prompts/kernel.prompt.md'),'# Kernel\n'); native(repo,'prompts/kernel.prompt.md');
}
const defects = {
  'unchecked-criteria': repo => scenario(repo,doc => { doc.steps[0].checks = []; }),
  'invalid-criterion': repo => scenario(repo,doc => { doc.criteria = []; }),
  'invalid-check': repo => scenario(repo,doc => { doc.steps[0].checks = null; }),
  'stale-native': (repo,path) => writeFileSync(join(repo,path),readFileSync(join(repo,path),'utf8')+'\nChanged lock contract.\n'),
};
for (const route of ['entry','call']) for (const [defect, edit] of Object.entries(defects)) {
  test(`2826: ${route} native-only stays local with ${defect} in JSON and text lint`,async t => {
    const setup = harbor(t,repo => {
      if (route === 'entry') native(repo); else called(repo);
      edit(repo,route === 'entry' ? PLACE : 'prompts/kernel.prompt.md');
    });
    const fake = await fakeRuntime(t,(entry,server) => server.normal(entry));
    for (const json of [true,false]) {
      const {ports} = portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin});
      const code = await runCheck({cwd:setup.repo,words:['place-order'],options:{'--lint':true,...(json ? {'--json':true} : {})}},ports);
      assert.equal(code,4,`native-refusal: ${ports.stdout.text}`);
      if (json) {
        const result = JSON.parse(ports.stdout.text), row = result.rows[0];
        assert.equal(row.state,'not run'); assert.ok(row.refusals.length);
        assert.ok(JSON.stringify(row).includes(reason),'native-reason retained');
      } else { assert.ok(ports.stdout.text.includes(reason),'native-reason retained in text'); }
      assert.equal(fake.posts.length,0,'native-upload forbidden');
    }
  });
}
test('2826: invalid criteria before a stale caller still discover its native-only call',async t => {
  const setup = harbor(t,repo => {
    called(repo); scenario(repo,doc => { doc.criteria = []; });
    writeFileSync(join(repo,PLACE),readFileSync(join(repo,PLACE),'utf8')+'\nChanged caller.\n');
  });
  const fake = await fakeRuntime(t,(entry,server) => server.normal(entry));
  const {ports} = portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin});
  assert.equal(await runCheck({cwd:setup.repo,words:['place-order'],options:{'--json':true}},ports),4);
  const row = JSON.parse(ports.stdout.text).rows[0];
  assert.equal(row.state,'not run'); assert.ok(JSON.stringify(row).includes(reason),'native-reason retained before validation');
  assert.equal(fake.posts.length,0);
});
async function check(t,{lint=false,allLocal=false}={}) {
  const setup = harbor(t,repo => {
    if (allLocal) native(repo);
    else {
      storyTest(repo,'kernel'); writeFileSync(join(repo,'prompts/kernel.prompt.md'),'# Kernel\n'); native(repo,'prompts/kernel.prompt.md');
      scenario(repo,doc => {doc.steps[0].entry_path='prompts/kernel.prompt.md';},'kernel');
    }
  });
  const fake = await fakeRuntime(t,(entry,server) => server.normal(entry));
  const env = {HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin}, {ports} = portsFor(env);
  assert.equal(await runCheck({cwd:setup.repo,options:{'--json':true,...(lint ? {'--lint':true} : {})}},ports),5,ports.stdout.text+ports.stderr.text);
  const result = JSON.parse(ports.stdout.text);
  const read = () => readRunResults({root:setup.repo},{env});
  return {setup,fake,env,result,read};
}
for (const changed of ['prompts/place_order.prompt.md','prompts/kernel.prompt.md','tests/kernel.json']) {
  test(`2826: mixed source is current and a later edit to ${changed} makes it stale`,async t => {
    const f = await check(t);
    const current = f.read().find(item => item.kind === 'pdd test');
    assert.equal(current.source,'current','mixed-source identity');
    assert.deepEqual(current.tests,f.result.rows.map(row => row.test).sort());
    const run = {root:f.setup.repo,pddHistory:[current]};
    assert.ok(ownStoryCount(run).pass > 0,'mixed-status source is current');
    writeFileSync(join(f.setup.repo,changed),readFileSync(join(f.setup.repo,changed),'utf8')+'\n');
    assert.equal(f.read().find(item => item.kind === 'pdd test').source,'changed');
    assert.equal(ownStoryCount(run).pass,0,'mixed-status source changed');
    for (const post of f.fake.posts) {
      const files = spawnSync('tar',['-tf','-'],{input:post.tar,encoding:'utf8'});
      assert.equal(files.status,0); assert.doesNotMatch(files.stdout,/kernel/);
    }
  });
}
for (const lint of [false,true]) for (const allLocal of [false,true]) {
  test(`2826: PR evidence retains coverage and native-only reasons (${lint ? 'lint' : 'check'}, ${allLocal ? 'local' : 'mixed'})`,async t => {
    const f = await check(t,{lint,allLocal}), evidence = f.read();
    const saved = evidence.find(item => item.kind === (lint ? 'pdd lint' : 'pdd test'));
    assert.ok(saved,'native-only evidence saved');
    assert.deepEqual(saved.coverage?.runtime,f.result.coverage.runtime,'saved-runtime coverage');
    assert.equal(saved.nativeOnly[0].state,'not run'); assert.equal(saved.nativeOnly[0].prompts[0].reason,reason);
    const lines = resultLines(evidence).join('\n');
    assert.match(lines,/Runtime coverage: \d+ of \d+ prompts checkable, 1 native-only/);
    assert.ok(lines.includes(reason)); assert.ok(lines.includes('not run'));
    if (lint) assert.ok(saved.states.every(row=>['passed','not run'].includes(row.state)));
    if (allLocal) assert.equal(f.fake.posts.length,0);
  });
}
for (const json of [false,true]) for (const list of [false,true]) for (const allLocal of [false,true]) {
  test(`2826: workflow status shows saved Runtime coverage and omissions (${json ? 'JSON' : 'text'}, ${list ? 'list' : 'detail'}, ${allLocal ? 'local' : 'mixed'})`,async t => {
    const checked = await check(t,{allLocal}), results = checked.read();
    const f = await workflow(t); assert.equal((await f.run()).exitCode,0);
    const run = f.record(); run.state='completed'; run.done.check={at:f.clock,area:run.areas[0].name,pddResults:results};
    writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run));
    const out = await runStatus({cwd:f.source,...(list ? {all:true} : {ref:'17'}),json},f.ports);
    assert.equal(out.exitCode,0,out.message);
    if (json) {
      const row = JSON.parse(out.message).runs[0];
      assert.deepEqual(row.runtimeCoverage,checked.result.coverage.runtime,'status-runtime coverage');
      assert.equal(row.nativeOnly[0].prompts[0].reason,reason);
    } else { assert.match(out.message,new RegExp(`Runtime coverage: ${allLocal ? '0 of 1' : '1 of 2'} prompts checkable, 1 native-only`)); assert.ok(out.message.includes(reason)); }
  });
}

for (const lint of [false,true]) test(`2826: all-local ${lint ? 'lint' : 'check'} saved reads need no authentication`,async t => {
  const f = await check(t,{lint,allLocal:true});
  assert.ok(f.result.batch,'local-native batch saved');
  const {ports} = portsFor(f.env); ports.gh = () => assert.fail('local-native read must not sign in');
  const code = await runCheck({cwd:f.setup.repo,options:{'--read':f.result.batch,'--json':true}},ports);
  assert.equal(code,5,ports.stderr.text+ports.stdout.text);
  const saved = JSON.parse(ports.stdout.text);
  assert.deepEqual(saved.coverage.runtime,f.result.coverage.runtime);
  assert.equal(saved.rows[0].state,'not run'); assert.ok(JSON.stringify(saved.rows[0]).includes(reason));
  assert.equal(f.fake.posts.length,0);
});

test('2826: a local refusal beside native-only evidence remains readable without authentication',async t => {
  const setup = harbor(t,repo => {
    writeFileSync(join(repo,'prompts/ordinary.prompt.md'),readFileSync(join(repo,PLACE)));
    native(repo); storyTest(repo,'broken');
    scenario(repo,doc => {doc.criteria=[];doc.steps[0].entry_path='prompts/ordinary.prompt.md';},'broken');
  });
  const {ports} = portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state});
  ports.gh = () => assert.fail('local selection must not sign in');
  assert.equal(await runCheck({cwd:setup.repo,words:['place-order','broken'],options:{'--json':true}},ports),5);
  const first = JSON.parse(ports.stdout.text); assert.ok(first.batch,'mixed-local evidence saved');
  const {ports:read} = portsFor(ports.env); read.gh = ports.gh;
  assert.equal(await runCheck({cwd:setup.repo,options:{'--read':first.batch,'--json':true}},read),5,read.stderr.text);
  const saved = JSON.parse(read.stdout.text);
  assert.equal(saved.rows.find(row => row.test==='tests/broken.json').state,'not run');
  assert.equal(saved.rows.find(row => row.test==='tests/place-order.json').state,'not run');
});
