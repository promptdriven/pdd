import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck, findTests, preflight, interfaceBlocks, proseSha256 } from '../../src/runtime-seam.mjs';
import { harbor, portsFor, PLACE, storyTest } from './runtime-fake.mjs';

const TEST = 'tests/place-order.json';
const read = (repo, path) => JSON.parse(readFileSync(join(repo, path), 'utf8'));
const write = (repo, path, value) => writeFileSync(join(repo, path), JSON.stringify(value));
function schema(repo, value) {
  let text = readFileSync(join(repo, PLACE), 'utf8');
  const block = interfaceBlocks(text)[0], iface = JSON.parse(block[1]);
  iface.entries[0].result_schema = value;
  iface.status = 'draft';
  text = text.slice(0, block.indices[1][0]) + JSON.stringify(iface) + text.slice(block.indices[1][1]);
  text = text.replace(/"prose_sha256"\s*:\s*"[^"]*"/, `"prose_sha256":"${proseSha256(text)}"`);
  writeFileSync(join(repo, PLACE), text);
}
const object = properties => ({type:'object', properties, required:[], additionalProperties:false});
const scalar = {type:'string'};

test('local lint admits selected cases offline and refuses malformed checks independently', async t => {
  const f = harbor(t, repo => storyTest(repo, 'another'));
  const doc = read(f.repo, TEST);
  doc.steps[0].checks[0].target = 'bogus';
  write(f.repo, TEST, doc);
  let calls = 0;
  const {ports} = portsFor({HOME:f.home, PDD_STATE_DIR:f.state}, {gh:()=>{calls++; throw Error('gh');}, fetch:()=>{calls++; throw Error('fetch');}});
  const code = await runCheck({cwd:f.repo, words:[TEST, 'tests/another.json'], options:{'--lint':true,'--local':true,'--json':true}}, ports);
  assert.equal(code, 4, ports.stderr.text);
  const result = JSON.parse(ports.stdout.text);
  assert.ok(result.problems.some(p => p.code === 'invalid-check' && p.path === TEST));
  assert.equal(result.state, 'partial');
  assert.equal(result.reason.code, 'local-only');
  assert.equal(calls, 0);
});

test('result pointers reject impossible paths but accept optional fields and viable variants', t => {
  const f = harbor(t), doc = read(f.repo, TEST);
  doc.steps[0].checks = [doc.steps[0].checks[0]];
  schema(f.repo, object({optional:object({'a/b':scalar}), list:{type:'array',items:object({value:scalar})}, choice:{oneOf:[object({first:scalar}),object({second:scalar})]}}));
  for (const [path, valid] of [['/optional/a~1b',true], ['/list/0/value',true], ['/choice/second',true], ['/missing',false], ['/list/0/missing',false], ['/choice/neither',false], ['/optional/bad~2escape',false]]) {
    doc.steps[0].checks[0].path = path;
    write(f.repo, TEST, doc);
    const found = findTests({root:f.repo});
    const row = preflight({root:f.repo, found, selected:found.tests.filter(item=>item.path===TEST)}).rows[0];
    assert.equal(row.refusals.some(item=>item.code==='invalid-check'), !valid, `${path}: ${JSON.stringify(row.refusals)}`);
  }
});

test('named selection ignores an unrelated invalid interface and refuses invalid JSON', async t => {
  const f = harbor(t, repo => storyTest(repo, 'another'));
  writeFileSync(join(f.repo, 'prompts/unrelated.prompt.md'), '# No interface\n');
  const {ports} = portsFor({HOME:f.home, PDD_STATE_DIR:f.state});
  let code = await runCheck({cwd:f.repo, words:['tests/another.json'], options:{'--lint':true,'--local':true,'--json':true}}, ports);
  assert.equal(code, 0, ports.stdout.text + ports.stderr.text);
  writeFileSync(join(f.repo, TEST), '{invalid');
  ports.stdout.text = ''; ports.stderr.text = '';
  code = await runCheck({cwd:f.repo, words:[TEST, 'tests/another.json'], options:{'--lint':true,'--local':true,'--json':true}}, ports);
  assert.equal(code, 4, ports.stdout.text + ports.stderr.text);
  assert.ok(JSON.parse(ports.stdout.text).problems.some(p=>p.code==='invalid-document' && p.path===TEST));
});

test('expected error keeps its error check and rejects an extra result check', t => {
  const f = harbor(t), doc = read(f.repo, TEST), step = doc.steps[0];
  step.expected_error = 'unknown-item';
  step.checks = [{criterion_id:doc.criteria[0].id,target:'error',path:'/code',op:'equals',value:'unknown-item'}, {criterion_id:doc.criteria[0].id,target:'result',path:'/totalCents',op:'equals',value:0}];
  write(f.repo, TEST, doc);
  const found = findTests({root:f.repo});
  const row = preflight({root:f.repo,found,selected:found.tests.filter(x=>x.path===TEST)}).rows[0];
  assert.ok(row.refusals.some(p=>p.code==='invalid-check' && /expected_error/.test(p.message)));
});

test('local selection refuses invalid input, missing interface and missing linked source offline', async t => {
  for (const variant of ['input','interface','source']) {
    const f = harbor(t), doc = read(f.repo, TEST);
    if (variant === 'input') { doc.steps[0].input = {}; write(f.repo, TEST, doc); }
    if (variant === 'interface') writeFileSync(join(f.repo, PLACE), '# No interface\n');
    if (variant === 'source') {
      const text = readFileSync(join(f.repo, PLACE), 'utf8');
      writeFileSync(join(f.repo, PLACE), text + '\n[Missing](missing.md)\n');
    }
    const {ports} = portsFor({HOME:f.home,PDD_STATE_DIR:f.state}, {gh:()=>assert.fail('gh'),fetch:()=>assert.fail('fetch')});
    for (const words of [[],[TEST]]) {
      ports.stdout.text = ''; ports.stderr.text = '';
      const exit = await runCheck({cwd:f.repo,words,options:{'--lint':true,'--local':true,'--json':true}},ports);
      assert.equal(exit,4,`${variant}: ${ports.stdout.text} ${ports.stderr.text}`);
    }
  }
});
