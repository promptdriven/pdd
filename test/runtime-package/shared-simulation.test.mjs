import test from 'node:test';
import assert from 'node:assert/strict';
import { expandSource } from '../../src/runtime/contract-refs.mjs';

const files = {
  'contracts/map.json': '{"read":{"kind":"read_world","value_template":{"$ref":"/world/stock"},"large":9007199254740993},"write":{"kind":"write_world","value_template":{"$ref":"/input/value"}},"__proto__":{"literal":{"$simulation":"untouched"}}}',
  'contracts/wrapper.json': '{"$simulation":"contracts/map.json#","simulation":{"read":{"kind":"replacement"}}}',
  'contracts/cycle.json': '{"$simulation":"contracts/cycle.json#"}',
  'contracts/records.md': '### Bindings\n```json\n{"read":{"kind":"read_world"}}\n```\n',
};
const port = { stat: ({path}) => ({exists:Object.hasOwn(files,path),is_symlink:path === 'contracts/link.json',size:Buffer.byteLength(files[path] ?? '')}), read: ({path}) => ({content:files[path]}) };
const expand = text => expandSource({path:'tests/scenario.json',text,format:'scenario'},port);

test('shared maps expand transitively, replace whole bindings, preserve literal keys and exact numbers', () => {
  const result = expand('{"before": 1, "$simulation": "contracts/wrapper.json#", "simulation": {"write":{"kind":"local"}}, "steps": [{"input":{"$simulation":"literal"}}]}');
  assert.equal(result.text, '{"before": 1, "simulation": {"read":{"kind":"replacement"},"write":{"kind":"local"},"__proto__":{"literal":{"$simulation":"untouched"}}}, "steps": [{"input":{"$simulation":"literal"}}]}');
  assert.deepEqual(result.references.map(r=>[r.source_pointer,r.target,r.kind]), [['/$simulation','contracts/map.json#','simulation'],['/$simulation','contracts/wrapper.json#','simulation']]);
  assert.match(result.references[0].value_json,/9007199254740993/);
  assert.equal(Object.hasOwn(JSON.parse(result.text).simulation,'__proto__'),true);
  assert.equal({}.polluted,undefined);
});

test('root replacement retains surrounding layout, and Markdown records are supported', () => {
  assert.equal(expand(' { "before": 1, "$simulation" : "contracts/records.md#Bindings", "after": 2 } ').text,' { "before": 1, "simulation" : {"read":{"kind":"read_world"}}, "after": 2 } ');
  const unchanged=' \n{"steps":[{"input":{"$simulation":"literal"}}]}\n';
  assert.equal(expand(unchanged).text,unchanged);
});

test('invalid, missing, unsafe and cyclic references report the scenario and location', () => {
  for (const [text,code] of [
    ['{"$simulation":5}','contract-invalid'],
    ['{"$simulation":"contracts/map.json#","simulation":[]}','contract-invalid'],
    ['{"$simulation":"contracts/missing.json#"}','contract-missing'],
    ['{"$simulation":"../secret.json#"}','contract-unsafe'],
    ['{"$simulation":"contracts/cycle.json#"}','contract-cycle'],
    ['{"$simulation":"contracts/map.json#bad"}','contract-invalid'],
  ]) assert.throws(()=>expand(text),e=>e.code===code && e.message.includes('tests/scenario.json') && e.message.includes('/$simulation'));
});

test('duplicate reference members are all removed with the last value selected', () => {
  const result=expand('{"$simulation":"contracts/missing.json#","x":1,"$simulation":"contracts/records.md#Bindings","simulation":{"extra":{}}}');
  assert.equal(result.text,'{"x":1,"simulation":{"read":{"kind":"read_world"},"extra":{}}}');
});

test('preflight and captured execution source use the same expanded bindings', async t => {
  const { cpSync, mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } = await import('node:fs');
  const { join } = await import('node:path');
  const { spawnSync } = await import('node:child_process');
  const { findTests, preflight, captureSource } = await import('../../src/runtime-seam.mjs');
  const repo=mkdtempSync(join(process.cwd(),'.shared-simulation-'));
  t.after(()=>rmSync(repo,{recursive:true,force:true}));
  cpSync(new URL('../fixtures/harbor/',import.meta.url),repo,{recursive:true});
  mkdirSync(join(repo,'contracts'),{recursive:true});
  const scenario=JSON.parse(readFileSync(join(repo,'tests/place-order.json'),'utf8'));
  const shared={'store.read':{action:'read_world',world_pointer:'/stock'},'store.write':{action:'write_world',world_pointer:'/stock'}};
  writeFileSync(join(repo,'contracts/bindings.json'),JSON.stringify(shared));
  scenario.$simulation='contracts/bindings.json#';
  scenario.simulation={'store.read':{action:'read_world',world_pointer:'/alternate'}};
  scenario.steps[0].simulation_overrides={'store.write':{action:'write_world',world_pointer:'/step'}};
  writeFileSync(join(repo,'tests/place-order.json'),JSON.stringify(scenario));
  for (const args of [['init','-q'],['add','-A']]) assert.equal(spawnSync('git',args,{cwd:repo}).status,0);
  const found=findTests({root:repo}), selected=found.tests.filter(item=>item.path==='tests/place-order.json');
  assert.deepEqual(preflight({root:repo,found,selected}).rows[0].refusals,[]);
  const capture=captureSource(repo,{tests:['tests/place-order.json']});
  const extracted=spawnSync('tar',['-xOf','-','tests/place-order.json'],{input:capture.tar});
  assert.equal(extracted.status,0,extracted.stderr.toString());
  const effective=JSON.parse(extracted.stdout.toString());
  assert.deepEqual(effective.simulation,{'store.read':scenario.simulation['store.read'],'store.write':shared['store.write']});
  assert.deepEqual(effective.steps[0].simulation_overrides,scenario.steps[0].simulation_overrides);
  assert.equal(Object.hasOwn(effective,'$simulation'),false);
});
