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

test('preflight and capture agree for shared and inline resource bindings', async t => {
  const { cpSync, mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } = await import('node:fs');
  const { join } = await import('node:path');
  const { spawnSync } = await import('node:child_process');
  const { findTests, preflight, captureSource, interfaceBlocks, proseSha256 } = await import('../../src/runtime-seam.mjs');
  const repo=mkdtempSync(join(process.cwd(),'.shared-simulation-'));
  t.after(()=>rmSync(repo,{recursive:true,force:true}));
  cpSync(new URL('../fixtures/harbor/',import.meta.url),repo,{recursive:true});
  mkdirSync(join(repo,'contracts'),{recursive:true});
  const promptPath=join(repo,'prompts/place_order.prompt.md');
  let prompt=readFileSync(promptPath,'utf8');
  const block=interfaceBlocks(prompt)[0], iface=JSON.parse(block[1]);
  const schema={type:'object',properties:{},required:[],additionalProperties:false};
  iface.resources=[{name:'store',kind:'key_value',access:'read_write',operations:['read','write'].map(name=>({name,arguments_schema:schema,result_schema:schema}))}];
  iface.entries[0].resource_operations=['store.read','store.write'];
  prompt=prompt.replace(block[1],JSON.stringify(iface));
  iface.prose_sha256=proseSha256(prompt);
  writeFileSync(promptPath,prompt.replace(interfaceBlocks(prompt)[0][1],JSON.stringify(iface)));
  const scenario=JSON.parse(readFileSync(join(repo,'tests/place-order.json'),'utf8'));
  const shared={'store.read':{kind:'read_world',value_template:{$ref:'/world/stock'}},'store.write':{kind:'write_world',value_template:{$ref:'/input/value'},result_template:{ok:true}}};
  const replacement={kind:'read_world',value_template:{$ref:'/world/alternate'}};
  const stepOverride={kind:'write_world',value_template:{$ref:'/input/other'},result_template:{ok:true}};
  writeFileSync(join(repo,'contracts/bindings.json'),JSON.stringify(shared));
  scenario.steps[0].simulation_overrides={'store.write':stepOverride};
  scenario.$simulation='contracts/bindings.json#';
  scenario.simulation={'store.read':replacement};
  const path=join(repo,'tests/place-order.json');
  writeFileSync(path,JSON.stringify(scenario));
  for (const args of [['init','-q'],['add','-A']]) assert.equal(spawnSync('git',args,{cwd:repo}).status,0);
  const inspect = () => {
    const found=findTests({root:repo}), selected=found.tests.filter(item=>item.path==='tests/place-order.json');
    const checked=preflight({root:repo,found,selected}).rows[0].refusals;
    const capture=captureSource(repo,{tests:['tests/place-order.json']});
    const source=JSON.parse(capture.sources.find(item=>item.path==='tests/place-order.json').bytes.toString());
    return {checked,source,plan:capture.bindingPlans[0]};
  };
  const { runPdd } = await import('../../src/pdd-cli.mjs');
  const explain = async () => {
    const stdout={text:'',write(value){this.text+=value;}}, stderr={text:'',write(value){this.text+=value;}};
    const exit=await runPdd(['test','--explain-bindings','place-order','--json'],{cwd:repo,env:process.env,stdout,stderr});
    assert.ok(stdout.text,stderr.text);
    return {exit,plan:JSON.parse(stdout.text).plans[0]};
  };
  const compact=inspect();
  const compactExplanation=await explain();
  assert.equal(compactExplanation.exit,0);
  assert.deepEqual(compact.checked,[]);
  assert.deepEqual(compact.source.simulation,{'store.read':replacement,'store.write':shared['store.write']});
  assert.deepEqual(compact.source.steps[0].simulation_overrides,{'store.write':stepOverride});
  assert.ok(compact.plan.edges.every(edge=>edge.state==='bound'));
  delete scenario.$simulation;
  scenario.simulation={'store.read':replacement,'store.write':shared['store.write']};
  writeFileSync(path,JSON.stringify(scenario));
  const inline=inspect();
  const inlineExplanation=await explain();
  assert.deepEqual(compactExplanation,inlineExplanation);
  assert.deepEqual(compact.source,inline.source);
  assert.deepEqual(compact.checked,inline.checked);
  assert.deepEqual(compact.plan.edges,inline.plan.edges);
  // The step's override binds write even when the scenario-level write is absent.
  delete scenario.simulation['store.write'];
  writeFileSync(path,JSON.stringify(scenario));
  assert.equal(inspect().plan.edges.find(edge=>edge.key==='store.write').state,'bound');
  delete scenario.steps[0].simulation_overrides;
  scenario.$simulation='contracts/incomplete.json#';
  scenario.simulation={};
  writeFileSync(join(repo,'contracts/incomplete.json'),JSON.stringify({'store.read':shared['store.read']}));
  writeFileSync(path,JSON.stringify(scenario));
  assert.equal(spawnSync('git',['add','contracts/incomplete.json'],{cwd:repo}).status,0);
  assert.equal(inspect().plan.edges.find(edge=>edge.key==='store.write').state,'missing');
  const refused=await explain();
  assert.equal(refused.exit,4);
  assert.equal(refused.plan.edges.find(edge=>edge.key==='store.write').state,'missing');
});
