import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runStatus } from '../src/workflow-runner.mjs';
import { fixture } from './helpers/workflow-runner-fixture.mjs';

const scenario = JSON.parse(readFileSync(new URL('./runtime/workflow-status-json-2571.json', import.meta.url)));

test('2571 scenario replay: empty machine list', async t => {
  const f = await fixture(t);
  for (const step of scenario.steps) {
    const result = await runStatus({...step.input, cwd:f.source}, {...f.ports, allRuns: () => JSON.parse(scenario.simulation["runs.allRuns"].result_template.json)});
    for (const check of step.checks) {
      assert.equal(check.target, 'result');
      const actual = check.path.slice(1).split('/').reduce((v,k) => v?.[k], result);
      if (check.op === 'equals') assert.deepEqual(actual, check.value);
      else if (check.op === 'contains') assert.ok(actual.includes(check.value));
      else assert.fail(`Unsupported operation ${check.op}`);
    }
  }
});

test('machine status forwards cancellation to the injected run index', async t => {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  const calls = [];
  const allRuns = (options, ports) => { calls.push({options, ports}); return [f.record()]; };
  const result = await runStatus({cwd:f.source, all:true, json:true, cancelled:true}, {...f.ports, allRuns});
  assert.deepEqual(calls.map(call => call.options), [{cancelled:true}]);
  assert.equal(calls[0].ports.allRuns, allRuns);
  assert.deepEqual(JSON.parse(result.message).runs.map(run => run.ref), ['example/project#17']);
});

test('2571 list projection preserves useful state and redacts private text', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode, 0);
  const path = join(f.source, '.git/pdd/runs/17/status.json');
  const record = f.record();
  record.issue.title = 'See https://runtime.example/s/secret/';
  record.question = {text:'Review https://runtime.example/s/private/', at: 99};
  record.gate = {kind:'approve-pr', area:record.areas[record.area].name, at: 1};
  record.pr = [{number:23,url:'https://github.com/example/project/pull/23',state:'open',draft:true,ci:'passing', raw:'private metadata'}];
  record.chats.at(-1).secret = 'private metadata';
  writeFileSync(path, JSON.stringify(record));
  const result = await runStatus({cwd:f.source,all:true,json:true}, {...f.ports, readPrStatus:async()=>({state:'open',draft:true,ci:'passing'}), herdr:async()=>{throw Error('unavailable');}});
  const data = JSON.parse(result.message), row = data.runs[0];
  assert.equal(data.version, 1); assert.equal(row.ref,'example/project#17');
  assert.deepEqual(row.prs,[{number:23,url:'https://github.com/example/project/pull/23',state:'open',draft:true,ci:'passing'}]);
  assert.equal(row.waiting.kind,'question'); assert.equal(row.waiting.gate,null);
  assert.equal(row.chat.session,'pdd'); assert.equal(row.chat.pane,row.chat.paneId);
  assert.ok(!result.message.includes('/s/secret')); assert.ok(!result.message.includes('/s/private'));
  assert.ok(!result.message.includes('private metadata')); assert.ok(!('chats' in row)); assert.ok(!('steps' in row));
  const old = JSON.parse((await runStatus({cwd:f.source,ref:'17',json:true},f.ports)).message);
  assert.equal(old.version,undefined); assert.ok(Array.isArray(old.runs[0].chats));
});

test('2571 waiting precedence, gate identity and absence of observation', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
  const path = join(f.source, '.git/pdd/runs/17/status.json');
  const initial = f.record(), area = initial.areas[initial.area].name;
  const status = async change => {
    const run = structuredClone(initial); change(run); writeFileSync(path, JSON.stringify(run));
    return JSON.parse((await runStatus({cwd:f.source,all:true,json:true}, {...f.ports, herdr:async()=>{throw Error('unavailable');}})).message).runs[0];
  };
  const gate = await status(run => {run.gate={id:'gate-1',kind:'approve-pr',area,at:1};});
  assert.deepEqual(gate.waiting,{kind:'gate',gate:'gate-1',question:null,reason:null});
  const startup = await status(run => {run.gate={id:'gate-1',kind:'approve-pr',area,at:1};run.question={text:'Q?',at:2};run.chatFailure={area,phase:'open',code:'failed',message:'failure',at:3};});
  assert.deepEqual(startup.waiting,{kind:'startup_failed',gate:null,question:null,reason:null});
  const noObservation = await status(run => {run.gate=null;run.question=null;});
  assert.equal(noObservation.waiting,null);
});

// Validate the public JSON against the repository contract, failing on unsupported schema keywords.
function validate(schema, value) {
  const allowed = new Set(['$schema','$id','type','properties','required','additionalProperties','items','anyOf','enum','const','minimum']);
  for (const key of Object.keys(schema)) assert.ok(allowed.has(key), `unsupported schema keyword ${key}`);
  if (schema.anyOf) return schema.anyOf.some(choice => { try { validate(choice, value); return true; } catch { return false; } }) || assert.fail('no schema alternative matched');
  if ('const' in schema) assert.deepEqual(value, schema.const);
  if (schema.enum) assert.ok(schema.enum.includes(value));
  if (schema.type) {
    const types = Array.isArray(schema.type) ? schema.type : [schema.type];
    const matches = type => type === 'null' ? value === null : type === 'array' ? Array.isArray(value) : type === 'object' ? value !== null && typeof value === 'object' && !Array.isArray(value) : type === 'integer' ? Number.isInteger(value) : typeof value === type;
    assert.ok(types.some(matches), `expected ${types.join('|')}`);
  }
  if (schema.minimum !== undefined) assert.ok(value >= schema.minimum);
  if (schema.items) for (const item of value) validate(schema.items, item);
  if (schema.properties) {
    for (const key of schema.required ?? []) assert.ok(Object.hasOwn(value,key), `missing ${key}`);
    for (const [key, val] of Object.entries(value)) {
      if (schema.properties[key]) validate(schema.properties[key], val);
      else if (schema.additionalProperties === false) assert.fail(`unexpected ${key}`);
    }
  }
}

test('2571 public output conforms to the versioned schema and rejects drift', async t => {
  const schema = JSON.parse(readFileSync(new URL('../docs/workflow-status-v1.schema.json', import.meta.url)));
  assert.equal(schema.properties.version.const, 1);
  const f = await fixture(t); assert.equal((await f.run()).exitCode, 0);
  const output = JSON.parse((await runStatus({cwd:f.source, all:true, json:true}, f.ports)).message);
  validate(schema, output);
  for (const mutate of [v => {v.version=2;}, v => {delete v.runs[0].waiting;}, v => {v.runs[0].prs=[{number:1,url:'u',state:'open',draft:'yes',ci:null}];}, v => {v.runs[0].extra=true;}, v => {v.runs[0].group='other';}]) {
    const invalid = structuredClone(output); mutate(invalid); assert.throws(() => validate(schema, invalid));
  }
});

test('2571 versioned list reports observed and previously recorded stops', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
  const run = f.record(), pane = f.herdr.paneOf(run.chats[0]);
  pane.agent = null; f.tick(60000);
  const read = async ports => JSON.parse((await runStatus({cwd:f.source,all:true,json:true},ports)).message).runs[0].waiting;
  assert.deepEqual(await read(f.ports), {kind:'chat_stopped',gate:null,question:null,reason:'exited'});
  const saved = f.record(); saved.chats[0].evidence = {kind:'other'};
  writeFileSync(join(f.source,'.git/pdd/runs/17/status.json'), JSON.stringify(saved));
  const down = {...f.ports, herdr:async()=>{throw Error('unavailable');}};
  assert.deepEqual(await read(down), {kind:'chat_stopped',gate:null,question:null,reason:'unknown'});
});

test('2571 list reads the current draft flag from GitHub', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
  const run = f.record(); run.state = 'waiting'; run.pr = [{number:23,url:'https://github.com/example/project/pull/23',state:'open',draft:false,ci:'none'}];
  writeFileSync(join(f.source,'.git/pdd/runs/17/status.json'),JSON.stringify(run));
  const calls = [], execFile = async (file,args,opts) => {
    if (file === 'gh' && args[0] === 'pr' && args[1] === 'view') {
      calls.push(args); return {stdout:JSON.stringify({state:'OPEN',statusCheckRollup:[],isDraft:true})};
    }
    return f.ports.execFile(file,args,opts);
  };
  const output = JSON.parse((await runStatus({cwd:f.source,all:true,json:true},{...f.ports,execFile})).message);
  assert.equal(output.runs[0].prs[0].draft,true);
  assert.ok(calls[0].at(-1).split(',').includes('isDraft'));
});


test('2571 live chat waiting follows the visible gate and question state', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode, 0);
  const path = join(f.source, '.git/pdd/runs/17/status.json');
  const run = f.record(), pane = f.herdr.paneOf(run.chats[0]);
  const read = async () => JSON.parse((await runStatus({cwd:f.source,all:true,json:true}, f.ports)).message).runs[0];
  run.gate = {id:'gate-live',kind:'approve-pr',area:run.areas[run.area].name,at:1};
  writeFileSync(path, JSON.stringify(run));
  pane.agent.agent_status = 'working';
  let row = await read();
  assert.equal(row.group, 'working'); assert.equal(row.waiting, null);
  pane.agent.agent_status = 'idle';
  row = await read();
  assert.equal(row.group, 'waiting'); assert.deepEqual(row.waiting,{kind:'gate',gate:'gate-live',question:null,reason:null});
  run.gate = null; run.state = 'running'; writeFileSync(path, JSON.stringify(run));
  pane.agent.agent_status = 'blocked';
  row = await read();
  assert.equal(row.group, 'waiting'); assert.match(row.words,/chat asks a question/);
  assert.deepEqual(row.waiting,{kind:'question',gate:null,question:null,reason:null});
});
