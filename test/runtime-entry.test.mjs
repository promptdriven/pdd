import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { Readable } from 'node:stream';
import * as api from '../src/runtime/index.mjs';
import * as numbers from '../src/runtime/scenario-json.mjs';
import * as preflight from '../src/runtime/runtime-preflight.mjs';
import * as output from '../src/runtime/runtime-output.mjs';
import { harbor, fakeRuntime, portsFor, sink } from './runtime-fake.mjs';

test('package API commands defer loading, forward inputs and ports, and retain delegate returns', () => {
  const script = `
    import assert from 'node:assert/strict';
    import { registerHooks } from 'node:module';
    const loaded = [];
    const owners = {
      'runtime-client.mjs': ['runCheck', 'runTry', 'checkRuntimeHealth', 'savedStoryEvidence'],
      'runtime-slots.mjs': ['runJobs'], 'try-mcp.mjs': ['runMcp'],
      'interface-draft.mjs': ['runInterfaceDraft'], 'contracts.mjs': ['runContracts'],
    };
    registerHooks({
      resolve(specifier, context, next) {
        const name = specifier.split('/').at(-1);
        return owners[name] && context.parentURL?.endsWith('/runtime/index.mjs')
          ? { url: 'mock:' + name, shortCircuit: true } : next(specifier, context);
      },
      load(url, context, next) {
        if (!url.startsWith('mock:')) return next(url, context);
        const name = url.slice(5); loaded.push(name);
        return { format: 'module', shortCircuit: true, source: owners[name].map(fn =>
          'export function ' + fn + '(input, ports) { return { name: ' + JSON.stringify(fn) + ', input, ports }; }'
        ).join('\\n') };
      },
    });
    const api = await import(${JSON.stringify(new URL('../src/runtime/index.mjs', import.meta.url).href)});
    api.version(); api.format.parseScenario('{}'); api.render({rows:[]}, {as:'summary'});
    assert.deepEqual(loaded, []);
    const ports = { stdout: {}, marker: {} };
    const workflow = { base_sha: 'base' }, client = { version: 'caller' };
    const cases = [
      ['check', {root:'/repo', tests:[{path:'tests/a.json'}, 'tests/b.json'], options:{'--json':true}, cache:true, workflow, client}, 'runCheck',
        {cwd:'/repo', words:['tests/a.json','tests/b.json'], options:{'--json':true}, cache:true, workflow, client}],
      ['check', {root:'/alias',cwd:'/explicit',tests:['ignored'],words:[],options:{}}, 'runCheck', {cwd:'/explicit',words:[],options:{}}],
      ['lint', {root:'/repo',options:{'--local':true}}, 'runCheck', {cwd:'/repo',options:{'--local':true,'--lint':true}}],
      ['read', {root:'/repo',batch:'batch'}, 'runCheck', {cwd:'/repo',batch:'batch',words:['batch'],options:{'--read':true}}],
      ['read', {call_id:'call',batch:'batch'}, 'runCheck', {call_id:'call',batch:'batch',words:['call'],options:{'--read':true}}],
      ['read', {}, 'runCheck', {options:{'--read':true}}],
      ['retry', {batch:'batch'}, 'runCheck', {batch:'batch',options:{'--retry':'batch'}}],
      ['retry', {options:{'--retry':'old'}}, 'runCheck', {options:{'--retry':'old'}}],
      ['simulate', {root:'/repo',test:'story',mode:'open'}, 'runTry', {cwd:'/repo',test:'story',mode:'open',words:['story']}],
      ...['cli','serve','save-last','stop'].map(mode => ['simulate', {mode,options:{'--json':true}}, 'runTry', {mode,options:{'--json':true,['--'+mode]:true}}]),
      ['jobs', {env:{HOME:'/home'},client}, 'runJobs', {env:{HOME:'/home'},client}],
      ['health', {env:{}}, 'checkRuntimeHealth', {env:{}}],
      ['mcp', {root:'/repo',story:'story',env:{}}, 'runMcp', {cwd:'/repo',story:'story',words:['story'],env:{}}],
      ...['files','fill-hash','explain-bindings'].map(what => ['local', {root:'/repo',what}, 'runCheck', {cwd:'/repo',what,options:{['--'+what]:true}}]),
      ['local', {options:{'--files':true}}, 'runCheck', {options:{'--files':true}}],
      ['draftInterfaces', {root:'/repo',paths:['a'],contract:'c',extend:true,refresh:true,all:true,json:true}, 'runInterfaceDraft',
        {cwd:'/repo',paths:['a'],words:['a'],contract:'c',extend:true,refresh:true,all:true,json:true}],
      ['contracts', {root:'/repo',sync:true,write:true}, 'runContracts', {cwd:'/repo',sync:true,write:true,words:['sync'],options:{'--write':true}}],
    ];
    for (const [name, input, delegate, expected] of cases) {
      const result = await api[name](input, ports);
      assert.equal(result.name, delegate, name);
      assert.deepEqual(result.input, expected, name);
      assert.equal(result.ports, ports, name);
    }
    const input = {root:'/repo',comparisonRoot:'/base'};
    const evidence = await api.saved.results(input, ports);
    assert.equal(evidence.name, 'savedStoryEvidence');
    assert.equal(evidence.input, input); assert.equal(evidence.ports, ports);
    assert.equal(api.contracts({}).name, 'runContracts'); // stays synchronous
    assert.throws(() => api.simulate({mode:'bad'}), TypeError);
    assert.throws(() => api.local({what:'bad'}), TypeError);
    assert.throws(() => api.local({}), TypeError);
    assert.deepEqual(loaded.sort(), Object.keys(owners).sort());
  `;
  const result = spawnSync(process.execPath, ['--input-type=module', '-e', script], { encoding: 'utf8' });
  assert.equal(result.status, 0, result.stderr);
});

test('command import failure reaches the invocation guard, leaving local readers usable', () => {
  const script = `
    import assert from 'node:assert/strict';
    import { registerHooks } from 'node:module';
    registerHooks({resolve(specifier, context, next) {
      if (specifier === './runtime-client.mjs') throw Error('client unavailable');
      return next(specifier, context);
    }});
    const api = await import(${JSON.stringify(new URL('../src/runtime/index.mjs', import.meta.url).href)});
    assert.equal(api.version().engine_sha, null);
    assert.equal(api.format.isScenario('{}'), false);
    for (const name of ['check','lint','read','retry','simulate','health']) {
      await assert.rejects(() => api[name](), /client unavailable/);
    }
    await assert.rejects(() => api.saved.results({root:'/repo'}), /client unavailable/);
  `;
  const result = spawnSync(process.execPath, ['--input-type=module', '-e', script], { encoding: 'utf8' });
  assert.equal(result.status, 0, result.stderr);
});

test('format group retains exact numbers, leaf binding identity and native reader shapes', () => {
  assert.equal(api.format.parseScenario, numbers.parseScenarioJson);
  assert.equal(api.format.stringifyScenario, numbers.stringifyScenarioJson);
  assert.equal(api.format.exactValue, numbers.exactValue);
  assert.equal(api.format.interfaceBlocks, api.interfaceBlocks);
  assert.equal(api.format.interfaceProblems, preflight.interfaceSchemaProblems);
  assert.equal(api.format.storyCriteria, preflight.storyCriteria);
  const text = '{"schema_version":"prompt-runtime.program-scenario.v1","n":9007199254740993}';
  assert.equal(api.format.parseScenario(text).n, 9007199254740993n);
  assert.equal(api.format.stringifyScenario(api.format.parseScenario(text)), text);
  assert.equal(api.format.isScenario(text), true);
  assert.equal(api.format.isScenario('null'), false);
  assert.throws(() => api.format.isScenario('{'), SyntaxError);
  assert.deepEqual(api.format.storyCriteria('## Acceptance criteria\n\n1. Works.\n'), ['Works.']);
});

const prompt = body => '# Prompt\n\nKeep prose.\n\n<details><summary>Runtime interface</summary>\n\n```json\n' + body + '\n```\n</details>\n';

test('metadata text editor preserves other bytes, nested keys and exact digits in either direction', () => {
  const original = prompt('{ "nested": {"status":"nested", "prose_sha256":"nested"}, "status" : "draft", "prose_sha256" : "old", "n":9007199254740993 }');
  const approved = api.format.setInterfaceStatus(original, {status:'approved',prose_sha256:'new"hash'});
  assert.equal(approved, original.replace('"status" : "draft"', '"status" : "approved"').replace('"prose_sha256" : "old"', '"prose_sha256" : "new\\"hash"'));
  assert.equal(api.proseSha256(approved), api.proseSha256(original));
  assert.equal(api.format.setInterfaceStatus(approved, {status:'draft',prose_sha256:'old'}), original);
});

test('metadata text editor refuses ambiguous and invalid interfaces', () => {
  for (const body of ['{', 'null', '[]', '{}', '{"status":null,"prose_sha256":""}',
    '{"status":"draft","prose_sha256":2}', '{"status":"draft","status":"draft","prose_sha256":""}',
    '{"status":"draft","prose_sha256":"","prose_sha256":""}']) {
    assert.equal(api.format.setInterfaceStatus(prompt(body), {status:'approved',prose_sha256:'hash'}), null, body);
  }
  const text = prompt('{"status":"draft","prose_sha256":""}');
  assert.equal(api.format.setInterfaceStatus(text + text, {status:'approved',prose_sha256:'hash'}), null);
  assert.equal(api.format.setInterfaceStatus(text, {status:'unknown',prose_sha256:'hash'}), null);
  assert.equal(api.format.setInterfaceStatus(text, {status:'approved'}), null);
});

test('render preserves the existing text, object, pair-list and summary results', () => {
  const result = {rows:[{test:'tests/a.json',story:'A',state:'passed',calls:0}],batch:null,repo:'/repo',exitCode:0};
  assert.equal(api.render(result), output.renderText(result));
  assert.deepEqual(api.render(result,{as:'json'}), output.renderJson(result));
  assert.deepEqual(api.render(result,{as:'story-lines'}), output.storyLines(result.rows));
  assert.equal(api.render(result,{as:'summary'}), output.summaryLine(result.rows));
  assert.throws(() => api.render(result,{as:'bad'}), TypeError);
});

test('source and workspace groups preserve capture bytes and policy behavior', t => {
  const setup = harbor(t);
  const capture = api.source.identity({root:setup.repo,tests:['tests/place-order.json']});
  assert.deepEqual(capture, api.captureSource(setup.repo,{tests:['tests/place-order.json']}));
  assert.ok(capture.tar.length > 0);
  assert.equal(api.workspace.policy, api.loadRuntimeWorkspace);
  assert.equal(api.workspace.allows, api.allowsRuntimePath);
  assert.deepEqual(api.workspace.policy({root:setup.repo}), {configured:false,allowed_paths:[]});
});

test('version uses local format facts and marks unavailable package, API and engine identities unknown', () => {
  assert.deepEqual(api.version(), {package:null,api_version:null,formats:{scenario:'prompt-runtime.program-scenario.v1'},limits:{bytes:10485760,files:10000},engine_sha:null});
  assert.equal(api.version().limits, api.LIMITS);
});

test('check, lint, read and retry wrappers run the existing fake Runtime flow with streamed JSON', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const {ports} = portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin});
  assert.equal(await api.lint({root:setup.repo,tests:[{path:'tests/place-order.json'}],options:{'--json':true}},ports), 0);
  ports.stdout.text = '';
  assert.equal(await api.check({root:setup.repo,tests:['tests/place-order.json'],options:{'--json':true}},ports), 0);
  const result = JSON.parse(ports.stdout.text);
  assert.equal(result.rows[0].state, 'passed');
  assert.equal(typeof result.batch, 'string');
  ports.stdout.text = '';
  assert.equal(await api.read({root:setup.repo,batch:result.batch,options:{'--json':true}},ports), 0);
  assert.equal(JSON.parse(ports.stdout.text).rows[0].state, 'passed');
  ports.stdout.text = '';
  assert.equal(await api.retry({root:setup.repo,batch:result.batch,options:{'--json':true}},ports), 0);
  assert.equal(JSON.parse(ports.stdout.text).rows[0].state, 'passed');
  assert.equal((await api.saved.results({root:setup.repo},ports)).stories.length, 1);
});

test('local, jobs, health, contracts, drafts and MCP preserve native returns without a live service', async t => {
  const setup = harbor(t);
  const env = {HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:'https://runtime.example.test'};
  const ports = {env,stdout:sink(),stderr:sink(),stdin:Readable.from([]),
    gh:() => ({status:1,stdout:''}),fetch:() => {throw Error('network forbidden');}};
  assert.equal(await api.local({root:setup.repo,tests:['tests/place-order.json'],what:'files'},ports), 0);
  assert.match(ports.stdout.text, /place_order/);
  assert.equal(await api.jobs({env},ports), 0);
  assert.equal((await api.health({env},ports)).state, 'access');
  assert.equal(api.contracts({root:setup.repo},ports), 0);
  assert.equal(await api.draftInterfaces({root:setup.repo,paths:['prompts/place_order.prompt.md']},ports), 0);
  assert.equal(await api.mcp({root:setup.repo,env},ports), 0);
  assert.ok(readFileSync(join(setup.repo,'prompts/place_order.prompt.md'),'utf8').length > 0);
});
