import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, existsSync, realpathSync, symlinkSync, unlinkSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { runCompiledTest } from '../src/compiled-test.mjs';
import { executableInterfaceText, parseScenarioJson, stringifyScenarioJson } from '../src/runtime-seam.mjs';
import {
  fixtureProject,
  pureProject,
  clean,
  read,
  save,
  report,
  run,
  scenarioPath,
  promptPath,
  version,
  seamModule,
} from './helpers/code-call-project.mjs';

const check = (criterion_id, target, path, value, op = 'equals') => ({ criterion_id, target, path, op, value });
const watch = text => "import {writeFileSync as markerWrite} from 'node:fs';markerWrite('LAUNCHED','yes');\n" + text;
const schema = type => ({ type });
const steps = data => data.stories[0].steps;

function makeRepo(t, options, pure = false) {
  const root = (pure ? pureProject : fixtureProject)(options);
  t.after(() => clean(root));
  return root;
}

function refusedBeforeLaunch(t, options) {
  const root = makeRepo(t, { appChange: watch, ...options });
  const { out, data } = report(root);
  assert.equal(out.status, 1, out.stderr);
  assert.equal(data.stories[0].status, 'not run');
  assert.equal(existsSync(join(root, 'LAUNCHED')), false);
  return { root, out, data };
}

test('typed request contains only original input, world and simulation; argv literals have no shell expansion', t => {
  const root = makeRepo(
    t,
    { implementation: { kind: 'call', command: [process.execPath, 'examples/fakes/service.mjs', '$(touch BAD)', 'two words'], symbol: 'lookup' } },
    true
  );
  const { out, data } = report(root);
  assert.equal(out.status, 0, out.stderr);
  assert.equal(data.ai_calls, 0);
  assert.equal(existsSync(join(root, 'BAD')), false);
  const request = parseScenarioJson(readFileSync(join(root, 'request.json'), 'utf8'));
  assert.deepEqual(Object.keys(request).sort(), ['schema_version', 'operation', 'symbol', 'input', 'initial_world', 'simulation'].sort());
  assert.equal(request.schema_version, version);
  assert.equal(request.symbol, 'lookup');
  assert.deepEqual(request.input, { id: 'book-7' });
  assert.deepEqual(request.initial_world, {});
  assert.deepEqual(request.simulation, {});
});

test('missing exact fixture arguments or index refuse without any live fallback and stop dependent steps', t => {
  for (const mutation of [
    d => { d.simulation['service.lookup'].cases[0].args.id = 'another'; },
    d => { d.simulation['service.lookup'].cases[0].call_index = 3; },
  ]) {
    const root = makeRepo(t, { change: mutation });
    const { out, data } = report(root);
    assert.equal(out.status, 1);
    assert.equal(steps(data)[0].status, 'not run');
    assert.match(steps(data)[0].reason, /exit 1/);
    assert.equal(steps(data)[1].status, 'not run');
    assert.match(steps(data)[1].reason, /starting world is unknown/);
  }
});

test('unsupported actions, malformed/overlapping fixture bindings and unsupported port kinds refuse before launch', t => {
  const cases = [
    { change: d => { d.simulation['service.lookup'].action = 'command.run'; } },
    { change: d => { d.simulation['service.lookup'].result_template = { label: 'live' }; } },
    { change: d => { d.simulation['service.lookup'].cases[1].call_index = 1; } },
    { change: d => { d.simulation['service.lookup'].extra = true; } },
    { change: d => { d.simulation['service.lookup'].cases[0].args.extra = 'not-complete'; } },
    { change: d => { d.simulation['service.lookup'].cases[0].result.label = 42; } },
    { change: d => { d.initial_world.fixture_counters.lookup = -1; } },
    { change: d => { d.simulation['unknown.lookup'] = d.simulation['service.lookup']; } },
    { change: d => { delete d.simulation['service.lookup']; } },
    { interfaceChange: i => { i.resources[0].kind = 'http'; } },
    {
      interfaceChange: i => { i.resources[0].operations.push({ ...i.resources[0].operations[0], name: 'other' }); },
      change: d => { d.simulation['service.other'] = { ...d.simulation['service.lookup'] }; },
    },
  ];
  for (const spec of cases) refusedBeforeLaunch(t, spec);
});

test('unknown targets, operations, modifiers, references and overrides never launch typed code', t => {
  const cases = [
    d => { d.steps[0].checks[0].target = 'ref'; },
    d => { d.steps[0].checks[0].op = 'contains'; },
    d => { d.steps[0].checks[0].html = { selector: 'div' }; },
    d => { d.steps[0].checks[0].json_path = '$.label'; },
    d => { d.steps[0].checks[0].integer_relation = 'equal'; },
    d => { d.steps[0].checks[0].value = { $step_result: { step_id: 'first-lookup', path: '/label' } }; },
    d => { d.steps[0].input = { $step_result: { step_id: 'x', path: '' } }; },
    d => { d.steps[0].simulation_overrides = { x: { action: 'fixture.lookup' } }; },
    d => { d.steps[0].checks[0].path = '/bad~2escape'; },
    d => { d.steps[0].operation = 'unknown'; },
  ];
  for (const change of cases) refusedBeforeLaunch(t, { change });
});

test('invalid metadata is refused by preflight or adapter check and never launched', t => {
  for (const implementation of [
    { kind: 'call', command: 'node examples/fakes/service.mjs', symbol: 'lookup' },
    { kind: 'call', command: [], symbol: 'lookup' },
    { kind: 'call', command: ['  '], symbol: 'lookup' },
    { kind: 'call', command: [process.execPath, 'bad\0arg'], symbol: 'lookup' },
    { kind: 'call', command: [process.execPath], symbol: '\0' },
    { kind: 'call', command: [process.execPath], symbol: ' ' },
    { kind: 'call', command: [process.execPath], symbol: 'lookup', extra: true },
    { kind: 'unknown', command: [process.execPath], symbol: 'lookup' },
  ]) {
    refusedBeforeLaunch(t, { implementation });
  }
});

test('shared preflight admission preserves stale/status/schema/Story/coverage refusals and admits committed call metadata', t => {
  const committed = makeRepo(t, { useCommittedPrompt: true });
  const rawCommitted = readFileSync(join(committed, promptPath), 'utf8');
  assert.match(rawCommitted, /"kind":\s*"call"/);
  assert.doesNotMatch(executableInterfaceText(rawCommitted), /"implementation"/);
  assert.equal(run(committed).status, 0);

  for (const edit of [
    s => s + '\nchanged prose\n',
    s => s.replace('"status": "draft"', '"status": "unknown"'),
    s => s.replace('"type": "string"', '"type": "string", "unsupported_keyword": true'),
  ]) {
    const root = makeRepo(t, { appChange: watch });
    writeFileSync(join(root, promptPath), edit(readFileSync(join(root, promptPath), 'utf8')));
    const { out, data } = report(root);
    assert.equal(out.status, 1);
    assert.equal(data.stories[0].status, 'not run');
    assert.equal(existsSync(join(root, 'LAUNCHED')), false);
  }
  for (const change of [
    d => { d.criteria[0].text = 'Invented criterion'; },
    d => { d.steps[1].checks = d.steps[0].checks; },
    d => { d.criteria_scope = ['AC1']; },
  ]) {
    refusedBeforeLaunch(t, { change });
  }
});

test('strict source boundaries refuse selected and required symlinks before adapter launch', t => {
  for (const target of [promptPath, scenarioPath, 'docs/code-call-adapters.md']) {
    const root = makeRepo(t, { appChange: watch });
    const outside = join(root, 'outside-content');
    save(root, 'outside-content', readFileSync(join(root, target), 'utf8'));
    unlinkSync(join(root, target));
    symlinkSync(outside, join(root, target));
    const out = run(root);
    assert.notEqual(out.status, 0, target);
    assert.equal(existsSync(join(root, 'LAUNCHED')), false, target);
  }
});

test('configured workspace preserves allowed source and refuses a required dependency outside policy', t => {
  const allowed = ['examples/', 'test/', 'user_stories/', 'docs/'];
  const root = makeRepo(t, { policy: { allowed_paths: allowed } });
  assert.equal(run(root).status, 0);
  const restricted = makeRepo(t, { appChange: watch, policy: { allowed_paths: allowed.filter(path => path !== 'docs/') } });
  const out = run(restricted);
  assert.equal(out.status, 1);
  assert.equal(existsSync(join(restricted, 'LAUNCHED')), false);
});

test('invalid responses, schema errors and process failures do not create a next world', t => {
  const responses = [
    'not json',
    JSON.stringify({ schema_version: version, result: { id: 'book-7' }, world: {}, calls: { resources: {}, internal: {} } }) + '\nnoise',
    { schema_version: version, result: { id: 'book-7' }, world: {}, calls: { resources: {}, internal: {} }, extra: true },
    { schema_version: 'other', result: { id: 'book-7' }, world: {}, calls: { resources: {}, internal: {} } },
    { schema_version: version, result: { id: 'book-7' }, error: { code: 'bad' }, world: {}, calls: { resources: {}, internal: {} } },
    { schema_version: version, result: { id: 'book-7' }, world: [], calls: { resources: {}, internal: {} } },
    { schema_version: version, result: { id: 42 }, world: {}, calls: { resources: {}, internal: {} } },
    { schema_version: version, result: { id: 'book-7' }, world: {}, calls: { resources: { unknown: 0 }, internal: {} } },
    { schema_version: version, result: { id: 'book-7' }, world: {}, calls: { resources: {}, internal: { unexpected: 1 } } },
    { schema_version: version, error: { code: 'undeclared' }, world: {}, calls: { resources: {}, internal: {} } },
  ];
  for (const response of responses) {
    const output = typeof response === 'string' ? response : JSON.stringify(response);
    const root = makeRepo(
      t,
      {
        inputSchema: { type: 'object', properties: { id: schema('string') }, required: ['id'], additionalProperties: false },
        resultSchema: { type: 'object', properties: { id: schema('string') }, required: ['id'], additionalProperties: false },
        app: `process.stdout.write(${JSON.stringify(output)});`,
      },
      true
    );
    const { out, data } = report(root);
    assert.equal(out.status, 1);
    assert.equal(steps(data)[0].status, 'not run');
    assert.equal(steps(data)[1].status, 'not run');
    assert.match(steps(data)[1].reason, /world is unknown/);
  }
  for (const app of ['process.exit(7);', "process.kill(process.pid,'SIGTERM');", 'process.stdout.write(Buffer.from([0xff]));']) {
    const root = makeRepo(t, { app }, true);
    const { out, data } = report(root);
    assert.equal(out.status, 1);
    assert.equal(steps(data)[0].status, 'not run');
  }
  const root = makeRepo(t, { implementation: { kind: 'call', command: ['/missing/pdd-native-app'], symbol: 'lookup' } }, true);
  assert.equal(steps(report(root).data)[0].status, 'not run');
});

test('timeout and signal handling retain bounded spawn options and do not report checks as passed', async t => {
  const root = makeRepo(t, {}, true);
  let launches = 0;
  let output = '';
  const exit = await runCompiledTest(
    { root, words: ['fake-recorded-call'], json: true },
    {
      stdout: { write: text => { output += text; } },
      stderr: { write: () => {} },
      spawn: (cmd, args, options) => {
        if (cmd === 'git') return spawnSync(cmd, args, options);
        launches++;
        assert.equal(options.timeout, 600000);
        assert.equal(options.maxBuffer, 10485760);
        assert.equal(options.cwd, realpathSync(root));
        assert.equal(options.encoding, null);
        assert.deepEqual(
          Object.keys(parseScenarioJson(options.input)).sort(),
          ['schema_version', 'operation', 'symbol', 'input', 'initial_world', 'simulation'].sort()
        );
        return { status: null, error: Object.assign(Error('timed out'), { code: 'ETIMEDOUT' }), signal: 'SIGTERM' };
      },
    }
  );
  assert.equal(exit, 1);
  assert.equal(launches, 1);
  assert.match(steps(parseScenarioJson(output))[0].reason, /timed out/);
});

test('equals/count handles root pointers, complete objects, Unicode, own properties and missing versus null', t => {
  const dataSchema = {
    type: 'object',
    properties: {
      nested: { type: 'object', properties: { a: { type: 'integer' }, b: { type: 'integer' } }, required: ['a', 'b'], additionalProperties: false },
      array: { type: 'array', items: { oneOf: [{ type: 'integer' }, { type: 'null' }] } },
      text: { type: 'string' },
      nullValue: { type: 'null' },
      'a/b': { type: 'object', properties: { '~key': { type: 'boolean' } }, required: ['~key'], additionalProperties: false },
    },
    required: ['nested', 'array', 'text', 'nullValue', 'a/b'],
    additionalProperties: false,
  };
  const root = makeRepo(
    t,
    {
      inputSchema: dataSchema,
      resultSchema: dataSchema,
      change: doc => {
        for (const step of doc.steps) {
          const id = step.checks[0].criterion_id;
          step.input = { nested: { b: 2, a: 1 }, array: [1, null, 2], text: 'A😀', nullValue: null, 'a/b': { '~key': true } };
          step.checks = [
            check(id, 'result', '', step.input),
            check(id, 'result', '/nested', { a: 1, b: 2 }),
            check(id, 'result', '/array', 3, 'count'),
            check(id, 'result', '/nested', 2, 'count'),
            check(id, 'result', '/text', 2, 'count'),
            check(id, 'result', '/nullValue', null),
            check(id, 'result', '/a~1b/~0key', true),
          ];
        }
      },
    },
    true
  );
  assert.equal(run(root).status, 0);
  for (const path of ['/absent', '/toString', '/array/01', '/array/length']) {
    const bad = makeRepo(
      t,
      { change: d => { for (const step of d.steps) step.checks = [check(step.checks[0].criterion_id, 'result', path, null)]; } },
      true
    );
    const { data } = report(bad);
    assert.equal(data.stories[0].status, 'failed');
    assert.deepEqual(steps(data)[0].checks[0].actual, { missing: true });
  }
});

test('exact integers survive native input, response, world, comparison, JSON/text and saved reports', t => {
  const values = [9007199254740993n, 9007199254740994n, -9007199254740993n, 9223372036854775807n];
  const root = makeRepo(
    t,
    {
      inputSchema: { type: 'object', properties: { id: schema('integer') }, required: ['id'], additionalProperties: false },
      resultSchema: { type: 'object', properties: { id: schema('integer') }, required: ['id'], additionalProperties: false },
      change: doc => {
        doc.initial_world = { sentinel: values };
        for (const [i, step] of doc.steps.entries()) {
          const id = step.checks[0].criterion_id;
          step.input = { id: values[i] };
          step.checks = [check(id, 'result', '/id', values[i]), check(id, 'world', '/sentinel', values)];
        }
      },
    },
    true
  );
  const { out, data } = report(root);
  assert.equal(out.status, 0, out.stderr);
  assert.equal(steps(data)[0].checks[0].actual, values[0]);
  const request = readFileSync(join(root, 'request.json'), 'utf8');
  assert.match(request, /"id":9007199254740994/);
  assert.match(request, /-9007199254740993/);
  const saved = readFileSync(join(root, '.pdd/code-test/latest.json'), 'utf8');
  assert.match(saved, /9223372036854775807/);
  // An adjacent large wrong answer must fail exact comparison, not round to a pass.
  const app = readFileSync(join(root, 'examples/fakes/service.mjs'), 'utf8');
  save(root, 'examples/fakes/service.mjs', app.replace('result:r.input', 'result:{id:r.input.id+1n}'));
  const failed = report(root);
  assert.equal(failed.out.status, 1);
  assert.equal(steps(failed.data)[0].checks[0].actual, values[0] + 1n);
  const text = run(root, { json: false });
  assert.match(text.stdout, /expected 9007199254740993, actual 9007199254740994/);
});

test('expected application errors are distinct from process failures and advance world even on outcome mismatch', t => {
  const app = `import {parseScenarioJson,stringifyScenarioJson} from ${JSON.stringify(seamModule)};let raw='';for await(const c of process.stdin)raw+=c;const r=parseScenarioJson(raw);const n=(r.initial_world.n??0)+1;process.stdout.write(stringifyScenarioJson({schema_version:r.schema_version,error:{code:'missing'},world:{n},calls:{resources:{},internal:{}}}));`;
  for (const expected of [true, false]) {
    const root = makeRepo(
      t,
      {
        app,
        errors: ['missing'],
        change: doc => {
          for (const [i, step] of doc.steps.entries()) {
            if (expected) step.expected_error = 'missing';
            const id = step.checks[0].criterion_id;
            step.checks = [check(id, 'error', '/code', 'missing'), check(id, 'world', '/n', i + 1)];
          }
        },
      },
      true
    );
    const { out, data } = report(root);
    assert.equal(out.status, expected ? 0 : 1);
    assert.equal(data.stories[0].status, expected ? 'passed' : 'failed');
    assert.equal(steps(data)[1].checks[1].actual, 2);
    if (!expected) assert.match(steps(data)[0].reason, /Unexpected application error/);
  }
});

test('an invalid scenario does not prevent independent scenario worlds from running', t => {
  const root = makeRepo(t, { change: d => { d.simulation['service.lookup'].cases[0].args.id = 'wrong'; } });
  const other = parseScenarioJson(read(scenarioPath));
  other.story_path = 'user_stories/other.md';
  save(root, 'user_stories/other.md', read('user_stories/fake-recorded-call.md'));
  save(root, 'test/runtime/other.json', stringifyScenarioJson(other));
  const { out, data } = report(root, { words: ['fake-recorded-call', 'other'] });
  assert.equal(out.status, 1);
  assert.deepEqual(data.stories.map(story => story.status), ['not run', 'passed']);
});

test('all protected report symlinks refuse writes and typed execution', t => {
  for (const path of ['.pdd', '.pdd/.gitignore', '.pdd/code-test', '.pdd/code-test/latest.json']) {
    const root = makeRepo(t, { appChange: watch });
    save(root, 'guard', 'keep');
    if (path !== '.pdd') save(root, path, 'placeholder');
    if (path !== '.pdd') unlinkSync(join(root, path));
    symlinkSync(join(root, 'guard'), join(root, path));
    const out = run(root);
    assert.equal(out.status, 1);
    assert.match(out.stderr, /symbolic link/);
    assert.equal(readFileSync(join(root, 'guard'), 'utf8'), 'keep');
    assert.equal(existsSync(join(root, 'LAUNCHED')), false);
  }
});

test('exact integer fixture arguments and saved replies reach the real application without rounding', t => {
  const a = 9007199254740992n;
  const b = 9007199254740993n;
  const root = makeRepo(t, {
    interfaceChange: iface => {
      iface.entries[0].input_schema.properties.id = { type: 'integer' };
      iface.entries[0].result_schema.properties.label = { type: 'integer' };
      iface.resources[0].operations[0].arguments_schema.properties.id = { type: 'integer' };
      iface.resources[0].operations[0].result_schema.properties.label = { type: 'integer' };
    },
    appChange: text =>
      text
        .replace("typeof request.input.id === 'string'", "['number','bigint'].includes(typeof request.input.id)")
        .replace("typeof item.args.id === 'string'", "['number','bigint'].includes(typeof item.args.id)")
        .replace("typeof item.result.label === 'string'", "['number','bigint'].includes(typeof item.result.label)"),
    change: doc => {
      for (const [i, step] of doc.steps.entries()) {
        step.input.id = i === 0 ? a : b;
        doc.simulation['service.lookup'].cases[i].args.id = step.input.id;
        doc.simulation['service.lookup'].cases[i].result.label = i === 0 ? b : a;
        step.checks[0].value = i === 0 ? b : a;
      }
    },
  });
  const { out, data } = report(root);
  assert.equal(out.status, 0, out.stdout + out.stderr);
  assert.equal(BigInt(steps(data)[0].checks[0].actual), b);
  assert.equal(BigInt(steps(data)[1].checks[0].actual), a);
  const doc = parseScenarioJson(readFileSync(join(root, scenarioPath), 'utf8'));
  doc.steps[0].input.id = b;
  save(root, scenarioPath, stringifyScenarioJson(doc));
  const fail = report(root);
  assert.equal(fail.out.status, 1);
  assert.equal(steps(fail.data)[0].status, 'not run');
});

test('invalid per-step resource counts cannot become a valid adapter observation', t => {
  for (const count of [-1, 1.5, 9007199254740992]) {
    const root = makeRepo(t, {
      appChange: () =>
        `process.stdout.write(${JSON.stringify(
          JSON.stringify({
            schema_version: version,
            result: { label: 'Available' },
            world: { fixture_counters: { lookup: 1 }, note: 'keep' },
            calls: { resources: { 'service-service-lookup': count }, internal: {} },
          })
        )});`,
    });
    const { out, data } = report(root);
    assert.equal(out.status, 1);
    assert.equal(steps(data)[0].status, 'not run');
    assert.match(steps(data)[0].reason, /calls/);
  }
});

test('direct service import leaves stdin unread and preserves the exported library operation', () => {
  const out = spawnSync(
    process.execPath,
    [
      '--input-type=module',
      '-e',
      `import {lookup} from ${JSON.stringify(new URL('../examples/fakes/service.mjs', import.meta.url).href)};process.stdout.write(JSON.stringify(lookup({lookup:args=>({label:args.id})},'import-only')));`,
    ],
    { input: 'not an adapter request', encoding: 'utf8' }
  );
  assert.equal(out.status, 0, out.stderr);
  assert.equal(out.stdout, '{"label":"import-only"}');
  assert.equal(out.stderr, '');
});

test('an absent result/error root remains a missing observation, distinct from present null', t => {
  const root = makeRepo(
    t,
    { change: doc => { for (const step of doc.steps) step.checks = [check(step.checks[0].criterion_id, 'error', '', null)]; } },
    true
  );
  const { out, data } = report(root);
  assert.equal(out.status, 1);
  assert.deepEqual(steps(data)[0].checks[0].actual, { missing: true });
});

test('a large nonnegative integer count expectation executes and fails without rounding', t => {
  const root = makeRepo(
    t,
    { change: doc => { for (const step of doc.steps) step.checks = [check(step.checks[0].criterion_id, 'result', '', 9007199254740993n, 'count')]; } },
    true
  );
  const { out, data } = report(root);
  assert.equal(out.status, 1);
  assert.equal(data.stories[0].status, 'failed');
  assert.equal(steps(data)[0].checks[0].actual, 1);
  assert.equal(steps(data)[0].checks[0].expected, 9007199254740993n);
});

test('later typed steps retain the admitted command when the trusted app changes prompt metadata', t => {
  const prefix = `import {readFileSync as admissionRead,writeFileSync as admissionWrite} from 'node:fs';
const path='examples/fakes/service.prompt.md';
const text=admissionRead(path,'utf8');
admissionWrite(path,text.replace(/"symbol": "lookup"/, '"symbol": "unadmitted-operation"'));
`;
  const root = makeRepo(t, { appChange: text => prefix + text });
  const { out, data } = report(root);
  assert.equal(out.status, 0, out.stdout + out.stderr);
  assert.equal(data.stories[0].status, 'passed');
  assert.equal(steps(data)[1].checks[0].actual, 'Reserved');
});
