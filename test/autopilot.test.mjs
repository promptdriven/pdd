import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { runAutopilot } from '../src/autopilot.mjs';
import { readApprovalPolicy } from '../src/approval-policy.mjs';

const stories = ['author', 'invalid-mode', 'invalid-type', 'mode', 'setup-auto', 'setup-observe', 'setup-trust', 'setup', 'trust'];
const at = (value, pointer) => pointer.split('/').slice(1).reduce((v, key) => v?.[key.replaceAll('~1', '/').replaceAll('~0', '~')], value);
const clone = value => structuredClone(value);

// Execute the exact approved scenarios through the real module, including all world/call assertions.
for (const name of stories) test(`autopilot-${name}: replay approved Story cases on native code`, async () => {
  const scenario = JSON.parse(fs.readFileSync(new URL(`runtime/autopilot-${name}.json`, import.meta.url)));
  const world = clone(scenario.initial_world), counts = {}, ports = {};
  for (const [binding, rule] of Object.entries(scenario.simulation)) {
    const [resource, operation] = binding.split('.');
    (ports[resource] ??= {})[operation] = async args => {
      const key = `/resources/${resource}-${operation}`;
      counts[key] = (counts[key] ?? 0) + 1;
      const result = clone(rule.result_template);
      if (rule.action === 'port.write') { at(world, rule.world_pointer).push(clone(args)); return result; }
      if (rule.action === 'fixture.lookup') {
        const parts = rule.world_pointer.split('/').slice(1), last = parts.pop();
        const parent = parts.reduce((v, key) => v[key], world), call = ++parent[last];
        const fixture = rule.cases.find(entry => entry.call_index === call);
        assert.ok(fixture, `No fixture for ${binding} call ${call}`); assert.deepEqual(args, fixture.args);
        return clone(fixture.result);
      }
      const store = at(world, rule.world_pointer), keyArg = at(args, rule.key_argument_pointer);
      if (rule.action === 'key-value.put') store[keyArg] = at(args, rule.value_argument_pointer);
      else assert.equal(rule.action, 'key-value.get');
      const value = store[keyArg] ?? null;
      const field = rule.result_value_pointer.slice(1);
      result[field] = clone(value); return result;
    };
  }
  for (const step of scenario.steps) {
    for (const key of Object.keys(counts)) counts[key] = 0;
    const result = await runAutopilot(step.input, ports);
    for (const check of step.checks) {
      const value = check.target === 'calls' ? counts[check.path] ?? 0 : at(check.target === 'world' ? world : result, check.path);
      const label = `${name}/${step.step_id}/${check.criterion_id} ${check.target} ${check.path}`;
      if (check.op === 'equals') assert.deepEqual(value, check.value, label);
      else if (check.op === 'contains') assert.ok(value.includes(check.value), label);
      else assert.fail(`Unmapped assertion ${check.op}: ${label}`);
    }
  }
});

function memory(raw = null, info = { owner: 'Ada', writers: ['Bo', 'Cy'], complete: true }) {
  const calls = []; let stored = raw;
  return { calls, raw: () => stored, ports: {
    config: { read: async () => ({ raw: stored }), save: async args => { calls.push(args); stored = args.raw; return args; } },
    github: { lookup: async () => info },
    terminal: { mode: async () => ({ answer: '' }), names: async () => ({ names: [] }) },
  } };
}

test('autopilot-author: a nonempty collaborator lookup never trusts an outside author; case is ignored', async () => {
  const m = memory('{"mode":"auto","trust":["Dana"]}');
  for (const author of ['Ada', 'ADA', 'ada', 'Bo', 'bO', 'cY', 'Dana', 'DANA']) {
    assert.equal((await runAutopilot({ action: 'isTrusted', author }, m.ports)).trusted, true, author);
  }
  for (const author of ['Eve', 'EVE', 'Bob', 'Adaline', 'Dan']) {
    assert.equal((await runAutopilot({ action: 'isTrusted', author }, m.ports)).trusted, false, author);
  }
  assert.deepEqual(m.calls, []);
});

test('autopilot-setup-trust: setup really saves additional names on initial and repeat setup', async () => {
  const m = memory(); let questions = 0;
  m.ports.terminal = { mode: async () => { questions++; return { answer: 'auto' }; }, names: async () => ({ names: ['Dana', 'dana'] }) };
  assert.equal((await runAutopilot({ action: 'setup', interactive: true, inRepo: true }, m.ports)).exitCode, 0);
  assert.deepEqual(JSON.parse(m.raw()), { mode: 'auto', trust: ['Dana'] });
  m.ports.terminal.names = async () => ({ names: ['Eli'] });
  await runAutopilot({ action: 'setup', interactive: true, inRepo: true }, m.ports);
  assert.deepEqual(JSON.parse(m.raw()), { mode: 'auto', trust: ['Dana', 'Eli'] });
  assert.equal(questions, 1);
});

test('autopilot-trust: case-insensitive removal cannot remove owner or write-access trust', async () => {
  const m = memory('{"mode":"auto","trust":["Bo","Dana"],"keep":7}');
  await runAutopilot({ action: 'untrust', names: ['bO'] }, m.ports);
  assert.deepEqual(JSON.parse(m.raw()), { mode: 'auto', trust: ['Dana'], keep: 7 });
  assert.equal((await runAutopilot({ action: 'isTrusted', author: 'BO' }, m.ports)).trusted, true);
  await runAutopilot({ action: 'trust', names: ['DANA', 'Eli', 'eli'] }, m.ports);
  assert.deepEqual(JSON.parse(m.raw()).trust, ['Dana', 'Eli']);
});

test('autopilot-invalid-mode/type: every invalid saved mode stays unchanged until mode command', async () => {
  for (const value of ['turbo', false, true, 0, null, [], {}]) {
    const raw = JSON.stringify({ mode: value, trust: [] }), m = memory(raw);
    const result = await runAutopilot({ action: 'setup', interactive: true, inRepo: true }, m.ports);
    assert.equal(result.exitCode, 0); assert.equal(result.mode, 'off'); assert.match(result.message, /invalid.*off/);
    assert.equal(m.raw(), raw); assert.deepEqual(m.calls, []);
    await runAutopilot({ action: 'mode', mode: 'auto' }, m.ports);
    assert.deepEqual(JSON.parse(m.raw()), { mode: 'auto', trust: [] });
  }
  for (const saved of [false, 'auto', null, ['auto']]) {
    const raw = JSON.stringify(saved), m = memory(raw);
    const result = await runAutopilot({ action: 'setup', interactive: true, inRepo: true }, m.ports);
    assert.equal(result.exitCode, 0); assert.equal(result.mode, 'off'); assert.equal(m.raw(), raw); assert.match(result.message, /invalid/);
  }
});

test('autopilot-mode/trust: invalid native arguments exit 2 without reads or saves', async () => {
  const ports = { config: { read() { assert.fail('Bad input cannot read configuration'); } } };
  for (const input of [{ action: 'unknown' }, { action: 'mode', mode: 'turbo' }, { action: 'mode' },
    { action: 'trust' }, { action: 'trust', names: [] }, { action: 'trust', names: ['Dana', ' '] },
    { action: 'untrust', names: [] }, { action: 'untrust', names: ['Dana', 'Bo'] }, { action: 'isTrusted', author: '' }]) {
    assert.equal((await runAutopilot(input, ports)).exitCode, 2, JSON.stringify(input));
  }
});

test('autopilot-author/setup-trust: lookup failures warn and preserve explicit trust without trusting strangers', async () => {
  const m = memory('{"mode":"auto","trust":["Dana"]}');
  m.ports.github.lookup = async () => { throw Error('lookup unavailable'); };
  for (const [author, expected] of [['Dana', true], ['Eve', false]]) {
    const result = await runAutopilot({ action: 'isTrusted', author }, m.ports);
    assert.equal(result.exitCode, 0); assert.equal(result.trusted, expected); assert.match(result.message, /incomplete/);
  }
  assert.equal((await runAutopilot({ action: 'setup', interactive: true, inRepo: true }, m.ports)).exitCode, 0);
});

function realRepo(t) {
  const cwd = fs.mkdtempSync(join(tmpdir(), 'pdd-autopilot-io-'));
  t.after(() => fs.rmSync(cwd, { recursive: true, force: true })); execFileSync('git', ['init', '-q', cwd]); return cwd;
}

test('autopilot-mode/trust/setup: failed write or rename leaves the actual original file unchanged', async t => {
  const cwd = realRepo(t), file = join(cwd, 'pdd.json'), before = '{"strict_approvals":true,"autopilot":{"mode":"off","trust":[]}}\n';
  for (const fail of ['writeFileSync', 'renameSync']) for (const input of [
    { action: 'mode', mode: 'auto' }, { action: 'trust', names: ['Dana'] }, { action: 'untrust', names: ['Dana'] },
    { action: 'setup', interactive: true, inRepo: true },
  ]) {
    fs.writeFileSync(file, before);
    const result = await runAutopilot(input, { cwd, fs: { ...fs, [fail]() { throw Error('synthetic write failure'); } },
      github: { lookup: async () => ({ owner: 'Ada', writers: [], complete: true }) },
      terminal: { names: async () => ({ names: ['Dana'] }) },
    });
    assert.equal(result.exitCode, 1, `${fail} ${input.action}`); assert.match(result.message, /Cannot write pdd.json/);
    assert.equal(fs.readFileSync(file, 'utf8'), before);
    assert.deepEqual(fs.readdirSync(cwd).sort(), ['.git', 'pdd.json']);
  }
});

test('autopilot-author: actual GitHub adapter uses only people with write access, including inherited team access', async t => {
  const cwd = realRepo(t), calls = [];
  const execFile = async (file, args) => {
    calls.push([file, args]);
    if (file === 'git') return { stdout: cwd };
    if (args[0] === 'repo') return { stdout: JSON.stringify({ nameWithOwner: 'Org/repo', owner: { login: 'Org' } }) };
    assert.deepEqual(args, ['api', 'repos/Org/repo/collaborators', '--paginate', '--slurp']);
    return { stdout: JSON.stringify([[{ login: 'Bo', permissions: { push: true } }, { login: 'ReadOnly', permissions: { pull: true } }], [{ login: 'TeamWriter', permissions: { push: true } }]]) };
  };
  for (const [author, trusted] of [['bO', true], ['teamwriter', true], ['ReadOnly', false], ['Eve', false]]) {
    const result = await runAutopilot({ action: 'isTrusted', author }, { cwd, execFile });
    assert.equal(result.exitCode, 0); assert.equal(result.trusted, trusted, author);
  }
  assert.equal(calls.filter(([file]) => file === 'gh').length, 8);
});

test('autopilot-mode: approval policy stays independent for all modes and still enforces strict policy', t => {
  const cwd = realRepo(t);
  for (const mode of ['off', 'observe', 'auto', 'turbo']) for (const strict_approvals of [true, false]) {
    fs.writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ strict_approvals, autopilot: { mode, trust: ['Dana'] } }));
    assert.deepEqual(readApprovalPolicy({ root: cwd }), { strictApprovals: strict_approvals });
  }
});
