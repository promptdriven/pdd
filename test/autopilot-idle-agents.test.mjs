import test from 'node:test';
import assert from 'node:assert/strict';
import {existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync} from 'node:fs';
import {execFileSync} from 'node:child_process';
import {join} from 'node:path';
import {healthyMachine} from './helpers/healthy-machine.mjs';
import {isolatedCheckCapacity} from './helpers/check-machine.mjs';
import {tickAutopilot} from '../src/autopilot-launcher.mjs';
import {nudgeIdleRun, openRun, runStatus} from '../src/workflow-runner.mjs';
import {fixture, packageRoot, matchingClaimPorts, matchingClaimObservation} from './helpers/workflow-runner-fixture.mjs';

const WAIT = 600000;
const save = (f, run) => writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
const prompts = f => f.herdr.calls.filter(a => a[0] === 'agent' && a[1] === 'prompt');
const launches = f => f.herdr.calls.filter(a => a[0] === 'pane' && a[1] === 'run');
function holdRun(f, hold) {
  const run = f.record();
  if (hold === 'gate') run.gate = {area: run.chats.at(-1).area, kind: 'approve', at: f.clock};
  if (hold === 'question') run.question = {text: 'Choose a case.', at: f.clock};
  if (hold === 'interpreter') {
    run.state = 'paused';
    run.runtimeWait = {reason: 'check-slot', batch: 'controlled-batch', at: f.clock};
  }
  save(f, run);
  return run;
}
function assertHold(f, held) {
  const saved = f.record();
  for (const key of ['state', 'gate', 'question', 'runtimeWait', 'done', 'decisions', 'area'])
    assert.deepEqual(saved[key], held[key], `resume must preserve ${key}`);
}
function useAlertService(f, ports) {
  const config = join(f.ports.env.XDG_CONFIG_HOME, 'pdd');
  mkdirSync(config, {recursive: true});
  writeFileSync(join(config, 'autopilot-alerts.json'), JSON.stringify({v: 1, service: 'discord',
    url: 'https://discord.com/api/webhooks/123456789012345678/test-fixture'}));
  const requests = [];
  delete ports.sendAlert;
  ports.alertPorts = {hostname: () => 'idle-machine', http: async request => {
    requests.push(request); return {status: 200, text: JSON.stringify({id: 'fixture-message', content: request.body.content})};
  }};
  return requests;
}
function alertIncident(f) {
  const folder = join(f.state, 'alerts');
  assert.ok(existsSync(folder), '3072: the alert service must retain custody of the saved idle incident');
  const files = readdirSync(folder);
  assert.equal(files.length, 1);
  return JSON.parse(readFileSync(join(folder, files[0]), 'utf8')).incidents['17:stuck'];
}
async function exhaustIdle(f, tick, idle) {
  idle(); await tick();
  for (let i = 0; i < 3; i++) {f.tick(WAIT); await tick();}
  assert.equal(prompts(f).length, 3);
  f.tick(WAIT);
}
async function setup(t, agent = 'claude', name = 'small-change') {
  const f = await fixture(t, {agent, name});
  f.ports.env.XDG_CONFIG_HOME = join(f.base, 'idle-config');
  assert.equal((await f.run()).exitCode, 0);
  assert.equal((await runStatus({ref: '17', cwd: f.source}, f.ports)).exitCode, 0);
  const run = f.record();
  run.automaticOrigin = {repository: run.repo, coordinatorId: 'idle-owner', machine: 'idle-machine', claim: {commentId: '11', labelEventId: '12'}};
  save(f, run);
  f.ports.owners = matchingClaimPorts(run);
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: 'auto', trust: []}}));
  const stateFile = join(f.state, 'launcher.json');
  writeFileSync(stateFile, JSON.stringify({enabled: true, defaultBranch: 'main', baseBranch: 'main', stateFile, cwd: f.source, repo: run.repo, packageRoot,
    coordinatorId: 'idle-owner', machine: 'idle-machine', activatedAt: 1,
    agent: {id: agent, kind: agent, command: agent}, environment: f.ports.env, retryAt: f.clock + 86400000}));
  const alerts = [], warnings = [];
  const ports = {...healthyMachine, ...f.ports, sendDigest: async () => ({exitCode: 0}), checkCapacityPorts: isolatedCheckCapacity(f.base), run: async (file, args, options) => ({code: 0, ...await f.ports.execFile(file, args, options)}),
    warn: text => warnings.push(text), sendAlert: async input => {alerts.push(input); return {exitCode: 0};}};
  const tick = () => tickAutopilot(stateFile, ports);
  const pane = () => f.herdr.paneOf(f.record().chats.at(-1));
  const idle = () => {pane().agent.agent_status = 'idle';};
  f.herdr.calls.length = 0;
  return {f, run, ports, tick, pane, idle, alerts, warnings, stateFile};
}

for (const agent of ['claude', 'codex']) for (const automatic of [false, true]) for (const closed of [false, true])
  test(`3072 resume continues once: ${agent}, automatic=${automatic}, rebuilt=${closed}`, async t => {
    const {f, run, tick, pane} = await setup(t, agent), chat = run.chats.at(-1);
    pane().agent = null; f.tick(60001);
    if (closed) await f.herdr.herdr(['workspace', 'close', chat.workspaceId]);
    let attached = 0, promptsAtAttach = null;
    const ports = {...f.ports, attach: async () => {attached++; promptsAtAttach = prompts(f).length;}};
    if (automatic) await tick();
    else assert.equal((await openRun({ref: '17', cwd: f.source, packageRoot}, ports)).exitCode, 0);
    assert.equal(launches(f).length, 1);
    assert.equal(prompts(f).length, 1, '3072: a resumed session needs one delivered continue request');
    assert.equal(prompts(f)[0][2], f.record().chats.at(-1).paneId);
    assert.ok(prompts(f)[0][3].includes('STEP.md'));
    assert.ok(prompts(f)[0][3].includes(run.areas[run.area].steps[0]));
    assert.equal(f.record().chats.at(-1).session.id, chat.session.id);
    for (const key of ['done', 'gate', 'decisions', 'area']) assert.deepEqual(f.record()[key], run[key]);
    await openRun({ref: '17', cwd: f.source, packageRoot}, f.ports);
    await tick();
    assert.equal(prompts(f).length, 1, 'opening the live chat and another tick must not repeat the continue');
    if (!automatic) {assert.equal(attached, 1); assert.equal(promptsAtAttach, 1, 'continue must precede terminal attachment');}
  });

for (const hold of ['gate', 'question', 'interpreter']) for (const agent of ['claude', 'codex']) for (const rebuilt of [false, true])
  test(`3072 repair 2: restore held ${hold} session, ${agent}, rebuilt=${rebuilt}`, async t => {
    const {f, pane} = await setup(t, agent), original = f.record().chats.at(-1);
    pane().agent = null; f.tick(60001);
    if (rebuilt) await f.herdr.herdr(['workspace', 'close', original.workspaceId]);
    const held = holdRun(f, hold);
    let attached = 0, promptsAtAttach;
    const ports = {...f.ports, attach: async () => {
      attached++;
      promptsAtAttach = prompts(f).length;
    }};
    assert.equal((await openRun({ref: '17', cwd: f.source, packageRoot}, ports)).exitCode, 0);
    assert.equal(attached, 1);
    assert.equal(launches(f).length, 1);
    assert.equal(f.record().chats.at(-1).session.id, original.session.id);
    assert.equal(prompts(f).length, 0, '3072: a deliberate hold must not receive a resume notice');
    assert.equal(promptsAtAttach, 0);
    assert.equal(f.record().chats.at(-1).continueAnchor, undefined);
    assert.equal(existsSync(join(held.runDir, 'delivery-journal.json')), false);
    assertHold(f, held);
    await openRun({ref: '17', cwd: f.source, packageRoot}, ports);
    assert.equal(launches(f).length, 1);
    assert.equal(prompts(f).length, 0);
    assertHold(f, held);
  });

for (const hold of ['gate', 'question', 'interpreter'])
  test(`3072 repair 2: ${hold} arriving at journal custody prevents notice creation`, async t => {
    const {f, pane} = await setup(t);
    pane().agent = null; f.tick(60001);
    let held, attached = 0;
    const ports = {...f.ports, deliveryFiles: {mkdirSync: (path, options) => {
      if (!held && path.endsWith('/.delivery-journal.lock')) held = holdRun(f, hold);
      return mkdirSync(path, options);
    }}, attach: async () => {attached++;}};
    assert.equal((await openRun({ref: '17', cwd: f.source, packageRoot}, ports)).exitCode, 0);
    assert.ok(held);
    assert.equal(attached, 1);
    assert.equal(launches(f).length, 1);
    assert.equal(prompts(f).length, 0);
    assert.equal(existsSync(join(held.runDir, 'delivery-journal.json')), false,
      '3072: a deliberate hold must prevent journal notice creation');
    assertHold(f, held);
  });

for (const hold of ['gate', 'question', 'interpreter'])
  test(`3072 repair 2: ${hold} arriving during submission or resume wins`, async t => {
    // First check the final submission guard. Then move the same hold earlier,
    // into native resume, before the runner reserves its continue notice.
    for (const phase of ['submission', 'resume']) {
      const {f, pane} = await setup(t);
      pane().agent = null; f.tick(60001);
      let held, attached = 0;
      const herdr = f.ports.herdr;
      const ports = {...f.ports, herdr: async args => {
        const target = phase === 'resume' ? args[0] === 'pane' && args[1] === 'run'
          : args[0] === 'pane' && args[1] === 'read' && existsSync(join(f.record().runDir, 'delivery-journal.json'));
        if (!held && target) held = holdRun(f, hold);
        return herdr(args);
      }, attach: async () => {attached++;}};
      assert.equal((await openRun({ref: '17', cwd: f.source, packageRoot}, ports)).exitCode, 0);
      assert.ok(held, `controlled hold must reach ${phase}`);
      assert.equal(attached, 1);
      assert.equal(launches(f).length, 1);
      assert.equal(prompts(f).length, 0, '3072: a concurrent hold must prevent resume continuation');
      assertHold(f, held);
      if (phase === 'resume') {
        assert.equal(f.record().chats.at(-1).continueAnchor, undefined);
        assert.equal(existsSync(join(held.runDir, 'delivery-journal.json')), false);
      } else {
        const journal = JSON.parse(readFileSync(join(held.runDir, 'delivery-journal.json'), 'utf8'));
        assert.equal(journal.requests.length, 1);
        assert.equal(journal.requests[0].state, 'pending');
        assert.equal(journal.requests[0].inFlight, undefined);
      }
    }
  });

test('3072 idle timing, three per-area nudges, then one stuck alert across ticks', async t => {
  const {f, tick, idle, ports, run} = await setup(t);
  const alerts = useAlertService(f, ports);
  idle(); await tick();
  f.tick(WAIT - 1); await tick(); assert.equal(prompts(f).length, 0);
  f.tick(1);
  for (let count = 1; count <= 3; count++) {
    await tick(); assert.equal(prompts(f).length, count, '3072: idle workers need bounded delivery');
    assert.equal(f.record().state, 'running');
    await tick(); assert.equal(prompts(f).length, count);
    f.tick(WAIT);
  }
  await tick(); assert.equal(f.record().state, 'stuck'); assert.equal(alerts.length, 1);
  assert.equal(alertIncident(f).result, 'delivered');
  assert.equal(f.record().chatIdleLimit.area, run.chats.at(-1).area);
  for (let i = 0; i < 3; i++) {f.tick(WAIT); await tick();}
  assert.equal(alerts.length, 1); assert.equal(prompts(f).length, 3);
});

test('3072 repair 1: retry an alert handoff that throws before service custody', async t => {
  const {f, tick, idle, ports} = await setup(t);
  const requests = useAlertService(f, ports);
  await exhaustIdle(f, tick, idle);
  let attempts = 0;
  ports.sendAlert = async () => {attempts++; throw Error('Controlled failure before alert custody');};
  await tick();
  assert.equal(attempts, 1); assert.equal(requests.length, 0);
  assert.equal(f.record().state, 'stuck');
  const stopped = f.record();
  delete ports.sendAlert;
  await tick(); await tick();
  assert.equal(requests.length, 1, '3072: a definitely unsent idle alert must reach the service on a later tick');
  assert.equal(alertIncident(f).result, 'delivered');
  assert.deepEqual(f.record(), stopped);
  assert.equal(prompts(f).length, 3); assert.equal(launches(f).length, 0);
});

for (const failure of ['failed', 'unconfirmed', 'not-configured']) test(`3072 repair 1: saved idle alerts preserve ${failure} service custody`, async t => {
  const {f, tick, idle, ports} = await setup(t);
  const requests = useAlertService(f, ports), http = ports.alertPorts.http;
  await exhaustIdle(f, tick, idle);
  ports.sendAlert = async () => {throw Error('Controlled failure before alert custody');};
  await tick(); assert.equal(f.record().state, 'stuck'); assert.equal(requests.length, 0);
  delete ports.sendAlert;
  if (failure === 'not-configured') writeFileSync(join(f.ports.env.XDG_CONFIG_HOME, 'pdd', 'autopilot-alerts.json'), '{}');
  else ports.alertPorts.http = async request => {
    requests.push(request);
    throw Object.assign(Error('Controlled alert transport failure'), {code: failure === 'failed' ? 'unreached' : 'unknown'});
  };
  await tick();
  assert.equal(requests.length, failure === 'not-configured' ? 0 : 1,
    '3072: a saved idle incident must be handed to the alert service');
  assert.equal(alertIncident(f).result, failure);
  if (failure === 'not-configured') useAlertService(f, ports);
  // Keep one request counter across the destination and transport recovery.
  ports.alertPorts.http = http;
  const before = requests.length;
  await tick(); await tick();
  assert.equal(requests.length - before, failure === 'unconfirmed' ? 0 : 1,
    '3072: retry known unsent alerts and retain unconfirmed custody');
  assert.equal(alertIncident(f).result, failure === 'unconfirmed' ? 'unconfirmed' : 'delivered');
  assert.equal(prompts(f).length, 3); assert.equal(launches(f).length, 0);
});

test('3072 repair 1: a fresh tick process hands off a saved idle stop once', async t => {
  const {f, tick, idle, ports, stateFile} = await setup(t);
  useAlertService(f, ports);
  await exhaustIdle(f, tick, idle);
  // Stop at the public runner boundary, before the launcher's alert handoff.
  const stopped = await nudgeIdleRun({ref: '17', cwd: f.source, packageRoot,
    coordinatorId: 'idle-owner', machine: 'idle-machine'}, ports);
  assert.equal(stopped.recovery, 'stuck');
  const saved = f.record();
  const script = `
    import {readFileSync} from 'node:fs';
    import {execFile} from 'node:child_process';
    import {promisify} from 'node:util';
    import {healthyMachine} from './test/helpers/healthy-machine.mjs';
    import {isolatedCheckCapacity} from './test/helpers/check-machine.mjs';
    import {tickAutopilot} from './src/autopilot-launcher.mjs';
    import {fakeHerdr} from './test/helpers/fake-herdr.mjs';
    const input = JSON.parse(readFileSync(0, 'utf8')), h = fakeHerdr(), exec = promisify(execFile);
    const requests = [], warnings = [];
    const execute = async (file, args, options) => {
      if (file !== 'git' || !['rev-parse', 'config', 'status', 'show-ref', 'symbolic-ref', 'remote', 'worktree', 'for-each-ref', 'merge-base', 'check-ref-format'].includes(args[0])) throw Error('Unexpected external command: ' + file + ' ' + args[0]);
      return {code: 0, ...await exec(file, args, options)};
    };
    const ports = {...healthyMachine, sendDigest: async () => ({exitCode: 0}), checkCapacityPorts: isolatedCheckCapacity(input.stateDir), stateDir: input.stateDir, env: input.env, layoutDirectory: input.layoutDirectory,
      now: () => input.now, herdr: h.herdr, owners: {read: async () => ({json: JSON.stringify(input.ownership)})}, findNativeSessions: async () => [], run: execute, execFile: execute,
      warn: value => warnings.push(value), alertPorts: {hostname: () => 'idle-machine',
        http: async request => {requests.push(request); return {status: 200,
          text: JSON.stringify({id: 'fixture-message', content: request.body.content})};}}};
    await tickAutopilot(input.stateFile, ports);
    await tickAutopilot(input.stateFile, ports);
    process.stdout.write(JSON.stringify({requests, warnings,
      deliveries: h.calls.filter(a => a[0] === 'agent' && a[1] === 'prompt'),
      launches: h.calls.filter(a => a[0] === 'pane' && a[1] === 'run')}));
  `;
  const result = JSON.parse(execFileSync(process.execPath, ['--input-type=module', '-e', script], {
    cwd: packageRoot, encoding: 'utf8', timeout: 10000,
    input: JSON.stringify({stateFile, stateDir: f.state, env: f.ports.env, layoutDirectory: f.ports.layoutDirectory, now: f.clock, ownership: matchingClaimObservation(saved)})
  }));
  assert.deepEqual(result.warnings, []);
  assert.equal(result.requests.length, 1, '3072: a saved idle stop must reach the alert service after restart');
  assert.equal(alertIncident(f).result, 'delivered');
  assert.equal(result.deliveries.length, 0); assert.equal(result.launches.length, 0);
  assert.deepEqual(f.record(), saved);
});

for (const hold of ['foreign-owner', 'foreign-machine', 'foreign-source', 'manual', 'paused', 'cancelled', 'closing', 'closed'])
  test(`3072 repair 1: saved idle alert respects ${hold}`, async t => {
    const {f, tick, idle, ports} = await setup(t);
    await exhaustIdle(f, tick, idle);
    const args = {ref: '17', cwd: f.source, packageRoot, coordinatorId: 'idle-owner', machine: 'idle-machine'};
    assert.equal((await nudgeIdleRun(args, ports)).recovery, 'stuck');
    assert.equal((await nudgeIdleRun(args, ports)).recovery, 'stuck', '3072: retain the saved idle incident for handoff');
    const run = f.record();
    if (hold === 'foreign-owner') run.automaticOrigin.coordinatorId = 'other';
    if (hold === 'foreign-machine') run.automaticOrigin.machine = 'other';
    if (hold === 'foreign-source') run.sourceRoot = run.root;
    if (hold === 'manual') delete run.automaticOrigin;
    if (['paused', 'cancelled'].includes(hold)) run.state = hold;
    if (hold === 'closing') run.layout.phase = 'close_intent';
    if (hold === 'closed') run.chats.at(-1).closed = {at: f.clock, reason: 'paused'};
    save(f, run);
    assert.equal((await nudgeIdleRun(args, ports)).recovery, 'skipped');
    assert.deepEqual(f.record(), run);
    assert.equal(prompts(f).length, 3); assert.equal(launches(f).length, 0);
  });

test('3072 all status views expose the idle interval and do not nudge', async t => {
  const {f, tick, idle, pane} = await setup(t);
  idle();
  const at = f.clock;
  for (const options of [{ref: '17'}, {}, {all: true}, {ref: '17', json: true}, {json: true}, {all: true, json: true}]) {
    const result = await runStatus({cwd: f.source, ...options}, {...f.ports, timeZone: 'UTC'});
    assert.equal(result.exitCode, 0);
    const words = options.json ? JSON.parse(result.message).runs[0].words : result.message;
    assert.match(words, /idle since \d{2}:\d{2}/, '3072: idle must be visible');
    assert.ok(words.includes(new Date(at).toISOString().slice(11, 16)));
  }
  assert.equal(f.record().chats.at(-1).idleSince, at);
  assert.equal(prompts(f).length, 0);
  f.tick(WAIT); await tick(); assert.equal(prompts(f).length, 1);
  pane().agent.agent_status = 'working';
  await runStatus({ref: '17', cwd: f.source}, f.ports);
  assert.equal(f.record().chats.at(-1).idleSince, undefined);
  idle(); await tick(); f.tick(WAIT - 1); await tick(); assert.equal(prompts(f).length, 1);
  f.tick(1); await tick(); assert.equal(prompts(f).length, 2);
});

test('3072 recorded step progress resets the allowance; working alone does not', async t => {
  const {f, tick, idle, pane} = await setup(t, 'claude', 'bug');
  idle(); await tick();
  for (let i = 0; i < 3; i++) {f.tick(WAIT); await tick();}
  assert.equal(prompts(f).length, 3);
  pane().agent.agent_status = 'working'; await tick(); idle(); await tick();
  const run = f.record(), area = run.areas[run.area];
  run.done[area.steps[0]] = {area: area.name, summary: 'Recorded controlled progress', at: f.clock}; save(f, run);
  f.tick(WAIT); await tick();
  assert.equal(f.record().state, 'running'); assert.equal(prompts(f).length, 4);
  assert.equal(f.record().chatIdleNudges[area.name].count, 1);
  assert.ok(prompts(f).at(-1)[3].includes(area.steps[1]));
});

for (const hold of ['gate', 'question', 'paused', 'cancelled', 'closed', 'closing', 'foreign-owner', 'foreign-machine', 'foreign-source', 'manual', 'observe', 'off', 'blocked', 'working', 'unknown', 'mismatched-session'])
  test(`3072 no idle nudge for ${hold}`, async t => {
    const {f, run, tick, idle, ports, pane, alerts} = await setup(t);
    idle();
    if (hold === 'gate') run.gate = {area: run.chats.at(-1).area, kind: 'approve', at: f.clock};
    if (hold === 'question') run.question = {text: 'Choose a case.', at: f.clock};
    if (['paused', 'cancelled'].includes(hold)) run.state = hold;
    if (hold === 'closed') run.chats.at(-1).closed = {at: f.clock, reason: 'paused'};
    if (hold === 'closing') run.layout.phase = 'close_intent';
    if (hold === 'foreign-owner') run.automaticOrigin.coordinatorId = 'other';
    if (hold === 'foreign-machine') run.automaticOrigin.machine = 'other';
    if (hold === 'foreign-source') run.sourceRoot = run.root;
    if (hold === 'manual') delete run.automaticOrigin;
    if (['observe', 'off'].includes(hold)) writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: hold}}));
    if (['blocked', 'working', 'unknown'].includes(hold)) pane().agent.agent_status = hold;
    if (hold === 'mismatched-session') pane().agent.agent_session.value = '00000000-0000-4000-8000-000000000099';
    save(f, run); await tick(); f.tick(WAIT); await tick();
    assert.equal(prompts(f).length, 0); assert.equal(alerts.length, 0);
  });

for (const change of ['question', 'cancel', 'progress', 'close']) test(`3072 concurrent ${change} prevents idle delivery`, async t => {
  const {f, tick, idle, ports} = await setup(t);
  idle(); await tick(); f.tick(WAIT);
  const herdr = ports.herdr; let changed = false;
  ports.herdr = async args => {
    if (!changed && args[0] === 'agent' && args[1] === 'get') {
      changed = true;
      const run = f.record();
      if (change === 'question') run.question = {text: 'Choose a case.', at: f.clock};
      if (change === 'cancel') run.state = 'cancelled';
      if (change === 'progress') run.done[run.areas[run.area].steps[0]] = {at: f.clock, summary: 'New progress'};
      if (change === 'close') run.chats.at(-1).closed = {at: f.clock, reason: 'paused'};
      save(f, run);
    }
    return herdr(args);
  };
  await tick(); assert.ok(changed); assert.equal(prompts(f).length, 0);
  assert.equal(f.record().chatIdleNudges?.[f.record().chats.at(-1).area]?.count ?? 0, 0);
});

for (const failure of ['pending', 'uncertain']) test(`3072 ${failure} delivery stays bounded and preserves journal custody`, async t => {
  const {f, tick, idle, pane, ports, alerts} = await setup(t);
  idle(); await tick(); f.tick(WAIT);
  const herdr = ports.herdr; let failed = false;
  ports.herdr = async args => {
    if (!failed && args[0] === 'agent' && args[1] === 'prompt') {
      failed = true;
      if (failure === 'uncertain') await herdr(args);
      throw Object.assign(Error('Controlled lost delivery'), {code: failure === 'pending' ? 'agent_not_found' : 'transport_lost'});
    }
    return herdr(args);
  };
  await tick();
  assert.equal(f.record().chatIdleNudges?.[f.record().chats.at(-1).area]?.count ?? 0, 1, '3072: idle delivery must be attempted');
  assert.ok(failed);
  assert.equal(f.record().chatIdleNudges[f.record().chats.at(-1).area].count, 1);
  for (let i = 0; i < 3; i++) {f.tick(WAIT); await tick();}
  assert.equal(pane().agent.prompts.length, failure === 'pending' ? 2 : 1);
  const journal = JSON.parse(readFileSync(join(f.record().runDir, 'delivery-journal.json'), 'utf8'));
  assert.equal(journal.requests.length, failure === 'pending' ? 2 : 1);
  assert.equal(journal.requests[0].state, failure === 'pending' ? 'delivered' : 'uncertain');
  assert.equal(f.record().state, 'stuck'); assert.equal(alerts.length, 1);
});

test('3072 the injected delivery port gets the saved current run and bounded attempts', async t => {
  const {f, tick, idle, ports, alerts} = await setup(t);
  const deliveries = [];
  ports.deliverContinue = async (run, text, supplied) => {
    assert.equal(supplied.now(), f.clock);
    assert.equal(run.runId, f.record().runId);
    assert.ok(text.includes('STEP.md'));
    assert.ok(supplied.deliveryGuard(f.record()));
    deliveries.push(f.clock);
    return {exitCode: 1, message: 'Controlled unsent request'};
  };
  idle(); await tick();
  for (let i = 0; i < 4; i++) {f.tick(WAIT); await tick();}
  assert.equal(deliveries.length, 3); assert.equal(alerts.length, 1);
  assert.equal(prompts(f).length, 0);
});

test('3072 working observations and another area do not refill the old area allowance', async t => {
  const {f, tick, idle, pane, alerts} = await setup(t);
  idle(); await tick();
  for (let i = 0; i < 3; i++) {f.tick(WAIT); await tick();}
  pane().agent.agent_status = 'working'; await tick(); idle(); await tick();
  const first = f.record(), oldChat = first.chats.at(-1);
  const second = structuredClone(first); second.area = 1;
  second.chats.push({...oldChat, area: second.areas[1].name}); save(f, second);
  f.tick(WAIT); await tick();
  assert.equal(prompts(f).length, 4); assert.equal(alerts.length, 0);
  assert.equal(f.record().chatIdleNudges[oldChat.area].count, 3);
  const back = f.record(); back.area = 0; save(f, back);
  f.tick(WAIT); await tick();
  assert.equal(f.record().state, 'stuck'); assert.equal(prompts(f).length, 4); assert.equal(alerts.length, 1);
});

for (const health of ['login', 'usage']) test(`3072 idle ${health} failures keep their hold`, async t => {
  const {f, tick, idle, pane, alerts} = await setup(t);
  idle(); pane().screen = health === 'login'
    ? '> Continue.\n  ⎿  Not logged in · Please run /login\n\n> \n'
    : "> Continue.\n  ⎿  You've hit your session limit · resets 7pm (UTC)\n\n> \n";
  await tick(); f.tick(WAIT); await tick();
  assert.equal(prompts(f).length, 0); assert.equal(alerts.length, 0);
  assert.equal(f.record().chatIdleNudges, undefined);
});

for (const change of ['question', 'cancel', 'progress', 'close', 'working']) test(`3072 final delivery read respects concurrent ${change}`, async t => {
  const {f, tick, idle, ports, pane} = await setup(t);
  idle(); await tick(); f.tick(WAIT);
  const herdr = ports.herdr; let changed = false;
  ports.herdr = async args => {
    if (!changed && args[0] === 'pane' && args[1] === 'read') {
      // chatHealth also reads the screen. Apply this change only after the
      // bounded attempt was reserved and the journal is testing delivery.
      const run = f.record();
      if (run.chatIdleNudges?.[run.chats.at(-1).area]?.count) {
        changed = true;
        if (change === 'question') run.question = {text: 'Choose a case.', at: f.clock};
        if (change === 'cancel') run.state = 'cancelled';
        if (change === 'progress') run.done[run.areas[run.area].steps[0]] = {at: f.clock, summary: 'New progress'};
        if (change === 'close') run.chats.at(-1).closed = {at: f.clock, reason: 'paused'};
        if (change === 'working') pane().agent.agent_status = 'working';
        save(f, run);
      }
    }
    return herdr(args);
  };
  await tick();
  assert.equal(f.record().chatIdleNudges?.[f.record().chats.at(-1).area]?.count ?? 0, 1, '3072: idle delivery must be attempted');
  assert.ok(changed); assert.equal(prompts(f).length, 0);
});

test('3072 an unfinished area with native done state also needs a continue', async t => {
  const {f, tick, pane} = await setup(t);
  pane().agent.agent_status = 'done';
  await tick(); f.tick(WAIT); await tick();
  assert.equal(prompts(f).length, 1, '3072: a completed turn is not a completed workflow step');
  assert.equal(f.record().state, 'running');
});

test('3072 manual run resume continues once and starts a fresh idle interval', async t => {
  const {f, run, pane} = await setup(t);
  delete run.automaticOrigin; save(f, run);
  pane().agent.agent_status = 'idle';
  await runStatus({ref: '17', cwd: f.source}, f.ports);
  const firstIdle = f.record().chats.at(-1).idleSince;
  pane().agent = null; f.tick(WAIT);
  assert.equal((await openRun({ref: '17', cwd: f.source, packageRoot}, f.ports)).exitCode, 0);
  assert.equal(prompts(f).length, 1, '3072: manual resumes also need continue delivery');
  pane().agent.agent_status = 'idle';
  await runStatus({ref: '17', cwd: f.source}, f.ports);
  assert.ok(f.record().chats.at(-1).idleSince > firstIdle);
  assert.equal(f.record().chats.at(-1).idleSince, f.clock);
});

for (const state of ['waiting', 'running', 'unavailable']) for (const mode of ['idle', 'resume']) {
  test(`3072 integration: suite ${state} holds ${mode} notices`, async t => {
    const {f, ports, idle, pane} = await setup(t);
    ports.readSuiteProgress = () => ({state, position: 1});
    if (mode === 'idle') {
      const args = {ref: '17', cwd: f.source, packageRoot, coordinatorId: 'idle-owner', machine: 'idle-machine'};
      idle(); await nudgeIdleRun(args, ports); f.tick(WAIT);
      await nudgeIdleRun(args, ports);
      assert.equal(f.record().chatIdleNudges, undefined);
    } else {
      pane().agent = null; f.tick(60001);
      const opened = await openRun({ref: '17', cwd: f.source, packageRoot}, ports);
      assert.equal(opened.exitCode, 0, opened.message);
      assert.equal(launches(f).length, 1);
      assert.equal(f.record().chats.at(-1).continueAnchor, undefined);
    }
    assert.equal(prompts(f).length, 0);
    assert.equal(existsSync(join(f.record().runDir, 'delivery-journal.json')), false);
  });
}

for (const phase of ['journal', 'submission']) {
  test(`3072 integration: suite wait arriving during ${phase} prevents idle delivery`, async t => {
    const {f, ports, idle} = await setup(t);
    const args = {ref: '17', cwd: f.source, packageRoot, coordinatorId: 'idle-owner', machine: 'idle-machine'};
    let held = false;
    ports.readSuiteProgress = () => held ? {state: 'waiting', position: 1} : null;
    idle(); await nudgeIdleRun(args, ports); f.tick(WAIT);
    if (phase === 'journal') ports.deliveryFiles = {mkdirSync: (path, options) => {
      if (path.endsWith('/.delivery-journal.lock')) held = true;
      return mkdirSync(path, options);
    }};
    else {
      const herdr = ports.herdr;
      ports.herdr = async args => {
        if (args[0] === 'pane' && args[1] === 'read' && existsSync(join(f.record().runDir, 'delivery-journal.json'))) held = true;
        return herdr(args);
      };
    }
    await nudgeIdleRun(args, ports);
    assert.ok(held);
    assert.equal(prompts(f).length, 0);
    if (phase === 'journal') assert.equal(existsSync(join(f.record().runDir, 'delivery-journal.json')), false);
    else {
      const journal = JSON.parse(readFileSync(join(f.record().runDir, 'delivery-journal.json'), 'utf8'));
      assert.equal(journal.requests[0].state, 'pending');
      assert.equal(journal.requests[0].inFlight, undefined);
    }
  });
}
