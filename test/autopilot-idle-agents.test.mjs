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

for (const agent of ['claude', 'codex']) for (const automatic of [false]) for (const closed of [false, true])
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

for (const health of ['login', 'usage']) test(`3072 idle ${health} failures keep their hold`, async t => {
  const {f, tick, idle, pane, alerts} = await setup(t);
  idle(); pane().screen = health === 'login'
    ? '> Continue.\n  ⎿  Not logged in · Please run /login\n\n> \n'
    : "> Continue.\n  ⎿  You've hit your session limit · resets 7pm (UTC)\n\n> \n";
  await tick(); f.tick(WAIT); await tick();
  assert.equal(prompts(f).length, 0); assert.equal(alerts.length, 0);
  assert.equal(f.record().chatIdleNudges, undefined);
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
