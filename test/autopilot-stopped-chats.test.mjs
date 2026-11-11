import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdirSync, readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {execFileSync} from 'node:child_process';
import {tickAutopilot} from '../src/autopilot-launcher.mjs';
import {acknowledgeRequest, askPerson, cancelRun, changeRun, openRun, runStatus, stepDone} from '../src/workflow-runner.mjs';
import {isolatedCheckCapacity} from './helpers/check-machine.mjs';
import {healthyMachine} from './helpers/healthy-machine.mjs';
import {closeFinishedChats} from '../src/workflow-chat.mjs';
import {fixture, packageRoot, matchingClaimPorts, matchingClaimObservation} from './helpers/workflow-runner-fixture.mjs';

const origin = {repository: 'example/project', coordinatorId: 'coordinator-a', machine: 'machine-a', claim: {commentId: '11', labelEventId: '12'}};
const save = (f, run) => writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
const launches = f => f.herdr.calls.filter(a => a[0] === 'pane' && a[1] === 'run');
async function setup(t, agent = 'claude', {observe = true} = {}) {
  const f = await fixture(t, {agent});
  assert.equal((await f.run()).exitCode, 0);
  if (observe) assert.equal((await runStatus({ref: '17', cwd: f.source}, f.ports)).exitCode, 0);
  f.ports.env.XDG_CONFIG_HOME = join(f.ports.env.HOME, '.config');
  const run = f.record(); run.automaticOrigin = structuredClone(origin); save(f, run);
  f.ports.owners = matchingClaimPorts(run);
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: 'auto', trust: []}}));
  const stateFile = join(f.state, 'launcher.json');
  writeFileSync(stateFile, JSON.stringify({enabled: true, defaultBranch: 'main', baseBranch: 'main', stateFile, cwd: f.source, repo: run.repo, packageRoot,
    coordinatorId: origin.coordinatorId, machine: origin.machine, activatedAt: 1,
    agent: {id: agent, kind: agent, command: agent}, environment: f.ports.env,
    retryAt: f.clock + 86400000}));
  const warnings = [], alerts = [];
  const ports = {...healthyMachine, ...f.ports, checkCapacityPorts:isolatedCheckCapacity(f.base), run: async (file, args, options) => ({code: 0, ...await f.ports.execFile(file, args, options)}),
    warn: text => warnings.push(text), sendAlert: async input => {alerts.push(input); return {exitCode: 0};}};
  const tick = () => tickAutopilot(stateFile, ports);
  const stop = () => {f.herdr.paneOf(f.record().chats.at(-1)).agent = null; f.herdr.calls.length = 0; f.tick(60001);};
  return {f, run, tick, stop, ports, stateFile, warnings, alerts};
}

for (const closed of [false, true]) test(`3068 repair 1: native proof recovers an unobserved acknowledged Claude launch (${closed})`, async t => {
  const {f, run, tick, stop} = await setup(t, 'claude', {observe: false});
  const chat = run.chats.at(-1);
  assert.equal(chat.state, 'starting');
  assert.ok(!chat.startUnconfirmed);
  assert.equal((await f.herdr.findNativeSessions({agent: 'claude', root: run.root, startedAt: chat.startedAt, endedAt: f.clock, sessionId: chat.session.id})).length, 1);
  stop();
  if (closed) await f.herdr.herdr(['workspace', 'close', chat.workspaceId]);
  await tick();
  assert.equal(launches(f).length, 1, 'native proof must permit recovery without an earlier status observation');
  assert.equal(f.record().chats.at(-1).session.id, chat.session.id);
});

for (const evidence of ['none', 'ambiguous', 'unreadable', 'unrelated', 'unconfirmed', 'grace']) test(`3068 repair 1: ${evidence} is not native proof for an unobserved launch`, async t => {
  const {f, run, tick, stop, ports} = await setup(t, 'claude', {observe: false});
  const chat = run.chats.at(-1), session = {id: chat.session.id};
  if (evidence === 'none') ports.findNativeSessions = async () => [];
  if (evidence === 'ambiguous') ports.findNativeSessions = async () => [session, session];
  if (evidence === 'unreadable') ports.findNativeSessions = async () => {throw Error('unreadable fixture');};
  if (evidence === 'unrelated') ports.findNativeSessions = async () => [{id: '00000000-0000-4000-8000-000000000099'}];
  if (evidence === 'unconfirmed') {chat.startUnconfirmed = true; save(f, run);}
  stop();
  if (evidence === 'grace') f.clock = chat.startedAt + 29999;
  await tick();
  assert.equal(launches(f).length, 0);
  assert.equal(f.record().chatResumes, undefined);
});

const recoveryWords = /resumed.*stopped/i;
async function statusViews(f) {
  const views = [];
  for (const options of [{ref: '17'}, {}, {all: true}, {ref: '17', json: true}, {json: true}, {all: true, json: true}]) {
    const result = await runStatus({cwd: f.source, ...options}, f.ports);
    assert.equal(result.exitCode, 0, result.message);
    if (options.all && options.json) { const doc = JSON.parse(result.message); assert.equal(doc.version, 1); assert.equal(doc.runs[0].id, 'example/project#17'); }
    else views.push(options.json ? JSON.parse(result.message).runs[0].words : result.message);
  }
  return views;
}

test('3068 repair 1: all status views show the successful automatic recovery attempt and expire at the hour', async t => {
  const {f, tick, stop} = await setup(t);
  for (let attempt = 1; attempt <= 3; attempt++) {
    stop(); await tick();
    assert.equal(launches(f).length, 1);
    for (const words of await statusViews(f)) {
      assert.match(words, recoveryWords);
      assert.match(words, new RegExp(`\\(${attempt} of 3\\)`));
    }
  }
  f.tick(3599999);
  for (const words of await statusViews(f)) assert.match(words, recoveryWords);
  f.tick(1);
  for (const words of await statusViews(f)) assert.doesNotMatch(words, recoveryWords);
  stop(); await tick();
  for (const words of await statusViews(f)) {assert.match(words, recoveryWords); assert.match(words, /\(1 of 3\)/);}
});

test('3068 repair 1: rebuilt Codex recovery saves successful status with its new pane', async t => {
  const {f, run, tick, stop} = await setup(t, 'codex');
  stop(); await f.herdr.herdr(['workspace', 'close', run.chats.at(-1).workspaceId]);
  await tick();
  assert.equal(launches(f).length, 1);
  assert.notEqual(f.record().chats.at(-1).paneId, run.chats.at(-1).paneId);
  for (const words of await statusViews(f)) {assert.match(words, recoveryWords); assert.match(words, /\(1 of 3\)/);}
});

for (const phase of ['close_intent', 'closed']) for (const race of ['before-inspection', 'during-inspection', 'before-dispatch']) test(`3068 repair 1: deliberate layout ${phase} ${race} uses no allowance or exhaustion alert`, async t => {
  const {f, run, tick, stop, ports, alerts} = await setup(t);
  if (race !== 'before-dispatch') run.chatResumes = {[run.chats.at(-1).area]: [f.clock, f.clock, f.clock]};
  save(f, run); stop();
  const close = () => {const fresh = f.record(); fresh.layout.phase = phase; save(f, fresh);};
  if (race === 'before-inspection') close();
  const herdr = ports.herdr; let closed = race === 'before-inspection';
  ports.herdr = async args => {
    const atBoundary = race === 'during-inspection' ? args[0] === 'agent' && args[1] === 'get'
      : race === 'before-dispatch' && args[0] === 'tab' && args[1] === 'get';
    if (!closed && atBoundary) {closed = true; close();}
    return herdr(args);
  };
  await tick();
  assert.ok(closed, 'the controlled close must reach the intended boundary');
  assert.equal(launches(f).length, 0);
  assert.deepEqual(f.record().chatResumes, run.chatResumes);
  assert.equal(f.record().chatResumeLimit, undefined);
  assert.equal(f.record().state, 'running');
  assert.equal(alerts.length, 0);
});

test('3068 repair 1: failed dispatch counts toward a later successful recovery without reporting success', async t => {
  const {f, tick, stop, ports} = await setup(t);
  const herdr = ports.herdr;
  stop();
  ports.herdr = async args => {
    if (args[0] === 'pane' && args[1] === 'run') throw Object.assign(Error('lost reply'), {code: 'transport_lost'});
    return herdr(args);
  };
  await tick();
  assert.equal(f.record().chatResumes[f.record().chats.at(-1).area].length, 1);
  for (const words of await statusViews(f)) assert.doesNotMatch(words, recoveryWords);
  // A subsequent positive observation resolves the uncertain dispatch before a later crash.
  const chat = f.record().chats.at(-1);
  f.herdr.paneOf(chat).agent = {agent: 'claude', agent_status: 'working', agent_session: {agent: 'claude', kind: 'id', value: chat.session.id}};
  await runStatus({ref: '17', cwd: f.source}, f.ports);
  ports.herdr = herdr;
  stop(); await tick();
  for (const words of await statusViews(f)) {assert.match(words, recoveryWords); assert.match(words, /\(2 of 3\)/);}
});

for (const newer of ['question', 'gate', 'failure', 'stopped', 'blocked', 'manual-resume', 'replacement', 'area']) test(`3068 repair 1: ${newer} supersedes recovery status`, async t => {
  const {f, tick, stop} = await setup(t);
  stop(); await tick();
  for (const words of await statusViews(f)) assert.match(words, recoveryWords);
  const run = f.record(), chat = run.chats.at(-1);
  if (newer === 'question') assert.equal((await askPerson({text: 'Choose the next step.', cwd: run.root}, f.ports)).exitCode, 0);
  if (newer === 'gate') {run.gate = {kind: 'approve', area: chat.area, at: f.clock}; save(f, run);}
  if (newer === 'failure') {run.chatFailure = {area: chat.area, phase: 'open', code: 'transport_lost', message: 'Unavailable fixture', at: f.clock}; chat.startUnconfirmed = true; save(f, run); stop();}
  if (newer === 'stopped') stop();
  if (newer === 'blocked') f.herdr.paneOf(chat).agent.agent_status = 'blocked';
  if (newer === 'manual-resume') {stop(); assert.equal((await openRun({ref: '17', cwd: f.source, packageRoot}, f.ports)).exitCode, 0);}
  if (newer === 'replacement') assert.equal((await openRun({ref: '17', cwd: f.source, packageRoot, newSession: true}, f.ports)).exitCode, 0);
  if (newer === 'area') {run.area++; save(f, run);}
  for (const words of await statusViews(f)) assert.doesNotMatch(words, recoveryWords);
});

for (const agent of ['claude', 'codex']) for (const closed of [false, true]) {
  test(`3068: tick resumes ${agent} in ${closed ? 'rebuilt' : 'existing'} workspace with same session`, async t => {
    const {f, run, tick, stop, warnings} = await setup(t, agent);
    const chat = run.chats.at(-1);
    if (closed) await f.herdr.herdr(['workspace', 'close', chat.workspaceId]);
    else stop();
    f.herdr.calls.length = 0;
    await tick();
    assert.equal(launches(f).length, 1, `tick must resume the stopped worker: ${warnings.join('; ')}`);
    const after = f.record(), next = after.chats.at(-1);
    assert.equal(next.session.id, chat.session.id);
    assert.ok(launches(f)[0][3].includes(chat.session.id));
    assert.match(launches(f)[0][3], /resume/);
    assert.equal(f.herdr.paneOf(next).agent.agent_session.value, chat.session.id);
    if (closed) assert.notEqual(next.workspaceId, chat.workspaceId);
    for (const key of ['runId', 'root', 'branch', 'area', 'done', 'gate', 'decisions', 'automaticOrigin']) assert.deepEqual(after[key], run[key], key);
    assert.equal(after.chatResumes[chat.area].length, 1);
    assert.equal(f.herdr.calls.filter(a => a[0] === 'tab' && a[1] === 'focus').length, 0);
    f.herdr.calls.length = 0;
    await tick();
    assert.equal(launches(f).length, 0, 'an alive worker is not resumed again');
  });
}

for (const closed of [false, true]) test(`3068: resumed startup input carries delivered requests until agent uptake (${closed})`, async t => {
  const {f, run, tick, stop} = await setup(t);
  const changed = await changeRun({ref: '17', text: 'Retry the local build with the saved recipe.', cwd: f.source}, f.ports);
  assert.equal(changed.exitCode, 0, changed.message);
  const status = JSON.parse((await runStatus({ref: '17', cwd: f.source, json: true}, f.ports)).message);
  const request = status.runs[0].requests.at(-1);
  assert.equal(request.ackedAt, null);
  stop();
  if (closed) await f.herdr.herdr(['workspace', 'close', run.chats.at(-1).workspaceId]);
  await tick();
  const command = launches(f)[0]?.[3] ?? '';
  const file = join(run.runDir, `${run.chats.at(-1).area}-resume.md`);
  assert.ok(command.includes(file), 'resume must supply the saved request at startup');
  const input = readFileSync(file, 'utf8');
  assert.ok(input.includes(request.id)); assert.ok(input.includes(request.text));
  assert.match(input, /workflow ack/);
  const after = JSON.parse((await runStatus({ref: '17', cwd: f.source, json: true}, f.ports)).message).runs[0].requests.at(-1);
  assert.deepEqual(after, request, 'showing the request never claims uptake or redelivery');
});

for (const error of ['authentication_failed', 'rate_limit']) for (const closed of [false, true]) {
  test(`3068: ${error} blocks stopped chat recovery (${closed ? 'closed' : 'present'} workspace)`, async t => {
    const {f, run, tick, stop} = await setup(t);
    const chat = run.chats.at(-1), folder = join(f.ports.env.CLAUDE_CONFIG_DIR, 'projects', run.root.replace(/[^a-zA-Z0-9]/g, '-'));
    mkdirSync(folder, {recursive: true});
    writeFileSync(join(folder, `${chat.session.id}.jsonl`), JSON.stringify({type: 'assistant', isApiErrorMessage: true, error,
      message: {role: 'assistant', content: [{type: 'text', text: error === 'rate_limit' ? 'Usage limit reached.' : 'Authentication failed.'}]}}) + '\n');
    if (closed) await f.herdr.herdr(['workspace', 'close', chat.workspaceId]); else stop();
    f.herdr.calls.length = 0; await tick();
    assert.equal(launches(f).length, 0);
    assert.equal(f.record().chatResumes, undefined);
    assert.equal(f.record().state, 'running');
  });
}

for (const hold of ['gate', 'question', 'paused', 'cancelled', 'unconfirmed', 'foreign-owner', 'foreign-machine', 'foreign-source', 'manual', 'observe', 'off', 'unknown']) {
  test(`3068: ${hold} is not automatic recovery permission`, async t => {
    const {f, run, tick, stop, ports} = await setup(t); stop();
    if (hold === 'gate') run.gate = {kind: 'approve', area: run.chats.at(-1).area, at: f.clock};
    if (hold === 'question') run.question = {text: 'Choose the next step.', at: f.clock};
    if (['paused', 'cancelled'].includes(hold)) run.state = hold;
    if (hold === 'unconfirmed') run.chats.at(-1).startUnconfirmed = true;
    if (hold === 'foreign-owner') run.automaticOrigin.coordinatorId = 'other';
    if (hold === 'foreign-machine') run.automaticOrigin.machine = 'other';
    if (hold === 'foreign-source') run.sourceRoot = run.root;
    if (hold === 'manual') delete run.automaticOrigin;
    if (['observe', 'off'].includes(hold)) writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({autopilot: {mode: hold, trust: []}}));
    if (hold === 'unknown') ports.herdr = async args => {if (args[0] === 'agent') throw Object.assign(Error('unavailable'), {code: 'server_unavailable'}); return f.herdr.herdr(args);};
    save(f, run); await tick();
    assert.equal(launches(f).length, 0);
    assert.equal(f.record().chatResumes, undefined);
  });
}

test('3068: three attempts in rolling hour then stuck; later ticks do not launch', async t => {
  const {f, tick, stop, ports} = await setup(t);
  delete ports.sendAlert;
  const config = join(f.ports.env.XDG_CONFIG_HOME, 'pdd'); mkdirSync(config, {recursive: true});
  writeFileSync(join(config, 'autopilot-alerts.json'), JSON.stringify({v: 1, service: 'discord', url: 'https://discord.com/api/webhooks/123456789012345678/test-fixture'}));
  const alerts = [];
  ports.alertPorts = {http: async request => {alerts.push(request); return {status: 204, text: ''};}, hostname: () => origin.machine};
  for (let i = 0; i < 3; i++) {stop(); await tick(); assert.equal(launches(f).length, 1, `attempt ${i + 1}`);}
  stop(); await tick();
  assert.equal(launches(f).length, 0);
  const run = f.record(); assert.equal(run.state, 'stuck'); assert.equal(run.chatResumes[run.chats.at(-1).area].length, 3);
  assert.match(run.parkReason, /3.*hour/); assert.equal(alerts.length, 1); assert.match(alerts[0].body.content, /stuck/);
  await tick(); assert.equal(launches(f).length, 0); assert.equal(alerts.filter(row => !/digest/i.test(row.body.content)).length, 1, 'repeat ticks send one incident alert');
});

test('3068: the hour boundary and each area have independent allowances; manual open spends none', async t => {
  const {f, run, tick, stop} = await setup(t);
  const area = run.chats.at(-1).area;
  run.chatResumes = {[area]: [f.clock + 60001 - 3600000, f.clock + 60001 - 3600000, f.clock + 60001 - 3600000], other: [f.clock, f.clock, f.clock]};
  save(f, run); stop(); await tick();
  assert.equal(launches(f).length, 1);
  assert.equal(f.record().chatResumes[area].length, 1);
  assert.equal(f.record().chatResumes.other.length, 3);
  stop(); const before = f.record().chatResumes;
  assert.equal((await openRun({ref: '17', cwd: f.source, packageRoot}, f.ports)).exitCode, 0);
  assert.deepEqual(f.record().chatResumes, before);
});


test('3068: recovery uses an injected process port without a separate execFile port', async t => {
  const {f, tick, stop, ports} = await setup(t); delete ports.execFile;
  const programs = [], execute = ports.run;
  ports.run = async (...args) => {programs.push(args[0]); return execute(...args);};
  stop(); await tick();
  assert.equal(launches(f).length, 1);
  assert.ok(programs.length > 0); assert.ok(programs.every(name => name === 'git'));
});

test('3068: acknowledgement excludes a request from a later saved-session resume', async t => {
  const {f, run, tick, stop} = await setup(t);
  assert.equal((await changeRun({ref: '17', text: 'Keep the verified local result.', cwd: f.source}, f.ports)).exitCode, 0);
  const request = JSON.parse((await runStatus({ref: '17', cwd: f.source, json: true}, f.ports)).message).runs[0].requests.at(-1);
  assert.equal((await acknowledgeRequest({requestId: request.id, summary: 'Kept the result.', cwd: run.root}, f.ports)).exitCode, 0);
  stop(); await tick();
  assert.equal(launches(f).length, 1);
  assert.ok(!launches(f)[0][3].includes('-resume.md'));
});

test('3068: tick starts the stopped Herdr server through workflow open before rebuilding', async t => {
  const {f, run, tick, ports} = await setup(t);
  await f.herdr.herdr(['workspace', 'close', run.chats.at(-1).workspaceId]);
  let running = false, starts = 0;
  ports.herdr = async args => {
    if (args[0] === 'status') return {running, compatible: true};
    if (!running) throw Object.assign(Error('server stopped'), {code: 'server_not_running'});
    return f.herdr.herdr(args);
  };
  ports.spawnServer = async () => {starts++; running = true; return {};};
  f.herdr.calls.length = 0;
  await tick();
  assert.equal(starts, 1, 'existing open path starts the stopped server');
  assert.equal(launches(f).length, 1);
  assert.equal(f.record().chats.at(-1).session.id, run.chats.at(-1).session.id);
});

for (const failure of ['config-folder', 'workspace-inventory', 'request-journal']) test(`3068: failed ${failure} preflight uses no dispatch allowance and can recover`, async t => {
  const {f, run, tick, stop, ports} = await setup(t); stop();
  const herdr = ports.herdr;
  if (failure === 'config-folder') {
    const changed = f.record(); changed.configDir = join(f.base, 'missing-profile'); changed.chats.at(-1).configDir = changed.configDir; changed.launchProfile.configDir = changed.configDir; changed.chats.at(-1).launchProfile.configDir = changed.configDir; save(f, changed);
  }
  if (failure === 'workspace-inventory') ports.herdr = async args => {
    if (args[0] === 'workspace' && args[1] === 'list') throw Object.assign(Error('unavailable'), {code: 'server_unavailable'});
    return herdr(args);
  };
  if (failure === 'request-journal') writeFileSync(join(run.runDir, 'delivery-journal.json'), '{');
  for (let i = 0; i < 4; i++) {await tick(); f.tick(60001);}
  assert.equal(launches(f).length, 0);
  assert.equal(f.record().chatResumes, undefined, 'no native dispatch means no automatic attempt');
  assert.equal(f.record().state, 'running');
  if (failure === 'config-folder') {const changed = f.record(); changed.configDir = run.configDir; changed.chats.at(-1).configDir = run.chats.at(-1).configDir; changed.launchProfile = run.launchProfile; changed.chats.at(-1).launchProfile = run.chats.at(-1).launchProfile; save(f, changed);}
  if (failure === 'workspace-inventory') ports.herdr = herdr;
  if (failure === 'request-journal') writeFileSync(join(run.runDir, 'delivery-journal.json'), JSON.stringify({requests: []}));
  await tick(); assert.equal(launches(f).length, 1);
  assert.equal(f.record().chatResumes[run.chats.at(-1).area].length, 1);
});

test('3068: a lost dispatch reply spends one attempt and preserves unconfirmed custody', async t => {
  const {f, tick, stop, ports} = await setup(t); stop();
  const herdr = ports.herdr; let dispatches = 0;
  ports.herdr = async args => {
    if (args[0] === 'pane' && args[1] === 'run') {dispatches++; throw Object.assign(Error('lost reply'), {code: 'transport_lost'});}
    return herdr(args);
  };
  for (let i = 0; i < 4; i++) {await tick(); f.tick(60001);}
  const after = f.record();
  assert.equal(dispatches, 1);
  assert.equal(after.chatResumes[after.chats.at(-1).area].length, 1);
  assert.equal(after.chats.at(-1).startUnconfirmed, true);
});

for (const state of ['starting', 'unknown', 'failed']) test(`3068: closed workspace with ${state} lifecycle alone is not permission to start over`, async t => {
  const {f, run, tick} = await setup(t);
  const chat = run.chats.at(-1); chat.state = state; chat.session = null; chat.startedAt = f.clock;
  save(f, run);
  await f.herdr.herdr(['workspace', 'close', chat.workspaceId]);
  f.herdr.calls.length = 0;
  await tick();
  assert.equal(launches(f).length, 0);
  assert.equal(f.record().chatResumes, undefined);
});

test('3068: a confirmed missing pane and tab resume through the ordinary tab recreation', async t => {
  const {f, run, tick, ports} = await setup(t);
  const chat = run.chats.at(-1);
  await f.herdr.herdr(['tab', 'close', chat.tabId]);
  const herdr = ports.herdr;
  ports.herdr = async args => {
    if (args[0] === 'agent' && args[1] === 'get' && args[2] === chat.paneId)
      throw Object.assign(Error('pane gone'), {code: 'pane_not_found'});
    return herdr(args);
  };
  f.herdr.calls.length = 0;
  await tick();
  const next = f.record().chats.at(-1);
  assert.equal(launches(f).length, 1);
  assert.notEqual(next.tabId, chat.tabId);
  assert.equal(next.workspaceId, chat.workspaceId);
  assert.equal(next.session.id, chat.session.id);
});

test('3068: stopped previously running chat without saved session waits for manual recovery', async t => {
  const {f, run, tick} = await setup(t);
  const chat = run.chats.at(-1); chat.session = null; save(f, run);
  await f.herdr.herdr(['workspace', 'close', chat.workspaceId]); f.herdr.calls.length = 0;
  await tick();
  assert.equal(launches(f).length, 0);
  assert.equal(f.record().chatResumes, undefined);
});

for (const action of ['question', 'cancel', 'step']) test(`3068: concurrent ${action} wins over stale exhausted-limit inspection`, async t => {
  const {f, run, tick, stop, ports, alerts} = await setup(t);
  const name = run.chats.at(-1).area; run.chatResumes = {[name]: [f.clock, f.clock, f.clock]}; save(f, run); stop();
  const herdr = ports.herdr; let changed = false, concurrent;
  ports.herdr = async args => {
    try {return await herdr(args);}
    finally {
      if (!changed && args[0] === 'agent' && args[1] === 'get') {
        changed = true;
        const result = action === 'question' ? await askPerson({text: 'Choose how to continue.', cwd: run.root}, f.ports)
          : action === 'cancel' ? await cancelRun({ref: '17', cwd: f.source}, f.ports)
            : await stepDone({step: run.areas[run.area].steps[0], summary: 'Prepared the change.', cwd: run.root}, f.agentPorts());
        assert.equal(result.exitCode, 0, result.message);
        concurrent = f.record();
      }
    }
  };
  await tick();
  assert.ok(changed); assert.ok(concurrent);
  const after = f.record();
  for (const key of ['state', 'area', 'gate', 'question', 'done']) assert.deepEqual(after[key], concurrent[key], key);
  assert.equal(after.chatResumeLimit, undefined);
  assert.equal(alerts.length, 0);
  assert.equal(launches(f).length, 0);
});


const closeMark = (f, reason, confirmed) => ({at: f.clock, reason, screen: null, ...(confirmed ? {confirmedAt: f.clock} : {})});
for (const reason of ['area-end', 'run-end', 'budget', 'cancel']) for (const confirmed of [false, true]) {
  for (const state of ['running', 'exhausted', 'stuck']) test(`3068 repair 2: ${reason} ${confirmed ? 'confirmed' : 'pending'} close blocks ${state} recovery`, async t => {
    const {f, run, tick, stop, alerts} = await setup(t);
    const chat = run.chats.at(-1), mark = closeMark(f, reason, confirmed);
    chat.closed = mark;
    if (state !== 'running') run.chatResumes = {[chat.area]: [f.clock, f.clock, f.clock]};
    if (state === 'stuck') {
      run.state = 'stuck'; run.parkReason = 'Resume allowance exhausted.';
      run.chatResumeLimit = {area: chat.area, at: f.clock};
    }
    save(f, run); stop();
    await f.herdr.herdr(['tab', 'close', chat.tabId]);
    // A normal observation and later ticks must preserve the persisted intent.
    assert.equal((await runStatus({ref: '17', cwd: f.source}, f.ports)).exitCode, 0);
    assert.deepEqual(f.record().chats.at(-1).closed, mark);
    for (let i = 0; i < 2; i++) {
      await tick();
      assert.equal(launches(f).length, 0);
      const after = f.record();
      assert.deepEqual(after.chats.at(-1).closed, mark);
      assert.deepEqual(after.chatResumes, run.chatResumes);
      assert.deepEqual(after.chatResumeLimit, run.chatResumeLimit);
      assert.equal(after.state, run.state);
      assert.equal(alerts.length, 0);
    }
  });
}

for (const confirmed of [false, true]) for (const target of ['present-tab', 'missing-tab', 'new-chat']) test(`3068 repair 2: ${confirmed ? 'confirmed' : 'pending'} close races dispatch to ${target}`, async t => {
  const {f, run, tick, stop, ports, alerts} = await setup(t);
  const mark = closeMark(f, 'budget', confirmed), chat = run.chats.at(-1);
  stop();
  if (target === 'missing-tab') await f.herdr.herdr(['tab', 'close', chat.tabId]);
  const herdr = ports.herdr; let closed = false;
  ports.herdr = async args => {
    if (!closed && args[0] === 'tab' && args[1] === 'get') {
      closed = true;
      const fresh = f.record();
      if (target === 'new-chat') fresh.chats.push({...fresh.chats.at(-1), session: {agent: 'claude', id: '00000000-0000-4000-8000-000000000099'}});
      fresh.chats.at(-1).closed = mark; save(f, fresh);
    }
    return herdr(args);
  };
  await tick();
  assert.ok(closed, 'the controlled close must reach dispatch preparation');
  assert.equal(launches(f).length, 0);
  const after = f.record();
  assert.deepEqual(after.chats.at(-1).closed, mark);
  assert.equal(after.chatResumes, undefined);
  assert.equal(after.chatResumeLimit, undefined);
  assert.equal(after.state, 'running');
  assert.equal(alerts.length, 0);
});

for (const confirmed of [false, true]) test(`3068 repair 2: ${confirmed ? 'confirmed' : 'pending'} close survives a fresh tick process`, async t => {
  const {f, run, stop, stateFile} = await setup(t);
  const mark = closeMark(f, 'run-end', confirmed);
  run.chats.at(-1).closed = mark; save(f, run); stop();
  // A fresh process has no prior run object or native server. Use the same repository fake.
  const script = `
    import {readFileSync} from 'node:fs';
    import {execFile} from 'node:child_process';
    import {promisify} from 'node:util';
    import {tickAutopilot} from './src/autopilot-launcher.mjs';
    import {fakeHerdr} from './test/helpers/fake-herdr.mjs';
    const input = JSON.parse(readFileSync(0, 'utf8')), h = fakeHerdr(), exec = promisify(execFile);
    const alerts = [], warnings = [];
    const execute = async (file, args, options) => {
      if (file !== 'git' || !['rev-parse', 'config', 'status', 'show-ref', 'symbolic-ref', 'remote', 'worktree', 'for-each-ref', 'merge-base', 'check-ref-format'].includes(args[0])) throw Error('Unexpected external command: ' + file + ' ' + args[0]);
      return {code: 0, ...await exec(file, args, options)};
    };
    await tickAutopilot(input.stateFile, {stateDir: input.stateDir, env: input.env,
      layoutDirectory: input.layoutDirectory, now: () => input.now, herdr: h.herdr, owners: {read: async () => ({json: JSON.stringify(input.ownership)})},
      findNativeSessions: async () => [], run: execute, execFile: execute,
      warn: value => warnings.push(value), sendAlert: async value => {alerts.push(value); return {exitCode: 0};}});
    process.stdout.write(JSON.stringify({launches: h.calls.filter(a => a[0] === 'pane' && a[1] === 'run'), alerts, warnings}));
  `;
  const result = JSON.parse(execFileSync(process.execPath, ['--input-type=module', '-e', script], {
    cwd: packageRoot, encoding: 'utf8', timeout: 10000,
    input: JSON.stringify({stateFile, stateDir: f.state, env: f.ports.env, layoutDirectory: f.ports.layoutDirectory, now: f.clock, ownership: matchingClaimObservation(run)})
  }));
  assert.equal(result.launches.length, 0);
  assert.deepEqual(result.warnings, []);
  assert.equal(result.alerts.length, 0);
  assert.deepEqual(f.record().chats.at(-1).closed, mark);
  assert.equal(f.record().chatResumes, undefined);
  assert.equal(f.record().chatResumeLimit, undefined);
  assert.equal(f.record().state, 'running');
});

for (const confirmed of [false, true]) test(`release: cleanup-owned close mark blocks tick resume (${confirmed})`, async t => {
  const {f, tick, ports, alerts} = await setup(t);
  const run = f.record(), chat = run.chats.at(-1), command = ports.herdr;
  f.herdr.idle();
  const cleanup = await closeFinishedChats(run, {...ports, force:true, graceMs:0,
    checkpoint:async marked => { if (marked) { Object.assign(chat, marked); save(f, run); } },
    herdr:async args => {
      if (!confirmed && ['tab', 'workspace'].includes(args[0]) && args[1] === 'close')
        throw Object.assign(Error('controlled refusal'), {code:'herdr_failed'});
      return command(args);
    }});
  assert.equal(cleanup.closed, confirmed ? 1 : 0);
  assert.ok(f.record().chats.at(-1).closed);
  assert.equal(Number.isFinite(f.record().chats.at(-1).closed.confirmedAt), confirmed);
  assert.ok(!['closed','close_intent'].includes(f.record().layout.phase));
  const remaining = f.herdr.paneOf(chat); if (remaining) remaining.agent = null;
  const before = f.record(); f.herdr.calls.length = 0; f.tick(60001);
  await tick();
  assert.equal(launches(f).length, 0);
  assert.deepEqual(f.record().chatResumes, before.chatResumes);
  assert.equal(f.record().chatResumeLimit, undefined);
  assert.deepEqual(f.record().chats.at(-1).closed, before.chats.at(-1).closed);
  assert.equal(alerts.length, 0);
});
