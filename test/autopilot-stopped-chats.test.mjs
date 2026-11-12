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
    views.push(options.json ? JSON.parse(result.message).runs[0].words : result.message);
  }
  return views;
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

test('3068: stopped previously running chat without saved session waits for manual recovery', async t => {
  const {f, run, tick} = await setup(t);
  const chat = run.chats.at(-1); chat.session = null; save(f, run);
  await f.herdr.herdr(['workspace', 'close', chat.workspaceId]); f.herdr.calls.length = 0;
  await tick();
  assert.equal(launches(f).length, 0);
  assert.equal(f.record().chatResumes, undefined);
});

const closeMark = (f, reason, confirmed) => ({at: f.clock, reason, screen: null, ...(confirmed ? {confirmedAt: f.clock} : {})});
for (const confirmed of [true]) test(`release: cleanup-owned close mark blocks tick resume (${confirmed})`, async t => {
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
