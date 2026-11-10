import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { launcher } from './helpers/environment-launcher-fixture.mjs';
import { runAutopilotLauncher } from '../src/autopilot-launcher.mjs';
const issue = number => ({ number, state: 'open', title: 'Synthetic work', body: 'Check local behavior', user: { login: 'owner' }, author_association: 'OWNER',
  created_at: '2026-11-06T11:00:00Z', updated_at: '2026-11-06T11:00:00Z', comments: 0, labels: [], html_url: `https://github.com/owner/repo/issues/${number}` });
const state = f => JSON.parse(readFileSync(f.stateFile(), 'utf8'));
const save = (f, patch) => writeFileSync(f.stateFile(), JSON.stringify({ ...state(f), ...patch }));
const limited = resetAt => ({ state: 'limited', resetAt, usedPercent: 100 });
const healthy = () => ({ state: 'healthy', resetAt: null, usedPercent: 4 });
const unknown = () => ({ state: 'unknown', resetAt: null, usedPercent: null });

test('usage stops admission and deduplicates one machine incident across issues and repeated ticks', async t => {
  const f = await launcher(t); await f.start(); f.prompts.length = 0;
  f.issues = [issue(12), issue(13)]; const reset = f.time + 60_000;
  f.ports.codexLimits = async () => limited(reset);
  for (let i = 0; i < 3; i++) { await f.tick(); f.time += 60_000; }
  assert.equal(f.prompts.length, 0, 'quota must withhold coordinator work');
  assert.equal(state(f).health?.paused, true);
  assert.equal(f.sent.length, 1);
  assert.match(f.sent[0], /usage-limit/); assert.ok(f.sent[0].includes(new Date(reset).toISOString()));
  assert.equal(state(f).seen?.[12], undefined, 'withheld work must stay undelivered');
  const before = state(f); assert.equal(before.health.usage.state, 'limited', 'elapsed reset does not prove recovery');
  assert.equal(before.enabled, true);
  f.ports.codexLimits = async () => healthy(); await f.tick();
  assert.equal(state(f).health.paused, false); assert.equal(f.sent.length, 2); assert.match(f.sent[1], /recovered/);
  assert.equal(f.prompts.length, 1); assert.deepEqual(f.packet().issues.map(row => row.number), [12, 13]);
  await f.tick(); assert.equal(f.sent.length, 2);
});

test('machine hold keeps claim heartbeats and progress reads, blocks retries and recovers without fresh work', async t => {
  const f = await launcher(t); await f.start(); f.prompts.length = 0;
  const owner = state(f); let beats = 0, progress = 0, reads = 0;
  const claim = { issue: issue(12).html_url, active: true, coordinatorId: owner.coordinatorId, machine: owner.machine, commentId: 'c', labelEventId: 'e' };
  f.ports.reconcileDependencyIntake = async () => ({ eligible: [], claims: [claim], queued: [], skipped: [] });
  f.ports.refreshClaimHeartbeat = async () => { beats++; return { state: 'refreshed', lastSeen: new Date(f.time).toISOString() }; };
  f.ports.readRunProgress = async () => { progress++; return []; };
  f.ports.machineHealth = async () => { reads++; return { healthy: false, causes: ['disk'], resources: null }; };
  f.environmentWaits = [{ number: 12, at: f.time - 60_000, nextAt: f.time, attempts: 0, area: 0, step: 'verify', reason: 'native suite stall' }];
  await f.tick(); await f.tick();
  assert.equal(beats, 2); assert.equal(progress, 2); assert.equal(reads, 2); assert.equal(f.prompts.length, 0);
  assert.equal(f.sent.length, 1); assert.match(f.sent[0], /resource/);
  f.environmentWaits = []; f.ports.machineHealth = async () => ({ healthy: true, causes: [], resources: null });
  await f.tick(); assert.equal(f.prompts.length, 1, 'recovery must wake without a new issue');
  assert.equal(f.packet().health.paused, false); assert.equal(state(f).health.recoveryPending, null);
  assert.equal(beats, 3); assert.equal(f.sent.length, 2);
});

test('unknown usage holds the incident until a positive read and recovery waits for idle delivery', async t => {
  const f = await launcher(t); await f.start(); f.prompts.length = 0; f.issues = [issue(12)];
  f.ports.codexLimits = async () => limited(f.time - 1); await f.tick();
  f.ports.codexLimits = async () => unknown(); await f.tick();
  assert.equal(f.sent.length, 1); assert.equal(f.prompts.length, 0);
  const herdr = f.ports.herdr;
  f.ports.herdr = async args => { const reply = await herdr(args); if (reply?.result?.agent) reply.result.agent.agent_status = 'working'; return reply; };
  f.ports.armCoordinatorIdle = () => {};
  f.ports.codexLimits = async () => healthy(); await f.tick();
  assert.equal(f.sent.length, 2); assert.equal(f.prompts.length, 0); assert.equal(state(f).health.recoveryPending, f.time);
  f.ports.herdr = herdr; await f.tick();
  assert.equal(f.prompts.length, 1); assert.equal(state(f).health.recoveryPending, null); assert.equal(f.sent.length, 2);
});

test('status reads saved health only and selected profile wins over ambient profile', async t => {
  const f = await launcher(t); await f.start();
  const seen = []; const home = f.home + '/saved-profile';
  save(f, { environment: { ...state(f).environment, CODEX_HOME: home } });
  f.ports.env = { CODEX_HOME: '/wrong-profile' };
  f.ports.codexLimits = async input => { seen.push(input); return limited(f.time + 60_000); };
  await f.tick(); assert.equal(seen.length, 1); assert.equal(seen[0].env.CODEX_HOME, home); assert.equal(seen[0].env.HOME, f.home);
  const status = await runAutopilotLauncher({ command: 'status', cwd: f.cwd, env: f.env }, f.ports);
  assert.equal(seen.length, 1); assert.match(status.message, /Health:.*paused/); assert.ok(status.message.includes(new Date(f.time + 60_000).toISOString()));
  const environment = { ...state(f).environment }; delete environment.CODEX_HOME; save(f, { environment });
  await f.tick(); assert.equal(seen[1].env.CODEX_HOME, undefined);
});

test('health is still observed during GitHub deferral and a probe failure is a visible hold', async t => {
  const f = await launcher(t); await f.start(); f.prompts.length = 0;
  let reads = 0; f.ports.codexLimits = async () => { reads++; throw Error('synthetic secret payload'); };
  save(f, { retryAt: f.time + 60_000 });
  await f.tick(); assert.equal(reads, 1); assert.equal(state(f).health?.paused, true);
  assert.equal(state(f).health.usage.state, 'unknown'); assert.equal(f.prompts.length, 0);
  assert.equal(JSON.stringify(state(f)).includes('synthetic secret payload'), false);
});

test('partial recovery closes only its own incident and does not wake until all blockers clear', async t => {
  const f = await launcher(t); await f.start(); f.prompts.length = 0; f.issues = [issue(12)];
  f.ports.codexLimits = async () => limited(null);
  f.ports.machineHealth = async () => ({ healthy: false, causes: ['memory'], resources: null });
  await f.tick(); assert.equal(f.sent.length, 2);
  f.ports.codexLimits = async () => healthy(); await f.tick();
  assert.equal(f.sent.length, 3); assert.equal(f.prompts.length, 0); assert.equal(state(f).health.paused, true);
  assert.deepEqual(Object.keys(state(f).health.incidents), ['resource']);
  f.ports.machineHealth = async () => ({ healthy: true, causes: [], resources: null }); await f.tick();
  assert.equal(f.sent.length, 4); assert.equal(f.prompts.length, 1);
});

test('malformed saved health does not break read-only status', async t => {
  const f = await launcher(t); await f.start();
  for (const health of [{ at: 'bad', paused: false }, { at: f.time, paused: false, resource: { causes: 'bad' } },
    { at: f.time, paused: false, resource: { healthy: true, causes: [] }, usage: { state: 'limited', resetAt: 'bad' } }]) {
    save(f, { health });
    const result = await runAutopilotLauncher({ command: 'status', cwd: f.cwd, env: f.env }, f.ports);
    assert.equal(result.exitCode, 0); assert.match(result.message, /^Health: unknown/m);
  }
});

test('health alert during a GitHub wait uses saved repository and webhook without a gh read', async t => {
  const f = await launcher(t); await f.start(); f.prompts.length = 0;
  save(f, { retryAt: f.time + 60_000, cachedIssues: [issue(12)] });
  const run = f.ports.run; let gh = 0;
  f.ports.run = async (command, ...args) => { if (command === 'gh') { gh++; throw Error('GitHub must wait'); } return run(command, ...args); };
  f.ports.codexLimits = async () => limited(f.time + 30_000);
  await f.tick(); assert.equal(gh, 0); assert.equal(f.sent.length, 1);
  assert.equal(state(f).health.paused, true); assert.equal(f.prompts.length, 0);
});

test('GitHub budget reserve and rate-limit pauses send one usage-limit alert with reset time and one recovered alert after reset', async t => {
  const f = await launcher(t); await f.start(); f.prompts.length = 0; f.issues = [issue(12)];
  const resetSec = Math.floor((f.time + 180_000) / 1000), resetIso = new Date(resetSec * 1000).toISOString();
  const run = f.ports.run;
  // Seed the GitHub rate-limit ledger below the 1000-call reserve floor via a real counted gh api header reply.
  f.ports.run = async (command, args, ...rest) => {
    if (command === 'gh' && args[0] === 'api') {
      return { code: 0, stdout: `HTTP/2.0 200 OK\r\nx-ratelimit-limit: 5000\r\nx-ratelimit-remaining: 400\r\nx-ratelimit-reset: ${resetSec}\r\nx-ratelimit-resource: core\r\n\r\n[]`, stderr: '' };
    }
    return run(command, args, ...rest);
  };
  const { githubLedger, githubEntry } = await import('../src/github-calls.mjs');
  githubLedger({ root: f.ports.stateRoot, repository: 'owner/repo' }).record(githubEntry(
    ['api', '-i', 'repos/owner/repo/issues'],
    { code: 0, stdout: `HTTP/2.0 200 OK\r\nx-ratelimit-limit: 5000\r\nx-ratelimit-remaining: 400\r\nx-ratelimit-reset: ${resetSec}\r\nx-ratelimit-resource: core\r\n\r\n[]`, stderr: '' },
    'issues',
    f.time,
  ));
  await f.tick();
  assert.equal(f.prompts.length, 0, 'reserve budget must pause coordinator admission');
  assert.equal(f.sent.length, 1, 'reserve pause sends one usage-limit alert');
  assert.match(f.sent[0], /usage-limit/);
  assert.ok(f.sent[0].includes(resetIso), 'alert includes the GitHub reset time');
  assert.equal(state(f).githubLimit?.resetAt, resetSec * 1000);

  // Repeated ticks while paused for the same GitHub budget window must not repeat the alert.
  f.time += 30_000; await f.tick();
  f.time += 30_000; await f.tick();
  assert.equal(f.sent.length, 1, 'no repeat alert per tick during the same GitHub pause');

  // After the reset window passes and GitHub reads succeed, send one recovered alert.
  f.time = resetSec * 1000 + 1_000;
  f.ports.run = run;
  await f.tick();
  assert.equal(f.sent.length, 2, 'resuming GitHub reads sends one recovered alert');
  assert.match(f.sent[1], /recovered/);
  assert.equal(state(f).githubLimit, undefined);
  assert.equal(f.prompts.length, 1);

  // Also verify a direct 429 rate-limit response from queryIssues pauses once and recovers once.
  const nextResetMs = f.time + 120_000, nextResetIso = new Date(nextResetMs).toISOString();
  f.issues = [issue(13)];
  f.ports.queryIssues = async () => ({ status: 429, rateLimited: true, resetAt: nextResetMs, issues: [] });
  await f.tick();
  assert.equal(f.sent.length, 3);
  assert.match(f.sent[2], /usage-limit/);
  assert.ok(f.sent[2].includes(nextResetIso));
  f.time += 30_000; await f.tick();
  assert.equal(f.sent.length, 3, 'no repeat on paused retryAt tick');
  f.time = nextResetMs + 1_000;
  f.ports.queryIssues = async () => ({ status: 200, etag: '"two"', issues: structuredClone(f.issues) });
  await f.tick();
  assert.equal(f.sent.length, 4);
  assert.match(f.sent[3], /recovered/);
});
