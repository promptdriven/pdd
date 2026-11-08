import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { launcher } from './helpers/environment-launcher-fixture.mjs';
const minute = 60_000;
const retry = (f, extra = {}) => ({ number: 12, at: f.time, step: 'verify', area: 0, reason: 'Native full suite filesystem journal I/O stall', attempts: 0, nextAt: f.time + 15 * minute, ...extra });

test('tick waits for due time and health, offers only the failed validation, and deduplicates across restart', async t => {
  const f = await launcher(t); f.env.PDD_SUITE_QUEUE = '/synthetic/shared-suite-queue'; await f.start(); f.prompts.length = 0;
  f.environmentWaits = [retry(f)];
  f.time += 14 * minute; await f.tick(); assert.equal(f.rules().length, 0);
  f.time += minute; f.machineHealthy = false; await f.tick(); assert.equal(f.rules().length, 0);
  f.machineHealthy = true; await f.tick();
  const offered = f.rules().filter(row => row.kind === 'environment-ready');
  assert.equal(offered.length, 1, 'healthy due validation must be retried');
  assert.deepEqual([offered[0].number, offered[0].step, offered[0].attempt, offered[0].limit], [12, 'verify', 1, 3]);
  assert.equal(offered[0].nextAt, f.environmentWaits[0].nextAt);
  assert.equal(JSON.parse(readFileSync(f.stateFile(), 'utf8')).environment.PDD_SUITE_QUEUE, '/synthetic/shared-suite-queue');
  assert.equal(f.healthInputs.at(-1).env.PDD_SUITE_QUEUE, '/synthetic/shared-suite-queue');
  assert.match(offered[0].reason, /Environment validation wake for 0:verify/);
  const sent = f.prompts.length;
  await f.tick(); assert.equal(f.prompts.length, sent);
  f.time += 30 * minute; await f.tick(); assert.equal(f.prompts.length, sent + 1, 'undelivered parks get a fresh later offer');
  assert.equal(f.sent.length, 0, 'no alert before the retry limit');
  // A new failure of the same target carries the spent budget and gets its own due wake.
  f.environmentWaits = [retry(f, { attempts: 1, nextAt: f.time + 60 * minute })];
  f.time += 60 * minute; await f.tick();
  assert.equal(f.rules().find(row => row.kind === 'environment-ready').attempt, 2);
});

test('exhaustion keeps the run stuck and sends one cause-specific alert over repeated ticks', async t => {
  const f = await launcher(t); await f.start(); f.prompts.length = 0;
  f.environmentWaits = [retry(f, { attempts: 3, nextAt: null })];
  for (let i = 0; i < 4; i++) { f.time += 30 * minute; await f.tick(); }
  assert.equal(f.prompts.length, 0, 'no retry offered at the limit');
  assert.equal(f.sent.length, 1, 'one alert after retry exhaustion');
  assert.match(f.sent[0], /filesystem journal I\/O/); assert.match(f.sent[0], /3.*verify/s);
  assert.equal(f.environmentWaits[0].attempts, 3);
});

test('old records need an explicit failed target and retry records belong to this coordinator and machine', async t => {
  const f = await launcher(t);
  delete f.ports.readEnvironmentWaits;
  const directory = join(f.cwd, 'pdd', 'runs', '12');
  const { mkdirSync } = await import('node:fs'); mkdirSync(directory, { recursive: true });
  await f.start(); f.prompts.length = 0;
  const state = JSON.parse(readFileSync(f.stateFile(), 'utf8'));
  const run = { v: 1, number: 12, repo: state.repo, state: 'stuck', updatedAt: f.time - 16 * minute,
    parkReason: 'Native full suite filesystem journal I/O stall', automaticOrigin: { coordinatorId: state.coordinatorId, machine: state.machine },
    area: 0, areas: [{ name: 'code', steps: ['build', 'verify', 'formal'] }], done: { build: {} } };
  const file = join(directory, 'status.json');
  // An old run with two unfinished validations cannot identify the failed one.
  writeFileSync(file, JSON.stringify(run)); await f.tick(); assert.equal(f.rules().length, 0);
  run.environmentRetry = retry(f, { at: run.updatedAt, nextAt: run.updatedAt + 15 * minute });
  delete run.environmentRetry.number;
  for (const origin of [{ ...run.automaticOrigin, machine: 'other' }, run.automaticOrigin]) {
    writeFileSync(file, JSON.stringify({ ...run, automaticOrigin: origin }));
    const before = readFileSync(file, 'utf8'); f.time += minute; await f.tick();
    assert.equal(readFileSync(file, 'utf8'), before, 'tick never edits run records');
    if (origin.machine === 'other') assert.equal(f.rules().length, 0);
    else assert.equal(f.rules().filter(row => row.kind === 'environment-ready').length, 1, 'owned explicit validation gets recovery');
  }
});
