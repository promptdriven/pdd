import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import { execFileSync } from 'node:child_process';
import { captureCosts, applyCostMeasurement, captureClosedCi, costReport, recordCostGithub } from '../src/cost-ledger.mjs';
import { nativeGithubCounter } from '../src/github-calls.mjs';
import { runAutopilotLauncher } from '../src/autopilot-launcher.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import * as runner from '../src/workflow-runner.mjs';
import { updateRun } from '../src/workflow-runs.mjs';
import { fixture } from './helpers/workflow-runner-fixture.mjs';

const at = Date.parse('2026-10-27T17:00:00Z');
const id = '22222222-2222-4222-8222-222222222222';
function world(t) {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-cost-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const run = { runId: 'attempt-1', number: 17, repo: 'acme/project', startedAt: at, runDir: root, root: join(root, 'worktree'),
    state: 'running', agent: 'claude', chats: [], pr: [], areas: [{ name: 'code' }] };
  const ports = { now: () => at, env: { HOME: root }, fs };
  return { root, run, ports };
}
function claudeFile(run, root) {
  const configDir = join(root, '.claude');
  run.chats = [{ agent: 'claude', configDir, session: { id }, startedAt: at }];
  const file = join(configDir, 'projects', run.root.replace(/[^a-zA-Z0-9]/g, '-'), `${id}.jsonl`);
  fs.mkdirSync(join(file, '..'), { recursive: true }); return file;
}
const usageRow = (messageId, output = 10) => JSON.stringify({ type: 'assistant', sessionId: id,
  message: { id: messageId, usage: { input_tokens: 20, output_tokens: output } } }) + '\n';

test('Claude reads a large transcript in bounded chunks, retains a partial row, and deduplicates streaming updates', t => {
  const { root, run, ports } = world(t), file = claudeFile(run, root);
  fs.writeFileSync(file, usageRow('first') + (JSON.stringify({ type: 'user', message: { content: 'synthetic padding'.repeat(50) } }) + '\n').repeat(500) + usageRow('last'));
  let bytes = 0;
  ports.sessionFs = { ...fs, readSync(fd, buffer, offset, length, position) { bytes += length; return fs.readSync(fd, buffer, offset, length, position); } };
  run.cost = captureCosts(null, run, ports);
  assert.ok(bytes <= 256 * 1024); assert.ok(run.cost.coverage.includes('session-backlog'));
  bytes = 0; run.cost = captureCosts(run, run, ports);
  assert.ok(bytes <= 256 * 1024); assert.equal(run.cost.tokens[0].total, 60);
  assert.ok(!run.cost.coverage.includes('session-backlog'));
  fs.appendFileSync(file, usageRow('last', 20).trimEnd());
  run.cost = captureCosts(run, run, ports); assert.equal(run.cost.tokens[0].total, 60);
  fs.appendFileSync(file, '\n'); run.cost = captureCosts(run, run, ports); assert.equal(run.cost.tokens[0].total, 70);
  fs.unlinkSync(file); run.cost = captureCosts(run, run, ports);
  assert.equal(run.cost.tokens[0].total, 70); assert.ok(run.cost.coverage.includes('session-unavailable'));
});

test('unknown usage is distinct from measured zero and file truncation cannot lower totals', t => {
  const { root, run, ports } = world(t), file = claudeFile(run, root);
  fs.writeFileSync(file, 'broken\n'); run.cost = captureCosts(null, run, ports);
  assert.deepEqual(run.cost.tokens, []); assert.ok(run.cost.coverage.includes('usage-unavailable'));
  fs.appendFileSync(file, usageRow('measured')); run.cost = captureCosts(run, run, ports);
  assert.equal(run.cost.tokens[0].total, 30);
  fs.writeFileSync(file, ''); run.cost = captureCosts(run, run, ports);
  assert.equal(run.cost.tokens[0].total, 30); assert.ok(run.cost.coverage.includes('session-truncated'));
});

test('explicit measurements are idempotent, validate input, preserve zero, and do not change workflow state', t => {
  const { run, ports } = world(t);
  const input = { id: 'suite-1', suiteMinutes: 2.5, personMinutes: 0, outcome: 'reverted' };
  applyCostMeasurement(run, input, at); applyCostMeasurement(run, { ...input }, at + 1000);
  run.cost = captureCosts(null, run, ports);
  assert.equal(run.cost.suiteMinutes, 2.5); assert.equal(run.cost.person.activeMinutes, 0);
  assert.equal(run.cost.outcome, 'reverted'); assert.equal(run.state, 'running');
  assert.equal(costReport([run], at).day.totals.person.activeMinutes, 0);
  assert.throws(() => applyCostMeasurement(run, { ...input, suiteMinutes: 3 }, at));
  for (const invalid of [null, {}, { id: 'bad' }, { id: 'bad', suiteMinutes: -1 }, { id: 'bad', personMinutes: Infinity }, { id: 'bad', outcome: 'invented' }, { id: 'bad', text: 'SECRET', suiteMinutes: 1 }])
    assert.throws(() => applyCostMeasurement(run, invalid, at));
});

test('CI closure makes one bounded read, filters PRs, keeps zero and never retries failures or a reservation', async t => {
  const { run, ports, root } = world(t), head = 'a'.repeat(40); let calls = 0;
  run.pr = [{ number: 23, state: 'open', headSha: head }];
  ports.execFile = async (file, args) => {
    calls++; assert.equal(file, 'gh'); assert.deepEqual(args, ['api', `repos/acme/project/actions/runs?head_sha=${head}&per_page=100`]);
    const workflow = (number, minutes) => ({ head_sha: head, pull_requests: [{ number }], status: 'completed', run_started_at: new Date(at).toISOString(), updated_at: new Date(at + minutes * 60000).toISOString() });
    return { stdout: JSON.stringify({ total_count: 3, workflow_runs: [workflow(23, 2), workflow(23, 3), workflow(99, 10)] }) };
  };
  await captureClosedCi(run, ports); assert.equal(calls, 0);
  run.pr[0].state = 'merged'; await Promise.all([captureClosedCi(run, ports), captureClosedCi(run, ports)]);
  await captureClosedCi(run, ports); assert.equal(calls, 1);
  run.cost = captureCosts(null, run, ports); assert.equal(run.cost.ciMinutes, 5);
  run.pr.push({ number: 24, state: 'closed', headSha: head });
  ports.execFile = async () => { calls++; throw Error('fake failure'); };
  await captureClosedCi(run, ports); await captureClosedCi(run, ports); assert.equal(calls, 2);
  assert.equal(JSON.parse(fs.readFileSync(join(root, 'cost-ci-24.json'))).minutes, null);
  run.pr.push({ number: 25, state: 'closed', headSha: head });
  fs.writeFileSync(join(root, 'cost-ci-25.json'), '{');
  await captureClosedCi(run, ports); assert.equal(calls, 2);
});

test('CI marks partial pages and unfinished workflows as incomplete', async t => {
  const { run, ports } = world(t); run.pr = [{ number: 23, state: 'closed', headSha: 'b'.repeat(40) }];
  ports.execFile = async () => ({ stdout: JSON.stringify({ total_count: 101, workflow_runs: [{ head_sha: 'b'.repeat(40), status: 'in_progress' }] }) });
  await captureClosedCi(run, ports); run.cost = captureCosts(null, run, ports);
  assert.ok(run.cost.coverage.includes('ci-unavailable'));
});

test('GitHub counts use the existing counter for normal runs and survive budget ledger compaction', async t => {
  const { run, ports, root } = world(t); let programs = 0;
  const counter = nativeGithubCounter(async () => { programs++; return { stdout: '{}' }; }, { env: { HOME: root }, stateRoot: join(root, 'budget'), now: ports.now, costRun: async () => run.runDir });
  await counter('gh', ['pr', 'view', '23'], { cwd: run.root });
  await counter('git', ['status'], { cwd: run.root });
  assert.equal(programs, 2); run.cost = captureCosts(null, run, ports); assert.equal(run.cost.githubCalls, 1);
  const error = Error('fake error');
  const failed = nativeGithubCounter(async () => { throw error; }, { env: { HOME: root }, now: ports.now, costRun: async () => run.runDir });
  await assert.rejects(failed('gh', ['pr', 'view', '23']), caught => caught === error);
  run.cost = captureCosts(run, run, ports); assert.equal(run.cost.githubCalls, 2);
  fs.rmSync(join(root, 'budget'), { recursive: true, force: true });
  run.cost = captureCosts(run, run, ports); assert.equal(run.cost.githubCalls, 2);
  assert.equal(fs.statSync(join(root, 'github-cost.jsonl')).mode & 0o777, 0o600);
});

test('per-issue percentiles combine attempts, separate repos, and use observed event windows', t => {
  const { run, ports } = world(t), runs = [];
  for (let i = 1; i <= 10; i++) {
    const attempt = { ...run, number: i, runId: `run-${i}`, startedAt: at - 1000, cost: undefined };
    applyCostMeasurement(attempt, { id: 'cost', suiteMinutes: i, outcome: 'merged' }, at);
    attempt.cost = captureCosts(null, attempt, ports); runs.push(attempt);
  }
  const retry = { ...run, number: 1, runId: 'old-attempt', startedAt: at - 2000, cost: undefined };
  applyCostMeasurement(retry, { id: 'cost', suiteMinutes: 1 }, at - 2 * 86400000); retry.cost = captureCosts(null, retry, ports); runs.push(retry);
  let report = costReport(runs, at);
  assert.equal(report.day.mergedIssues, 10); assert.equal(report.day.totals.suiteMinutes, 55);
  assert.equal(report.week.totals.suiteMinutes, 56); assert.equal(report.day.p50.suiteMinutes, 5); assert.equal(report.day.p90.suiteMinutes, 9);
  const other = { ...run, repo: 'other/project', cost: undefined };
  applyCostMeasurement(other, { id: 'cost', suiteMinutes: 50, outcome: 'merged' }, at); other.cost = captureCosts(null, other, ports);
  report = costReport([...runs, other], at); assert.equal(report.day.mergedIssues, 11); assert.equal(report.day.p90.suiteMinutes, 10);
  other.cost.outcome = 'reverted'; assert.equal(costReport([other], at).day.mergedIssues, 0);
  assert.equal(costReport([], at).day.p50, null);
});

test('status JSON includes normal runs without launcher state, with no GitHub, Herdr or timer probes', async t => {
  const f = await fixture(t); f.ports.skipMetricsDelivery = true; assert.equal((await f.run()).exitCode, 0);
  const saved = f.record();
  const result = await runAutopilotLauncher({ command: 'status', json: true, cwd: f.source, env: f.ports.env }, {
    ...f.ports, costRuns: async () => [saved], run: () => assert.fail('No external program in cost status'), timer: () => assert.fail('No timer probe'), herdr: () => assert.fail('No Herdr probe')
  });
  assert.equal(result.exitCode, 0); const report = JSON.parse(result.message);
  assert.equal(report.schema, 'pdd.cost-report.v1'); assert.equal(report.runs[0].issue, 17);
  assert.ok(report.runs[0].coverage.includes('suite-unavailable'));
});

test('workflow cost records and reads local data without workflow effects', async t => {
  const f = await fixture(t); f.ports.skipMetricsDelivery = true; assert.equal((await f.run()).exitCode, 0);
  const before = f.record(), calls = f.herdr.calls.length;
  const input = { id: 'suite-1', suiteMinutes: 4, personMinutes: 1 };
  for (let i = 0; i < 2; i++) assert.equal((await runner.runCosts({ ref: '17', cwd: f.source, input }, f.ports)).exitCode, 0);
  const result = await runner.runCosts({ ref: '17', cwd: f.source }, f.ports), row = JSON.parse(result.message), after = f.record();
  assert.equal(row.suiteMinutes, 4); assert.equal(row.person.activeMinutes, 1);
  assert.deepEqual(after.done, before.done); assert.deepEqual(after.gate, before.gate); assert.equal(after.state, before.state);
  assert.equal(f.herdr.calls.length, calls); assert.equal(f.pushes.length, 0); assert.equal(f.edits.length, 0);
});

test('CLI routes JSON status without settings reads and cost input without approval dispatch', async () => {
  let out = '', err = '', supplied;
  const dependencies = { stdout: { write: text => { out += text; } }, stderr: { write: text => { err += text; } }, cwd: '/synthetic', env: {},
    autopilotLauncher: { runAutopilotLauncher: async input => { supplied = input; return { exitCode: 0, message: '{"schema":"pdd.cost-report.v1"}' }; } },
    autopilotGithub: { checkAutopilotSettings: () => assert.fail('No settings read') } };
  assert.equal(await runPdd(['autopilot', 'status', '--json'], dependencies), 0); assert.equal(supplied.json, true); assert.equal(err, ''); assert.equal(JSON.parse(out).schema, 'pdd.cost-report.v1');
  out = ''; supplied = null;
  dependencies.stdin = { async *[Symbol.asyncIterator]() { yield '{"id":"suite-1","suiteMinutes":2}'; } };
  dependencies.workflowRunner = { runCosts: async input => { supplied = input; return { exitCode: 0, message: '{"suiteMinutes":2}' }; } };
  assert.equal(await runPdd(['workflow','cost','17','--input','-'], dependencies), 0); assert.equal(supplied.input.suiteMinutes, 2);
});

// Native process recipe: real CLI, Git and local files; no live services.
test('real CLI process records measured costs and renders local machine JSON', async t => {
  const f = await fixture(t); f.ports.skipMetricsDelivery = true; assert.equal((await f.run()).exitCode, 0);
  const bin = new URL('../bin/pdd.mjs', import.meta.url).pathname;
  const denied = join(f.base, 'denied-programs'); fs.mkdirSync(denied);
  const marker = join(f.base, 'external-call');
  for (const program of ['gh', 'herdr', 'systemctl']) {
    fs.writeFileSync(join(denied, program), '#!/bin/sh\nprintf called >> "' + marker + '"\nexit 19\n', { mode: 0o700 });
  }
  const options = { cwd: f.source, encoding: 'utf8', env: { HOME: f.ports.env.HOME, PATH: denied + ':' + process.env.PATH }, stdio: ['pipe','pipe','pipe'] };
  const row = JSON.parse(execFileSync(process.execPath, [bin, 'workflow','cost','17','--input','-'], { ...options, input: JSON.stringify({ id: 'real-suite', suiteMinutes: 1.25 }) }));
  assert.equal(row.suiteMinutes, 1.25);
  const report = JSON.parse(execFileSync(process.execPath, [bin, 'autopilot','status','--json'], options));
  assert.equal(report.schema, 'pdd.cost-report.v1'); assert.equal(report.runs[0].suiteMinutes, 1.25);
  assert.equal(fs.existsSync(marker), false);
});

test('native GitHub attribution selects the exact run worktree and excludes repository-wide calls', async t => {
  const f = await fixture(t); f.ports.skipMetricsDelivery = true; assert.equal((await f.run()).exitCode, 0);
  const run = f.record(), count = nativeGithubCounter(f.ports.execFile, { env: f.ports.env, now: () => f.clock });
  await count('gh', ['repo', 'view', '--json', 'nameWithOwner'], { cwd: run.root });
  await count('gh', ['repo', 'view', '--json', 'nameWithOwner'], { cwd: f.source });
  const saved = updateRun(run.runDir, latest => latest, f.ports);
  assert.equal(saved.cost.githubCalls, 1);
});

test('workflow prove measures both native phase wall times without saving command text in cost rows', async () => {
  const { proveRun } = await import('../src/workflow-prove.mjs');
  const values = [0, 120000, 120000, 150000], measurements = [];
  const result = await proveRun({ ref: '17', cwd: '/synthetic', test: 'PRIVATE_COMMAND', expect: 'missing-case' }, {
    readRun: async () => ({ run: { runId: 'attempt', root: '/synthetic', runDir: '/synthetic/run', baseBranch: 'main' } }),
    snapshot: async () => ({ snapshot: { baseSha: 'a'.repeat(40), headSha: 'b'.repeat(40), baseAvailable: true, headAvailable: true, files: [] } }),
    createWorktree: async ({ phase }) => ({ worktree: `/synthetic/${phase}` }),
    runProcess: async () => ({ result: { exitCode: 0, signal: '', timedOut: false, outputLimited: false, stdout: '', stderr: '', error: '', setupError: '' } }),
    cleanup: async () => ({}), saveProof: async () => ({}), suiteNow: () => values.shift(), recordSuiteCost: async row => measurements.push(row)
  });
  assert.equal(result.exitCode, 1); // An old-code proof with a passing base is not proof.
  assert.deepEqual(measurements.map(row => row.suiteMinutes), [2, 0.5]);
  assert.equal(new Set(measurements.map(row => row.id)).size, 2);
  assert.ok(!JSON.stringify(measurements).includes('PRIVATE_COMMAND'));
});

test('manual approvals recorded by an agent count through native said/chat evidence, including saved history', t => {
  const { run, ports } = world(t);
  run.decisions = ['said','chat','terminal'].map((route, index) => ({
    gateId: `gate-${index}`, gateAt: at - 60000, stage: 'code', decision: 'approve', via: route, at,
    evidence: { id: `approval-${index}`, route, actor: { kind: route === 'terminal' ? 'terminal' : 'agent', id: 'synthetic-recorder' }, at, words: 'PRIVATE_APPROVAL', prompts: [] }
  }));
  run.cost = captureCosts(null, run, ports);
  assert.equal(run.cost.person.approvals, 3); assert.equal(run.cost.person.waitingMinutes, 3);
  run.cost = captureCosts(run, run, ports);
  assert.equal(run.cost.person.approvals, 3); assert.equal(run.cost.person.waitingMinutes, 3);
  assert.equal(run.cost.person.activeMinutes, null); assert.ok(!JSON.stringify(run.cost).includes('PRIVATE_APPROVAL'));
});

test('report token totals keep unknown distinct from a real measured zero', t => {
  const { root, run, ports } = world(t);
  run.cost = captureCosts(null, run, ports);
  assert.equal(costReport([run], at).day.totals.totalTokens, null);
  const file = claudeFile(run, root);
  fs.writeFileSync(file, JSON.stringify({ type: 'assistant', sessionId: id, message: { id: 'zero', usage: { input_tokens: 0, output_tokens: 0 } } }) + '\n');
  run.cost = captureCosts(run, run, ports);
  assert.equal(costReport([run], at).day.totals.totalTokens, 0);
});

test('archived attempts retain their own costs when their old runDir now belongs to a new attempt', async t => {
  const f = await fixture(t); f.ports.skipMetricsDelivery = true; assert.equal((await f.run()).exitCode, 0);
  const old = updateRun(f.record().runDir, run => applyCostMeasurement(run, { id: 'old-suite', suiteMinutes: 2, outcome: 'closed' }, f.clock), f.ports);
  const archivedDir = `${old.runDir}-cancelled-aabbcc`; fs.renameSync(old.runDir, archivedDir);
  fs.mkdirSync(old.runDir);
  const current = { ...old, runId: 'new-attempt', startedAt: f.clock + 1000, state: 'running', cost: undefined };
  applyCostMeasurement(current, { id: 'new-suite', suiteMinutes: 5, outcome: 'merged' }, f.clock + 1000);
  fs.writeFileSync(join(current.runDir, 'status.json'), JSON.stringify(current));
  f.tick(2000);
  const reply = await runAutopilotLauncher({ command: 'status', json: true, cwd: f.source, env: f.ports.env }, f.ports);
  assert.equal(reply.exitCode, 0); const report = JSON.parse(reply.message);
  assert.equal(report.runs.length, 2);
  assert.deepEqual(report.runs.map(row => row.suiteMinutes).sort((a,b) => a-b), [2,5]);
  assert.equal(report.day.totals.suiteMinutes, 7); assert.equal(report.day.mergedIssues, 1); assert.equal(report.day.p50.suiteMinutes, 7);
  assert.equal(JSON.parse(fs.readFileSync(join(archivedDir, 'status.json'))).cost.suiteMinutes, 2);
});

test('workflow status fetches CI duration once when its normal PR observation sees closure', async t => {
  const f = await fixture(t); f.ports.skipMetricsDelivery = true; assert.equal((await f.run()).exitCode, 0);
  const run = f.record(), headSha = 'c'.repeat(40);
  updateRun(run.runDir, latest => { latest.pr = [{ number: 23, url: 'https://github.com/example/project/pull/23', stage: latest.areas.at(-1).name, state: 'open' }]; return latest; }, f.ports);
  const exec = f.ports.execFile; let durationCalls = 0;
  f.ports.readPrStatus = async () => ({ state: 'merged', ci: 'passing', headSha });
  f.ports.execFile = async (program, args, options) => {
    if (program === 'gh' && args[0] === 'api' && args[1].includes('/actions/runs?')) {
      durationCalls++; return { stdout: JSON.stringify({ total_count: 1, workflow_runs: [{ head_sha: headSha, pull_requests: [{ number: 23 }], status: 'completed', run_started_at: new Date(f.clock - 120000).toISOString(), updated_at: new Date(f.clock).toISOString() }] }) };
    }
    return exec(program, args, options);
  };
  for (let i = 0; i < 2; i++) assert.equal((await runner.runStatus({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  assert.equal(durationCalls, 1); assert.equal(f.record().cost.ciMinutes, 2); assert.equal(f.record().cost.outcome, 'merged');
});

test('CI branch read includes earlier PR heads, excludes other PRs, and reports complete bounded data', async t => {
  const { run, ports } = world(t);
  run.pr = [{ number: 23, state: 'merged', branch: 'feature/issue-17', headSha: 'b'.repeat(40) }];
  ports.execFile = async (_program, args) => {
    assert.equal(args[1], 'repos/acme/project/actions/runs?branch=feature%2Fissue-17&per_page=100');
    const workflow = (sha, number) => ({ head_sha: sha.repeat(40), head_branch: 'feature/issue-17', pull_requests: [{ number }], status: 'completed', run_started_at: new Date(at).toISOString(), updated_at: new Date(at + 60000).toISOString() });
    return { stdout: JSON.stringify({ total_count: 3, workflow_runs: [workflow('a',23), workflow('b',23), workflow('c',99)] }) };
  };
  await captureClosedCi(run, ports); run.cost = captureCosts(null, run, ports);
  assert.equal(run.cost.ciMinutes, 2); assert.ok(!run.cost.coverage.includes('ci-unavailable'));
});
