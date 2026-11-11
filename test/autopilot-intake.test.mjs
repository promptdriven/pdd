import test from 'node:test';
import assert from 'node:assert/strict';
import { writeFileSync, readFileSync, existsSync, mkdirSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { coreWorld } from './helpers/core-world.mjs';
import { nativeFacts, issueVersion, personComments, readCard, readIntake, intakeText, intakeMode, intakeFolders, wouldPick } from '../src/autopilot-intake.mjs';

const intakeJobs = w => w.started.filter(job => job.role === 'intake');
const workJobs = w => w.started.filter(job => job.role !== 'intake').map(job => `${job.issue}:${job.role}`);
const writes = w => w.github.calls.filter(call => call.method !== 'GET').map(call => `${call.method} ${call.endpoint}`);
const card = (w, n, result) => {
  const job = [...intakeJobs(w)].reverse().find(j => j.issue === n);
  w.alive.delete(job.pid);
  if (result !== undefined) writeFileSync(job.result, JSON.stringify(result));
  writeFileSync(job.exit, JSON.stringify({ code: 0, signal: null, at: w.now() }));
  return job;
};
const ready = { class: 'ready', reason: 'Clear and small.', confidence: 0.9, canonical: null, suggested_links: [], question: null, area_hint: ['src/a.mjs'], model: 'gpt-test' };
async function shadowWorld(t, settings = { runs: 1 }) {
  const w = await coreWorld(t, { settings });
  w.settings.intake = 'shadow';
  return w;
}

test('autopilot-intake-shadow: native facts hold, wait, track and park with no AI call', () => {
  assert.deepEqual(nativeFacts({ assignees: [{ login: 'ada' }] }), { kind: 'held', reason: 'assigned to @ada' });
  assert.equal(nativeFacts({ issue_dependencies_summary: { blocked_by: 1, total_blocked_by: 1 } }).kind, 'waiting');
  assert.equal(nativeFacts({ sub_issues_summary: { total: 3, completed: 1 } }).kind, 'tracking');
  assert.equal(nativeFacts({ sub_issues_summary: { total: 2, completed: 2 } }), null);
  for (const name of ['pdd:stuck', 'pdd:needs-decision', 'pdd:would-merge']) assert.equal(nativeFacts({ labels: [{ name }] }).kind, 'parked');
  assert.equal(nativeFacts({ labels: ['pdd:working'] }).kind, 'working');
  assert.equal(nativeFacts({ title: 'Blocked by #4', body: 'Decide later. Blocked by #4.' }), null, 'text patterns are never native facts');
  assert.equal(intakeMode('shadow'), 'shadow'); assert.equal(intakeMode('gate'), 'off'); assert.equal(intakeMode(undefined), 'off');
});

test('autopilot-intake-shadow: the version changes with what a person can change, and machine comments are left out', () => {
  const row = { title: 'A', body: 'B', labels: [{ name: 'x' }], assignees: [], comments: 0 };
  assert.equal(issueVersion(row), issueVersion({ ...row, labels: ['x'] }));
  for (const change of [{ title: 'A2' }, { body: 'B2' }, { labels: ['x', 'y'] }, { assignees: ['ada'] }, { comments: 1 }, { issue_dependencies_summary: { blocked_by: 1 } }])
    assert.notEqual(issueVersion({ ...row, ...change }), issueVersion(row), JSON.stringify(change));
  const kept = personComments([{ body: 'Please also keep the old flag.', user: { login: 'ada' }, created_at: '2026-11-10T00:00:00Z' },
    { body: 'Claim.\n<!-- pdd:autopilot-core:claim -->', user: { login: 'ada' } }, { body: '```json\n{"a":1}\n```', user: { login: 'ada' } },
    { body: 'ok', user: { login: 'renovate[bot]' } }, { body: 'beep', user: { login: 'x', type: 'Bot' } }, { body: '   ', user: { login: 'ada' } }]);
  assert.deepEqual(kept, [{ author: 'ada', at: '2026-11-10T00:00:00Z', body: 'Please also keep the old flag.' }]);
});

test('autopilot-intake-shadow: a card result outside the allowed shape is a failed card, never a guess', () => {
  assert.equal(readCard({ class: 'maybe', reason: 'x' }), null);
  assert.equal(readCard({ class: 'ready', reason: '  ' }), null);
  assert.equal(readCard('invalid'), null);
  const c = readCard({ class: 'duplicate', reason: 'Same bug as #4.', confidence: 3, canonical: 4, suggested_links: [{ to: 4, type: 'duplicate-of', reason: 'same' }, { to: -1, type: 'blocked-by' }, { to: 5, type: 'related' }],
    question: 'ignored', area_hint: ['a', 'b', 'c', 'd', 'e', 'f', 'g'], model: 'm1' });
  assert.deepEqual({ ...c, area_hint: c.area_hint.length }, { class: 'duplicate', start: false, reason: 'Same bug as #4.', confidence: null, canonical: 4,
    suggested_links: [{ to: 4, type: 'duplicate-of', reason: 'same' }], question: null, area_hint: 6, reported_model: 'm1' });
  assert.equal(readCard({ class: 'improve', reason: 'Needs criteria.' }).start, true);
});

test('autopilot-intake-shadow: one card job per issue version, at most 2 per tick, with native reasons and no AI call for held, waiting and parked issues', async t => {
  const w = await shadowWorld(t);
  // Outside authors: the core starts none of them (not trusted), so the cards are alone here.
  for (const n of [11, 13, 15, 16]) w.issue(n, { user: 'eve' });
  w.issue(12, { assignees: ['ada'], user: 'eve' }); w.issue(14, { labels: ['pdd:needs-decision'], user: 'eve' });
  w.github.link(13, 11);
  await w.tick();
  assert.deepEqual(intakeJobs(w).map(j => j.issue), [11, 15], 'oldest first, at most 2 per tick, none for #12 (held), #13 (waiting), #14 (parked)');
  const job = intakeJobs(w)[0];
  assert.equal(job.command, 'codex'); assert.equal(job.cwd, w.cwd);
  assert.match(job.input, /Issue \(JSON\)/); assert.match(job.input, /Make part 11 work\./); assert.match(job.input, /#16 Issue 16/, 'the titles of the other open issues');
  assert.match(job.input, /do not use the network/);
  await w.tick();
  assert.equal(intakeJobs(w).length, 2, 'at most 2 card jobs run at once');
  card(w, 11, ready); card(w, 15, { ...ready, class: 'person', reason: 'Needs a product choice.', question: 'Which unit?' });
  await w.tick();
  assert.deepEqual(intakeJobs(w).map(j => j.issue), [11, 15, 16], 'a free slot takes the next issue');
  assert.equal(existsSync(job.result) || existsSync(job.exit) || existsSync(job.log), false, 'a finished card job leaves no job files');
  const report = readIntake({ root: w.root, now: w.now() });
  const byIssue = Object.fromEntries(report.cards.map(c => [c.issue, c]));
  assert.equal(byIssue[11].card.class, 'ready'); assert.deepEqual(byIssue[11].agent, { kind: 'codex', model: null }); assert.equal(byIssue[11].card.reported_model, 'gpt-test');
  assert.equal(byIssue[15].card.question, 'Which unit?');
  assert.deepEqual([byIssue[12].native.kind, byIssue[13].native.kind, byIssue[14].native.kind], ['held', 'waiting', 'parked']);
  assert.deepEqual(report.running, [16]);
  assert.ok(report.diff.some(r => r.kind === 'card' && r.issue === 11 && r.from === null && r.to === 'ready'));
  assert.ok(report.diff.some(r => r.kind === 'card' && r.issue === 13 && r.to === 'native:waiting'));
  // The same version gets no second card; a new person comment makes a new version and a new card job.
  card(w, 16, ready); await w.tick();
  assert.equal(intakeJobs(w).filter(j => j.issue === 11).length, 1);
  w.github.comment(11, 'Also support the old flag.', 'ada');
  await w.tick();
  const again = [...intakeJobs(w)].reverse().find(j => j.issue === 11);
  assert.notEqual(again, intakeJobs(w)[0]); assert.match(again.input, /Also support the old flag\./);
  const text = intakeText(readIntake({ root: w.root, now: w.now() }));
  assert.match(text, /^Intake cards \(shadow; they never change what starts\): 6; running: #11/);
  assert.match(text, /#15 person 0\.9: Needs a product choice\. \[codex, says gpt-test\]/);
  assert.match(text, /#12 held \(native\): assigned to @ada/);
});

test('autopilot-intake-shadow: the core starts the same issues and makes the same GitHub writes with intake shadow as with intake off', async t => {
  const run = async shadow => {
    const w = await coreWorld(t, { settings: { runs: 1 } });
    if (shadow) w.settings.intake = 'shadow';
    w.issue(21); w.issue(22); w.issue(23);
    await w.tick();
    if (shadow) { for (const j of intakeJobs(w)) card(w, j.issue, { ...ready, class: j.issue === 21 ? 'person' : 'ready', reason: 'x' }); }
    w.build(21, { body: 'Fixes #21.\n\nRuntime: PASS' });
    await w.tick(); w.advance(60000); await w.tick();
    return { w, starts: workJobs(w), writes: writes(w) };
  };
  const off = await run(false), on = await run(true);
  assert.deepEqual(on.starts, off.starts, 'a "person" card for #21 does not stop its start');
  assert.deepEqual(on.writes, off.writes, 'the intake pass writes nothing to GitHub');
  assert.equal(intakeJobs(off.w).length, 0, 'intake off starts no card job');
  assert.equal(existsSync(intakeFolders(off.w.root).base), false, 'intake off writes no intake files');
  assert.ok(intakeJobs(on.w).length > 0);
  const started = readIntake({ root: on.w.root, now: on.w.now() }).diff.filter(r => r.kind === 'started');
  assert.deepEqual(started.map(r => r.issue), [21], 'the change file records the issue that the core really started');
});

test('autopilot-intake-shadow: a failed card waits 6 hours, a timeout is stopped, and a broken pass never stops the tick', async t => {
  const w = await shadowWorld(t, { runs: 1 });
  w.issue(31, { user: 'eve' }); w.issue(32, { user: 'eve' });
  await w.tick();
  card(w, 31, { class: 'maybe', reason: 'unsure' }); card(w, 32);
  await w.tick();
  let report = readIntake({ root: w.root, now: w.now() });
  assert.deepEqual(report.cards.map(c => [c.issue, Boolean(c.error)]), [[31, true], [32, true]]);
  assert.ok(report.diff.some(r => r.issue === 31 && r.to === 'error'));
  const failed = intakeJobs(w).find(j => j.issue === 31);
  assert.equal(existsSync(failed.log), true, 'a failed card keeps its job log'); assert.equal(existsSync(failed.result), false);
  const count = () => intakeJobs(w).length;
  const before = count();
  w.advance(60 * 60000); await w.tick();
  assert.equal(count(), before, 'no new job within 6 hours for the same version');
  w.advance(6 * 60 * 60000); await w.tick();
  assert.equal(count(), before + 2, 'a new try after 6 hours');
  w.advance(21 * 60000); await w.tick();
  assert.ok(w.stopped.some(id => id.startsWith('intake-31-')), 'a card job that runs longer than 20 minutes is stopped');
  report = readIntake({ root: w.root, now: w.now() });
  assert.match(report.cards.find(c => c.issue === 31).error, /ran out of time/);
  // A pass that throws is one warning; the tick goes on and its message is the core's.
  const warnings = [];
  rmSync(join(w.root, 'intake', 'cards'), { recursive: true }); writeFileSync(join(w.root, 'intake', 'cards'), 'not a folder'); // the cards path is now unusable
  const r = await w.tick({ warn: text => warnings.push(text) }).catch(error => ({ crashed: error }));
  assert.equal(r.crashed, undefined); assert.equal(r.exitCode, 0); assert.match(r.message, /^Autopilot core: /);
  assert.ok(warnings.some(text => /Autopilot intake/.test(text)), warnings.join('\n'));
});

test('autopilot-intake-shadow: would pick puts issues that unblock others first, then the oldest; only ready cards of the current version', () => {
  const rows = [{ number: 3, created_at: '2026-11-01T00:00:00Z', title: 'c' }, { number: 1, created_at: '2026-11-02T00:00:00Z', title: 'a' },
    { number: 2, created_at: '2026-11-03T00:00:00Z', title: 'b', issue_dependencies_summary: { blocked_by: 0, total_blocking: 2 } }, { number: 4, created_at: '2026-10-01T00:00:00Z', title: 'd' }];
  const cards = new Map(rows.map(row => [row.number, { issue: row.number, version: issueVersion(row), card: { class: row.number === 4 ? 'improve' : 'ready' } }]));
  cards.set(1, { ...cards.get(1), version: 'old' });
  assert.deepEqual(wouldPick(rows, cards), [2, 3]);
});

test('autopilot-intake-shadow: start --intake saves the machine mode, the tick uses it, and pdd autopilot intake prints the cards', async t => {
  const { runAutopilotLauncher, tickAutopilot } = await import('../src/autopilot-launcher.mjs');
  const { spawnSync } = await import('node:child_process');
  const w = await coreWorld(t);
  writeFileSync(join(w.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [], testCommand: 'npm test' } }));
  w.issue(41);
  const cwd = w.git(w.cwd, 'rev-parse', '--show-toplevel'), stateRoot = join(w.dir, 'state');
  const stateFile = join(stateRoot, `${createHash('sha256').update(cwd).digest('hex').slice(0, 20)}.json`);
  mkdirSync(stateRoot, { recursive: true });
  const saved = { enabled: true, cwd, repo: 'acme/widgets', defaultBranch: 'main', coordinatorId: 'coord-a', machine: 'machine-a', engine: 'core',
    agent: { id: 'codex', kind: 'codex', command: 'codex' }, packageRoot: join(w.dir, 'pkg') };
  writeFileSync(stateFile, JSON.stringify(saved));
  const ports = { stateRoot, now: w.now, env: { HOME: process.env.HOME, PATH: process.env.PATH }, timer: async () => true, warn: () => {},
    run: async (command, args, options = {}) => {
      if (command === 'gh') return w.gh(args, options);
      if (command !== 'git') assert.fail(`unexpected program ${command}`);
      const r = spawnSync('git', args, { cwd: options.cwd ?? cwd, encoding: 'utf8' }); return { code: r.status, stdout: r.stdout, stderr: r.stderr };
    },
    corePorts: { jobs: w.jobs, checkBase: async () => ({ exitCode: 0, message: 'ok' }), agentReady: async () => true, reportRoot: w.reportRoot } };
  await tickAutopilot(stateFile, ports);
  assert.equal(intakeJobs(w).length, 0, 'no saved intake mode: off');
  writeFileSync(stateFile, JSON.stringify({ ...JSON.parse(readFileSync(stateFile, 'utf8')), intake: 'shadow' }));
  w.issue(42, { user: 'eve' });
  await tickAutopilot(stateFile, ports);
  assert.deepEqual(intakeJobs(w).map(j => j.issue), [42], '#41 holds pdd:working (a running job); #42 gets a card job');
  card(w, 42, { ...ready, reason: 'Clear: one value.' });
  await tickAutopilot(stateFile, ports);
  const shown = await runAutopilotLauncher({ command: 'intake', cwd, packageRoot: join(w.dir, 'pkg'), env: ports.env, issues: [] }, ports);
  assert.equal(shown.exitCode, 0, shown.message);
  assert.match(shown.message, /^Intake: shadow on this machine\./); assert.match(shown.message, /#42 ready 0\.9: Clear: one value\./); assert.match(shown.message, /#41 working \(native\)/);
  const json = JSON.parse((await runAutopilotLauncher({ command: 'intake', cwd, packageRoot: join(w.dir, 'pkg'), env: ports.env, issues: [], json: true }, ports)).message);
  assert.equal(json.intake, 'shadow'); assert.equal(json.repository, 'acme/widgets'); assert.ok(json.cards.some(c => c.issue === 42 && c.card.class === 'ready'));
  assert.ok(json.diff.some(r => r.kind === 'would-pick' && r.issues.includes(42)));
  const bad = await runAutopilotLauncher({ command: 'start', cwd, packageRoot: join(w.dir, 'pkg'), env: ports.env, issues: [], intake: 'gate' }, ports);
  assert.equal(bad.exitCode, 2); assert.equal(bad.message, 'Use --intake off or --intake shadow.');
});
