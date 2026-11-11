// Generated from prompts/test/autopilot-factory.prompt.md (sha256: 61d3de537d4efddcdaf86f230341acde843c248eb8f33933e44d71eee27dd249).
// The core factory: each user path of Autopilot end to end through the real launcher (start, tick, status, add,
// stop) and the real core tick, with real Git (a bare origin and clones), a fake GitHub and scripted agent jobs.
import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { coreWorld } from './helpers/core-world.mjs';
import { runAutopilotLauncher, tickAutopilot } from '../src/autopilot-launcher.mjs';

const MIN = 60 * 1000;
const agent = async () => ({ id: 'codex', kind: 'codex', command: 'codex' });
const endComments = (w, n) => w.comments(n).filter(body => body.includes('<!-- pdd:autopilot-core:end:'));

// A person's repository and this machine: pdd.json in the checkout, a package root, a state folder and the timer.
async function factory(t, autopilot = {}) {
  const w = await coreWorld(t);
  writeFileSync(join(w.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [], testCommand: 'npm test', report: 'draft', ...autopilot } }));
  mkdirSync(join(w.dir, 'pkg'), { recursive: true }); writeFileSync(join(w.dir, 'pkg', 'package.json'), JSON.stringify({ version: '0.1.29' }));
  const home = join(w.dir, 'home'); mkdirSync(home, { recursive: true });
  const cwd = w.git(w.cwd, 'rev-parse', '--show-toplevel'), stateRoot = join(w.dir, 'state');
  const stateFile = join(stateRoot, `${createHash('sha256').update(cwd).digest('hex').slice(0, 20)}.json`);
  const f = { w, cwd, stateFile, timer: [], programs: [], active: false };
  const run = async (command, args, options = {}) => {
    f.programs.push(command);
    if (command === 'gh' && args[0] === 'repo') return { code: 0, stdout: JSON.stringify({ nameWithOwner: 'acme/widgets', defaultBranchRef: { name: 'main' } }), stderr: '' };
    if (command === 'gh' && args[0] === 'auth') return { code: 0, stdout: '', stderr: '' };
    // The label itself (pdd autopilot add creates it when it is missing).
    if (command === 'gh' && args.includes('repos/acme/widgets/labels')) return { code: 0, stdout: '{}', stderr: '' };
    // pdd autopilot add sends the label as a form field (-f labels[]=NAME).
    const labelled = command === 'gh' && /^repos\/acme\/widgets\/issues\/(\d+)\/labels$/.exec(args.find(arg => String(arg).startsWith('repos/')) ?? '');
    if (labelled && args.includes('-f')) { w.github.label(Number(labelled[1]), args[args.indexOf('-f') + 1].replace(/^labels\[\]=/, '')); return { code: 0, stdout: '[]', stderr: '' }; }
    if (command === 'gh') return w.gh(args, options);
    if (command === 'git') { const r = spawnSync('git', args, { cwd: options.cwd ?? cwd, encoding: 'utf8' }); return { code: r.status, stdout: r.stdout, stderr: r.stderr }; }
    if (['herdr', 'launchctl', 'systemctl'].includes(command)) assert.fail(`the core never calls ${command} here`);
    return { code: 0, stdout: '', stderr: '' };
  };
  f.ports = { stateRoot, now: w.now, env: { HOME: home, PATH: process.env.PATH }, warn: () => {}, notice: () => {}, run, selectAgent: agent,
    timer: async action => { if (action === 'status') return f.active; f.timer.push(action); f.active = action === 'start'; return f.active; },
    doctorPorts: { run: async (command, args, options) => command === 'git' ? run(command, args, options) : { code: 0, stdout: '', stderr: '' }, selectAgent: agent },
    movePorts: { processes: async () => '', releaseSlots: async () => false },
    corePorts: { jobs: w.jobs, checkBase: async () => ({ exitCode: 0, message: 'Base check ok.' }), agentReady: async () => true, runtimeEvidence: w.ports().runtimeEvidence } };
  const call = (command, extra = {}) => runAutopilotLauncher({ command, cwd, packageRoot: join(w.dir, 'pkg'), env: f.ports.env, issues: [], ...extra }, f.ports);
  f.start = extra => call('start', extra);
  f.status = () => call('status');
  f.stop = () => call('stop');
  f.add = (...issues) => call('add', { issues: issues.map(String) });
  f.tick = async () => { w.advance(10 * MIN); return tickAutopilot(stateFile, f.ports); };
  f.state = () => JSON.parse(readFileSync(stateFile, 'utf8'));
  return f;
}

test('core factory 1: start, opt-in label, intake, build, PR, review, suite and one merge', async t => {
  const f = await factory(t, { label: 'pdd:autopilot' }), { w } = f;
  w.issue(17, { title: 'Use value two', body: 'The value must be 2.', labels: ['pdd:autopilot'] });
  w.issue(18, { title: 'Not chosen', body: 'No label.' });
  const started = await f.start();
  assert.equal(started.exitCode, 0, started.message);
  assert.match(started.message, /Mode auto · issues with pdd:autopilot · agent codex/);
  assert.deepEqual(f.timer, ['start']);
  assert.ok(w.job(17, 'build'), 'the first tick of start claims the labeled issue and starts its build');
  assert.equal(w.job(18), undefined, 'an issue without the label is never taken');
  assert.deepEqual(w.labels(17), ['pdd:autopilot', 'pdd:working']);
  const { pr, head } = w.build(17);
  await f.tick();
  assert.equal(w.job(17, 'review').head, head); assert.equal(w.job(17, 'suite').head, head);
  w.review(17, 'PASS'); w.suite(17, 0);
  const merged = await f.tick();
  assert.match(merged.message, /1 merged/);
  assert.deepEqual(w.github.merges, [pr.number]);
  assert.equal(w.github.issues.get(17).state, 'closed');
  const status = await f.status();
  assert.match(status.message, /Autopilot enabled; timer active/); assert.match(status.message, /#17 merged/);
  assert.ok(!f.programs.includes('herdr'));
});

test('core factory 2: a start without a label asks for one; add marks an issue; a labeled start takes only it', async t => {
  const f = await factory(t), { w } = f;
  w.issue(17); w.issue(18);
  const asked = await f.start();
  assert.equal(asked.exitCode, 1); assert.match(asked.message, /opt-in label.*Nothing was started or claimed\.$/);
  assert.deepEqual(f.timer, []); assert.equal(existsSync(f.stateFile), false);
  assert.deepEqual(w.labels(17), []); assert.deepEqual(w.labels(18), []);
  const added = await f.add(18);
  assert.equal(added.exitCode, 0, added.message); assert.deepEqual(w.labels(18), ['pdd:autopilot']);
  const started = await f.start({ label: 'pdd:autopilot' });
  assert.equal(started.exitCode, 0, started.message);
  assert.ok(w.job(18, 'build') && !w.job(17), 'only the marked issue starts');
  assert.equal(f.state().label, 'pdd:autopilot');
});

test('core factory 3: a red full suite gets one repair on the same branch, then the merge', async t => {
  const f = await factory(t, { label: 'pdd:autopilot' }), { w } = f;
  w.issue(17, { labels: ['pdd:autopilot'] });
  assert.equal((await f.start()).exitCode, 0);
  const first = w.build(17); await f.tick();
  w.review(17, 'PASS'); w.suite(17, 1); await f.tick();
  const repair = w.job(17, 'repair');
  assert.ok(repair, 'a repair job starts'); assert.match(repair.input, /full test suite/i);
  assert.equal(repair.branch, w.job(17, 'build').branch);
  const second = w.build(17, { role: 'repair' }); await f.tick();
  assert.equal(w.job(17, 'review').head, second.head);
  w.review(17, 'PASS'); w.suite(17, 0); await f.tick();
  assert.deepEqual(w.github.merges, [first.pr.number]);
});

test('core factory 4: a review FAIL after the last repair ends the job with one END comment and pdd:stuck', async t => {
  const f = await factory(t, { label: 'pdd:autopilot', maxRepairs: 1 }), { w } = f;
  w.issue(17, { labels: ['pdd:autopilot'] });
  assert.equal((await f.start()).exitCode, 0);
  w.build(17); await f.tick();
  w.review(17, 'FAIL', ['Test does not cover the issue case']); w.suite(17, 0); await f.tick();
  assert.match(w.job(17, 'repair').input, /Test does not cover the issue case/);
  w.build(17, { role: 'repair' }); await f.tick();
  w.review(17, 'FAIL', ['Still missing']); w.suite(17, 0); await f.tick();
  assert.equal(w.github.merges.length, 0);
  const end = endComments(w, 17);
  assert.equal(end.length, 1); assert.match(end[0], /Still missing/);
  assert.ok(w.labels(17).includes('pdd:stuck')); assert.ok(!w.labels(17).includes('pdd:working'));
  assert.match((await f.status()).message, /#17 ended/);
});

test('core factory 5: needs a person: one question and pdd:needs-decision; the answer and the label removal start the next build', async t => {
  const f = await factory(t, { label: 'pdd:autopilot' }), { w } = f;
  w.issue(17, { labels: ['pdd:autopilot'] });
  assert.equal((await f.start()).exitCode, 0);
  w.finish(17, 'build', { result: { outcome: 'needs-person', kind: 'blocker', question: 'Should the total count hyphenated words as one word or two?' } });
  await f.tick();
  assert.match(w.comments(17).find(body => body.includes('<!-- pdd:autopilot-core:question:17:')), /> Should the total count hyphenated words as one word or two\?/);
  assert.ok(w.labels(17).includes('pdd:needs-decision')); assert.ok(!w.labels(17).includes('pdd:working'));
  w.github.comment(17, 'One word: "well-known" counts once.', 'acme');
  await f.tick();
  assert.equal(w.started.filter(job => job.issue === 17).length, 1, 'the label keeps the issue waiting');
  w.github.unlabel(17, 'pdd:needs-decision');
  await f.tick();
  const next = w.job(17, 'build');
  assert.match(next.input, /Question: Should the total count hyphenated words as one word or two\?/);
  assert.match(next.input, /acme: One word: "well-known" counts once\./);
  const { pr } = w.build(17); await f.tick(); w.review(17, 'PASS'); w.suite(17, 0); await f.tick();
  assert.deepEqual(w.github.merges, [pr.number]);
});

test('core factory 6: a conflict with the base starts a conflict update, not a repair; then the PR merges', async t => {
  const f = await factory(t, { label: 'pdd:autopilot' }), { w } = f;
  w.baseCommit('list.txt', 'alpha\nbeta\ngamma\n');
  w.issue(17, { labels: ['pdd:autopilot'] });
  assert.equal((await f.start()).exitCode, 0);
  const job = w.job(17, 'build');
  w.git(job.cwd, 'fetch', '-q', 'origin', 'main'); w.git(job.cwd, 'merge', '-q', 'origin/main');
  writeFileSync(join(job.cwd, 'list.txt'), 'alpha\nbeta from the PR\ngamma\n');
  const { pr } = w.build(17); await f.tick();
  w.review(17, 'PASS'); w.suite(17, 0);
  w.baseCommit('list.txt', 'alpha\nbeta from the base\ngamma\n');
  await f.tick(); await f.tick();
  const fix = w.job(17, 'conflict');
  assert.ok(fix, 'an agent conflict update starts'); assert.equal(w.job(17, 'repair'), undefined);
  assert.match(fix.input, /conflict/i);
  w.git(fix.cwd, 'fetch', '-q', 'origin', 'main');
  try { w.git(fix.cwd, 'merge', '-q', 'origin/main'); } catch { /* the conflict */ }
  writeFileSync(join(fix.cwd, 'list.txt'), 'alpha\nbeta from the PR\nbeta from the base\ngamma\n'); w.git(fix.cwd, 'add', '.'); w.git(fix.cwd, 'commit', '-qm', 'merge main');
  w.build(17, { role: 'conflict', write: false }); await f.tick();
  for (let i = 0; i < 4 && !w.github.merges.length; i++) {
    const review = w.job(17, 'review'); if (review && w.alive.has(review.pid)) w.review(17, 'PASS');
    const suite = w.job(17, 'suite'); if (suite && w.alive.has(suite.pid)) w.suite(17, 0);
    const head = JSON.parse(readFileSync(join(f.stateFile.replace(/\.json$/, '-core'), 'jobs', '17.json'), 'utf8')).head; w.github.setChecks(head);
    await f.tick();
  }
  assert.deepEqual(w.github.merges, [pr.number]);
});

test('core factory 7: stop disables the timer and every later tick; a person who removes pdd:working stops the job', async t => {
  const f = await factory(t, { label: 'pdd:autopilot' }), { w } = f;
  w.issue(17, { labels: ['pdd:autopilot'] }); w.issue(18, { labels: ['pdd:autopilot'] });
  assert.equal((await f.start()).exitCode, 0);
  assert.ok(w.job(17, 'build') && w.job(18, 'build'));
  // A person stops one issue: the local job stops and its slot is free; GitHub keeps the person's change.
  w.github.unlabel(17, 'pdd:working');
  await f.tick();
  assert.ok(w.stopped.includes(w.job(17, 'build').id), 'the job of #17 is stopped');
  assert.ok(!w.labels(17).includes('pdd:stuck'));
  const stopped = await f.stop();
  assert.equal(stopped.exitCode, 0); assert.match(stopped.message, /Autopilot stopped on this machine/);
  assert.equal(f.timer.at(-1), 'stop'); assert.equal(f.state().enabled, false);
  const before = w.started.length;
  w.issue(19, { labels: ['pdd:autopilot'] });
  assert.equal((await f.tick()).message, 'Autopilot stopped.');
  assert.equal(w.started.length, before, 'a stopped machine starts no job');
  assert.match((await f.status()).message, /^Autopilot disabled; timer inactive/);
});
