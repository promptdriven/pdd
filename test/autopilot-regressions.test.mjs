import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { regressionScan, runAutopilotRegressions } from '../src/autopilot-regressions.mjs';
import { runPdd } from '../src/pdd-cli.mjs';

const repo = 'sample/project', M = 'a'.repeat(40), P = 'b'.repeat(40), R = 'c'.repeat(40);
const mergedAt = '2026-11-01T10:00:00Z', later = '2026-11-02T12:00:00Z', now = Date.parse('2026-11-05T00:00:00Z');
const url = (type, id) => `https://github.com/${repo}/${type}/${id}`;
function fixture(t) {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-regressions-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const rows = [{ at: Date.parse(mergedAt), issue: 7, pr: 12, outcome: 'merged' }];
  const routes = new Map([
    ['pulls/12', { number: 12, title: 'Fix thing', merged_at: mergedAt, merge_commit_sha: M }],
    [`commits/${M}`, { sha: M, parents: [{ sha: P }] }],
    [`commits/${M}/check-runs?filter=all&per_page=100`, { check_runs: [] }],
    [`commits/${P}/check-runs?filter=all&per_page=100`, { check_runs: [] }],
    [`commits/${M}/statuses?per_page=100`, []], [`commits/${P}/statuses?per_page=100`, []],
    ['issues/12/timeline?per_page=100', []], ['issues/7/timeline?per_page=100', []],
    [`issues?state=all&since=${encodeURIComponent(new Date(mergedAt).toISOString())}&per_page=100`, []],
    ['pulls?state=all&per_page=100', []],
    [`commits?since=${encodeURIComponent(new Date(mergedAt).toISOString())}&per_page=100`, []],
  ]);
  const calls = [], links = new Map();
  const gh = async args => {
    calls.push(args);
    assert.deepEqual(args.slice(0, 4), ['api', '--include', '--method', 'GET']);
    const endpoint = args[4];
    assert.ok(endpoint.startsWith(`repos/${repo}/`), endpoint);
    const key = endpoint.slice(`repos/${repo}/`.length);
    assert.ok(routes.has(key), `Unexpected GitHub read: ${key}`);
    const value = routes.get(key);
    if (value instanceof Error) throw value;
    return { code: 0, stdout: `HTTP/2 200 OK\r\n${links.has(key) ? `Link: ${links.get(key)}\r\n` : ''}\r\n${JSON.stringify(value)}`, stderr: '' };
  };
  const save = () => fs.writeFileSync(join(root, 'history.jsonl'), rows.map(r => typeof r === 'string' ? r : JSON.stringify(r)).join('\n') + '\n');
  const ports = { root, repo, fs, gh, now: () => now };
  return { root, rows, routes, calls, links, ports, save, scan: () => { save(); return regressionScan(ports); } };
}
const check = (conclusion, when = later, id = 1, app = 3) => ({ id, name: 'suite', app: { id: app }, conclusion, status: 'completed', completed_at: when, html_url: url('actions/runs', id) });
const status = (state, at = later, id = 1) => ({ id, context: 'vm-suite', state, created_at: at, target_url: url('actions/runs', id) });
const newIssue = (body, extra = {}) => ({ number: 99, title: 'Broken behavior', body, created_at: later, html_url: url('issues', 99), ...extra });
function issues(f, rows) { f.routes.set([...f.routes.keys()].find(k => k.startsWith('issues?')), rows); }
function commits(f, rows) { f.routes.set([...f.routes.keys()].find(k => k.startsWith('commits?')), rows); }

test('empty and missing history are complete and do not call GitHub', async t => {
  const f = fixture(t), scan = await regressionScan(f.ports);
  assert.deepEqual(scan.counts, { ok: 0, suspect: 0, proven: 0 });
  assert.equal(scan.complete, true); assert.deepEqual(f.calls, []);
});
test('only distinct core merged PRs are scanned, with SHA and first parent resolved', async t => {
  const f = fixture(t); f.rows.push(f.rows[0], { outcome: 'ended', pr: 88 }, { outcome: 'merged', pr: 88, repo: 'other/project' });
  const r = await f.scan(); assert.equal(r.complete, true); assert.equal(r.merges.length, 1);
  assert.deepEqual(r.counts, { ok: 1, suspect: 0, proven: 0 });
  assert.equal(r.merges[0].mergeCommit, M); assert.equal(r.merges[0].parent, P);
});
test('cut history lines and missing PR identity are visible without hiding later merges', async t => {
  const f = fixture(t); f.rows.unshift('{cut', { outcome: 'merged', pr: null });
  const r = await f.scan(); assert.equal(r.complete, false); assert.equal(r.merges.length, 1); assert.equal(r.errors.length, 2);
});
test('same check red on merge and green on parent is proven', async t => {
  const f = fixture(t); f.routes.set(`commits/${M}/check-runs?filter=all&per_page=100`, { check_runs: [check('failure')] });
  f.routes.set(`commits/${P}/check-runs?filter=all&per_page=100`, { check_runs: [check('success', mergedAt, 2)] });
  const r = await f.scan(); assert.equal(r.merges[0].classification, 'proven');
  assert.equal(r.merges[0].signals[0].parentUrl, url('actions/runs', 2));
  assert.deepEqual(r.days, [{ date: '2026-11-02', proven: 1 }]);
});
test('vm-suite commit status participates in parent comparison', async t => {
  const f = fixture(t); f.routes.set(`commits/${M}/statuses?per_page=100`, [status('error')]);
  f.routes.set(`commits/${P}/statuses?per_page=100`, [status('success', mergedAt, 2)]);
  const r = await f.scan(); assert.equal(r.merges[0].classification, 'proven'); assert.match(r.merges[0].signals[0].detail, /vm-suite/);
});
test('inherited red, unrelated app and check/status name collisions are only suspect', async t => {
  const f = fixture(t); f.routes.set(`commits/${M}/check-runs?filter=all&per_page=100`, { check_runs: [check('failure')] });
  f.routes.set(`commits/${P}/check-runs?filter=all&per_page=100`, { check_runs: [check('failure', mergedAt), check('success', mergedAt, 2, 44)] });
  f.routes.set(`commits/${P}/statuses?per_page=100`, [{ ...status('success'), context: 'suite' }]);
  const r = await f.scan(); assert.equal(r.merges[0].classification, 'suspect'); assert.deepEqual(r.days, []);
});
test('latest successful reruns clear old failures independent of response order', async t => {
  const f = fixture(t); f.routes.set(`commits/${M}/check-runs?filter=all&per_page=100`, { check_runs: [check('success', later, 9), check('failure', mergedAt, 1)] });
  f.routes.set(`commits/${M}/statuses?per_page=100`, [status('error', mergedAt, 1), status('success', later, 9)]);
  assert.equal((await f.scan()).merges[0].classification, 'ok');
});
test('pending, neutral and skipped checks do not create regressions', async t => {
  const f = fixture(t); f.routes.set(`commits/${M}/check-runs?filter=all&per_page=100`, { check_runs: [check('neutral'), { ...check(null, later, 2, 4), status: 'in_progress' }, check('skipped', later, 3, 5)] });
  f.routes.set(`commits/${M}/statuses?per_page=100`, [status('pending')]);
  assert.equal((await f.scan()).merges[0].classification, 'ok');
});
test('an exact later revert commit is proven', async t => {
  const f = fixture(t); commits(f, [{ sha: R, html_url: url('commit', R), commit: { message: `Revert thing\n\nThis reverts commit ${M}.`, committer: { date: later } } }]);
  const r = await f.scan(); assert.equal(r.merges[0].classification, 'proven'); assert.equal(r.merges[0].signals[0].kind, 'revert');
});
test('merged revert links prove while proposed and title-only reverts stay suspect', async t => {
  const f = fixture(t);
  for (const [body, merged_at, expected] of [['Reverts sample/project#12', later, 'proven'], ['Reverts #12', null, 'suspect'], [`Reverts ${url('pull', 12)}`, later, 'proven'], ['', later, 'suspect']]) {
    f.routes.set('pulls?state=all&per_page=100', [{ number: 33, title: 'Revert "Fix thing"', body, created_at: later, merged_at, html_url: url('pull', 33) }]);
    assert.equal((await f.scan()).merges[0].classification, expected);
  }
});
test('exact regression attribution accepts same-repo references and URLs', async t => {
  const f = fixture(t);
  for (const ref of ['#12', 'sample/project#12', url('pull', 12)]) {
    issues(f, [newIssue(`Regressed by ${ref}`)]);
    const r = await f.scan(); assert.equal(r.merges[0].classification, 'proven', ref);
  }
});
test('generic links to the PR or issue remain suspect; unrelated identities are ignored', async t => {
  const f = fixture(t);
  for (const body of ['Related to #12', 'Duplicate of #7', url('issues', 7)]) {
    issues(f, [newIssue(body)]); assert.equal((await f.scan()).merges[0].classification, 'suspect', body);
  }
  for (const body of ['Regressed by #123', 'Regressed by other/project#12', 'Regressed by https://github.com/other/project/pull/12']) {
    issues(f, [newIssue(body)]); assert.equal((await f.scan()).merges[0].classification, 'ok', body);
  }
});
test('reopen and timeline cross-reference are suspect, including a source not in the issues listing', async t => {
  const f = fixture(t); f.routes.set('issues/7/timeline?per_page=100', [{ event: 'reopened', created_at: later, actor: { login: 'person' } }, { event: 'cross-referenced', created_at: later, source: { issue: newIssue('', { repository_url: `https://api.github.com/repos/${repo}` }) } }]);
  const r = await f.scan(); assert.equal(r.merges[0].classification, 'suspect'); assert.equal(r.merges[0].signals.length, 2);
});
test('engine-marked reopens are skipped without treating all same-account actions as machine actions', async t => {
  const f = fixture(t); f.routes.set('issues/7/timeline?per_page=100', [
    { event: 'reopened', created_at: later, actor: { login: 'same-user' } },
    { event: 'commented', created_at: later, user: { login: 'same-user' }, body: '<!-- pdd:audit-revert -->' },
    { event: 'reopened', created_at: '2026-11-03T12:00:00Z', actor: { login: 'same-user' } },
  ]);
  const r = await f.scan(); assert.equal(r.merges[0].signals.length, 1); assert.equal(r.merges[0].signals[0].at, '2026-11-03T12:00:00.000Z');
});
test('old issues, old reverts and future events do not blame the merge', async t => {
  const f = fixture(t); issues(f, [newIssue('Regressed by #12', { created_at: '2026-10-01T00:00:00Z' }), newIssue('Regressed by #12', { created_at: '2027-01-01T00:00:00Z' })]);
  f.routes.set('issues/7/timeline?per_page=100', [{ event: 'reopened', created_at: '2026-10-01T00:00:00Z' }]);
  commits(f, [{ sha: R, commit: { message: `This reverts commit ${M}.`, committer: { date: '2026-10-01T00:00:00Z' } } }]);
  assert.equal((await f.scan()).merges[0].classification, 'ok');
});
test('multiple signals and duplicate rows count once on the earliest proof date, consistently across scans', async t => {
  const f = fixture(t); f.rows.push(f.rows[0]); issues(f, [newIssue('Regressed by #12'), newIssue('Regressed by #12', { number: 100, created_at: '2026-11-03T12:00:00Z' })]);
  f.routes.set('pulls?state=all&per_page=100', [{ number: 33, body: 'Reverts #12', merged_at: '2026-11-04T12:00:00Z', created_at: later }]);
  const a = await f.scan(), b = await f.scan(); assert.deepEqual(a, b);
  assert.deepEqual(a.counts, { ok: 0, suspect: 0, proven: 1 }); assert.deepEqual(a.days, [{ date: '2026-11-02', proven: 1 }]);
});
test('pagination includes late CI and issue evidence', async t => {
  const f = fixture(t); const key = `commits/${M}/check-runs?filter=all&per_page=100`;
  f.links.set(key, `<https://api.github.com/repos/${repo}/${key}&page=2>; rel="next"`);
  f.routes.set(`${key}&page=2`, { check_runs: [check('failure')] });
  const issueKey = [...f.routes.keys()].find(k => k.startsWith('issues?'));
  f.links.set(issueKey, `<https://api.github.com/repos/${repo}/${issueKey}&page=2>; rel="next"`); f.routes.set(`${issueKey}&page=2`, [newIssue('Regressed by #12')]);
  const r = await f.scan(); assert.equal(r.complete, true); assert.equal(r.merges[0].classification, 'proven'); assert.equal(r.merges[0].signals.length, 2);
});
test('failed reads preserve other proof and report incompleteness without leaking raw errors', async t => {
  const f = fixture(t); f.routes.set(`commits/${M}/check-runs?filter=all&per_page=100`, Error('DO_NOT_PRINT_TOKEN'));
  issues(f, [newIssue('Regressed by #12')]); const r = await f.scan();
  assert.equal(r.complete, false); assert.equal(r.merges[0].classification, 'proven'); assert.equal(JSON.stringify(r).includes('DO_NOT_PRINT_TOKEN'), false);
});
test('malformed and unavailable commit observations never yield ok', async t => {
  const f = fixture(t); f.routes.set(`commits/${M}`, {});
  const r = await f.scan(); assert.equal(r.complete, false); assert.equal(r.merges[0].classification, 'suspect');
});
test('pagination refuses cycles and foreign next links without following them', async t => {
  const f = fixture(t), key = 'pulls?state=all&per_page=100';
  for (const link of [`https://api.github.com/repos/${repo}/${key}`, 'https://evil.example/repos/sample/project/pulls?page=2']) {
    f.links.set(key, `<${link}>; rel="next"`); const r = await f.scan(); assert.equal(r.complete, false);
  }
});
test('CLI dispatch forwards options, bypasses launcher and settings, and rejects bad syntax', async () => {
  let stdout = '', stderr = '', calls = 0;
  const deps = { cwd: '/fixture', env: { HOME: '/fake-home' }, stdout: { write: x => stdout += x }, stderr: { write: x => stderr += x },
    autopilotRegressions: { runAutopilotRegressions: async input => { calls++; assert.equal(input.json, true); assert.equal(input.file, 'report.json'); return { exitCode: 0, message: '{"safe":true}' }; } },
    autopilotLauncher: { runAutopilotLauncher: () => assert.fail('launcher must not load') }, autopilotGithub: { checkAutopilotSettings: () => assert.fail('no settings read') } };
  assert.equal(await runPdd(['autopilot', 'regressions', '--json', '--file', 'report.json'], deps), 0); assert.equal(stdout, '{"safe":true}\n'); assert.equal(stderr, '');
  for (const args of [['extra'], ['--file'], ['--unknown']]) assert.equal(await runPdd(['autopilot', 'regressions', ...args], deps), 2);
  assert.equal(calls, 1);
});
test('command resolves launcher hash/core folder read-only and exclusively creates report', async t => {
  const f = fixture(t), stateRoot = join(f.root, 'state'), cwd = join(f.root, 'checkout'); fs.mkdirSync(stateRoot); fs.mkdirSync(cwd);
  const id = createHash('sha256').update(cwd).digest('hex').slice(0, 20), core = join(stateRoot, `${id}-core`); fs.mkdirSync(core);
  fs.writeFileSync(join(stateRoot, `${id}.json`), JSON.stringify({ repo, cwd })); fs.writeFileSync(join(core, 'history.jsonl'), '');
  const run = async (file, args) => { assert.equal(file, 'git'); assert.deepEqual(args, ['rev-parse', '--show-toplevel']); return { code: 0, stdout: cwd }; };
  const result = await runAutopilotRegressions({ cwd, env: {}, json: true, file: 'report.json' }, { stateRoot, fs, run, gh: f.ports.gh, now: f.ports.now });
  assert.equal(result.exitCode, 0); assert.deepEqual(JSON.parse(result.message).counts, { ok: 0, suspect: 0, proven: 0 });
  assert.equal(fs.readFileSync(join(cwd, 'report.json'), 'utf8'), result.message + '\n');
  const again = await runAutopilotRegressions({ cwd, env: {}, file: 'report.json' }, { stateRoot, fs, run, gh: f.ports.gh, now: f.ports.now }); assert.equal(again.exitCode, 1);
  assert.deepEqual(fs.readdirSync(stateRoot).sort(), [`${id}-core`, `${id}.json`]); assert.deepEqual(fs.readdirSync(core), ['history.jsonl']);
});
test('command discovery errors are finite, and text explains suspect signals', async t => {
  const f = fixture(t); f.save(); issues(f, [newIssue('See #12')]);
  const r = await runAutopilotRegressions({ cwd: f.root, env: {} }, f.ports); assert.equal(r.exitCode, 0); assert.match(r.message, /1 suspect/); assert.match(r.message, /#12 suspect/);
  const bad = await runAutopilotRegressions({ cwd: f.root, env: {} }, { run: async () => { throw Error('DO_NOT_PRINT_TOKEN'); } }); assert.equal(bad.exitCode, 1); assert.ok(!bad.message.includes('DO_NOT_PRINT_TOKEN'));
});
