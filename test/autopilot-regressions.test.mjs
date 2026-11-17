import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { checkPostMergeRegressions, regressionScan, runAutopilotRegressions } from '../src/autopilot-regressions.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { PUBLIC_HELP_TEXT } from '../src/command-catalog.mjs';

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
test('standard merge reverts require an exact full merge SHA in either Git message form', async t => {
  const f = fixture(t);
  for (const [target, suffix, expected] of [
    [M, `, reversing\nchanges made to ${P}.`, 'proven'],
    [M.toUpperCase(), '.', 'proven'],
    [P, `, reversing\nchanges made to ${M}.`, 'ok'],
    [M.slice(0, 39) + 'd', ', reversing\nchanges made to parent.', 'ok'],
    [M.slice(0, 12), '.', 'ok'],
    [M + 'a', ', reversing\nchanges made to parent.', 'ok'],
  ]) {
    commits(f, [{ sha: R, html_url: url('commit', R), commit: { message: `Revert merge\n\nThis reverts commit ${target}${suffix}`, committer: { date: later } } }]);
    const r = await f.scan();
    assert.equal(r.complete, true); assert.equal(r.merges[0].classification, expected, target + suffix);
    assert.deepEqual(r.days, expected === 'proven' ? [{ date: '2026-11-02', proven: 1 }] : []);
  }
});
test('rate exhaustion and Retry-After stop the entire scan, preserving proof and remaining merge identities', async t => {
  const cases = [
    [429, '', false],
    [403, 'X-RateLimit-Remaining: 0\r\nX-RateLimit-Reset: 9999999999\r\n', false],
    [200, 'X-RateLimit-Remaining: 0\r\n', false],
    [503, 'Retry-After: 60\r\n', false],
    [429, 'Retry-After: 60\r\n', true],
  ];
  for (const [code, headers, throws] of cases) {
    const f = fixture(t), gh = f.ports.gh;
    for (let pr = 13; pr <= 37; pr++) f.rows.push({ outcome: 'merged', pr });
    f.routes.set(`commits/${M}/statuses?per_page=100`, [status('failure')]);
    f.routes.set(`commits/${P}/statuses?per_page=100`, [status('success', mergedAt, 2)]);
    f.ports.gh = async args => {
      if (!args[4].endsWith('/pulls/13')) return gh(args);
      f.calls.push(args);
      const response = { code: code === 200 ? 0 : 1, stdout: `HTTP/2 ${code}\r\n${headers}\r\n${JSON.stringify({ number: 13, merge_commit_sha: R, merged_at: mergedAt })}`, stderr: 'DO_NOT_PRINT_TOKEN' };
      if (throws) throw Object.assign(Error('DO_NOT_PRINT_TOKEN'), response);
      return response;
    };
    const r = await f.scan();
    assert.equal(f.calls.length, 7, `${code} ${headers}`);
    assert.equal(r.complete, false); assert.equal(r.merges.length, 26);
    assert.deepEqual(r.counts, { ok: 0, suspect: 25, proven: 1 });
    assert.deepEqual(r.days, [{ date: '2026-11-02', proven: 1 }]);
    assert.match(r.errors.join('\n'), /rate limit|Retry-After/i);
    assert.equal(JSON.stringify(r).includes('DO_NOT_PRINT_TOKEN'), false);
    assert.deepEqual(fs.readdirSync(f.root), ['history.jsonl']);
  }
});
test('a scan-wide request budget bounds distinct pagination URLs and retains earlier page evidence', async t => {
  const f = fixture(t), gh = f.ports.gh;
  f.ports.gh = async args => {
    if (!args[4].startsWith(`repos/${repo}/issues?`)) return gh(args);
    f.calls.push(args);
    const endpoint = new URL(`https://api.github.com/${args[4]}`), page = Number(endpoint.searchParams.get('page') ?? 1);
    endpoint.searchParams.set('page', String(page + 1));
    return { code: 0, stdout: `HTTP/2 200 OK\r\n${page < 105 ? `Link: <${endpoint}>; rel="next"\r\n` : ''}\r\n${JSON.stringify(page === 1 ? [newIssue('Regressed by #12')] : [])}`, stderr: '' };
  };
  const r = await f.scan();
  assert.equal(f.calls.length, 100); assert.equal(r.complete, false);
  assert.equal(r.merges[0].classification, 'proven');
  assert.deepEqual(r.days, [{ date: '2026-11-02', proven: 1 }]);
  assert.match(r.errors.join('\n'), /request budget/i);
});
test('the same request budget applies across distinct historical merges', async t => {
  const f = fixture(t);
  f.rows.splice(0, 1, ...Array.from({ length: 105 }, (_, i) => ({ outcome: 'merged', pr: i + 1 })));
  f.ports.gh = async args => { f.calls.push(args); return { code: 1, stdout: 'HTTP/2 404\r\n\r\n{}', stderr: '' }; };
  const r = await f.scan();
  assert.equal(f.calls.length, 100); assert.equal(r.merges.length, 105);
  assert.deepEqual(r.counts, { ok: 0, suspect: 105, proven: 0 });
  assert.equal(r.complete, false); assert.match(r.errors.join('\n'), /request budget/i);
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
test('regressions route stays outside the exact prompting help contract and leaves topic output unchanged', async () => {
  const contract = fs.readFileSync(new URL('../prompts/cli/command-catalog.prompt.md', import.meta.url), 'utf8');
  const literal = [...contract.matchAll(/```text\n([\s\S]*?)\n```/g)].find(m => m[1].startsWith('In PDD,'));
  assert.ok(literal);
  assert.deepEqual(literal[1].split('\n'), PUBLIC_HELP_TEXT.promptingLines);
  assert.match(contract.replace(/```[^\n]*\n[\s\S]*?\n```/g, ''), /## Regression scan\n/);
  let stdout = '', stderr = '';
  assert.equal(await runPdd(['help', 'prompting'], { packageRoot: '/package', stdout: { write: s => stdout += s }, stderr: { write: s => stderr += s } }), 0);
  assert.equal(stdout, [PUBLIC_HELP_TEXT.heading, '', ...literal[1].split('\n'), '', 'Prompting guide: /package/docs/prompting-guide.md', 'RUNBOOK: /package/RUNBOOK.md', ''].join('\n'));
  assert.equal(stderr, '');
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

test('malformed CI rows mark the scan incomplete rather than silently yielding ok', async t => {
  const f = fixture(t);
  for (const field of ['check-runs?filter=all&per_page=100', 'statuses?per_page=100']) {
    const key = `commits/${M}/${field}`, prior = f.routes.get(key);
    f.routes.set(key, field.startsWith('check') ? { check_runs: [{}] } : [{}]);
    const r = await f.scan(); assert.equal(r.complete, false); assert.equal(r.merges[0].classification, 'suspect');
    f.routes.set(key, prior);
  }
});
test('a failed later page retains earlier exact attribution', async t => {
  const f = fixture(t); issues(f, [newIssue('Regressed by #12')]);
  const key = [...f.routes.keys()].find(k => k.startsWith('issues?'));
  f.links.set(key, `<https://api.github.com/repos/${repo}/${key}&page=2>; rel="next"`);
  f.routes.set(`${key}&page=2`, Error('Unavailable'));
  const r = await f.scan(); assert.equal(r.complete, false); assert.equal(r.merges[0].classification, 'proven');
});
test('native command process substitution does no filesystem writes without --file', async t => {
  const f = fixture(t), checkout = '/fixture/checkout';
  const id = createHash('sha256').update(checkout).digest('hex').slice(0, 20), folder = '/fixture/state';
  const files = {
    readFileSync: path => {
      if (path === `${folder}/${id}.json`) return JSON.stringify({ repo });
      if (path === `${folder}/${id}-core/history.jsonl`) return '';
      assert.fail(`Unexpected read: ${path}`);
    },
    writeFileSync: () => assert.fail('No local writes'), mkdirSync: () => assert.fail('No local writes'), appendFileSync: () => assert.fail('No ledger writes'),
  };
  const result = await runAutopilotRegressions({ cwd: checkout, env: {} }, { stateRoot: folder, fs: files, now: f.ports.now,
    run: async (file, args) => { assert.equal(file, 'git'); assert.deepEqual(args, ['rev-parse', '--show-toplevel']); return { code: 0, stdout: checkout }; } });
  assert.equal(result.exitCode, 0);
});

test('default native process adapter reads fake gh without changing an existing accounting ledger', async t => {
  const f = fixture(t); f.save();
  const bin = join(f.root, 'bin'), ledgerFolder = join(f.root, '.local', 'state', 'pdd', 'autopilot', 'github');
  fs.mkdirSync(bin); fs.mkdirSync(ledgerFolder, { recursive: true });
  const ledger = join(ledgerFolder, createHash('sha256').update(repo).digest('hex').slice(0, 20) + '.jsonl');
  fs.writeFileSync(ledger, 'sentinel\n');
  const routes = join(f.root, 'routes.json'); fs.writeFileSync(routes, JSON.stringify(Object.fromEntries(f.routes)));
  const program = `#!${process.execPath}\nimport {readFileSync} from 'node:fs';\nconst args = process.argv.slice(2);\nif (args.slice(0,4).join(' ') !== 'api --include --method GET') process.exit(8);\nconst key = args[4].slice(${JSON.stringify(`repos/${repo}/`)}.length);\nconst routes = JSON.parse(readFileSync(${JSON.stringify(routes)}, 'utf8'));\nif (!(key in routes)) process.exit(9);\nprocess.stdout.write('HTTP/2 200 OK\\r\\n\\r\\n' + JSON.stringify(routes[key]));\n`;
  fs.writeFileSync(join(bin, 'gh'), program, { mode: 0o700 });
  const result = await runAutopilotRegressions({ cwd: f.root, env: { HOME: f.root, PATH: bin }, json: true }, { root: f.root, repo, now: f.ports.now });
  assert.equal(result.exitCode, 0, result.message); assert.equal(JSON.parse(result.message).merges[0].classification, 'ok');
  assert.equal(fs.readFileSync(ledger, 'utf8'), 'sentinel\n');
});

test('checkPostMergeRegressions sweeps merges across ticks with a saved cursor and never marks unexamined merges suspect (#3182)', async t => {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-post-merge-cursor-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const totalMerges = 12;
  const baseMs = Date.parse('2026-11-01T00:00:00Z');
  const tickNow = Date.parse('2026-11-10T00:00:00Z');
  const historyRows = [];
  const routes = new Map([
    ['pulls?state=all&sort=updated&direction=desc&per_page=100', []],
  ]);

  for (let i = 1; i <= totalMerges; i += 1) {
    const pr = 100 + i;
    const issue = i;
    const mSha = i.toString(16).padStart(40, 'a');
    const pSha = i.toString(16).padStart(40, 'b');
    const mIso = new Date(baseMs + i * 3600_000).toISOString();
    historyRows.push(JSON.stringify({ at: baseMs + i * 3600_000, issue, pr, outcome: 'merged' }));
    routes.set(`pulls/${pr}`, { number: pr, title: `Merge ${pr}`, merged: true, merged_at: mIso, merge_commit_sha: mSha });
    routes.set(`commits/${mSha}`, { sha: mSha, parents: [{ sha: pSha }] });
    routes.set(`commits/${mSha}/check-runs?filter=all&per_page=100`, { check_runs: [] });
    routes.set(`commits/${mSha}/statuses?per_page=100`, []);
    routes.set(`commits/${pSha}/check-runs?filter=all&per_page=100`, { check_runs: [] });
    routes.set(`commits/${pSha}/statuses?per_page=100`, []);
    routes.set(`issues/${issue}`, { number: issue, state: 'closed', updated_at: mIso, html_url: url('issues', issue) });
    routes.set(`issues/${issue}/timeline?per_page=100`, []);
  }
  fs.writeFileSync(join(root, 'history.jsonl'), historyRows.join('\n') + '\n');

  let callCount = 0;
  const gh = async args => {
    callCount += 1;
    const key = args[4].slice(`repos/${repo}/`.length);
    if (key.startsWith('commits?since=')) return { code: 0, stdout: 'HTTP/2 200 OK\r\n\r\n[]', stderr: '' };
    assert.ok(routes.has(key), `Unexpected endpoint: ${key}`);
    return { code: 0, stdout: `HTTP/2 200 OK\r\n\r\n${JSON.stringify(routes.get(key))}`, stderr: '' };
  };

  // Budget of 20 requests can inspect only 2 uncached merges (8 reads each + 2 shared = 18 <= 20) and stops before merge #3.
  const tick1 = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => tickNow, maxMerges: 10, maxRequests: 20, minRecheckMs: 0 });
  assert.equal(tick1.budgetStopped, true);
  assert.ok(tick1.requests <= 20, `respected 20-read budget (used ${tick1.requests})`);
  assert.equal(tick1.counts.tracked, 12);
  assert.equal(tick1.counts.ok, 2);
  assert.equal(tick1.counts.pending, 10, 'unexamined merges stay pending');
  assert.equal(tick1.counts.suspect, 0, 'budget stop never marks unexamined merges suspect');
  assert.equal(tick1.state.cursor, 2);

  // Sweep remaining merges across bounded ticks until all 12 are checked.
  let latest = tick1;
  for (let step = 0; step < 6 && latest.counts.pending > 0; step += 1) {
    latest = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => tickNow + (step + 1) * 1000, maxMerges: 10, maxRequests: 20, minRecheckMs: 0 });
  }
  assert.equal(latest.counts.pending, 0);
  assert.equal(latest.counts.ok, 12);
  assert.equal(latest.counts.regressions, 0);

  // Recheck sweep uses cached immutable PR/parent metadata (fewer GitHub calls per merge).
  const beforeRecheck = callCount;
  const recheck = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => tickNow + 3600_000, maxMerges: 2, maxRequests: 40, minRecheckMs: 60_000 });
  assert.equal(recheck.budgetStopped, false);
  assert.equal(callCount - beforeRecheck, 10, '2 cached merges need only 4 per-merge reads each + 2 shared reads = 10 total');
});

test('checkPostMergeRegressions detects reopened primary/companion issues, reverts, and post-merge CI breaks once per signal (#3182)', async t => {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-post-merge-signals-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const m1 = '1'.repeat(40), p1 = '2'.repeat(40);
  const m2 = '3'.repeat(40), p2 = '4'.repeat(40);
  const m3 = '5'.repeat(40), p3 = '6'.repeat(40);
  const m4 = '7'.repeat(40), p4 = '8'.repeat(40);
  const revSha = '9'.repeat(40);

  const history = [
    { at: Date.parse(mergedAt), issue: 11, issues: [11, 12], pr: 201, outcome: 'merged' },
    { at: Date.parse(mergedAt), issue: 13, pr: 202, outcome: 'merged' },
    { at: Date.parse(mergedAt), issue: 14, pr: 203, outcome: 'merged' },
    { at: Date.parse(mergedAt), issue: 15, pr: 204, outcome: 'merged' },
  ];
  fs.writeFileSync(join(root, 'history.jsonl'), history.map(r => JSON.stringify(r)).join('\n') + '\n');

  const routes = new Map([
    ['pulls/201', { number: 201, title: 'Fix 11 and 12', merged: true, merged_at: mergedAt, merge_commit_sha: m1 }],
    [`commits/${m1}`, { sha: m1, parents: [{ sha: p1 }] }],
    [`commits/${m1}/check-runs?filter=all&per_page=100`, { check_runs: [] }],
    [`commits/${m1}/statuses?per_page=100`, []],
    [`commits/${p1}/check-runs?filter=all&per_page=100`, { check_runs: [] }],
    [`commits/${p1}/statuses?per_page=100`, []],
    ['issues/11', { number: 11, state: 'closed', updated_at: mergedAt, html_url: url('issues', 11) }],
    ['issues/11/timeline?per_page=100', []],
    ['issues/12', { number: 12, state: 'open', updated_at: later, html_url: url('issues', 12) }],
    ['issues/12/timeline?per_page=100', [{ id: 55, event: 'reopened', created_at: later, actor: { login: 'greg' } }]],

    ['pulls/202', { number: 202, title: 'Machine reopen ignored', merged: true, merged_at: mergedAt, merge_commit_sha: m2 }],
    [`commits/${m2}`, { sha: m2, parents: [{ sha: p2 }] }],
    [`commits/${m2}/check-runs?filter=all&per_page=100`, { check_runs: [] }],
    [`commits/${m2}/statuses?per_page=100`, []],
    [`commits/${p2}/check-runs?filter=all&per_page=100`, { check_runs: [] }],
    [`commits/${p2}/statuses?per_page=100`, []],
    ['issues/13', { number: 13, state: 'open', updated_at: later, html_url: url('issues', 13) }],
    ['issues/13/timeline?per_page=100', [
      { id: 56, event: 'reopened', created_at: later, actor: { login: 'bot' } },
      { id: 57, event: 'commented', created_at: later, user: { login: 'bot' }, body: 'auto note\n<!-- pdd:autopilot-core:note -->' },
    ]],

    ['pulls/203', { number: 203, title: 'Reverted merge', merged: true, merged_at: mergedAt, merge_commit_sha: m3 }],
    [`commits/${m3}`, { sha: m3, parents: [{ sha: p3 }] }],
    [`commits/${m3}/check-runs?filter=all&per_page=100`, { check_runs: [] }],
    [`commits/${m3}/statuses?per_page=100`, []],
    [`commits/${p3}/check-runs?filter=all&per_page=100`, { check_runs: [] }],
    [`commits/${p3}/statuses?per_page=100`, []],
    ['issues/14', { number: 14, state: 'closed', updated_at: mergedAt, html_url: url('issues', 14) }],
    ['issues/14/timeline?per_page=100', []],

    ['pulls/204', { number: 204, title: 'Post-merge CI red', merged: true, merged_at: mergedAt, merge_commit_sha: m4 }],
    [`commits/${m4}`, { sha: m4, parents: [{ sha: p4 }] }],
    [`commits/${m4}/check-runs?filter=all&per_page=100`, { check_runs: [check('failure', later, 91, 3)] }],
    [`commits/${m4}/statuses?per_page=100`, []],
    [`commits/${p4}/check-runs?filter=all&per_page=100`, { check_runs: [check('success', mergedAt, 90, 3)] }],
    [`commits/${p4}/statuses?per_page=100`, []],
    ['issues/15', { number: 15, state: 'closed', updated_at: mergedAt, html_url: url('issues', 15) }],
    ['issues/15/timeline?per_page=100', []],

    ['pulls?state=all&sort=updated&direction=desc&per_page=100', []],
  ]);

  const gh = async args => {
    const key = args[4].slice(`repos/${repo}/`.length);
    if (key.startsWith('commits?since=')) {
      return {
        code: 0,
        stdout: `HTTP/2 200 OK\r\n\r\n${JSON.stringify([
          { sha: revSha, html_url: url('commit', revSha), commit: { message: `Revert "Reverted merge"\n\nThis reverts commit ${m3}.`, committer: { date: later } } },
        ])}`,
        stderr: '',
      };
    }
    assert.ok(routes.has(key), `Unexpected endpoint: ${key}`);
    return { code: 0, stdout: `HTTP/2 200 OK\r\n\r\n${JSON.stringify(routes.get(key))}`, stderr: '' };
  };

  const first = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now, maxRequests: 60, minRecheckMs: 0 });
  assert.deepEqual(first.counts, {
    tracked: 4,
    pending: 0,
    ok: 1, // PR #202 (machine-marked reopen ignored)
    reopened: 1, // PR #201 (companion #12 reopened)
    reverted: 1, // PR #203
    ci: 1, // PR #204
    regressions: 3,
    reopenOrRevert: 2,
    suspect: 0,
  });
  assert.deepEqual(
    first.newlyDetected.map(d => [d.pr, d.issue, d.code]),
    [
      [201, 12, 'post-merge-reopen'],
      [203, 14, 'post-merge-revert'],
      [204, 15, 'post-merge-ci'],
    ],
  );

  // Subsequent sweep emits zero duplicate newlyDetected items when nothing new happened.
  const second = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now + 60_000, maxRequests: 60, minRecheckMs: 0 });
  assert.deepEqual(second.newlyDetected, []);
  assert.equal(second.counts.regressions, 3);
});

test('checkPostMergeRegressions follows Link rel="next" pagination across timeline, check-runs, commits, and pulls (#3182)', async t => {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-post-merge-pages-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const m1 = 'a'.repeat(40), p1 = 'b'.repeat(40);
  const m2 = 'c'.repeat(40), p2 = 'd'.repeat(40);
  const revSha = 'e'.repeat(40);

  fs.writeFileSync(
    join(root, 'history.jsonl'),
    [
      { at: Date.parse(mergedAt), issue: 31, pr: 301, outcome: 'merged' },
      { at: Date.parse(mergedAt), issue: 32, pr: 302, outcome: 'merged' },
    ].map(r => JSON.stringify(r)).join('\n') + '\n',
  );

  const pageReply = (body, nextPath = null) => ({
    code: 0,
    stdout: [
      'HTTP/2 200 OK',
      ...(nextPath ? [`Link: <https://api.github.com/repos/${repo}/${nextPath}>; rel="next"`] : []),
      '',
      JSON.stringify(body),
    ].join('\r\n'),
    stderr: '',
  });

  const gh = async args => {
    const key = args[4].slice(`repos/${repo}/`.length);
    if (key === 'pulls/301') return pageReply({ number: 301, title: 'Paged reopen + CI', merged: true, merged_at: mergedAt, merge_commit_sha: m1 });
    if (key === `commits/${m1}`) return pageReply({ sha: m1, parents: [{ sha: p1 }] });
    if (key === `commits/${p1}/check-runs?filter=all&per_page=100`) return pageReply({ check_runs: [{ ...check('neutral', mergedAt, 10, 4), name: 'lint' }] }, `commits/${p1}/check-runs?filter=all&per_page=100&page=2`);
    if (key === `commits/${p1}/check-runs?filter=all&per_page=100&page=2`) return pageReply({ check_runs: [check('success', mergedAt, 11, 4)] });
    if (key === `commits/${p1}/statuses?per_page=100`) return pageReply([]);
    if (key === `commits/${m1}/check-runs?filter=all&per_page=100`) return pageReply({ check_runs: [{ ...check('success', later, 12, 4), name: 'lint' }] }, `commits/${m1}/check-runs?filter=all&per_page=100&page=2`);
    if (key === `commits/${m1}/check-runs?filter=all&per_page=100&page=2`) return pageReply({ check_runs: [check('failure', later, 13, 4)] });
    if (key === `commits/${m1}/statuses?per_page=100`) return pageReply([]);
    // Issue #31 was reopened on page 2 and later re-closed, so only page-2 timeline reveals the post-merge reopen!
    if (key === 'issues/31') return pageReply({ number: 31, state: 'closed', updated_at: later, html_url: url('issues', 31) });
    if (key === 'issues/31/timeline?per_page=100') return pageReply([{ id: 1, event: 'labeled', created_at: mergedAt }], 'issues/31/timeline?per_page=100&page=2');
    if (key === 'issues/31/timeline?per_page=100&page=2') return pageReply([{ id: 2, event: 'reopened', created_at: later, actor: { login: 'serhan' } }]);

    if (key === 'pulls/302') return pageReply({ number: 302, title: 'Paged revert', merged: true, merged_at: mergedAt, merge_commit_sha: m2 });
    if (key === `commits/${m2}`) return pageReply({ sha: m2, parents: [{ sha: p2 }] });
    if (key === `commits/${p2}/check-runs?filter=all&per_page=100` || key === `commits/${m2}/check-runs?filter=all&per_page=100`) return pageReply({ check_runs: [] });
    if (key === `commits/${p2}/statuses?per_page=100` || key === `commits/${m2}/statuses?per_page=100`) return pageReply([]);
    if (key === 'issues/32') return pageReply({ number: 32, state: 'closed', updated_at: mergedAt, html_url: url('issues', 32) });
    if (key === 'issues/32/timeline?per_page=100') return pageReply([]);

    if (key.startsWith('commits?since=') && !key.includes('&page=2')) {
      return pageReply([{ sha: '0'.repeat(40), html_url: url('commit', '0'.repeat(40)), commit: { message: 'Unrelated', committer: { date: later } } }], `${key}&page=2`);
    }
    if (key.startsWith('commits?since=') && key.includes('&page=2')) {
      return pageReply([{ sha: revSha, html_url: url('commit', revSha), commit: { message: `Revert\n\nThis reverts commit ${m2}.`, committer: { date: later } } }]);
    }
    if (key === 'pulls?state=all&sort=updated&direction=desc&per_page=100') return pageReply([]);
    assert.fail(`Unexpected endpoint: ${key}`);
  };

  const res = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now, maxRequests: 50, minRecheckMs: 0 });
  assert.equal(res.counts.pending, 0);
  assert.equal(res.counts.reopened, 1);
  assert.equal(res.counts.ci, 1);
  assert.equal(res.counts.reverted, 1);
  assert.deepEqual(
    res.newlyDetected.map(d => [d.pr, d.code]).sort(),
    [
      [301, 'post-merge-ci'],
      [301, 'post-merge-reopen'],
      [302, 'post-merge-revert'],
    ],
  );
});

test('checkPostMergeRegressions keeps merges pending and parentChecked false on transient HTTP 500 reads, then recovers on retry (#3182)', async t => {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-post-merge-retry-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const m1 = '1'.repeat(40), p1 = '2'.repeat(40);
  fs.writeFileSync(join(root, 'history.jsonl'), JSON.stringify({ at: Date.parse(mergedAt), issue: 41, pr: 401, outcome: 'merged' }) + '\n');

  let mode = 'fail-parent';
  const okJson = body => ({ code: 0, stdout: `HTTP/2 200 OK\r\n\r\n${JSON.stringify(body)}`, stderr: '' });
  const err500 = () => ({ code: 1, stdout: 'HTTP/2 500 Internal Server Error\r\n\r\n{"message":"boom"}', stderr: 'gh: HTTP 500' });

  const gh = async args => {
    const key = args[4].slice(`repos/${repo}/`.length);
    if (key === 'pulls/401') return okJson({ number: 401, title: 'Retry test', merged: true, merged_at: mergedAt, merge_commit_sha: m1 });
    if (key === `commits/${m1}`) return okJson({ sha: m1, parents: [{ sha: p1 }] });
    if (key === `commits/${p1}/check-runs?filter=all&per_page=100`) {
      return mode === 'fail-parent' ? err500() : okJson({ check_runs: [check('success', mergedAt, 20, 5)] });
    }
    if (key === `commits/${p1}/statuses?per_page=100`) return okJson([]);
    if (key === `commits/${m1}/check-runs?filter=all&per_page=100`) {
      return okJson({ check_runs: [check(mode === 'healthy' ? 'failure' : 'success', later, 21, 5)] });
    }
    if (key === `commits/${m1}/statuses?per_page=100`) return okJson([]);
    if (key === 'issues/41') return okJson({ number: 41, state: 'closed', updated_at: mergedAt, html_url: url('issues', 41) });
    if (key === 'issues/41/timeline?per_page=100') return mode === 'fail-timeline' ? err500() : okJson([]);
    if (key.startsWith('commits?since=')) return mode === 'fail-shared' ? err500() : okJson([]);
    if (key === 'pulls?state=all&sort=updated&direction=desc&per_page=100') return okJson([]);
    assert.fail(`Unexpected endpoint: ${key}`);
  };

  // 1) Transient 500 on parent check-runs: parentChecked MUST stay false and status MUST stay pending (never ok).
  const sweep1 = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now, maxRequests: 40, minRecheckMs: 60_000 });
  assert.equal(sweep1.counts.pending, 1);
  assert.equal(sweep1.counts.ok, 0);
  assert.equal(sweep1.state.merges['401'].parentChecked, false);
  assert.equal(sweep1.state.merges['401'].checkedAt, null);

  // 2) Transient 500 on timeline: parentChecked now succeeds, but merge stays pending with checkedAt null.
  mode = 'fail-timeline';
  const sweep2 = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now + 1000, maxRequests: 40, minRecheckMs: 60_000 });
  assert.equal(sweep2.counts.pending, 1);
  assert.equal(sweep2.counts.ok, 0);
  assert.equal(sweep2.state.merges['401'].parentChecked, true);
  assert.equal(sweep2.state.merges['401'].checkedAt, null);

  // 3) Healthy GitHub on sweep 3: cached green parent proves the post-merge CI break and advances checkedAt!
  mode = 'healthy';
  const sweep3 = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now + 2000, maxRequests: 40, minRecheckMs: 60_000 });
  assert.equal(sweep3.counts.pending, 0);
  assert.equal(sweep3.counts.ci, 1);
  assert.equal(sweep3.newlyDetected.length, 1);
  assert.equal(sweep3.newlyDetected[0].code, 'post-merge-ci');
  assert.ok(sweep3.state.merges['401'].checkedAt);
});


test('checkPostMergeRegressions resumes multi-page pagination across budget-stopped ticks, refreshes pending parent CI, and preserves proven signals across later HTTP 500s (#3182)', async t => {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-post-merge-round2-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const m1 = 'a'.repeat(40), p1 = 'b'.repeat(40);
  const m2 = 'c'.repeat(40), p2 = 'd'.repeat(40);
  const revSha = 'e'.repeat(40);

  fs.writeFileSync(
    join(root, 'history.jsonl'),
    [
      { at: Date.parse(mergedAt), issue: 51, pr: 501, outcome: 'merged' },
      { at: Date.parse(mergedAt), issue: 52, pr: 502, outcome: 'merged' },
    ].map(r => JSON.stringify(r)).join('\n') + '\n',
  );

  let parentCiDone = false;
  let timeline52Fail = true;
  let merge52Recovered = false;
  const pageReply = (body, nextPath = null) => ({
    code: 0,
    stdout: [
      'HTTP/2 200 OK',
      ...(nextPath ? [`Link: <https://api.github.com/repos/${repo}/${nextPath}>; rel="next"`] : []),
      '',
      JSON.stringify(body),
    ].join('\r\n'),
    stderr: '',
  });
  const err500 = () => ({ code: 1, stdout: 'HTTP/2 500 Internal Server Error\r\n\r\n{"message":"boom"}', stderr: 'gh: HTTP 500' });

  const gh = async args => {
    const key = args[4].slice(`repos/${repo}/`.length);
    if (key === 'pulls/501') return pageReply({ number: 501, title: 'Pending parent + multi-page revert', merged: true, merged_at: mergedAt, merge_commit_sha: m1 });
    if (key === `commits/${m1}`) return pageReply({ sha: m1, parents: [{ sha: p1 }] });
    if (key === `commits/${p1}/check-runs?filter=all&per_page=100`) {
      return pageReply({
        check_runs: [parentCiDone
          ? check('success', mergedAt, 30, 6)
          : { id: 30, name: 'suite', app: { id: 6 }, status: 'in_progress', conclusion: null, started_at: mergedAt, html_url: url('actions/runs', 30) }],
      });
    }
    if (key === `commits/${p1}/statuses?per_page=100`) return pageReply([]);
    if (key === `commits/${m1}/check-runs?filter=all&per_page=100`) return pageReply({ check_runs: [check('failure', later, 31, 6)] });
    if (key === `commits/${m1}/statuses?per_page=100`) return pageReply([]);
    if (key === 'issues/51') return pageReply({ number: 51, state: 'closed', updated_at: mergedAt, html_url: url('issues', 51) });
    if (key === 'issues/51/timeline?per_page=100') return pageReply([]);

    if (key === 'pulls/502') return pageReply({ number: 502, title: 'Proven CI before timeline 500', merged: true, merged_at: mergedAt, merge_commit_sha: m2 });
    if (key === `commits/${m2}`) return pageReply({ sha: m2, parents: [{ sha: p2 }] });
    if (key === `commits/${p2}/check-runs?filter=all&per_page=100`) return pageReply({ check_runs: [check('success', mergedAt, 40, 6)] });
    if (key === `commits/${p2}/statuses?per_page=100`) return pageReply([]);
    if (key === `commits/${m2}/check-runs?filter=all&per_page=100`) {
      return pageReply({ check_runs: [check(merge52Recovered ? 'success' : 'failure', later, 41, 6)] });
    }
    if (key === `commits/${m2}/statuses?per_page=100`) return pageReply([]);
    if (key === 'issues/52') return pageReply({ number: 52, state: 'closed', updated_at: mergedAt, html_url: url('issues', 52) });
    if (key === 'issues/52/timeline?per_page=100') return timeline52Fail ? err500() : pageReply([]);

    // 3 pages of commits?since=... so tight maxRequests=4 must resume shared pagination across ticks!
    if (key.startsWith('commits?since=') && !key.includes('&page=')) {
      return pageReply([{ sha: '0'.repeat(40), html_url: url('commit', '0'.repeat(40)), commit: { message: 'c1', committer: { date: later } } }], `${key}&page=2`);
    }
    if (key.startsWith('commits?since=') && key.endsWith('&page=2')) {
      const baseKey = key.replace(/&page=2$/, '');
      return pageReply([{ sha: 'f'.repeat(40), html_url: url('commit', 'f'.repeat(40)), commit: { message: 'c2', committer: { date: later } } }], `${baseKey}&page=3`);
    }
    if (key.startsWith('commits?since=') && key.endsWith('&page=3')) {
      return pageReply([{ sha: revSha, html_url: url('commit', revSha), commit: { message: `Revert\n\nThis reverts commit ${m1}.`, committer: { date: later } } }]);
    }
    if (key === 'pulls?state=all&sort=updated&direction=desc&per_page=100') return pageReply([]);
    assert.fail(`Unexpected endpoint: ${key}`);
  };

  // Sweep with tiny maxRequests=4 across multiple ticks:
  // - PR #501 has in_progress parent CI -> parentChecked stays false!
  // - Shared commits has 3 pages -> activeSweep resumes page-by-page without stalling, finding page-3 revert of PR #501!
  // - PR #502 has proven CI break followed by timeline HTTP 500 -> post-merge-ci is STILL emitted immediately and persisted!
  const seenCodes = [];
  let last;
  for (let step = 0; step < 8; step += 1) {
    last = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now + step * 1000, maxMerges: 2, maxRequests: 4, minRecheckMs: 60_000 });
    for (const item of last.newlyDetected) seenCodes.push(`${item.pr}:${item.code}`);
  }
  assert.ok(seenCodes.includes('501:post-merge-revert'), 'page-3 revert detected across budget-stopped ticks without stalling');
  assert.ok(seenCodes.includes('502:post-merge-ci'), 'proven CI break on PR #502 preserved despite timeline HTTP 500');
  assert.equal(last.state.merges['501'].parentChecked, false, 'pending parent CI was NOT cached as parentChecked: true');

  // Now parent CI on PR #501 finishes green, and PR #502 CI recovers green while timeline succeeds:
  // - PR #501 upgrades to proven CI break too ('501:post-merge-ci')!
  // - PR #502 remains proven ('ci'), never overwritten to 'ok'!
  parentCiDone = true;
  timeline52Fail = false;
  merge52Recovered = true;
  for (let step = 0; step < 4; step += 1) {
    last = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now + 120_000 + step * 1000, maxMerges: 2, maxRequests: 10, minRecheckMs: 60_000 });
    for (const item of last.newlyDetected) seenCodes.push(`${item.pr}:${item.code}`);
  }
  assert.ok(seenCodes.includes('501:post-merge-ci'), 'once pending parent CI turned green, red merge #501 upgraded from suspect to proven');
  assert.equal(last.state.merges['501'].parentChecked, true);
  assert.equal(last.state.merges['502'].classification, 'proven', 'PR #502 kept its proven regression after CI rerun');
  assert.equal(last.counts.pending, 0);
});


test('checkPostMergeRegressions persists proven check-runs before statuses HTTP 500 and keeps green merges pending while parent CI is in_progress (#3182)', async t => {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-post-merge-round3-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const m1 = '1'.repeat(40), p1 = '2'.repeat(40);
  const m2 = '3'.repeat(40), p2 = '4'.repeat(40);
  fs.writeFileSync(
    join(root, 'history.jsonl'),
    [
      { at: Date.parse(mergedAt), issue: 61, pr: 601, outcome: 'merged' },
      { at: Date.parse(mergedAt), issue: 62, pr: 602, outcome: 'merged' },
    ].map(r => JSON.stringify(r)).join('\n') + '\n',
  );

  let statuses601Fail = true;
  let merge601ReranGreen = false;
  let parent602Done = false;
  const okJson = body => ({ code: 0, stdout: `HTTP/2 200 OK\r\n\r\n${JSON.stringify(body)}`, stderr: '' });
  const err500 = () => ({ code: 1, stdout: 'HTTP/2 500 Internal Server Error\r\n\r\n{"message":"boom"}', stderr: 'gh: HTTP 500' });

  const gh = async args => {
    const key = args[4].slice(`repos/${repo}/`.length);
    if (key === 'pulls/601') return okJson({ number: 601, title: 'Statuses 500 after red check', merged: true, merged_at: mergedAt, merge_commit_sha: m1 });
    if (key === `commits/${m1}`) return okJson({ sha: m1, parents: [{ sha: p1 }] });
    if (key === `commits/${p1}/check-runs?filter=all&per_page=100`) return okJson({ check_runs: [check('success', mergedAt, 60, 7)] });
    if (key === `commits/${p1}/statuses?per_page=100`) return okJson([]);
    if (key === `commits/${m1}/check-runs?filter=all&per_page=100`) {
      return okJson({ check_runs: [check(merge601ReranGreen ? 'success' : 'failure', later, 61, 7)] });
    }
    if (key === `commits/${m1}/statuses?per_page=100`) return statuses601Fail ? err500() : okJson([]);
    if (key === 'issues/61') return okJson({ number: 61, state: 'closed', updated_at: mergedAt, html_url: url('issues', 61) });
    if (key === 'issues/61/timeline?per_page=100') return okJson([]);

    if (key === 'pulls/602') return okJson({ number: 602, title: 'Green merge with pending parent CI', merged: true, merged_at: mergedAt, merge_commit_sha: m2 });
    if (key === `commits/${m2}`) return okJson({ sha: m2, parents: [{ sha: p2 }] });
    if (key === `commits/${p2}/check-runs?filter=all&per_page=100`) {
      return okJson({
        check_runs: [parent602Done
          ? check('success', mergedAt, 70, 7)
          : { id: 70, name: 'suite', app: { id: 7 }, status: 'in_progress', conclusion: null, started_at: mergedAt, html_url: url('actions/runs', 70) }],
      });
    }
    if (key === `commits/${p2}/statuses?per_page=100`) return okJson([]);
    if (key === `commits/${m2}/check-runs?filter=all&per_page=100`) return okJson({ check_runs: [check('success', later, 71, 7)] });
    if (key === `commits/${m2}/statuses?per_page=100`) return okJson([]);
    if (key === 'issues/62') return okJson({ number: 62, state: 'closed', updated_at: mergedAt, html_url: url('issues', 62) });
    if (key === 'issues/62/timeline?per_page=100') return okJson([]);

    if (key.startsWith('commits?since=')) return okJson([]);
    if (key === 'pulls?state=all&sort=updated&direction=desc&per_page=100') return okJson([]);
    assert.fail(`Unexpected endpoint: ${key}`);
  };

  // Sweep 1:
  // - PR #601: mChecks red vs green parent, then mStatuses 500 -> proven CI recorded immediately!
  // - PR #602: mChecks green while parent CI is in_progress -> stays pending with checkedAt null (never ok)!
  const sweep1 = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now, maxRequests: 40, minRecheckMs: 60_000 });
  assert.deepEqual(sweep1.newlyDetected.map(d => `${d.pr}:${d.code}`), ['601:post-merge-ci']);
  assert.equal(sweep1.state.merges['601'].status, 'ci');
  assert.equal(sweep1.state.merges['601'].checkedAt, null);
  assert.equal(sweep1.state.merges['602'].parentChecked, false);
  assert.equal(sweep1.state.merges['602'].status, 'pending');
  assert.equal(sweep1.state.merges['602'].checkedAt, null);
  assert.equal(sweep1.counts.ok, 0);

  // Sweep 2: PR #601 reruns green and statuses recovers; PR #602 parent CI finishes green:
  // - PR #601 keeps its proven CI regression (never overwritten to ok)!
  // - PR #602 now verifies ok with parentChecked: true and checkedAt set!
  statuses601Fail = false;
  merge601ReranGreen = true;
  parent602Done = true;
  const sweep2 = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now + 1000, maxRequests: 40, minRecheckMs: 60_000 });
  assert.equal(sweep2.state.merges['601'].status, 'ci');
  assert.equal(sweep2.state.merges['601'].classification, 'proven');
  assert.ok(sweep2.state.merges['601'].checkedAt);
  assert.equal(sweep2.state.merges['602'].parentChecked, true);
  assert.equal(sweep2.state.merges['602'].status, 'ok');
  assert.ok(sweep2.state.merges['602'].checkedAt);
  assert.equal(sweep2.counts.ci, 1);
  assert.equal(sweep2.counts.ok, 1);
});


test('checkPostMergeRegressions preserves cached green parent evidence and emits proven CI before a failed late-parent refresh (#3182)', async t => {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-post-merge-round4-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const m1 = '7'.repeat(40), p1 = '8'.repeat(40);
  fs.writeFileSync(join(root, 'history.jsonl'), JSON.stringify({ at: Date.parse(mergedAt), issue: 71, pr: 701, outcome: 'merged' }) + '\n');

  let phase = 'seed';
  const okJson = body => ({ code: 0, stdout: `HTTP/2 200 OK\r\n\r\n${JSON.stringify(body)}`, stderr: '' });
  const err500 = () => ({ code: 1, stdout: 'HTTP/2 500 Internal Server Error\r\n\r\n{"message":"boom"}', stderr: 'gh: HTTP 500' });
  const namedCheck = (name, conclusion, atIso, id) => ({ ...check(conclusion, atIso, id, 9), name });

  const gh = async args => {
    const key = args[4].slice(`repos/${repo}/`.length);
    if (key === 'pulls/701') return okJson({ number: 701, title: 'Late parent refresh 500', merged: true, merged_at: mergedAt, merge_commit_sha: m1 });
    if (key === `commits/${m1}`) return okJson({ sha: m1, parents: [{ sha: p1 }] });
    if (key === `commits/${p1}/check-runs?filter=all&per_page=100`) {
      if (phase === 'refresh-500') return err500();
      return okJson({ check_runs: [namedCheck('check-A', 'success', mergedAt, 80)] });
    }
    if (key === `commits/${p1}/statuses?per_page=100`) return okJson([]);
    if (key === `commits/${m1}/check-runs?filter=all&per_page=100`) {
      if (phase === 'seed' || phase === 'rerun-green') return okJson({ check_runs: [namedCheck('check-A', 'success', later, 81)] });
      return okJson({ check_runs: [namedCheck('check-A', 'failure', later, 82), namedCheck('check-B', 'failure', later, 83)] });
    }
    if (key === `commits/${m1}/statuses?per_page=100`) return okJson([]);
    if (key === 'issues/71') return okJson({ number: 71, state: 'closed', updated_at: mergedAt, html_url: url('issues', 71) });
    if (key === 'issues/71/timeline?per_page=100') return okJson([]);
    if (key.startsWith('commits?since=')) return okJson([]);
    if (key === 'pulls?state=all&sort=updated&direction=desc&per_page=100') return okJson([]);
    assert.fail(`Unexpected endpoint: ${key}`);
  };

  // 1) Cache green parent check-A on sweep 1.
  const s1 = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now, maxRequests: 40, minRecheckMs: 0 });
  assert.equal(s1.state.merges['701'].status, 'ok');

  // 2) Merge now has failing check-A and new failing check-B, while parent refresh returns HTTP 500:
  //    check-A proof MUST still be recorded immediately and cached parent check-A preserved!
  phase = 'refresh-500';
  const s2 = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now + 1000, maxRequests: 40, minRecheckMs: 0 });
  assert.deepEqual(s2.newlyDetected.map(d => `${d.pr}:${d.code}`), ['701:post-merge-ci']);
  assert.equal(s2.state.merges['701'].status, 'ci');
  assert.equal(s2.state.merges['701'].classification, 'proven');
  assert.equal(s2.state.merges['701'].parentObservations.length, 1);

  // 3) Later green rerun keeps proven regression on PR #701!
  phase = 'rerun-green';
  const s3 = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now + 2000, maxRequests: 40, minRecheckMs: 0 });
  assert.equal(s3.state.merges['701'].status, 'ci');
  assert.equal(s3.state.merges['701'].classification, 'proven');
});


test('checkPostMergeRegressions keeps parentChecked false when an overlapping same-named parent run is in_progress and upgrades multi-tick late parent contexts (#3182)', async t => {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-post-merge-round5-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const m1 = '9'.repeat(40), p1 = 'a'.repeat(40);
  const m2 = 'b'.repeat(40), p2 = 'c'.repeat(40);
  fs.writeFileSync(
    join(root, 'history.jsonl'),
    [
      { at: Date.parse(mergedAt), issue: 81, pr: 801, outcome: 'merged' },
      { at: Date.parse(mergedAt), issue: 82, pr: 802, outcome: 'merged' },
    ].map(r => JSON.stringify(r)).join('\n') + '\n',
  );

  let overlapDone = false;
  let lateParentPosted = false;
  const okJson = body => ({ code: 0, stdout: `HTTP/2 200 OK\r\n\r\n${JSON.stringify(body)}`, stderr: '' });

  const gh = async args => {
    const key = args[4].slice(`repos/${repo}/`.length);
    // PR #801: parent has completed success (10:05) AND overlapping in_progress run (started 10:04) with the SAME app/name
    if (key === 'pulls/801') return okJson({ number: 801, title: 'Overlapping parent check', merged: true, merged_at: mergedAt, merge_commit_sha: m1 });
    if (key === `commits/${m1}`) return okJson({ sha: m1, parents: [{ sha: p1 }] });
    if (key === `commits/${p1}/check-runs?filter=all&per_page=100`) {
      return okJson({
        check_runs: [
          check('success', mergedAt, 90, 8),
          overlapDone
            ? check('success', later, 91, 8)
            : { id: 91, name: 'suite', app: { id: 8 }, status: 'in_progress', conclusion: null, started_at: '2026-11-16T09:59:00Z', html_url: url('actions/runs', 91) },
        ],
      });
    }
    if (key === `commits/${p1}/statuses?per_page=100`) return okJson([]);
    if (key === `commits/${m1}/check-runs?filter=all&per_page=100`) return okJson({ check_runs: [check('success', later, 92, 8)] });
    if (key === `commits/${m1}/statuses?per_page=100`) return okJson([]);
    if (key === 'issues/81') return okJson({ number: 81, state: 'closed', updated_at: mergedAt, html_url: url('issues', 81) });
    if (key === 'issues/81/timeline?per_page=100') return okJson([]);

    // PR #802: parent initially has no external status; merge fails external status on tick 2 (still absent on parent), then parent posts green external status on tick 3!
    if (key === 'pulls/802') return okJson({ number: 802, title: 'Multi-tick late parent context', merged: true, merged_at: mergedAt, merge_commit_sha: m2 });
    if (key === `commits/${m2}`) return okJson({ sha: m2, parents: [{ sha: p2 }] });
    if (key === `commits/${p2}/check-runs?filter=all&per_page=100`) return okJson({ check_runs: [check('success', mergedAt, 95, 8)] });
    if (key === `commits/${p2}/statuses?per_page=100`) {
      return okJson(lateParentPosted ? [{ id: 96, context: 'ext/deploy', state: 'success', created_at: mergedAt, target_url: url('statuses', 96) }] : []);
    }
    if (key === `commits/${m2}/check-runs?filter=all&per_page=100`) return okJson({ check_runs: [check('success', later, 97, 8)] });
    if (key === `commits/${m2}/statuses?per_page=100`) {
      return okJson([{ id: 98, context: 'ext/deploy', state: 'failure', created_at: later, target_url: url('statuses', 98) }]);
    }
    if (key === 'issues/82') return okJson({ number: 82, state: 'closed', updated_at: mergedAt, html_url: url('issues', 82) });
    if (key === 'issues/82/timeline?per_page=100') return okJson([]);

    if (key.startsWith('commits?since=')) return okJson([]);
    if (key === 'pulls?state=all&sort=updated&direction=desc&per_page=100') return okJson([]);
    assert.fail(`Unexpected endpoint: ${key}`);
  };

  // Tick 1: PR #801 overlapping parent run keeps parentChecked: false & status: pending; PR #802 refreshes parent once and stays suspect
  const t1 = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now, maxRequests: 40, minRecheckMs: 0 });
  assert.equal(t1.state.merges['801'].parentChecked, false);
  assert.equal(t1.state.merges['801'].status, 'pending');
  assert.equal(t1.state.merges['801'].checkedAt, null);
  assert.equal(t1.state.merges['802'].status, 'suspect');

  // Tick 2: parent context STILL absent -> still refreshes once without permanently disabling future refreshes
  const t2 = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now + 1000, maxRequests: 40, minRecheckMs: 0 });
  assert.equal(t2.state.merges['802'].status, 'suspect');

  // Tick 3: overlapping parent run finishes green AND late parent status posts green -> PR #801 verifies ok, PR #802 upgrades to proven ci!
  overlapDone = true;
  lateParentPosted = true;
  const t3 = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now + 2000, maxRequests: 40, minRecheckMs: 0 });
  assert.equal(t3.state.merges['801'].parentChecked, true);
  assert.equal(t3.state.merges['801'].status, 'ok');
  assert.ok(t3.state.merges['801'].checkedAt);
  assert.equal(t3.state.merges['802'].status, 'ci');
  assert.equal(t3.state.merges['802'].classification, 'proven');
  assert.deepEqual(t3.newlyDetected.map(d => `${d.pr}:${d.code}`), ['802:post-merge-ci']);
});


test('checkPostMergeRegressions still detects merged Reverts #N PR when shared commits endpoint returns HTTP 500 (#3182)', async t => {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-post-merge-round6-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const m1 = 'd'.repeat(40), p1 = 'e'.repeat(40);
  fs.writeFileSync(join(root, 'history.jsonl'), JSON.stringify({ at: Date.parse(mergedAt), issue: 91, pr: 901, outcome: 'merged' }) + '\n');

  const okJson = body => ({ code: 0, stdout: `HTTP/2 200 OK\r\n\r\n${JSON.stringify(body)}`, stderr: '' });
  const err500 = () => ({ code: 1, stdout: 'HTTP/2 500 Internal Server Error\r\n\r\n{"message":"boom"}', stderr: 'gh: HTTP 500' });

  const gh = async args => {
    const key = args[4].slice(`repos/${repo}/`.length);
    if (key === 'pulls/901') return okJson({ number: 901, title: 'Feature 901', merged: true, merged_at: mergedAt, merge_commit_sha: m1 });
    if (key === `commits/${m1}`) return okJson({ sha: m1, parents: [{ sha: p1 }] });
    if (key === `commits/${p1}/check-runs?filter=all&per_page=100`) return okJson({ check_runs: [check('success', mergedAt, 100, 9)] });
    if (key === `commits/${p1}/statuses?per_page=100`) return okJson([]);
    if (key === `commits/${m1}/check-runs?filter=all&per_page=100`) return okJson({ check_runs: [check('success', later, 101, 9)] });
    if (key === `commits/${m1}/statuses?per_page=100`) return okJson([]);
    if (key === 'issues/91') return okJson({ number: 91, state: 'closed', updated_at: mergedAt, html_url: url('issues', 91) });
    if (key === 'issues/91/timeline?per_page=100') return okJson([]);
    if (key.startsWith('commits?since=')) return err500();
    if (key === 'pulls?state=all&sort=updated&direction=desc&per_page=100') {
      const longBody = `${'Context details.\n'.repeat(600)}\nReverts #901`;
      return okJson([{ number: 902, title: 'Rollback 901', body: longBody, merged: true, merged_at: later, created_at: later, updated_at: later, html_url: url('pull', 902) }]);
    }
    assert.fail(`Unexpected endpoint: ${key}`);
  };

  const res = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now, maxRequests: 40, minRecheckMs: 0 });
  assert.deepEqual(res.newlyDetected.map(d => `${d.pr}:${d.code}`), ['901:post-merge-revert']);
  assert.equal(res.state.merges['901'].status, 'reverted');
  assert.equal(res.state.merges['901'].classification, 'proven');
  assert.equal(res.state.merges['901'].checkedAt, null, 'incomplete commits stream still withholds checkedAt');
});


test('checkPostMergeRegressions reevaluates red merge checks against newly fetched green parent checks even when parent statuses return HTTP 500 (#3182)', async t => {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-post-merge-round7-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const m1 = 'a'.repeat(40), p1 = 'b'.repeat(40);
  fs.writeFileSync(join(root, 'history.jsonl'), JSON.stringify({ at: Date.parse(mergedAt), issue: 95, pr: 951, outcome: 'merged' }) + '\n');

  let step = 'seed';
  const okJson = body => ({ code: 0, stdout: `HTTP/2 200 OK\r\n\r\n${JSON.stringify(body)}`, stderr: '' });
  const err500 = () => ({ code: 1, stdout: 'HTTP/2 500 Internal Server Error\r\n\r\n{"message":"boom"}', stderr: 'gh: HTTP 500' });
  const namedCheck = (name, conclusion, atIso, id) => ({ ...check(conclusion, atIso, id, 10), name });

  const gh = async args => {
    const key = args[4].slice(`repos/${repo}/`.length);
    if (key === 'pulls/951') return okJson({ number: 951, title: 'Partial late parent refresh', merged: true, merged_at: mergedAt, merge_commit_sha: m1 });
    if (key === `commits/${m1}`) return okJson({ sha: m1, parents: [{ sha: p1 }] });
    if (key === `commits/${p1}/check-runs?filter=all&per_page=100`) {
      if (step === 'seed') return okJson({ check_runs: [namedCheck('base', 'success', mergedAt, 110)] });
      return okJson({ check_runs: [namedCheck('base', 'success', mergedAt, 110), namedCheck('late-suite', 'success', mergedAt, 111)] });
    }
    if (key === `commits/${p1}/statuses?per_page=100`) {
      return step === 'partial-refresh' ? err500() : okJson([]);
    }
    if (key === `commits/${m1}/check-runs?filter=all&per_page=100`) {
      if (step === 'partial-refresh') return okJson({ check_runs: [namedCheck('base', 'success', later, 112), namedCheck('late-suite', 'failure', later, 113)] });
      return okJson({ check_runs: [namedCheck('base', 'success', later, 112), namedCheck('late-suite', 'success', later, 114)] });
    }
    if (key === `commits/${m1}/statuses?per_page=100`) return okJson([]);
    if (key === 'issues/95') return okJson({ number: 95, state: 'closed', updated_at: mergedAt, html_url: url('issues', 95) });
    if (key === 'issues/95/timeline?per_page=100') return okJson([]);
    if (key.startsWith('commits?since=')) return okJson([]);
    if (key === 'pulls?state=all&sort=updated&direction=desc&per_page=100') return okJson([]);
    assert.fail(`Unexpected endpoint: ${key}`);
  };

  // 1) Seed healthy state without late-suite.
  await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now, maxRequests: 40, minRecheckMs: 0 });

  // 2) Merge fails late-suite; late parent refresh gets green late-suite check-run + statuses HTTP 500 -> MUST still prove CI regression immediately!
  step = 'partial-refresh';
  const s2 = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now + 1000, maxRequests: 40, minRecheckMs: 0 });
  assert.deepEqual(s2.newlyDetected.map(d => `${d.pr}:${d.code}`), ['951:post-merge-ci']);
  assert.equal(s2.state.merges['951'].status, 'ci');
  assert.equal(s2.state.merges['951'].classification, 'proven');

  // 3) Merge reruns green -> proven CI regression remains recorded!
  step = 'rerun-green';
  const s3 = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now + 2000, maxRequests: 40, minRecheckMs: 0 });
  assert.equal(s3.state.merges['951'].status, 'ci');
  assert.equal(s3.state.merges['951'].classification, 'proven');
});


test('checkPostMergeRegressions rotates cursor across later merges when shared commits returns HTTP 500 so later reopens are never starved (#3182)', async t => {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-post-merge-round9-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const shas = {
    1001: ['1'.repeat(40), '2'.repeat(40)],
    1002: ['3'.repeat(40), '4'.repeat(40)],
    1003: ['5'.repeat(40), '6'.repeat(40)],
  };
  fs.writeFileSync(
    join(root, 'history.jsonl'),
    [
      { at: Date.parse(mergedAt), issue: 101, pr: 1001, outcome: 'merged' },
      { at: Date.parse(mergedAt), issue: 102, pr: 1002, outcome: 'merged' },
      { at: Date.parse(mergedAt), issue: 103, pr: 1003, outcome: 'merged' },
    ].map(r => JSON.stringify(r)).join('\n') + '\n',
  );

  let commitsFail = true;
  const okJson = body => ({ code: 0, stdout: `HTTP/2 200 OK\r\n\r\n${JSON.stringify(body)}`, stderr: '' });
  const err500 = () => ({ code: 1, stdout: 'HTTP/2 500 Internal Server Error\r\n\r\n{"message":"boom"}', stderr: 'gh: HTTP 500' });

  const gh = async args => {
    const key = args[4].slice(`repos/${repo}/`.length);
    for (const [prStr, [mSha, pSha]] of Object.entries(shas)) {
      const prNum = Number(prStr);
      const issueNum = prNum - 900;
      if (key === `pulls/${prNum}`) return okJson({ number: prNum, title: `PR ${prNum}`, merged: true, merged_at: mergedAt, merge_commit_sha: mSha });
      if (key === `commits/${mSha}`) return okJson({ sha: mSha, parents: [{ sha: pSha }] });
      if (key === `commits/${pSha}/check-runs?filter=all&per_page=100`) return okJson({ check_runs: [check('success', mergedAt, prNum, 11)] });
      if (key === `commits/${pSha}/statuses?per_page=100`) return okJson([]);
      if (key === `commits/${mSha}/check-runs?filter=all&per_page=100`) return okJson({ check_runs: [check('success', later, prNum + 10, 11)] });
      if (key === `commits/${mSha}/statuses?per_page=100`) return okJson([]);
      if (key === `issues/${issueNum}`) {
        return okJson({ number: issueNum, state: issueNum === 102 ? 'open' : 'closed', updated_at: later, html_url: url('issues', issueNum) });
      }
      if (key === `issues/${issueNum}/timeline?per_page=100`) {
        return okJson(issueNum === 102 ? [{ id: 500, event: 'reopened', created_at: later, actor: { login: 'dev' } }] : []);
      }
    }
    if (key.startsWith('commits?since=')) return commitsFail ? err500() : okJson([]);
    if (key === 'pulls?state=all&sort=updated&direction=desc&per_page=100') return okJson([]);
    assert.fail(`Unexpected endpoint: ${key}`);
  };

  // Tick 1 checks PR #1001; shared commits 500 withholds checkedAt while rotating cursor to 1!
  const t1 = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now, maxMerges: 1, maxRequests: 40, minRecheckMs: 60_000 });
  assert.equal(t1.state.cursor, 1);
  assert.equal(t1.state.merges['1001'].checkedAt, null);

  // Tick 2 rotates to PR #1002 even while shared commits still returns 500 -> detects issue #102 reopen immediately!
  const t2 = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now + 1000, maxMerges: 1, maxRequests: 40, minRecheckMs: 60_000 });
  assert.deepEqual(t2.newlyDetected.map(d => `${d.pr}:${d.code}`), ['1002:post-merge-reopen']);
  assert.equal(t2.state.cursor, 2);

  // Tick 3 checks PR #1003 and wraps cursor back to 0; Tick 4 with healthy commits verifies PR #1001!
  const t3 = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now + 2000, maxMerges: 1, maxRequests: 40, minRecheckMs: 60_000 });
  assert.equal(t3.state.cursor, 0);
  commitsFail = false;
  const t4 = await checkPostMergeRegressions({ root, repo, fs, gh, now: () => now + 3000, maxMerges: 1, maxRequests: 40, minRecheckMs: 60_000 });
  assert.equal(t4.state.merges['1001'].status, 'ok');
  assert.ok(t4.state.merges['1001'].checkedAt);
});
