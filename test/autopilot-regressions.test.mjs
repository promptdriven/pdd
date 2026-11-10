import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { regressionScan, runAutopilotRegressions } from '../src/autopilot-regressions.mjs';
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
