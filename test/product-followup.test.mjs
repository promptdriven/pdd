import test from 'node:test';
import assert from 'node:assert/strict';
import { cpSync, mkdtempSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { productStart, productStatus, runProduct } from '../src/product.mjs';

const marker = run => `<!-- pdd-product: run=${run} -->`;
const issue = (run, number, extra = {}) => ({ number, body: marker(run), user: { login: 'maintainer' }, author_association: 'MEMBER', created_at: '2026-10-01T00:00:00Z', state: 'OPEN', ...extra });
function setup(t) {
  const cwd = mkdtempSync(join(tmpdir(), 'pdd-followup-'));
  t.after(() => rmSync(cwd, { recursive: true, force: true }));
  cpSync(new URL('../examples/coffee-pickup/', import.meta.url), cwd, { recursive: true });
  const git = (...args) => execFileSync('git', args, { cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  git('init', '-q', '-b', 'release'); git('config', 'user.name', 'Test'); git('config', 'user.email', 'test@example.invalid');
  git('add', '.'); git('commit', '-qm', 'base');
  const s = { issues: [], indexed: null, runs: [], searches: [], direct: [], creates: [], starts: [], actors: 0, prs: [], events: {} };
  const ports = {
    resolveRepository: async () => ({ repository: 'example/coffee', defaultBranch: 'release' }),
    listRuns: async () => s.runs,
    planOnBase: async () => true,
    storyEvidence: async record => record.rows ?? [],
    issuePage: async args => { s.searches.push(args); const rows = (s.indexed ?? s.issues).filter(row => row.body.includes(args.marker)); return { items: rows.slice((args.page - 1) * args.perPage, args.page * args.perPage), total_count: rows.length, incomplete_results: false }; },
    issueByNumber: async args => { s.direct.push(args.number); return s.issues.find(row => row.number === args.number); },
    currentActor: async () => { s.actors++; if (s.actorError) throw Error('account unavailable'); return s.actorReply ?? { login: 'person' }; },
    createIssue: async payload => { s.creates.push(payload); const row = issue('unused', 200 + s.creates.length, { body: payload.body }); s.issues.push(row); return { url: `https://github.com/example/coffee/issues/${row.number}` }; },
    startRun: async args => { s.starts.push(args); return { exitCode: 0, message: 'Started.' }; },
    timelinePage: async ({ issue }) => s.events[issue] ?? [],
    pullRequest: async ({ number }) => s.prs.find(row => row.number === number),
    execFile: async (file, args, options) => { assert.equal(file, 'git', 'all GitHub reads use their raw fake ports'); try { return { stdout: execFileSync(file, args, { ...options, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }) }; } catch (error) { return { stdout: '', code: error.status, stderr: String(error.stderr) }; } },
  };
  return { cwd, s, ports };
}

test('an issue prepared before indexing is reused and bound before launching the workflow', async t => {
  const f = setup(t); f.s.indexed = [];
  const prepared = await productStart({ cwd: f.cwd, run: 'phone-1', noRun: true }, f.ports);
  assert.equal(prepared.exitCode, 0);
  const before = f.s.searches.length;
  const started = await productStart({ cwd: f.cwd, run: 'phone-1' }, f.ports);
  assert.equal(started.issue, prepared.issue, 'search lag must not create a second issue');
  assert.equal(f.s.creates.length, 1); assert.deepEqual(f.s.starts.map(row => row.issue), [prepared.issue]);
  assert.ok(f.s.direct.includes(prepared.issue), 'saved binding is checked through ordinary issue lookup');
  assert.equal(f.s.searches.length, before, 'saved binding takes precedence over any search');
});

test('a trusted candidate with a saved feature run wins over an older duplicate', async t => {
  const f = setup(t);
  f.s.issues = [issue('phone-1', 80), issue('phone-1', 90, { created_at: '2026-10-02T00:00:00Z' })];
  f.s.runs = [{ workflow: 'feature', number: 90, state: 'running', branch: 'feature-90', rows: [{ story: 'P01-menu', pass: true, current: true, at: 1 }] }];
  const status = await productStatus({ cwd: f.cwd }, f.ports);
  assert.equal(status.runs.find(row => row.run === 'phone-1').issue, 90);
  assert.equal(status.parts.find(row => row.part === 'phone').pass, 1);
});

test('a complete issue snapshot is shared by all planned runs and reused by a later command', async t => {
  const f = setup(t); f.s.issues = [issue('phone-1', 80)];
  assert.equal((await runProduct({ command: 'status', cwd: f.cwd }, f.ports)).exitCode, 0);
  assert.equal(f.s.searches.length, 1, 'all planned markers share one prefix search');
  assert.ok(f.s.searches.every(args => args.perPage <= 10));
  assert.equal((await runProduct({ command: 'next', cwd: f.cwd }, f.ports)).exitCode, 0);
  assert.equal(f.s.searches.length, 1, 'recent complete raw search is reusable');
  assert.ok(f.s.direct.includes(80), 'cached selected issue is revalidated');
});

for (const mode of ['failed', 'malformed']) test(`${mode} account lookup leaves outsiders untrusted and all commands usable`, async t => {
  const f = setup(t); f.s.actorError = mode === 'failed'; f.s.actorReply = {};
  f.s.issues = [issue('journeys', 75, { author_association: 'NONE', user: { login: 'outsider' } }), issue('barista-1', 76, { author_association: 'NONE', user: { login: 'outsider' } })];
  for (const command of ['status', 'next', 'start']) {
    const before = f.s.actors;
    const out = await runProduct({ command, cwd: f.cwd, run: 'phone-1', noRun: true }, f.ports);
    assert.equal(out.exitCode, 0, `${command}: unavailable account must not abort the command`);
    assert.ok(f.s.actors - before <= 1, 'unavailable identity is memoized within a command');
  }
  assert.equal(f.s.creates.length, 1); assert.equal(f.s.starts.length, 0);
});

test('normal cross references to another product run stay quiet', async t => {
  const f = setup(t); f.s.issues = [issue('server-1', 80)];
  f.s.events[80] = [{ event: 'cross-referenced', source: { issue: { pull_request: { html_url: 'https://github.com/example/coffee/pull/30' } } } }];
  f.s.prs = [{ number: 30, url: 'https://github.com/example/coffee/pull/30', body: marker('phone-1'), state: 'MERGED', isCrossRepository: false, headRepository: { name: 'coffee' }, headRepositoryOwner: { login: 'example' } }];
  const status = await productStatus({ cwd: f.cwd }, f.ports);
  assert.deepEqual(status.runs.find(row => row.run === 'server-1').prs, []);
  assert.equal((status.warnings ?? []).some(text => /could not be verified/.test(text)), false);
});

test('human status explains the actual local comparison branch and how to update it', async t => {
  const f = setup(t);
  f.s.issues = [issue('phone-1', 80)];
  f.s.runs = [{ workflow: 'feature', number: 80, state: 'completed', branch: 'feature-80', baseBranch: 'release' }];
  f.s.events[80] = [{ event: 'cross-referenced', source: { issue: { pull_request: { html_url: 'https://github.com/example/coffee/pull/30' } } } }];
  f.s.prs = [{ number: 30, url: 'https://github.com/example/coffee/pull/30', body: marker('phone-1') + '\n<!-- pdd-workflow:own:code -->', state: 'MERGED', isCrossRepository: false, headRepository: { name: 'coffee' }, headRepositoryOwner: { login: 'example' } }];
  const status = await runProduct({ command: 'status', cwd: f.cwd }, f.ports);
  assert.equal(status.exitCode, 0);
  assert.match(status.message, /local.*release/i); assert.match(status.message, /git pull/);
});
