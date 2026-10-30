import test from 'node:test';
import assert from 'node:assert/strict';
import { cpSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync, spawn, spawnSync } from 'node:child_process';
import { productStart, productStatus, runProduct } from '../src/product.mjs';

const marker = run => `<!-- pdd-product: run=${run} -->`;
const issue = (run, number, extra = {}) => ({ number, body: marker(run), user: { login: 'maintainer' }, author_association: 'MEMBER', created_at: '2026-10-01T00:00:00Z', state: 'OPEN', ...extra });
function setup(t) {
  const cwd = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-last-fixes-')));
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


function saved(f, bindings, search) {
  let json = JSON.stringify({ version: 1, repository: 'example/coffee', productRoot: f.cwd, bindings, ...(search ? { search } : {}) });
  f.ports.readProductState = async () => ({ json });
  f.ports.writeProductState = async input => { json = input.json; return {}; };
  return () => JSON.parse(json);
}

test('a delayed search preserves the newer complete cache committed by another command', async t => {
  const f = setup(t), state = saved(f, []);
  let clock = 100000, release, entered;
  const waiting = new Promise(resolve => { entered = resolve; });
  const gate = new Promise(resolve => { release = resolve; });
  f.ports.now = async () => ({ milliseconds: clock });
  f.ports.issuePage = async () => { entered(); await gate; return { items: [], total_count: 0, incomplete_results: false }; };
  const older = productStatus({ cwd: f.cwd }, f.ports);
  await waiting;
  clock = 100001;
  await productStatus({ cwd: f.cwd }, { ...f.ports, issuePage: async () => ({ items: [], total_count: 0, incomplete_results: false }) });
  assert.deepEqual(state().search, { at: 100001, items: [] });
  release(); await older;
  assert.deepEqual(state().search, { at: 100001, items: [] }, 'older search cannot overwrite the newer complete snapshot');
});

test('a genuinely future-dated cache is replaced by the complete current search', async t => {
  const f = setup(t), state = saved(f, [], { at: 900000, items: [issue('phone-1', 80)] });
  f.ports.now = async () => ({ milliseconds: 100001 });
  await productStatus({ cwd: f.cwd }, f.ports);
  assert.deepEqual(state().search, { at: 100001, items: [] });
  assert.equal(f.s.searches.length, 1);
});
for (const mode of ['404', 'wrong-marker', 'untrusted', 'transport', 'malformed', 'actor-unavailable']) {
  test(`saved ${mode} issue isolates only its own run`, async t => {
    const f = setup(t), state = saved(f, [{ run: 'phone-1', issue: 80 }]);
    const raw = mode === '404' ? { status: 404, message: 'Not Found' }
      : mode === 'wrong-marker' ? issue('server-1', 80)
      : mode === 'malformed' ? { number: 80 }
      : issue('phone-1', 80, ['untrusted', 'actor-unavailable'].includes(mode) ? { author_association: 'NONE', user: { login: 'outsider' } } : {});
    f.ports.issueByNumber = async () => { if (mode === 'transport') throw Error('HTTP 404 in an unstructured transport message'); return raw; };
    f.s.actorError = mode === 'actor-unavailable';
    f.s.runs = [{ workflow: 'feature', number: 80, productMarker: marker('phone-1'), state: 'completed', rows: [{ story: 'P01-menu', pass: true, current: true }] }];
    const result = await runProduct({ command: 'status', cwd: f.cwd, json: true }, f.ports);
    assert.equal(result.exitCode, 0, result.message);
    const out = JSON.parse(result.message), row = out.runs.find(row => row.run === 'phone-1');
    assert.equal(row.state, 'unverified');
    assert.equal(out.parts.find(row => row.part === 'phone').pass, 0);
    assert.ok(!out.ready.includes('phone-1'));
    assert.match(out.warnings.join(' '), /pdd product start phone-1/);
    assert.equal((await runProduct({ command: 'next', cwd: f.cwd }, f.ports)).exitCode, 0);
    assert.equal((await productStart({ cwd: f.cwd, run: 'server-1', noRun: true }, f.ports)).exitCode, 0);
    const target = await productStart({ cwd: f.cwd, run: 'phone-1', noRun: true }, f.ports);
    const confirmed = ['404', 'wrong-marker', 'untrusted'].includes(mode);
    assert.equal(target.exitCode, confirmed ? 0 : 1, target.message);
    assert.equal(f.s.creates.length, confirmed ? 2 : 1);
    assert.equal(state().bindings.find(row => row.run === 'phone-1')?.issue, confirmed ? target.issue : 80);
  });
}
test('a stale cached issue cannot abort unrelated status or start', async t => {
  const f = setup(t);
  saved(f, [], { at: 100000, items: [issue('phone-1', 80)] });
  f.ports.now = async () => ({ milliseconds: 100001 });
  f.ports.issueByNumber = async () => ({ status: 404, message: 'Not Found' });
  const out = await runProduct({ command: 'status', cwd: f.cwd, json: true }, f.ports);
  assert.equal(out.exitCode, 0, out.message);
  assert.equal(JSON.parse(out.message).runs.find(row => row.run === 'phone-1').state, 'unverified');
  assert.equal((await productStart({ cwd: f.cwd, run: 'server-1', noRun: true }, f.ports)).exitCode, 0);
});

test('actual Git worktrees share a prepared issue through search-index lag', async t => {
  const f = setup(t); f.s.indexed = [];
  const prepared = await productStart({ cwd: f.cwd, run: 'phone-1', noRun: true }, f.ports);
  assert.equal(prepared.exitCode, 0);
  const sibling = join(f.cwd, 'sibling');
  execFileSync('git', ['worktree', 'add', '--detach', sibling, 'HEAD'], { cwd: f.cwd, stdio: 'pipe' });
  const out = await productStart({ cwd: realpathSync(sibling), run: 'phone-1', noRun: true }, f.ports);
  assert.equal(out.issue, prepared.issue, 'physical common dir owns the binding');
  assert.equal(f.s.creates.length, 1);
});

test('legacy folder-key state migrates when first read from a sibling worktree', async t => {
  const f = setup(t); f.s.indexed = []; f.s.issues = [issue('phone-1', 80)];
  const { createHash } = await import('node:crypto');
  const dir = join(f.cwd, '.git/pdd/products'); mkdirSync(dir, { recursive: true });
  const key = createHash('sha256').update(`example/coffee\0${f.cwd}`).digest('hex');
  writeFileSync(join(dir, `${key}.json`), JSON.stringify({ version: 1, repository: 'example/coffee', productRoot: f.cwd, bindings: [{ run: 'phone-1', issue: 80 }] }));
  const sibling = join(f.cwd, 'sibling');
  execFileSync('git', ['worktree', 'add', '--detach', sibling, 'HEAD'], { cwd: f.cwd, stdio: 'pipe' });
  const out = await productStart({ cwd: realpathSync(sibling), run: 'phone-1', noRun: true }, f.ports);
  assert.equal(out.issue, 80); assert.equal(f.s.creates.length, 0);
});

test('an unrelated stale writer cannot restore a concurrently deleted dead binding', async t => {
  const f = setup(t), state = saved(f, [{ run: 'phone-1', issue: 80 }]);
  f.s.issues = [issue('phone-1', 80)];
  let release, entered;
  const waiting = new Promise(resolve => { entered = resolve; });
  const gate = new Promise(resolve => { release = resolve; });
  const create = f.ports.createIssue;
  f.ports.createIssue = async args => { entered(); await gate; return create(args); };
  const starting = productStart({ cwd: f.cwd, run: 'server-1', noRun: true }, f.ports);
  await waiting;
  f.ports.issueByNumber = async () => ({ status: 404, message: 'Not Found' });
  const invalidated = await runProduct({ command: 'status', cwd: f.cwd }, f.ports);
  release();
  const started = await starting;
  assert.equal(invalidated.exitCode, 0, invalidated.message);
  assert.equal(started.exitCode, 0, started.message);
  assert.equal(state().bindings.some(row => row.run === 'phone-1'), false);
  assert.equal(state().bindings.find(row => row.run === 'server-1').issue, started.issue);
});

test('two actual parallel CLI starts preserve both links without holding the state lock during creation', async t => {
  const f = setup(t), bin = join(f.cwd, 'fake-bin'); mkdirSync(bin);
  const data = join(bin, 'issues'); mkdirSync(data);
  execFileSync('git', ['remote', 'add', 'origin', 'https://github.com/example/coffee.git'], { cwd: f.cwd });
  writeFileSync(join(bin, 'gh'), `#!/usr/bin/env node
const fs = require('node:fs'), path = require('node:path'), a = process.argv.slice(2), data = ${JSON.stringify(data)};
if (a[0] === 'repo') process.stdout.write(JSON.stringify({nameWithOwner:'example/coffee',defaultBranchRef:{name:'release'},url:'https://github.com/example/coffee'}));
else if (a[0] === 'issue' && a[1] === 'create') {
 const body = a[a.indexOf('--body')+1], number = body.includes('run=phone-1') ? 201 : 202;
 fs.writeFileSync(path.join(data, number + '.ready'), 'ready');
 const end = Date.now() + 10000;
 while (!(fs.existsSync(path.join(data, '201.ready')) && fs.existsSync(path.join(data, '202.ready')))) {
  if (Date.now() > end) { process.stderr.write('creation barrier timed out: network held under state lock'); process.exit(2); }
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 10);
 }
 fs.writeFileSync(path.join(data, number+'.json'), JSON.stringify({number,body,user:{login:'member'},author_association:'MEMBER',created_at:'2026-10-01T00:00:00Z'}));
 process.stdout.write('https://github.com/example/coffee/issues/'+number);
} else if (a[1]?.startsWith('search/issues?')) process.stdout.write(JSON.stringify({items:[],total_count:0,incomplete_results:false}));
else if (a[1]?.includes('/timeline?')) process.stdout.write('[]');
else if (/\\/issues\\/\\d+$/.test(a[1] ?? '')) process.stdout.write(fs.readFileSync(path.join(data,a[1].split('/').at(-1)+'.json')));
else { process.stderr.write('Unexpected gh: '+JSON.stringify(a)); process.exit(2); }
`, { mode: 0o755 });
  const cli = new URL('../bin/pdd.mjs', import.meta.url).pathname;
  const invoke = run => new Promise(resolve => {
    const child = spawn(process.execPath, [cli, 'product', 'start', run, '--no-run'], { cwd: f.cwd, env: { ...process.env, HOME: f.cwd, PATH: `${bin}:${process.env.PATH}` } });
    let stdout = '', stderr = ''; child.stdout.on('data', chunk => stdout += chunk); child.stderr.on('data', chunk => stderr += chunk);
    child.on('close', code => resolve({ code, stdout, stderr }));
  });
  const results = await Promise.all([invoke('phone-1'), invoke('server-1')]);
  for (const out of results) assert.equal(out.code, 0, out.stderr + out.stdout);
  const dir = join(f.cwd, '.git/pdd/products');
  const states = readdirSync(dir).filter(name => name.endsWith('.json')).map(name => JSON.parse(readFileSync(join(dir, name), 'utf8')));
  const bindings = states.flatMap(state => state.bindings);
  assert.ok(bindings.some(row => row.run === 'phone-1' && row.issue === 201), 'phone link survives concurrent server start');
  assert.ok(bindings.some(row => row.run === 'server-1' && row.issue === 202), 'server link survives concurrent phone start');
});

test('discarding observed dead issue 80 preserves a concurrently replaced issue 81', async t => {
  const f = setup(t), state = saved(f, [{ run: 'phone-1', issue: 80 }]);
  f.ports.issueByNumber = async ({ number }) => {
    if (number === 80) {
      await f.ports.writeProductState({ json: JSON.stringify({ ...state(), bindings: [{ run: 'phone-1', issue: 81 }] }) });
      return { status: 404, message: 'Not Found' };
    }
    return issue('phone-1', 81);
  };
  const out = await runProduct({ command: 'status', cwd: f.cwd }, f.ports);
  assert.equal(out.exitCode, 0, out.message);
  assert.equal(state().bindings.find(row => row.run === 'phone-1')?.issue, 81);
});

test('an authoritative v2 deletion never reimports the untouched legacy file', async t => {
  const f = setup(t); f.s.indexed = []; f.s.issues = [issue('phone-1', 80)];
  const { createHash } = await import('node:crypto');
  const dir = join(f.cwd, '.git/pdd/products'); mkdirSync(dir, { recursive: true });
  const key = createHash('sha256').update(`example/coffee\0${f.cwd}`).digest('hex');
  writeFileSync(join(dir, `${key}.json`), JSON.stringify({ version: 1, repository: 'example/coffee', productRoot: f.cwd, bindings: [{ run: 'phone-1', issue: 80 }] }));
  assert.equal((await productStart({ cwd: f.cwd, run: 'phone-1', noRun: true }, f.ports)).issue, 80);
  const rawLookup = f.ports.issueByNumber;
  f.ports.issueByNumber = async () => ({ status: 404, message: 'Not Found' });
  assert.equal((await runProduct({ command: 'status', cwd: f.cwd }, f.ports)).exitCode, 0);
  f.ports.issueByNumber = rawLookup;
  const before = f.s.direct.length;
  const status = await productStatus({ cwd: f.cwd }, f.ports);
  assert.equal(status.runs.find(row => row.run === 'phone-1').issue, null);
  assert.equal(f.s.direct.length, before, 'v2 empty binding is authoritative over still-present v1 hint');
});

for (const status of [404, 503]) test(`default issue adapter retains the actual HTTP ${status} status`, async t => {
  const f = setup(t), state = saved(f, [{ run: 'phone-1', issue: 80 }]);
  delete f.ports.issueByNumber;
  const git = f.ports.execFile;
  f.ports.execFile = async (file, args, options) => {
    if (file === 'git') return git(file, args, options);
    assert.equal(file, 'gh'); assert.ok(args.includes('--include'));
    throw Object.assign(Error('nonzero gh response'), { code: 1, stdout: `HTTP/2.0 ${status} Failure\r\ncontent-type: application/json\r\n\r\n{"message":"lookup failed"}` });
  };
  const out = await runProduct({ command: 'status', cwd: f.cwd, json: true }, f.ports);
  assert.equal(out.exitCode, 0, out.message);
  assert.equal(JSON.parse(out.message).runs.find(row => row.run === 'phone-1').state, 'unverified');
  assert.equal(state().bindings.some(row => row.run === 'phone-1'), status !== 404);
});
