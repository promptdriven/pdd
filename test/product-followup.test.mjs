import test from 'node:test';
import assert from 'node:assert/strict';
import { cpSync, mkdirSync, mkdtempSync, realpathSync, readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync, spawnSync } from 'node:child_process';
import { productStart, productStatus, runProduct } from '../src/product.mjs';

const marker = run => `<!-- pdd-product: run=${run} -->`;
const issue = (run, number, extra = {}) => ({ number, body: marker(run), user: { login: 'maintainer' }, author_association: 'MEMBER', created_at: '2026-10-01T00:00:00Z', state: 'OPEN', ...extra });
function setup(t) {
  const cwd = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-followup-')));
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

test('a saved binding cannot hide a trusted own-marker feature record on another issue', async t => {
  const f = setup(t);
  f.s.issues = [issue('phone-1', 201), issue('phone-1', 202, { created_at: '2026-10-02T00:00:00Z' })];
  let json = JSON.stringify({ version: 1, repository: 'example/coffee', productRoot: f.cwd, bindings: [{ run: 'phone-1', issue: 201 }] });
  f.ports.readProductState = async () => ({ json }); f.ports.writeProductState = async args => { json = args.json; return {}; };
  f.s.runs = [{ workflow: 'feature', number: 202, productMarker: marker('phone-1'), state: 'running' }];
  const out = await productStart({ cwd: f.cwd, run: 'phone-1', noRun: true }, f.ports);
  assert.equal(out.issue, 202); assert.equal(f.s.searches.length, 0);
  assert.equal(JSON.parse(json).bindings.find(row => row.run === 'phone-1').issue, 202);
});

test('unavailable account on a bound self exception keeps only an unverified hint', async t => {
  const f = setup(t); f.s.actorError = true;
  f.s.issues = [issue('phone-1', 80, { author_association: 'NONE', user: { login: 'person' } })];
  f.s.runs = [{ workflow: 'feature', number: 80, productMarker: marker('phone-1'), state: 'completed', rows: [{ story: 'P01-menu', pass: true, current: true }] }];
  let timelines = 0, evidence = 0;
  f.ports.timelinePage = async () => { timelines++; return []; }; f.ports.storyEvidence = async () => { evidence++; return []; };
  const status = await productStatus({ cwd: f.cwd }, f.ports);
  assert.equal(status.runs.find(row => row.run === 'phone-1').state, 'unverified');
  assert.equal(status.runs.find(row => row.run === 'phone-1').issue, 80);
  assert.equal(status.parts.find(row => row.part === 'phone').pass, 0);
  assert.ok(!status.ready.includes('phone-1')); assert.equal(timelines, 0); assert.equal(evidence, 0);
  const next = await runProduct({ command: 'next', cwd: f.cwd }, f.ports); assert.equal(next.exitCode, 0);
  const before = f.s.searches.length;
  const start = await productStart({ cwd: f.cwd, run: 'phone-1' }, f.ports);
  assert.equal(start.exitCode, 1); assert.equal(start.issue, 80); assert.equal(f.s.searches.length, before);
  assert.equal(f.s.creates.length, 0); assert.equal(f.s.starts.length, 0);
});

test('confirmed invalid saved issues can relink while unknown replies fail closed', async t => {
  for (const mode of ['foreign-marker', 'number', 'untrusted', 'transport']) {
    const f = setup(t);
    f.ports.readProductState = async () => ({ json: JSON.stringify({ version: 1, repository: 'example/coffee', productRoot: f.cwd, bindings: [{ run: 'phone-1', issue: 80 }] }) });
    f.ports.issueByNumber = async () => { if (mode === 'transport') throw Error('not accessible'); return issue(mode === 'foreign-marker' ? 'server-1' : 'phone-1', mode === 'number' ? 81 : 80, mode === 'untrusted' ? { author_association: 'NONE', user: { login: 'outsider' } } : {}); };
    const out = await productStart({ cwd: f.cwd, run: 'phone-1', noRun: true }, f.ports);
    const confirmed = ['foreign-marker', 'untrusted'].includes(mode);
    assert.equal(out.exitCode, confirmed ? 0 : 1, mode);
    assert.equal(f.s.creates.length, confirmed ? 1 : 0); assert.equal(f.s.starts.length, 0);
    assert.equal(f.s.searches.length, confirmed ? 1 : 0);
  }
});

test('a failed binding write reports the created issue and stops before workflow startup', async t => {
  const f = setup(t); let writes = 0;
  f.ports.writeProductState = async () => { if (++writes === 2) throw Error('disk full'); return {}; };
  const out = await productStart({ cwd: f.cwd, run: 'phone-1' }, f.ports);
  assert.equal(out.exitCode, 1); assert.equal(out.issue, 201); assert.equal(out.created, true);
  assert.equal(f.s.creates.length, 1); assert.equal(f.s.starts.length, 0);
});

test('cache age boundaries and cached negatives require at most one fresh query', async t => {
  for (const [age, expected] of [[0, 0], [59999, 0], [60000, 1], [-1, 1]]) {
    const f = setup(t); f.s.issues = [issue('phone-1', 80)];
    let json = JSON.stringify({ version: 1, repository: 'example/coffee', productRoot: f.cwd, bindings: [], search: { at: 100000 - age, items: f.s.issues } });
    f.ports.now = async () => ({ milliseconds: 100000 });
    f.ports.readProductState = async () => ({ json }); f.ports.writeProductState = async args => { json = args.json; return {}; };
    const out = await productStatus({ cwd: f.cwd }, f.ports);
    assert.equal(out.runs.find(row => row.run === 'phone-1').issue, 80); assert.equal(f.s.searches.length, expected, `age ${age}`);
  }
  const f = setup(t);
  f.ports.now = async () => ({ milliseconds: 100000 });
  f.ports.readProductState = async () => ({ json: JSON.stringify({ version: 1, repository: 'example/coffee', productRoot: f.cwd, bindings: [], search: { at: 99999, items: [] } }) });
  const out = await productStart({ cwd: f.cwd, run: 'phone-1', noRun: true }, f.ports);
  assert.equal(out.created, true); assert.equal(f.s.searches.length, 1);
});

test('separate CLI processes persist a paginated snapshot and a newly prepared issue despite search lag and unavailable actor', t => {
  const f = setup(t), bin = join(f.cwd, 'fake-bin'), log = join(bin, 'calls.jsonl'), created = join(bin, 'created.json');
  mkdirSync(bin);
  execFileSync('git', ['remote', 'add', 'origin', 'https://github.com/example/coffee.git'], { cwd: f.cwd });
  writeFileSync(join(bin, 'gh'), `#!/usr/bin/env node
const fs = require('node:fs'), a = process.argv.slice(2), log = ${JSON.stringify(log)}, saved = ${JSON.stringify(created)};
fs.appendFileSync(log, JSON.stringify(a) + '\\n');
const marker = run => '<!-- pdd-product: run=' + run + ' -->';
if (a[0] === 'repo') process.stdout.write(JSON.stringify({nameWithOwner:'example/coffee',defaultBranchRef:{name:'release'},url:'https://github.com/example/coffee'}));
else if (a[0] === 'issue' && a[1] === 'create') {
  fs.writeFileSync(saved, JSON.stringify({number:201,body:a[a.indexOf('--body')+1],user:{login:'maintainer'},author_association:'MEMBER',created_at:'2026-10-01T00:00:00Z'}));
  process.stdout.write('https://github.com/example/coffee/issues/201');
} else if (a[0] === 'api' && a[1] === 'user') { process.stderr.write('HTTP 403: account unavailable'); process.exit(1); }
else if (a[1].startsWith('search/issues?')) {
  const q = new URL('https://api.github.com/' + a[1]).searchParams, page = Number(q.get('page')), size = Number(q.get('per_page'));
  const rows = Array.from({length:11}, (_,i) => ({number:80+i,body:marker('journeys'),user:{login:'outsider'},author_association:'NONE',created_at:'2026-10-01T00:00:00Z'}));
  process.stdout.write(JSON.stringify({items:rows.slice((page-1)*size,page*size),total_count:rows.length,incomplete_results:false}));
} else if (a[1].endsWith('/issues/201')) process.stdout.write(fs.readFileSync(saved));
else if (a[1].includes('/timeline?')) process.stdout.write('[]');
else { process.stderr.write('Unexpected gh call: ' + JSON.stringify(a)); process.exit(2); }
`, { mode: 0o755 });
  const cli = new URL('../bin/pdd.mjs', import.meta.url).pathname;
  const invoke = args => {
    const reply = spawnSync(process.execPath, [cli, 'product', ...args], { cwd: f.cwd, encoding: 'utf8', env: { ...process.env, HOME: f.cwd, PATH: `${bin}:${process.env.PATH}` } });
    assert.equal(reply.status, 0, `${args}: ${reply.stderr} ${reply.stdout}`); return reply.stdout;
  };
  invoke(['status']); invoke(['next']);
  assert.match(invoke(['start', 'phone-1', '--no-run']), /Issue #201/);
  assert.match(invoke(['start', 'phone-1', '--no-run']), /Issue #201/);
  const calls = readFileSync(log, 'utf8').trim().split('\n').map(JSON.parse);
  const searches = calls.filter(args => args[1]?.startsWith('search/issues?'));
  assert.equal(searches.length, 4, 'one two-page query for status, none for next, one fresh negative refresh before creation, none after binding');
  assert.equal(calls.filter(args => args[0] === 'issue').length, 1);
  assert.equal(calls.filter(args => args[1] === 'user').length, 3, 'unavailable actor is memoized across eleven claims in each of three searching commands');
  assert.ok(calls.some(args => args[1]?.endsWith('/issues/201')));
  for (const args of searches) {
    const query = new URL('https://api.github.com/' + args[1]).searchParams;
    assert.equal(query.get('per_page'), '10'); assert.match(query.get('q'), /in:body.*<!-- pdd-product: run=/);
    assert.ok(args.includes('--jq')); assert.match(args.at(-1), /author_association/);
    assert.equal(args.includes('--paginate') || args.includes('--slurp'), false);
  }
  const stateFiles = readdirSync(join(f.cwd, '.git/pdd/products'));
  assert.equal(stateFiles.length, 1); assert.ok(stateFiles[0].endsWith('.json'));
  const state = JSON.parse(readFileSync(join(f.cwd, '.git/pdd/products', stateFiles[0]), 'utf8'));
  assert.equal(state.repository, 'example/coffee'); assert.equal(state.version, 2); assert.equal('productRoot' in state, false);
  assert.deepEqual(state.bindings, [{ run: 'phone-1', issue: 201 }]); assert.equal(state.search.items.length, 11);
});

test('a cache from another scope is a miss while foreign bindings fail closed', async t => {
  for (const bindings of [[], [{ run: 'phone-1', issue: 80 }]]) {
    const f = setup(t);
    f.ports.readProductState = async () => ({ json: JSON.stringify({ version: 1, repository: 'foreign/repo', productRoot: '/other', bindings, search: { at: 100000, items: [] } }) });
    f.ports.now = async () => ({ milliseconds: 100000 }); f.ports.writeProductState = async () => ({});
    const out = await runProduct({ command: 'status', cwd: f.cwd }, f.ports);
    assert.equal(out.exitCode, bindings.length ? 1 : 0);
    assert.equal(f.s.searches.length, bindings.length ? 0 : 1);
  }
});

test('a bound start does not claim that unexamined dependencies remain unmet', async t => {
  const f = setup(t); f.s.issues = [issue('journeys', 80)];
  f.s.runs = [{ workflow: 'feature', number: 80, productMarker: marker('journeys'), state: 'running' }];
  const out = await productStart({ cwd: f.cwd, run: 'journeys', noRun: true }, f.ports);
  assert.equal(out.exitCode, 0); assert.equal(out.issue, 80); assert.equal(f.s.searches.length, 0);
  assert.doesNotMatch(out.message, /still needs/);
});
