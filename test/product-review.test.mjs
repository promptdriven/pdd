import test from 'node:test';
import assert from 'node:assert/strict';
import { cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync, existsSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync, spawnSync } from 'node:child_process';
import { productStatus, productNext, productStart, runProduct } from '../src/product.mjs';
import { storyEvidence } from '../src/workflow-runner.mjs';
import { sourceFingerprint } from '../src/workflow-replay.mjs';

const marker = run => `<!-- pdd-product: run=${run} -->`;
const item = (run, number = 81, extra = {}) => ({ number, body: marker(run), user: { login: 'member' }, author_association: 'MEMBER', created_at: '2026-10-01T00:00:00Z', ...extra });
const pr = (run, number, extra = {}) => ({ number, url: `https://github.com/example/coffee/pull/${number}`, body: `${marker(run)}\n<!-- pdd-workflow:instance-${number}:code -->`, state: 'MERGED', isDraft: false,
  updatedAt: '2026-10-02T00:00:00Z', headRefName: `topic-${number}`, isCrossRepository: false, headRepository: { name: 'coffee' }, headRepositoryOwner: { login: 'example' }, ...extra });
const xref = (number, extra = {}) => ({ event: 'cross-referenced', source: { issue: { pull_request: { html_url: `https://github.com/example/coffee/pull/${number}` } } }, ...extra });
function fixture(t) {
  const cwd = mkdtempSync(join(tmpdir(), 'pdd-product-review-'));
  t.after(() => rmSync(cwd, { recursive: true, force: true }));
  cpSync(new URL('../examples/coffee-pickup/', import.meta.url), cwd, { recursive: true });
  const state = { issues: [], runs: [], prs: [], events: {}, starts: [], creates: [], reads: [], actor: 'person', views: [], closed: [] };
  const ports = {
    readProductState: async () => ({ json: state.productState ?? null }),
    writeProductState: async ({ json }) => { state.productState = json; return {}; },
    now: async () => ({ milliseconds: (state.clock = (state.clock ?? 0) + 60000) }),
    issueByNumber: async ({ number }) => {
      if (state.fail) throw Error('GitHub unavailable');
      const row = (state.pages?.flat() ?? state.issues).find(item => item.number === number);
      return row && { author_association: 'MEMBER', user: { login: 'member' }, created_at: '2026-10-01T00:00:00Z', ...row };
    },
    listRuns: async () => state.runs,
    resolveRepository: async () => ({ repository: 'example/coffee', defaultBranch: 'alpha' }),
    planOnBase: async () => true,
    storyEvidence: async run => run.rows ?? [],
    startRun: async args => { state.starts.push(args); return { exitCode: 0, message: 'Started.' }; },
    createIssue: async payload => { state.creates.push(payload); const number = 200 + state.creates.length; state.issues.push(item('unused', number, { body: payload.body })); return { url: `https://github.com/example/coffee/issues/${number}` }; },
    issuePage: async args => { state.reads.push(args); const issues = state.issues.filter(issue => issue.body.includes(args.marker)); return { items: issues.slice((args.page - 1) * args.perPage, args.page * args.perPage), total_count: issues.length, incomplete_results: false }; },
    timelinePage: async args => { const rows = state.events[args.issue] ?? []; return rows.slice((args.page - 1) * args.perPage, args.page * args.perPage); },
    pullRequest: async ({ number }) => state.prs.find(row => row.number === number),
    currentActor: async () => ({ login: state.actor }),
    openBaseSource: async args => { state.views.push(args); return { root: cwd, handle: null }; },
    closeBaseSource: async ({ handle }) => { state.closed.push(handle); return {}; },
    // The pre-fix implementation has no raw read ports. Keep its actual gh
    // boundary fake too: controls must fail assertions, never contact GitHub.
    execFile: async (file, args) => {
      assert.equal(file, 'gh');
      if (args[0] === 'api') {
        if (state.large) throw Error('stdout maxBuffer length exceeded');
        const issue = /issues\/(\d+)\/timeline/.exec(args.find(arg => arg.includes('/timeline')) ?? '')?.[1];
        return { stdout: JSON.stringify(issue ? [state.events[issue] ?? []] : [state.issues]) };
      }
      if (args[0] === 'pr') return { stdout: JSON.stringify(state.prs.find(row => row.number === Number(args[2]))) };
      assert.fail(`Unexpected process: ${file} ${args.join(' ')}`);
    },
  };
  return { cwd, state, ports };
}

test('all three product commands use bounded marker searches, never the whole repository buffer', async t => {
  const f = fixture(t); f.state.large = true;
  for (const command of ['status', 'next', 'start']) {
    const result = await runProduct({ cwd: f.cwd, command, run: 'phone-1', noRun: true }, f.ports);
    assert.equal(result.exitCode, 0, `${command}: ${result.message}`);
  }
  assert.ok(f.state.reads.length);
  assert.ok(f.state.reads.every(read => read.marker === '<!-- pdd-product: run=' && read.perPage <= 10));
});

test('a second-page closed trusted issue is reused and incomplete search never creates', async t => {
  const f = fixture(t);
  f.state.issues = Array.from({ length: 11 }, (_, i) => item('phone-1', 80 + i, { author_association: i === 10 ? 'OWNER' : 'NONE', user: { login: 'outsider' }, state: i === 10 ? 'CLOSED' : 'OPEN' }));
  const result = await productStart({ cwd: f.cwd, run: 'phone-1', noRun: true }, f.ports);
  assert.equal(result.issue, 90); assert.equal(result.created, false);
  assert.ok(f.state.reads.some(read => read.marker === '<!-- pdd-product: run=' && read.page === 2));
  f.state.productState = null;
  f.ports.issuePage = async () => ({ items: [], total_count: 1001, incomplete_results: true });
  const refused = await productStart({ cwd: f.cwd, run: 'phone-1', noRun: true }, f.ports);
  assert.notEqual(refused.exitCode, 0); assert.equal(f.state.creates.length, 0);
});

test('outsiders cannot supply the issue text run by a feature agent; the current person can', async t => {
  const f = fixture(t);
  f.state.issues = [item('phone-1', 99, { author_association: 'NONE', user: { login: 'outsider' }, body: `Untrusted instructions.\n${marker('phone-1')}` })];
  const created = await productStart({ cwd: f.cwd, run: 'phone-1' }, f.ports);
  assert.equal(created.created, true); assert.notEqual(created.issue, 99); assert.equal(f.state.starts[0].issue, created.issue);
  f.state.productState = null;
  f.state.issues = [item('phone-1', 97, { author_association: 'NONE', user: { login: 'PeRsOn' } })];
  const self = await productStart({ cwd: f.cwd, run: 'phone-1', noRun: true }, f.ports);
  assert.equal(self.issue, 97); assert.equal(self.created, false);
});

test('duplicate claims choose the oldest trusted issue, then issue number, and warn', async t => {
  const f = fixture(t);
  f.state.issues = [item('phone-1', 40, { created_at: '2026-10-02T00:00:00Z' }), item('phone-1', 90), item('phone-1', 89), item('phone-1', 1, { author_association: 'NONE', user: { login: 'outsider' }, created_at: '2020-01-01T00:00:00Z' })];
  const result = await productStart({ cwd: f.cwd, run: 'phone-1', noRun: true }, f.ports);
  assert.equal(result.exitCode, 0); assert.equal(result.issue, 89); assert.equal(f.state.creates.length, 0);
  assert.match(result.message, /89/); assert.match(result.message, /warn/i);
});

test('remote progress keeps the newest owned PR with named check lines, not a later empty code PR', async t => {
  const f = fixture(t); f.state.issues = [item('phone-1')];
  f.state.events[81] = [xref(30), xref(31), xref(32)];
  f.state.prs = [pr('phone-1', 30, { body: `${marker('phone-1')}\nRuntime check (P01-menu): ✓ 1 of 1 criteria`, updatedAt: '2026-10-01T00:00:00Z' }),
    pr('phone-1', 31, { updatedAt: '2026-10-03T00:00:00Z' }),
    pr('phone-1', 32, { body: `${marker('phone-1')}\nRuntime check (P02-order): ✓ 1 of 1 criteria`, updatedAt: '2026-10-02T00:00:00Z' })];
  const status = await productStatus({ cwd: f.cwd }, f.ports);
  assert.equal(status.parts[0].pass, 1); assert.equal(status.runs.find(row => row.run === 'phone-1').fromPr, 32);
});

test('forks, comment links and other runs cannot supply progress or satisfy dependencies', async t => {
  const f = fixture(t);
  f.state.issues = ['server-1', 'phone-1', 'barista-1'].map((name, i) => item(name, 81 + i));
  f.state.events[81] = [xref(40), xref(41), xref(42), xref(43, { event: 'commented' }), xref(44), xref(45), xref(46)];
  f.state.events[82] = [xref(40)]; f.state.events[83] = [xref(40)];
  f.state.prs = [pr('phone-1', 40), pr('server-1', 41, { isCrossRepository: true, headRepositoryOwner: { login: 'fork-owner' } }),
    pr('server-1', 42, { isCrossRepository: false, headRepositoryOwner: { login: 'foreign-owner' } }),
    pr('server-1', 43), pr('server-1',44,{headRepository:{name:'foreign'}}),
    pr('server-1',45,{url:'https://github.com/foreign/coffee/pull/45'}), pr('server-1',46,{number:999})];
  assert.deepEqual((await productNext({ cwd: f.cwd }, f.ports)).ready, []);
  const status = await productStatus({ cwd: f.cwd }, f.ports);
  assert.deepEqual(status.runs.find(row => row.run === 'server-1').prs, []);
  assert.deepEqual(status.runs.find(row => row.run === 'barista-1').prs, []);
});

test('an actual saved own branch is acceptable while legacy unrelated branch prose is not', async t => {
  const f = fixture(t); f.state.issues = [item('phone-1')];
  f.state.runs = [{ number: 81, state: 'running', branch: 'own-branch', pr: [{ number: 30, stage: 'code', branch: 'own-branch' }], rows: [] }];
  f.state.prs = [pr('unused', 30, { body: 'PR 2 of this run: the code.', headRefName: 'own-branch' })];
  assert.equal((await productStatus({ cwd: f.cwd }, f.ports)).runs.find(row => row.run === 'phone-1').state, 'merged');
  f.state.prs[0].headRefName = 'some-other-branch';
  assert.notEqual((await productStatus({ cwd: f.cwd }, f.ports)).runs.find(row => row.run === 'phone-1').state, 'merged');
});

test('created issue tells the agent the leading Story-id filename rule', async t => {
  const f = fixture(t); await productStart({ cwd: f.cwd, run: 'phone-1', noRun: true }, f.ports);
  assert.match(f.state.creates[0].body, /P01-[^\s]+\.md/);
  assert.match(f.state.creates[0].body, /Story file/i);
});

test('long Unicode issue titles compact without losing the complete Story handoff', async t => {
  const f = fixture(t), map = join(f.cwd, 'product/map.md'), plan = join(f.cwd, 'product/plan.md');
  const ids = Array.from({ length: 60 }, (_, i) => `P${100 + i}`);
  writeFileSync(map, readFileSync(map, 'utf8').replace('# Coffee pickup: map', `# ${'🚀'.repeat(260)}: map`).replace('## Journeys', ids.map(id => `| ${id} | phone | I use ${id}. | CORE |`).join('\n') + '\n\n## Journeys'));
  writeFileSync(plan, readFileSync(plan, 'utf8').replace('P01, P02, P03, P04 | plan PR', `${ids.join(', ')} | plan PR`));
  const out = await productStart({ cwd: f.cwd, run: 'phone-1', noRun: true }, f.ports);
  assert.equal(out.exitCode, 0); assert.ok([...f.state.creates[0].title].length <= 256); assert.match(out.message, /warn/i);
  for (const id of ids) assert.ok(f.state.creates[0].body.includes(`${id}:`));
});

test('Needs cycles and self-cycles are finite advice, not an explicit-start gate', async t => {
  for (const need of ['journeys', 'server-1']) {
    const f = fixture(t), plan = join(f.cwd, 'product/plan.md');
    writeFileSync(plan, readFileSync(plan, 'utf8').replace('S01, S02, S03, S04 | plan PR', `S01, S02, S03, S04 | ${need}`));
    for (const command of ['status', 'next']) {
      const result = await runProduct({ command, cwd: f.cwd }, f.ports);
      assert.equal(result.exitCode, 0); assert.match(result.message, /cycle/i); assert.match(result.message, /server-1.*→.*server-1/);
    }
    assert.equal((await productStart({ cwd: f.cwd, run: 'server-1', noRun: true }, f.ports)).exitCode, 0);
  }
});

test('comparison-root evidence uses base files, including null as explicitly unavailable', t => {
  const f = fixture(t), base = fixture(t);
  for (const cwd of [f.cwd, base.cwd]) { execFileSync('git', ['init', '-q'], { cwd }); execFileSync('git', ['add', '.'], { cwd }); }
  const run = { root: f.cwd, runtimeHistory: [{ at: 1, source: { kind: 'git-content-v1', sha256: sourceFingerprint(f.cwd) }, summary: 'Runtime check (P01-menu): ✓' }] };
  writeFileSync(join(f.cwd, 'contracts/world.md'), 'changed run worktree');
  assert.equal(storyEvidence(run, { comparisonRoot: base.cwd })[0].current, true);
  assert.equal(storyEvidence(run, { comparisonRoot: null })[0].current, false);
  assert.equal(storyEvidence(run)[0].current, false);
});

test('merged evidence uses a shared base view once and closes it even on failure', async t => {
  const f = fixture(t); f.state.issues = [item('phone-1')];
  f.state.runs = [{ number: 81, root: '/retired-worktree', baseBranch: 'alpha', pr: [{ number: 30, stage: 'code', branch: 'own-branch' }] }];
  f.state.prs = [pr('phone-1', 30, { headRefName: 'own-branch' })];
  f.ports.openBaseSource = async args => { f.state.views.push(args); return { root: '/current-base', handle: 'owned-view' }; };
  f.ports.storyEvidence = async (_run, options) => { assert.equal(options?.comparisonRoot, '/current-base'); throw Error('unreadable receipt'); };
  await assert.rejects(productStatus({ cwd: f.cwd }, f.ports), /unreadable receipt/);
  assert.deepEqual(f.state.closed, ['owned-view']);
});

test('actual Git base views prefer checked-out edits, isolate detached snapshots and always remove owned clones', async t => {
  const f=fixture(t), git=(...args)=>execFileSync('git',args,{cwd:f.cwd,encoding:'utf8',stdio:['ignore','pipe','pipe']}).trim();
  git('init','-q','-b','alpha');git('config','user.name','Test');git('config','user.email','test@example.invalid');git('add','.');git('commit','-qm','base');
  const oldRoot=mkdtempSync(join(tmpdir(),'pdd-retired-run-'));t.after(()=>rmSync(oldRoot,{recursive:true,force:true}));git('worktree','add','--detach',oldRoot,'HEAD');
  const baseSha=git('rev-parse','HEAD'), receipt={kind:'git-content-v1',sha256:sourceFingerprint(f.cwd)};
  f.state.issues=[item('phone-1')];f.state.events[81]=[xref(61)];f.state.prs=[pr('phone-1',61)];
  f.state.runs=[{number:81,baseBranch:'alpha',root:oldRoot,runtimeHistory:[{at:1,source:receipt,summary:'Runtime check (P01-menu): ✓'}]}];
  delete f.ports.openBaseSource;delete f.ports.closeBaseSource;delete f.ports.storyEvidence;
  const commands=[], snapshots=[];
  f.ports.execFile=async(file,args,options)=>{
    assert.equal(file,'git');commands.push(args);
    if(args.includes('clone')) snapshots.push(args.at(-1));
    try{return {stdout:execFileSync(file,args,{...options,encoding:'utf8',stdio:['ignore','pipe','pipe']})};}
    catch(error){return {stdout:'',stderr:error.stderr?.toString(),code:error.status};}
  };
  assert.equal((await productStatus({cwd:f.cwd},f.ports)).parts[0].pass,1);
  writeFileSync(join(f.cwd,'contracts/world.md'),'current base edit');
  assert.equal(storyEvidence(f.state.runs[0])[0].current,true,'the retired worktree still matches its original receipt');
  assert.equal((await productStatus({cwd:f.cwd},f.ports)).parts[0].stale,1);
  git('restore','contracts/world.md');git('checkout','-qb','topic');
  writeFileSync(join(f.cwd,'contracts/world.md'),'old topic changed');git('add','contracts/world.md');git('commit','-qm','topic only');
  git('update-ref','refs/remotes/origin/alpha','HEAD');
  const before=git('show-ref'), hooks=join(f.cwd,'.git/hooks/post-checkout'), trap=join(f.cwd,'hook-ran');
  writeFileSync(hooks,`#!/bin/sh\ntouch '${trap}'\n`,{mode:0o755});
  const status=await productStatus({cwd:f.cwd},f.ports);
  assert.equal(status.parts[0].pass,1,'comparison uses alpha, not the current topic');
  assert.equal(git('show-ref'),before);assert.equal(existsSync(trap),false);
  assert.equal(snapshots.length,1);assert.equal(existsSync(snapshots[0]),false);
  assert.equal(commands.some(args=>args.includes('fetch')||args.includes('update-ref')),false);
  git('branch','-D','alpha');
  assert.equal((await productStatus({cwd:f.cwd},f.ports)).parts[0].stale,1,'origin is used only after the local base is absent');
  git('update-ref','-d','refs/remotes/origin/alpha');
  const unavailable=await productStatus({cwd:f.cwd},f.ports);
  assert.equal(unavailable.parts[0].pass,0);assert.match(unavailable.warnings.join(' '),/base source is unavailable/);
  git('branch','alpha',baseSha);
  f.ports.storyEvidence=()=>{throw Error('evidence failed');};
  await assert.rejects(productStatus({cwd:f.cwd},f.ports),/evidence failed/);
  assert.equal(snapshots.length,3);assert.ok(snapshots.every(path=>!existsSync(path)));delete f.ports.storyEvidence;
});

test('full timeline pages of unrelated events still reach the owned PR on the next page', async t => {
  const f=fixture(t);f.state.issues=[item('phone-1')];f.state.prs=[pr('phone-1',61,{body:`${marker('phone-1')}\nRuntime check (P01-menu): ✓`})];
  f.state.events[81]=[...Array.from({length:10},()=>({event:'commented',body:'unrelated'})),xref(61)];
  assert.equal((await productStatus({cwd:f.cwd},f.ports)).runs[1].fromPr,61);
});

test('real CLI subprocesses stay below the default buffer with a large unrelated issue history', t => {
  const f=fixture(t), git=(...args)=>execFileSync('git',args,{cwd:f.cwd,stdio:['ignore','pipe','pipe']});
  git('init','-q','-b','alpha');git('config','user.name','Test');git('config','user.email','test@example.invalid');
  git('remote','add','origin','https://github.com/example/coffee.git');git('add','.');git('commit','-qm','base');
  const bin=mkdtempSync(join(tmpdir(),'pdd-review-gh-')), log=join(bin,'calls.jsonl');t.after(()=>rmSync(bin,{recursive:true,force:true}));
  writeFileSync(join(bin,'gh'),`#!/usr/bin/env node
const fs=require('node:fs'),a=process.argv.slice(2);fs.appendFileSync(${JSON.stringify(log)},JSON.stringify(a)+'\\n');
if(a[0]==='repo') process.stdout.write(JSON.stringify({nameWithOwner:'example/coffee',defaultBranchRef:{name:'alpha'},url:'https://github.com/example/coffee'}));
else if(a[1].startsWith('search/issues?')) {const q=new URL('https://api.github.com/'+a[1]).searchParams;const body='<!-- pdd-product: run=phone-1 -->';const rows=q.get('q').includes('<!-- pdd-product: run=')?[{number:81,body,user:{login:'member'},author_association:'MEMBER',created_at:'2026-10-01T00:00:00Z'}]:[];process.stdout.write(JSON.stringify({items:rows,total_count:rows.length,incomplete_results:false}));}
else if(a[1].endsWith('/issues/81')) process.stdout.write(JSON.stringify({number:81,body:'<!-- pdd-product: run=phone-1 -->',user:{login:'member'},author_association:'MEMBER',created_at:'2026-10-01T00:00:00Z'}));
else if(a[1].includes('/timeline?')) process.stdout.write('[]');
else process.stdout.write(JSON.stringify(Array.from({length:150},()=>({body:'x'.repeat(65536)}))));
`,{mode:0o755});
  const cli=new URL('../bin/pdd.mjs',import.meta.url).pathname;
  for(const args of [['status'],['next'],['start','phone-1','--no-run']]) {
    const result=spawnSync(process.execPath,[cli,'product',...args],{cwd:f.cwd,encoding:'utf8',env:{...process.env,HOME:f.cwd,PATH:`${bin}:${process.env.PATH}`}});
    assert.equal(result.status,0,`${args}: ${result.stderr} ${result.stdout}`);
  }
  const calls=readFileSync(log,'utf8').trim().split('\n').map(JSON.parse), searches=calls.filter(a=>a[1]?.startsWith('search/issues?'));
  assert.equal(searches.length,1);assert.equal(calls.some(a=>a.includes('--slurp')||a.includes('--paginate')),false);
  for(const args of searches){const query=new URL('https://api.github.com/'+args[1]).searchParams;assert.ok(Number(query.get('per_page'))<=10);assert.match(query.get('q'),/in:body.*<!-- pdd-product: run=/);}
});


test('ambiguous product markers do not bind an issue or a remote PR to two planned runs', async t => {
  const f=fixture(t), body=`${marker('phone-1')}\n${marker('server-1')}`;
  f.state.issues=[item('phone-1',81,{body})];
  const started=await productStart({cwd:f.cwd,run:'phone-1',noRun:true},f.ports);
  assert.equal(started.created,true);assert.match(started.message,/ambiguous/i);
  f.state.productState=null;
  f.state.issues=[item('phone-1')];f.state.events[81]=[xref(61)];
  f.state.prs=[pr('phone-1',61,{body:body+'\nRuntime check (P01-menu): ✓'})];
  assert.equal((await productStatus({cwd:f.cwd},f.ports)).parts[0].pass,0);
});

test('a short search page with more promised results is an error, never permission to create', async t => {
  const f=fixture(t);f.ports.issuePage=async()=>({items:[item('phone-10')],total_count:11,incomplete_results:false});
  const result=await productStart({cwd:f.cwd,run:'phone-1',noRun:true},f.ports);
  assert.equal(result.exitCode,1);assert.equal(f.state.creates.length,0);
});


test('an unavailable authenticated identity never grants the self exemption to an outsider', async t => {
  const f=fixture(t);f.state.issues=[item('phone-1',81,{author_association:'NONE'})];
  f.ports.currentActor=async()=>{throw Error('identity unavailable');};
  const result=await productStart({cwd:f.cwd,run:'phone-1',noRun:true},f.ports);
  assert.equal(result.exitCode,0);assert.equal(f.state.creates.length,1);assert.notEqual(result.issue,81);assert.equal(f.state.starts.length,0);
});
