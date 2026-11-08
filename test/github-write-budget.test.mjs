import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, rmSync, readFileSync, writeFileSync, mkdirSync, readdirSync } from 'node:fs';
import * as fs from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { spawn, execFileSync } from 'node:child_process';
import { nativeGithubCounter, githubLedger } from '../src/github-calls.mjs';
import { githubWriteBudget, githubWriteCost, githubWriteStatus } from '../src/github-writes.mjs';
import { githubWriteRunner, githubWriteEnvironment, observeGithubWriteClaims, githubWriteUsage, githubWriteUsages } from '../src/github-write-proxy.mjs';
import { createGithubRepoFake } from './helpers/github-repo-fake.mjs';
import { replayWriteDay } from './helpers/github-write-day.mjs';
const NOW = Date.parse('2026-11-07T00:00:00Z'), minute = 60_000;
function world(t) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-write-budget-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const w = { root, time: NOW };
  w.budget = extra => githubWriteBudget({ root, now: () => w.time, identity: 'acme', machine: 'one', ...extra });
  return w;
}
const api = (method, path, body) => ({ args: ['api', '--include', '--method', method, path, ...(body ? ['--input', '-'] : [])], options: body ? { input: JSON.stringify(body) } : {} });

test('all repositories and runner objects share rolling minute/hour admission, with a reserve for people', t => {
  const w = world(t), one = w.budget(), two = w.budget();
  for (let n = 0; n < 60; n++) (n % 2 ? one : two).reserve(1);
  assert.throws(() => two.reserve(1), { code: 'github_write_budget', retryAt: NOW + minute });
  assert.deepEqual([two.usage().minute, two.usage().hour], [60, 60]);
  w.time += minute;
  for (let n = 0; n < 290; n++) { if (n && n % 60 === 0) w.time += minute; one.reserve(1); }
  assert.equal(two.usage().hour, 350);
  assert.throws(() => one.reserve(1), { code: 'github_write_budget', retryAt: NOW + 60 * minute });
  w.time = NOW + 60 * minute; two.reserve(1);
  assert.equal(one.usage().hour, 291);
});

test('host and identity buckets are independent; case variants share one identity', t => {
  const w = world(t);
  w.budget().reserve(60);
  assert.throws(() => w.budget({ identity: 'AcMe' }).reserve(1), { code: 'github_write_budget' });
  w.budget({ identity: 'other' }).reserve(1);
  w.budget({ host: 'enterprise.example' }).reserve(1);
  assert.equal(w.budget({ identity: 'other' }).usage().hour, 1);
});

test('active claims across repositories divide the share; duplicate, expired and inactive machines do not', t => {
  const w = world(t), b = w.budget();
  b.observeClaims('acme/a', [{ active: true, machine: 'two', lastSeen: new Date(w.time).toISOString() }, { active: false, machine: 'three', lastSeen: new Date(w.time).toISOString() }]);
  b.observeClaims('acme/b', [{ active: true, machine: 'two', lastSeen: new Date(w.time).toISOString() }, { active: true, machine: 'expired', lastSeen: new Date(w.time - 4 * 60 * minute).toISOString() }]);
  assert.deepEqual([b.usage().machines, b.usage().minuteLimit, b.usage().hourLimit], [2, 30, 175]);
  b.reserve(30);
  assert.throws(() => b.reserve(1), { code: 'github_write_budget' });
  w.time += 4 * 60 * minute;
  assert.equal(b.usage().machines, 1);
});

test('claims observed before identity lookup still divide the authenticated writer share', async t => {
  const w = world(t);
  observeGithubWriteClaims({ root: w.root, env: {}, now: () => w.time, machine: 'one', repository: 'acme/a', claims: [{ active: true, machine: 'two', lastSeen: new Date(w.time).toISOString() }] });
  const run = githubWriteRunner(async () => ({ code: 0, stdout: '{}' }), { root: w.root, env: {}, identity: 'acme', machine: 'one', now: () => w.time });
  const request = api('PATCH', 'repos/acme/a/issues/1', { title: 'x' }); await run('gh', request.args, request.options);
  assert.equal(w.budget().usage().machines, 2);
});

test('failed or uncertain writes remain charged and keep the original error', async t => {
  const w = world(t), error = Object.assign(Error('lost response'), { stderr: 'transport' });
  const run = githubWriteRunner(async () => { throw error; }, { root: w.root, env: {}, identity: 'acme', machine: 'one', now: () => w.time });
  await assert.rejects(run('gh', ['api', '--method', 'PATCH', 'repos/acme/a/issues/1']), e => e === error);
  assert.equal(w.budget().usage().hour, 1);
});

test('secondary-limit cooldowns are shared across processes and respect seconds and HTTP dates', t => {
  const w = world(t), one = w.budget(), two = w.budget();
  one.observe({ stdout: 'HTTP/2.0 429\r\nRetry-After: 90\r\n\r\n{}' });
  assert.throws(() => two.reserve(1), { code: 'github_write_budget', retryAt: NOW + 90_000 });
  w.time += 90_000; two.reserve(1);
  two.observe({ stderr: 'HTTP 403 secondary rate limit' });
  assert.throws(() => one.reserve(1), { code: 'github_write_budget', retryAt: w.time + minute });
  w.time += minute;
  one.observe({ stdout: `HTTP/2.0 403\r\nRetry-After: ${new Date(w.time + 120_000).toUTCString()}\r\n\r\n` });
  assert.throws(() => two.reserve(1), { code: 'github_write_budget', retryAt: w.time + 120_000 });
});

test('bad storage and a live lock defer; a dead lock is reclaimed', t => {
  const w = world(t), b = w.budget(); b.reserve(1);
  const folder = join(w.root, 'github-writes'), file = join(folder, readdirSync(folder).find(x => !x.startsWith('active-')));
  const lock = join(folder, `${createHash('sha256').update('github.com').digest('hex').slice(0,20)}.lock`);
  writeFileSync(lock, String(process.pid));
  assert.throws(() => b.reserve(1), { code: 'github_write_budget' });
  writeFileSync(lock, '2147483647'); b.reserve(1);
  assert.equal(b.usage().hour, 2);
  writeFileSync(file, '{}');
  assert.throws(() => b.reserve(1), { code: 'github_write_budget' });
  assert.equal(b.usage().state, 'deferred');
});

test('separate Node processes cannot overspend the machine minute budget', async t => {
  const w = world(t), module = new URL('../src/github-writes.mjs', import.meta.url).href;
  const script = `import {githubWriteBudget} from ${JSON.stringify(module)}; const b=githubWriteBudget({root:process.argv[1],identity:'acme',machine:'one',now:()=>${NOW}}); let n=0; for(let i=0;i<60;i++) try { b.reserve(1); n++; } catch(e) { if(e.code!=='github_write_budget') throw e; } process.stdout.write(String(n));`;
  const run = () => new Promise((resolve, reject) => { const child = spawn(process.execPath, ['--input-type=module', '-e', script, w.root]); let out = ''; child.stdout.on('data', x => { out += x; }); child.on('error', reject); child.on('close', code => code ? reject(Error(`child ${code}`)) : resolve(Number(out))); });
  const counts = await Promise.all([run(), run(), run(), run()]);
  const admitted = counts.reduce((a,b) => a+b, 0);
  assert.ok(admitted > 0 && admitted <= 60);
  assert.equal(w.budget().usage().hour, admitted);
  for (let n = admitted; n < 60; n++) w.budget().reserve(1);
  assert.equal(w.budget().usage().hour, 60);
});

test('marked progress reuses one owned comment and skips unchanged text; evidence stays append-only', async t => {
  const w = world(t), fake = createGithubRepoFake({ issues: 1, now: () => w.time });
  fake.comment(1, '<!-- pdd:autopilot:status --> other', 'someone');
  const run = githubWriteRunner((_file,args,opts) => fake.gh(args,opts), { root: w.root, env: {}, identity: 'acme', now: () => w.time, machine: 'one' });
  const send = body => { const r=api('POST', 'repos/acme/widgets/issues/1/comments', {body}); return run('gh', r.args, r.options); };
  await send('one <!-- pdd:autopilot:status -->'); await send('one <!-- pdd:autopilot:status -->'); await send('two <!-- pdd:autopilot:status -->');
  await send('checker evidence'); await send('checker evidence');
  assert.equal(fake.issues.get(1).comments.length, 4);
  assert.equal(fake.issues.get(1).comments[0].body, '<!-- pdd:autopilot:status --> other');
  assert.equal(w.budget().usage().hour, 4);
});

test('combined label changes preserve unrelated labels and skip an unchanged set', async t => {
  const w = world(t), fake = createGithubRepoFake({ issues: 1 }); fake.label(1, 'pdd:working'); fake.label(1, 'old');
  const run = githubWriteRunner((_file,args,opts) => fake.gh(args,opts), { root: w.root, env: {}, identity: 'acme', now: () => w.time, machine: 'one' });
  const args = ['issue', 'edit', '1', '--repo', 'acme/widgets', '--add-label', 'ready,tracked', '--remove-label', 'old'];
  assert.equal((await run('gh', args)).stdout, 'https://github.com/acme/widgets/issues/1\n');
  assert.equal((await run('gh', args)).stdout, 'https://github.com/acme/widgets/issues/1\n');
  assert.deepEqual(fake.issues.get(1).labels.slice().sort(), ['pdd:working','ready','tracked']);
  assert.equal(w.budget().usage().hour, 2); // two atomic mutations, one HTTP request
  assert.equal(fake.calls.filter(c => c.endpoint === 'graphql').length, 1);
});

test('GraphQL queries, REST reads and a named claims mutation have independent write classification', () => {
  assert.equal(githubWriteCost(['api','--method','HEAD','user']), 0);
  assert.equal(githubWriteCost(['api','graphql','-f','query=query { viewer { login } }']), 0);
  assert.equal(githubWriteCost(['api','graphql','--input','-'], {input:JSON.stringify({query:'mutation { a:addComment(input:{}) {id} b:addComment(input:{}) {id} }'})}), 2);
  assert.equal(githubWriteCost(['api','--method','PATCH','repos/a/b/issues/comments/1']), 1);
});

test('private gh wrapper forwards literal arguments, stdin and a failing exit; status uses local files only', t => {
  const w = world(t), bin = join(w.root, 'bin'); mkdirSync(bin);
  writeFileSync(join(bin, 'gh'), `#!${process.execPath}\nlet data=''; for await (const part of process.stdin) data+=part; process.stdout.write(JSON.stringify({args:process.argv.slice(2),data})); process.stderr.write('fixture-error'); process.exitCode=7;\n`, {mode:0o700});
  const env = { PATH: `${bin}:/usr/bin:/bin`, HOME: w.root, PDD_GITHUB_COUNTED: '1', ...githubWriteEnvironment({root:w.root,env:{PATH:`${bin}:/usr/bin:/bin`}}) };
  let result;
  try { execFileSync(join(env.PATH.split(':')[0], 'gh'), ['api', '--method', 'PATCH', 'literal;$(nope)'], {env,input:'body\n',encoding:'utf8',stdio:['pipe','pipe','pipe']}); assert.fail(); }
  catch (error) { result = error; }
  assert.equal(result.status, 7); assert.equal(String(result.stderr), 'fixture-error');
  assert.deepEqual(JSON.parse(result.stdout), {args:['api','--method','PATCH','literal;$(nope)'],data:'body\n'});
  const usage = githubWriteUsage({root:w.root,env:{},now:()=>w.time});
  assert.match(githubWriteStatus(usage), /0\/60.*0\/350/);
});

test('one synthetic day reduces writes while preserving final issue labels and progress', async t => {
  const after = await replayWriteDay();
  assert.equal(after.writes, 288);
  assert.equal(after.labelWrites, 96);
  assert.equal(after.postComments, 8);
  assert.equal(after.comments, 16);
  t.diagnostic(JSON.stringify(after));
});

// The review cases preserve authority and close accounting bypasses.
test('a concurrent label addition survives the combined mutation', async t => {
  const w=world(t), fake=createGithubRepoFake({issues:1}); fake.label(1,'old');
  fake.beforeRequest=call => { if(call.endpoint==='graphql') fake.label(1,'pdd:stuck'); };
  const run=githubWriteRunner((_file,args,opts)=>fake.gh(args,opts),{root:w.root,env:{},identity:'acme',machine:'one',now:()=>w.time});
  await run('gh',['issue','edit','1','--repo','acme/widgets','--add-label','ready','--remove-label','old']);
  assert.deepEqual(fake.issues.get(1).labels.slice().sort(),['pdd:stuck','ready']);
});

test('a selected mutation after a query and compact method options cannot bypass admission', () => {
  const query='query Q {viewer {login}} mutation M {addComment(input:{}) {clientMutationId}}';
  assert.equal(githubWriteCost(['api','graphql','-f',`query=${query}`,'-f','operationName=M']),1);
  assert.equal(githubWriteCost(['api','--method=DELETE','repos/a/b/issues/comments/1']),1);
  assert.equal(githubWriteCost(['api','-XDELETE','repos/a/b/issues/comments/1']),1);
  assert.equal(githubWriteCost(['api','repos/a/b/issues/comments/1','--input=-']),1);
});

test('unknown identity cannot obtain a new allowance after known use, or vice versa', t => {
  const w=world(t); w.budget().reserve(60);
  assert.throws(()=>w.budget({identity:'unknown'}).reserve(1),{code:'github_write_budget'});
  w.time+=minute; w.budget({identity:'unknown'}).reserve(60);
  assert.throws(()=>w.budget().reserve(1),{code:'github_write_budget'});
});

test('status exposes each local identity without looking up GitHub', t=>{
  const w=world(t); w.budget().reserve(2); w.budget({identity:'other'}).reserve(1);
  const usages=githubWriteUsages({root:w.root,env:{},now:()=>w.time,machine:'one'});
  assert.deepEqual(usages.map(x=>[x.identity,x.hour]),[['acme',2],['other',1]]);
});

test('a hash inside GraphQL strings cannot hide a selected mutation',()=>{
  for(const literal of ['"#"','"""# block string\n"""']) {
    const query=`query Q {repository(owner:${literal},name:"x"){id}} mutation M {addComment(input:{}){clientMutationId}}`;
    assert.equal(githubWriteCost(['api','graphql','-f',`query=${query}`,'-f','operationName=M']),1);
  }
});

test('secondary cooldown follows known and unknown identities in both directions',t=>{
  const w=world(t); w.budget().observe({stderr:'HTTP 403 secondary rate limit'});
  assert.throws(()=>w.budget({identity:'unknown'}).reserve(1),{code:'github_write_budget',retryAt:w.time+minute});
  w.time+=minute; w.budget({identity:'unknown'}).observe({stderr:'HTTP 403 secondary rate limit'});
  assert.throws(()=>w.budget().reserve(1),{code:'github_write_budget',retryAt:w.time+minute});
});

test('a labels-only addition declares only GraphQL variables it uses',async t=>{
  const w=world(t), fake=createGithubRepoFake({issues:1});
  const run=githubWriteRunner((_file,args,opts)=>fake.gh(args,opts),{root:w.root,env:{},identity:'acme',machine:'one',now:()=>w.time});
  await run('gh',['issue','edit','1','--repo','acme/widgets','--add-label','ready']);
  const query=fake.calls.find(c=>c.endpoint==='graphql').query;
  assert.equal((query.match(/\$remove/g)??[]).length,0);
  assert.equal((query.match(/\$add/g)??[]).length,2);
});

test('derived comment operations retain an explicit hostname',async t=>{
  const w=world(t), fake=createGithubRepoFake({issues:1}), hosts=[];
  const run=githubWriteRunner((_file,args,opts)=>{hosts.push(opts.env.GH_HOST);return fake.gh(args,opts);},{root:w.root,env:{},identity:'acme',machine:'one',now:()=>w.time});
  const r=api('POST','repos/acme/widgets/issues/1/comments',{body:'update <!-- pdd:autopilot:status -->'});
  r.args.push('--hostname=ghe.example'); await run('gh',r.args,r.options);
  assert.ok(hosts.length===2 && hosts.every(host=>host==='ghe.example'));
});

test('a status call with output transforms or without include preserves native output',async t=>{
  const w=world(t); let dispatched=0;
  const run=githubWriteRunner(async()=>{dispatched++;return {code:0,stdout:'native-output',stderr:''};},{root:w.root,env:{},identity:'acme',machine:'one',now:()=>w.time});
  const body={input:JSON.stringify({body:'update <!-- pdd:autopilot:status -->'})};
  for(const args of [
    ['api','--method','POST','repos/acme/widgets/issues/1/comments','--input','-'],
    ['api','--include','--method','POST','repos/acme/widgets/issues/1/comments','--input','-','--jq','.id']
  ]) assert.equal((await run('gh',args,body)).stdout,'native-output');
  assert.equal(dispatched,2);
});

test('absolute API URLs charge their actual host',async t=>{
  const w=world(t);
  const run=githubWriteRunner(async()=>({code:0,stdout:'{}'}),{root:w.root,env:{},identity:'acme',machine:'one',now:()=>w.time});
  await run('gh',['api','--method','PATCH','https://ghe.example/api/v3/repos/acme/widgets/issues/1']);
  assert.equal(w.budget({host:'ghe.example'}).usage().hour,1);
  assert.equal(w.budget().usage().hour,0);
});

test('a native adapter that drops env does not charge the private wrapper twice',async t=>{
  const w=world(t), bin=join(w.root,'original-bin'); mkdirSync(bin);
  const executable=join(bin,'gh');
  writeFileSync(executable,`#!${process.execPath}\nconst args=process.argv.slice(2);if(args[0]==='auth')process.stdout.write(JSON.stringify({hosts:{'github.com':[{login:'acme',active:true}]}}));else process.stdout.write('HTTP/2.0 200 OK\\r\\n\\r\\n{}');\n`,{mode:0o700});
  const env={HOME:w.root,...githubWriteEnvironment({root:w.root,env:{PATH:bin+':/usr/bin:/bin'}})};
  githubLedger({root:w.root,repository:'acme/widgets'}).record({at:w.time,api:'rest',purpose:'setup',status:200});
  const programs=[];
  const run=nativeGithubCounter(async(file,args,options)=>{programs.push(file);return {code:0,stdout:execFileSync(file,args,{env,input:options.input,encoding:'utf8'})};},{env,stateRoot:w.root,now:()=>w.time});
  await run('gh',['api','--include','--method','PATCH','repos/acme/widgets/issues/1','--input','-'],{input:'{}'});
  assert.ok(programs.length===2 && programs.every(file=>file===executable));
  assert.equal(w.budget().usage().hour,1);
});

test('absolute GraphQL endpoints retain conservative multi-mutation accounting',()=>{
  const query='mutation M { first: addComment(input:{}) {clientMutationId} second: addComment(input:{}) {clientMutationId} }';
  assert.equal(githubWriteCost(['api','https://api.github.com/graphql','--input','-'],{input:JSON.stringify({query})}),2);
  assert.equal(githubWriteCost(['api','https://api.github.com/graphql','--input','-'],{input:JSON.stringify({query:'query {viewer {login}}'})}),0);
  assert.equal(githubWriteCost(['api','graphql','--input','-'],{input:JSON.stringify({query:'mutation {first second}'})}),2);
});
