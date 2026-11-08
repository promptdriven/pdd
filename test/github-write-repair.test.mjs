import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { createHash } from 'node:crypto';
import { spawn, spawnSync } from 'node:child_process';
import { setTimeout as delay } from 'node:timers/promises';
import { createGithubRepoFake } from './helpers/github-repo-fake.mjs';

const source = process.env.PDD_WRITE_REPAIR_SOURCE
  ? pathToFileURL(resolve(process.env.PDD_WRITE_REPAIR_SOURCE) + '/') : new URL('../src/', import.meta.url);
const budgetModule = new URL('github-writes.mjs', source).href;
const runnerModule = new URL('github-write-proxy.mjs', source).href;
const { githubWriteBudget } = await import(budgetModule);
const { githubWriteRunner } = await import(runnerModule);
const NOW = Date.parse('2026-11-07T00:00:00Z');
const STATUS = '<!-- pdd:autopilot:status -->';
function world(t) {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-write-repair-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  return root;
}
const lockAt = root => join(root, 'github-writes', createHash('sha256').update('github.com').digest('hex').slice(0, 20) + '.lock');

test('a process killed at recovery publication cannot block later reservations', t => {
  for (const phase of ['directory', 'owner', 'replacement']) {
    const root = world(t), lock = lockAt(root);
    fs.mkdirSync(join(root, 'github-writes'));
    fs.writeFileSync(lock, '2147483647');
    const script = `import * as fs from 'node:fs';
      import {githubWriteBudget} from ${JSON.stringify(budgetModule)};
      const port = {...fs, mkdirSync(path,...args) {
        const result = fs.mkdirSync(path,...args);
        if(${JSON.stringify(phase)}==='directory' && path.endsWith('.reap')) process.kill(process.pid,'SIGKILL');
        return result;
      }, writeFileSync(path,...args) {
        const result = fs.writeFileSync(path,...args);
        if(${JSON.stringify(phase)}==='owner' && path.includes('.reap/')) process.kill(process.pid,'SIGKILL');
        return result;
      }, linkSync(from,to) {
        const result = fs.linkSync(from,to);
        if(${JSON.stringify(phase)}==='replacement' && to.endsWith('.lock')) process.kill(process.pid,'SIGKILL');
        return result;
      }};
      githubWriteBudget({root:process.argv[1],identity:'acme',fs:port}).reserve(1);`;
    const child = spawnSync(process.execPath, ['--input-type=module', '-e', script, root], { encoding: 'utf8', timeout: 10_000 });
    assert.equal(child.signal, 'SIGKILL');
    assert.ok(fs.existsSync(lock + '.reap'));
    const budget = githubWriteBudget({ root, identity: 'acme', now: () => NOW });
    assert.doesNotThrow(() => budget.reserve(1));
    assert.equal(budget.usage().hour, 1);
    assert.equal(budget.usage().state, 'normal');
  }
});

test('status reports an unavailable budget while a live host lock blocks admission', t => {
  const root = world(t), lock = lockAt(root);
  const budget = githubWriteBudget({ root, identity: 'acme', now: () => NOW });
  budget.reserve(2);
  fs.writeFileSync(lock, String(process.pid));
  assert.throws(() => budget.reserve(1), { code: 'github_write_budget' });
  assert.equal(budget.usage().state, 'deferred');
  assert.equal(budget.usage().unavailable, true);
  fs.unlinkSync(lock);
  assert.equal(budget.usage().hour, 2);
});

for (const graphql of [false, true]) test(`${graphql ? 'thrown GraphQL query' : 'REST read'} throttle delays a separate writer without charging reads`, async t => {
  const root = world(t); let time = NOW, dispatched = 0;
  const outcome = { code: 1, stdout: 'HTTP/2.0 429\r\nRetry-After: 90\r\n\r\n{}', stderr: 'gh: HTTP 429 secondary rate limit' };
  const options = { root, env: {}, identity: 'acme', now: () => time };
  const reader = githubWriteRunner(async () => { if (graphql) throw outcome; return outcome; }, options);
  const writer = githubWriteRunner(async () => { dispatched++; return { code: 0, stdout: '{}' }; }, options);
  const args = graphql ? ['api', 'graphql', '-f', 'query=query {viewer {login}}'] : ['api', '--include', '--method', 'GET', 'repos/acme/widgets/issues/1'];
  if (graphql) await assert.rejects(reader('gh', args), error => error === outcome);
  else assert.equal(await reader('gh', args), outcome);
  assert.equal(githubWriteBudget(options).usage().hour, 0);
  const write = () => writer('gh', ['api', '--method', 'PATCH', 'repos/acme/widgets/issues/1']);
  await assert.rejects(write(), { code: 'github_write_budget', retryAt: NOW + 90_000 });
  time += 89_999;
  await assert.rejects(write(), { code: 'github_write_budget', retryAt: NOW + 90_000 });
  assert.equal(dispatched, 0);
  time++;
  await write();
  assert.equal(dispatched, 1);
  assert.equal(githubWriteBudget(options).usage().hour, 1);
});

test('simultaneous status submissions from separate runners reconcile one owned comment', async t => {
  const root = world(t), fake = createGithubRepoFake({ issues: 1, now: () => NOW });
  fake.comment(1, STATUS + ' another actor', 'someone');
  const options = { root, env: {}, identity: 'acme', now: () => NOW };
  const send = async () => {
    const run = githubWriteRunner((_file, args, opts) => fake.gh(args, opts), options);
    return run('gh', ['api', '--include', '--method', 'POST', 'repos/acme/widgets/issues/1/comments', '--input', '-'], { input: JSON.stringify({ body: STATUS + ' same progress' }) });
  };
  await Promise.all([send(), send(), send()]);
  assert.equal(fake.issues.get(1).comments.filter(c => c.user === 'acme').length, 1);
  assert.equal(fake.issues.get(1).comments.filter(c => c.user === 'someone').length, 1);
  assert.equal(fake.calls.filter(c => c.method === 'POST').length, 1);
  assert.equal(githubWriteBudget(options).usage().hour, 1);
});

test('separate chat processes serialize the listing and creation of a status comment', { timeout: 10_000 }, async t => {
  const root = world(t), fake = createGithubRepoFake({ issues: 1, now: () => NOW });
  const script = `import {githubWriteRunner} from ${JSON.stringify(runnerModule)};
    let id=0; const pending=new Map();
    process.on('message', message => {pending.get(message.id)(message.result); pending.delete(message.id);});
    const exec=(_file,args,options)=>new Promise(resolve=>{pending.set(++id,resolve);process.send({id,args,options});});
    const run=githubWriteRunner(exec,{root:process.argv[1],identity:'acme',env:{},now:()=>${NOW}});
    try { await run('gh',['api','--include','--method','POST','repos/acme/widgets/issues/1/comments','--input','-'],
      {input:JSON.stringify({body:${JSON.stringify(STATUS + ' same progress')}})}); }
    catch(error) {process.stderr.write(String(error.code||error));process.exitCode=1;}
    process.disconnect();`;
  const children = [];
  let posted;
  const firstPost = new Promise(resolvePost => { posted = resolvePost; });
  t.after(() => { for (const child of children) if (child.exitCode === null && child.signalCode === null) child.kill('SIGKILL'); });
  const run = () => new Promise((resolveChild, reject) => {
    const child = spawn(process.execPath, ['--input-type=module', '-e', script, root], { stdio: ['ignore', 'pipe', 'pipe', 'ipc'] });
    children.push(child); let stderr = '';
    child.stderr.on('data', data => { stderr += data; });
    child.on('error', reject);
    child.on('message', async ({ id, args, options }) => {
      // Keep the first create in flight long enough for an unguarded peer to
      // list the empty issue. The fake remains the single server for both chats.
      if (args.includes('POST')) { posted(); await delay(300); }
      const result = await fake.gh(args, options);
      if (child.connected) child.send({ id, result });
    });
    child.on('close', code => code === 0 ? resolveChild() : reject(Error(`child exit ${code}: ${stderr}`)));
  });
  const first = run();
  await firstPost;
  await Promise.all([first, run()]);
  assert.equal(fake.issues.get(1).comments.length, 1);
  assert.equal(fake.calls.filter(c => c.method === 'POST').length, 1);
});
