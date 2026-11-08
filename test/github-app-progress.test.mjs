import test from 'node:test';
import assert from 'node:assert/strict';
import { githubAppRunner } from '../src/github-app.mjs';
import { githubWriteRunner } from '../src/github-write-proxy.mjs';
import { githubWriteBudget } from '../src/github-writes.mjs';
import { githubAppWorld } from './helpers/github-app-world.mjs';
import { createGithubRepoFake } from './helpers/github-repo-fake.mjs';

const STATUS = '<!-- pdd:autopilot:status -->';
async function progressWorld(t, { injected = false, uncertain = false } = {}) {
  const w = await githubAppWorld(t);
  const fake = createGithubRepoFake({ issues: 1, owner: w.bot, now: () => w.time });
  let lost = uncertain;
  const transport = githubAppRunner(async (file, args, options) => {
    if (file === 'git') return w.gitExec(file, args, options);
    assert.equal(file, 'gh');
    assert.ok(w.tokens.includes(options.env.GH_TOKEN));
    // A personal auth status failure must not hide verified App metadata.
    if (args[0] === 'auth') {
      if (uncertain) throw Object.assign(Error('No personal login'), { code: 1 });
      return { code: 1, stdout: '', stderr: 'No personal login' };
    }
    const result = await fake.gh(args, options);
    if (lost && fake.calls.at(-1)?.method === 'POST') {
      lost = false;
      throw Error('Response lost after the server accepted the comment');
    }
    return result;
  }, { ...w.appPorts, env: w.env });
  const runner = () => githubWriteRunner(transport, {
    root: w.stateRoot, env: w.env, now: () => w.time,
    ...(injected ? { identity: () => w.identity } : {}),
  });
  const send = (run, body) => run('gh', ['api', '--include', '--method', 'POST',
    'repos/acme/widgets/issues/1/comments', '--input', '-'], {
    cwd: w.cwd, env: w.env, input: JSON.stringify({ body: `${STATUS} ${body}` }),
  });
  const usage = identity => githubWriteBudget({ root: w.stateRoot, env: w.env, identity, now: () => w.time }).usage();
  return { w, fake, runner, send, usage };
}

for (const injected of [false, true]) test(`App progress reconciles bot ownership with injected installation ${injected}`, async t => {
  const { w, fake, runner, send, usage } = await progressWorld(t, { injected });
  // Require pagination, and preserve comments from a person and another App.
  for (let n = 0; n < 101; n++) fake.comment(1, `${STATUS} other ${n}`, n % 2 ? 'someone' : 'other-app[bot]');
  const others = structuredClone(fake.issues.get(1).comments);
  const run = runner();
  await send(run, 'one');
  await send(run, 'one');
  await send(run, 'two');
  const comments = fake.issues.get(1).comments;
  assert.equal(fake.calls.filter(call => call.method === 'POST').length, 1);
  assert.equal(fake.calls.filter(call => call.method === 'PATCH').length, 1);
  assert.deepEqual(comments.slice(0, 101), others);
  assert.deepEqual(comments.filter(row => row.user === w.bot).map(row => row.body), [`${STATUS} two`]);
  assert.equal(usage(w.identity).hour, 2);
  assert.equal(usage(w.bot).hour, 0);
});

test('App progress retry lists afresh after an uncertain POST and skips the accepted body', async t => {
  const { w, fake, runner, send, usage } = await progressWorld(t, { injected: true, uncertain: true });
  await assert.rejects(send(runner(), 'one'));
  const reads = fake.calls.filter(call => call.method === 'GET').length;
  const retry = runner();
  await send(retry, 'one');
  assert.ok(fake.calls.filter(call => call.method === 'GET').length > reads);
  await send(retry, 'two');
  assert.equal(fake.calls.filter(call => call.method === 'POST').length, 1);
  assert.equal(fake.calls.filter(call => call.method === 'PATCH').length, 1);
  assert.equal(fake.issues.get(1).comments.length, 1);
  assert.equal(fake.issues.get(1).comments[0].body, `${STATUS} two`);
  assert.equal(usage(w.identity).hour, 2);
});

for (const metadata of [
  {},
  { githubIdentity: 'app:1234:installation:9877', githubBot: 'other-app[bot]' },
  { githubIdentity: 'app:1234:installation:9876', githubBot: 'someone' },
]) test(`App progress refuses unavailable or mismatched ownership metadata: ${JSON.stringify(metadata)}`, async t => {
  const w = await githubAppWorld(t);
  let effects = 0;
  const run = githubWriteRunner(async (_file, args) => {
    if (args[0] === 'auth') return { code: 1, stdout: '', stderr: '', ...metadata };
    effects++;
    return { code: 0, stdout: 'HTTP/2.0 200 OK\r\n\r\n[]', stderr: '' };
  }, { root: w.stateRoot, env: w.env, identity: w.identity, now: () => w.time });
  await assert.rejects(run('gh', ['api', '--include', '--method', 'POST',
    'repos/acme/widgets/issues/1/comments', '--input', '-'], {
    input: JSON.stringify({ body: `${STATUS} one` }),
  }), { code: 'github_identity_unknown' });
  assert.equal(effects, 0);
  assert.equal(githubWriteBudget({ root: w.stateRoot, identity: w.identity, now: () => w.time }).usage().hour, 0);
});
