// Issue 2901: replay caller login and pane dispatch through the public runner with fake Herdr and fake agents.
import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash, randomUUID } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, readdirSync, statSync, symlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { fixture } from './helpers/workflow-runner-fixture.mjs';

// These expectations come from the requested login contract, independent of LOGIN_VARIABLES in the implementation.
const CODEX_LOGIN = ['CODEX_ACCESS_TOKEN', 'OPENAI_FEDERATION_RULE_ID', 'OPENAI_IDENTITY_TOKEN_FILE', 'OPENAI_WORKLOAD_IDENTITY_CONTEXT'];
const hash = value => createHash('sha256').update(value).digest('hex');
const loginFiles = dir => readdirSync(dir).filter(name => /^login-[0-9a-f-]+\.env$/.test(name));

async function world(t, agent) {
  const f = await fixture(t, { agent });
  f.ports.skipMetricsDelivery = true;
  const bin = join(f.base, 'bin');
  mkdirSync(bin);
  // Force the login child to use bash as sh. Bash reads exported SHELLOPTS even with -c.
  symlinkSync('/bin/bash', join(bin, 'sh'));
  const names = [...CODEX_LOGIN, 'CLAUDE_CODE_OAUTH_TOKEN'];
  writeFileSync(join(bin, agent), `#!${process.execPath}
import { createHash } from 'node:crypto';
const values = Object.fromEntries(${JSON.stringify(names)}.map(name => [name,
  process.env[name] === undefined ? null : createHash('sha256').update(process.env[name]).digest('hex')]));
process.stdout.write(JSON.stringify(values));
`, { mode: 0o755 });
  f.serverEnv = { HOME: f.ports.env.HOME, PATH: `${bin}:/usr/bin:/bin` };
  f.commands = [];
  const herdr = f.ports.herdr;
  f.ports.herdr = async args => {
    if (args[0] === 'pane' && args[1] === 'run') f.commands.push(args[3]);
    return herdr(args);
  };
  f.execute = command => {
    const out = spawnSync('/bin/bash', ['-c', command], { cwd: f.base, env: f.serverEnv, encoding: 'utf8' });
    assert.equal(out.status, 0, 'the recorded chat command starts the fake agent');
    return { values: JSON.parse(out.stdout), stderr: out.stderr };
  };
  return f;
}

for (const name of CODEX_LOGIN) {
  test(`2901: Codex removes the server's ${name} when the caller has none`, async t => {
    const f = await world(t, 'codex');
    f.serverEnv[name] = `stale-${randomUUID()}`;
    assert.equal((await f.run()).exitCode, 0);
    assert.equal(f.execute(f.commands[0]).values[name], null, 'the server login is absent in the chat');
  });

  test(`2901: Codex receives the caller's ${name} instead of the server's value`, async t => {
    const f = await world(t, 'codex');
    const value = `caller-${randomUUID()}`;
    f.ports.env[name] = value;
    f.serverEnv[name] = `stale-${randomUUID()}`;
    assert.equal((await f.run()).exitCode, 0);
    assert.equal(f.execute(f.commands[0]).values[name], hash(value), 'the caller login reaches the chat');
    assert.deepEqual(loginFiles(f.record().runDir), []);
  });
}

for (const options of ['xtrace', 'verbose', 'xtrace:verbose']) {
  test(`2901: inherited SHELLOPTS=${options} cannot print the chat's login values`, async t => {
    const f = await world(t, 'claude');
    const value = `synthetic-${randomUUID()}`;
    f.ports.env.CLAUDE_CODE_OAUTH_TOKEN = value;
    f.serverEnv.SHELLOPTS = options;
    assert.equal((await f.run()).exitCode, 0);
    const out = f.execute(f.commands[0]);
    assert.equal(out.values.CLAUDE_CODE_OAUTH_TOKEN, hash(value), 'the agent still receives the login');
    assert.equal(out.stderr.includes(value), false, 'shell output does not contain the login value');
    assert.deepEqual(loginFiles(f.record().runDir), []);
  });
}

test('2901: a failed pane run deletes its private login file without retrying the launch', async t => {
  const f = await world(t, 'claude');
  f.ports.env.CLAUDE_CODE_OAUTH_TOKEN = `synthetic-${randomUUID()}`;
  const herdr = f.ports.herdr;
  let file, mode, dispatches = 0;
  f.ports.herdr = async args => {
    if (args[0] !== 'pane' || args[1] !== 'run') return herdr(args);
    dispatches++;
    const dir = f.record().runDir;
    const name = loginFiles(dir)[0];
    if (name) { file = join(dir, name); mode = statSync(file).mode & 0o777; }
    throw Object.assign(new Error('injected transport failure'), { code: 'transport_error' });
  };
  await f.run();
  assert.equal(dispatches, 1, 'an uncertain pane dispatch is not retried');
  assert.ok(file, 'a private login file exists when the pane launch is sent');
  assert.equal(mode, 0o600);
  assert.equal(existsSync(file), false, 'a failed pane launch deletes the login file');
  assert.deepEqual(loginFiles(f.record().runDir), []);
});
