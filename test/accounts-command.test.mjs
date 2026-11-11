import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs/promises';
import { existsSync, mkdtempSync, readFileSync, realpathSync } from 'node:fs';
import { EventEmitter } from 'node:events';
import { PassThrough } from 'node:stream';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { runAccounts } from '../src/accounts-command.mjs';
import { poolPaths, readLog, readPool, updatePool } from '../src/accounts-store.mjs';

const ZONE = 'America/Los_Angeles';
const NOW = Date.parse('2026-11-11T14:58:00-08:00');
const pst = text => Date.parse(`2026-${text}:00-08:00`);
const freshHome = () => realpathSync(mkdtempSync(join(tmpdir(), 'pdd-accounts-command-')));
const sink = isTTY => ({ text: '', isTTY, write(chunk) { this.text += chunk; return true; } });

// Fake login facts: a fake auth.json holds only a synthetic account key; no real login is ever read.
const fakeLogin = (overrides = {}) => ({ calls: [], async codexLoginFacts(home) {
  this.calls.push(home);
  if (overrides[home]) return overrides[home];
  const file = join(home, 'auth.json');
  if (!existsSync(file)) return { state: 'none', accessExpiresAt: null, accountKey: null };
  const key = readFileSync(file, 'utf8').trim();
  return { state: key.startsWith('access-') ? 'access' : 'full', accessExpiresAt: null, accountKey: key || null };
} });

// Fake pick rules with the DESIGN.md section 5 shapes; `special` can fix the readiness of one login.
const makePick = (special = () => null) => ({
  loginReadiness(login, usage, now) {
    const fixed = special(login);
    if (fixed) return fixed;
    if (login.paused) return { ready: false, reason: 'paused', until: null };
    if (!usage) return { ready: false, reason: 'unknown', until: null };
    if (now - usage.readAt > 10 * 60_000) return { ready: false, reason: 'stale', until: null };
    if (usage.state === 'expired') return { ready: false, reason: 'expired', until: null };
    if (usage.state === 'unknown') return { ready: false, reason: 'unknown', until: null };
    if (usage.limitedUntil) return { ready: false, reason: 'limited', until: usage.limitedUntil };
    if (usage.week && usage.week.usedPercent >= login.stop.week) return { ready: false, reason: 'week', until: usage.week.resetsAt };
    if (usage.fiveHour && usage.fiveHour.usedPercent >= login.stop.fiveHour) return { ready: false, reason: 'five-hour', until: usage.fiveHour.resetsAt };
    return { ready: true, reason: 'ready', until: null };
  },
  poolSummary({ logins, usage, now }) {
    const rows = logins.map(login => ({ login, readiness: this.loginReadiness(login, usage[login.name] ?? null, now) }));
    const ready = rows.filter(row => row.readiness.ready), waiting = rows.filter(row => row.readiness.until).sort((a, b) => a.readiness.until - b.readiness.until);
    return { ready: ready.length, total: logins.length, next: ready[0]?.login.name ?? null,
      nextFree: waiting[0] ? { name: waiting[0].login.name, at: waiting[0].readiness.until } : null };
  },
});
const fakePick = makePick();

const fakeUsage = rows => ({ reads: 0, loads: 0,
  async readAllUsage(logins, { now }) { this.reads++; return logins.map(login => ({ name: login.name, ...rows[login.name] })); },
  async loadUsage() { this.loads++; return { version: 1, rows }; } });

async function run(action, { env, operands = [], options = {}, tty = false, input = '', ports = {}, cwd } = {}) {
  const stdout = sink(tty), stderr = sink(false), stdin = new PassThrough();
  stdin.isTTY = tty;
  if (input) stdin.write(input);
  const code = await runAccounts({ action, operands, options, cwd: cwd ?? env.HOME, env, stdin, stdout, stderr },
    { timeZone: ZONE, now: () => NOW, ...ports });
  return { code, out: stdout.text, err: stderr.text };
}

async function seed(env, logins, extra = {}) {
  await updatePool({ env }, pool => ({ ...pool, ...extra, logins: logins.map(row => ({ provider: 'codex', home: `/synthetic/${row.name}`, ...row })) }));
}

async function makeFolder(root, name, key) {
  const folder = join(root, name);
  await fs.mkdir(folder, { recursive: true });
  if (key !== undefined) await fs.writeFile(join(folder, 'auth.json'), `${key}\n`);
  return folder;
}

async function designPool() {
  const env = { HOME: freshHome() }, root = join(env.HOME, '.pdd-codex');
  const kinds = { cx5: 'acct-cx5', cx6: 'acct-cx6', work3: 'access-work3', work2: 'access-work2', cx2: 'acct-cx2', work1: 'access-work1' };
  for (const [name, key] of Object.entries(kinds)) await makeFolder(root, name, key);
  await seed(env, Object.keys(kinds).map(name => ({ name, home: join(root, name), paused: name === 'cx2' })), { order: Object.keys(kinds) });
  const rows = {
    cx5: { state: 'ok', plan: 'team', week: { usedPercent: 39, resetsAt: pst('11-17T12:49') }, fiveHour: { usedPercent: 31, resetsAt: pst('11-11T18:53') }, accessExpiresAt: pst('11-21T14:33'), readAt: NOW },
    cx6: { state: 'ok', plan: 'team', week: { usedPercent: 16, resetsAt: pst('11-18T11:48') }, fiveHour: { usedPercent: 100, resetsAt: pst('11-11T16:48') }, accessExpiresAt: pst('11-21T08:56'), readAt: NOW },
    work3: { state: 'ok', plan: 'pro', week: { usedPercent: 100, resetsAt: pst('11-13T15:28') }, fiveHour: null, accessExpiresAt: pst('11-21T10:02'), readAt: NOW },
    work2: { state: 'ok', plan: 'pro', week: { usedPercent: 32, resetsAt: pst('11-16T17:34') }, fiveHour: null, accessExpiresAt: pst('11-21T10:02'), readAt: NOW },
    cx2: { state: 'ok', plan: 'team', week: { usedPercent: 37, resetsAt: pst('11-17T12:49') }, fiveHour: { usedPercent: 0, resetsAt: pst('11-11T19:42') }, accessExpiresAt: pst('11-15T17:50'), readAt: NOW },
    work1: { state: 'expired', plan: null, week: null, fiveHour: null, accessExpiresAt: Date.parse('2026-10-27T23:02:00-07:00'), readAt: NOW },
  };
  return { env, root, rows };
}

const DESIGN_LIST = `Logins on this machine (local mode, no login server). Usage read 14:58 PST. Read only: no refresh, nothing spent.

#   NAME   KIND         PLAN  WEEK  WEEK RESETS   5H    5H RESETS     ACCESS ENDS   STATE
1   cx5    login        team  39%   Nov 17 12:49  31%   Nov 11 18:53  Nov 21 14:33  ready
2   cx6    login        team  16%   Nov 18 11:48  100%  Nov 11 16:48  Nov 21 08:56  limited (5h) until Nov 11 16:48
3   work3  access copy  pro   100%  Nov 13 15:28  -     -             Nov 21 10:02  limited (week) until Nov 13 15:28
4   work2  access copy  pro   32%   Nov 16 17:34  -     -             Nov 21 10:02  ready
-   cx2    login        team  37%   Nov 17 12:49  0%    Nov 11 19:42  Nov 15 17:50  paused
-   work1  access copy  -     -     -             -     -             Oct 27 23:02  access ended (this read never refreshes)

Next step uses cx5. Ready: 2 of 6. Next free: cx6 at Nov 11 16:48 PST.
Resets: never for every login.
`;

test('list reproduces the design table from fake facts, usage and pick rows', async () => {
  const { env, rows } = await designPool(), usage = fakeUsage(rows);
  const result = await run('list', { env, ports: { accountsLogin: fakeLogin(), accountsUsage: usage, accountsPick: fakePick } });
  assert.equal(result.err, '');
  assert.equal(result.out, DESIGN_LIST);
  assert.equal(result.code, 0);
  assert.equal(usage.reads, 1);
  assert.equal(usage.loads, 0);
});

test('list --json gives the same facts as data', async () => {
  const { env, rows } = await designPool();
  const result = await run('list', { env, options: { '--json': true }, ports: { accountsLogin: fakeLogin(), accountsUsage: fakeUsage(rows), accountsPick: fakePick } });
  assert.equal(result.code, 0);
  const data = JSON.parse(result.out);
  assert.deepEqual(Object.keys(data), ['mode', 'readAt', 'logins', 'next', 'ready', 'total', 'nextFree']);
  assert.deepEqual({ ...data, logins: data.logins.length }, { mode: 'local', readAt: NOW, logins: 6, next: 'cx5', ready: 2, total: 6, nextFree: { name: 'cx6', at: pst('11-11T16:48') } });
  assert.deepEqual(data.logins[1], { position: 2, name: 'cx6', provider: 'codex', kind: 'login', plan: 'team',
    week: { usedPercent: 16, resetsAt: pst('11-18T11:48') }, fiveHour: { usedPercent: 100, resetsAt: pst('11-11T16:48') }, accessExpiresAt: pst('11-21T08:56'),
    state: 'limited (5h) until Nov 11 16:48', reason: 'five-hour', until: pst('11-11T16:48'), paused: false, reset: 'never' });
  assert.deepEqual(data.logins[4].position, 5);
  assert.deepEqual([data.logins[4].paused, data.logins[4].reason], [true, 'paused']);
  assert.deepEqual([data.logins[5].kind, data.logins[5].week, data.logins[5].state], ['access copy', null, 'access ended (this read never refreshes)']);
});

test('list --no-read uses the cache only and marks old rows stale', async () => {
  const { env, rows } = await designPool();
  const old = Object.fromEntries(Object.entries(rows).map(([name, row]) => [name, { ...row, readAt: NOW - 30 * 60_000 }]));
  const usage = fakeUsage(old);
  const result = await run('list', { env, options: { '--no-read': true }, ports: { accountsLogin: fakeLogin(), accountsUsage: usage, accountsPick: fakePick } });
  assert.equal(result.code, 0);
  assert.deepEqual([usage.reads, usage.loads], [0, 1]);
  assert.match(result.out, /^Logins on this machine \(local mode, no login server\)\. Usage from the cache, read 14:28 PST\. Read only/);
  assert.match(result.out, /\n1 +cx5 .* stale\n/);
  assert.match(result.out, /\n- +cx2 .* paused\n/);
  assert.match(result.out, /No login is ready now\. Ready: 0 of 6\.\n/);
});

test('list states its other reasons, reset settings and the empty pool', async () => {
  const env = { HOME: freshHome() };
  const empty = await run('list', { env, ports: { accountsLogin: null, accountsUsage: null, accountsPick: null } });
  assert.deepEqual(empty, { code: 0, out: 'No logins on this machine yet. Run pdd accounts import PATH or pdd accounts add NAME.\n', err: '' });
  await seed(env, [{ name: 'a', reset: 'ask' }, { name: 'b', reset: 'auto' }, { name: 'c' }, { name: 'd', reset: 'ask' }], { order: ['a', 'b', 'c', 'd'] });
  const rows = { a: { state: 'unknown', note: 'read timed out', readAt: NOW }, b: { state: 'ok', limitedUntil: pst('11-12T09:05'), limitReason: 'credits', readAt: NOW },
    c: { state: 'no-login', readAt: NOW }, d: { state: 'ok', plan: 'plus', week: { usedPercent: 12.9, resetsAt: null }, readAt: NOW } };
  const pick = makePick(login => login.name === 'c' ? { ready: false, reason: 'no-login', until: null } : null);
  const result = await run('list', { env, ports: { accountsLogin: fakeLogin(), accountsUsage: fakeUsage(rows), accountsPick: pick } });
  assert.equal(result.code, 0);
  assert.match(result.out, /\n1 +a +- +- .* unknown \(read timed out\)\n/);
  assert.match(result.out, /\n2 +b .* limited \(credits\) until Nov 12 09:05\n/);
  assert.match(result.out, /\n- +c .* no login\n/);
  assert.match(result.out, /\n4 +d +- +plus +12% +- .* ready\n/);
  assert.match(result.out, /Next step uses d\. Ready: 1 of 4\. Next free: b at Nov 12 09:05 PST\.\nResets: ask for a, d; auto for b; never for the others\.\n$/);
});

test('a missing module gives one clear line and exit 2', async () => {
  const { env, rows } = await designPool();
  const result = await run('list', { env, ports: { accountsLogin: fakeLogin(), accountsUsage: fakeUsage(rows), accountsPick: null } });
  assert.deepEqual(result, { code: 2, out: '', err: 'pdd accounts list needs src/accounts-pick.mjs, which this pdd does not have yet.\n' });
  const lacking = await run('list', { env, ports: { accountsLogin: {}, accountsUsage: fakeUsage(rows), accountsPick: fakePick } });
  assert.equal(lacking.err, 'pdd accounts list needs src/accounts-login.mjs, which this pdd does not have yet.\n');
  for (const [action, operands, options, file] of [['share', ['cx5'], { '--with': 'ali' }, 'accounts-cloud.mjs'], ['accept', ['cx5'], {}, 'accounts-cloud.mjs'],
    ['group-create', ['friends'], { '--github': 'promptdriven' }, 'accounts-cloud.mjs'], ['reset', ['cx5'], {}, 'accounts-reset.mjs']]) {
    const missing = await run(action, { env, operands, options, ports: { accountsCloud: null, accountsReset: null } });
    assert.deepEqual(missing, { code: 2, out: '', err: `pdd accounts ${action.replace('-', ' ')} needs src/${file}, which this pdd does not have yet.\n` });
  }
});

test('import registers folders as they are and refuses links, missing logins, bad names and repeats', async () => {
  const env = { HOME: freshHome() }, root = join(env.HOME, '.pdd-codex');
  const cx5 = await makeFolder(root, 'cx5', 'acct-1'), work2 = await makeFolder(root, 'work2', 'access-2');
  const empty = await makeFolder(root, 'empty-codex-home'), bad = await makeFolder(root, 'Bad Name', 'acct-3');
  const twin = await makeFolder(root, 'twin', 'acct-1'), odd = await makeFolder(root, 'odd', 'acct-4');
  await fs.symlink(join(env.HOME, '.codex'), join(root, 'interactive'));
  const linked = await makeFolder(root, 'linked');
  await fs.symlink(join(cx5, 'auth.json'), join(linked, 'auth.json'));
  await fs.writeFile(join(root, 'plain-file'), 'x');
  const before = await fs.stat(join(cx5, 'auth.json'));
  const login = fakeLogin({ [odd]: { state: 'unreadable', accessExpiresAt: null, accountKey: null } });
  const paths = ['.pdd-codex/cx5', work2, empty, bad, twin, odd, join(root, 'interactive'), linked, join(root, 'plain-file'), join(root, 'missing'), cx5];
  const result = await run('import', { env, operands: paths, ports: { accountsLogin: login } });
  assert.equal(result.code, 1);
  assert.equal(result.out, `Imported cx5 from ${cx5} (login).\nImported work2 from ${work2} (access copy).\n`);
  assert.deepEqual(result.err.trimEnd().split('\n'), [
    `No Codex login in ${empty}. Use pdd accounts add NAME to sign in.`,
    'Bad Name is not a valid login name. Use --name NAME with a-z, 0-9, ., _ or - (at most 32).',
    `${twin} has the same Codex account as cx5. pdd keeps one name for each account.`,
    `pdd cannot read the Codex login in ${odd}.`,
    `${join(root, 'interactive')} is a link (to ${join(env.HOME, '.codex')}). pdd imports only a folder with its own login file.`,
    `${join(linked, 'auth.json')} is a link (to ${join(cx5, 'auth.json')}). pdd imports only a folder with its own login file.`,
    `${join(root, 'plain-file')} is not a folder.`,
    `No folder at ${join(root, 'missing')}.`,
    'The name cx5 is in use. Use --name NAME.',
  ]);
  const pool = await readPool({ env });
  assert.deepEqual(pool.logins.map(row => [row.name, row.home, row.source, row.mode, row.reset, row.paused]),
    [['cx5', cx5, 'import', 'local', 'never', false], ['work2', work2, 'import', 'local', 'never', false]]);
  assert.deepEqual(pool.order, []);
  const after = await fs.stat(join(cx5, 'auth.json'));
  assert.equal(readFileSync(join(cx5, 'auth.json'), 'utf8'), 'acct-1\n');
  assert.deepEqual([after.mtimeMs, after.mode, after.ino], [before.mtimeMs, before.mode, before.ino]);
  assert.deepEqual((await readLog({ env })).map(row => [row.action, row.login, row.detail]), [['import', 'cx5', `folder ${cx5}`], ['import', 'work2', `folder ${work2}`]]);

  const again = await run('import', { env, operands: [cx5], options: { '--name': 'other' }, ports: { accountsLogin: login } });
  assert.deepEqual([again.code, again.err], [1, `${cx5} is already in the pool as cx5.\n`]);
  const named = await run('import', { env, operands: [bad], options: { '--name': 'cx3' }, ports: { accountsLogin: login } });
  assert.deepEqual([named.code, named.out], [0, `Imported cx3 from ${bad} (login).\n`]);
  assert.deepEqual((await run('import', { env, operands: [cx5, work2], options: { '--name': 'x' } })).code, 2);
  assert.deepEqual(await run('import', { env, operands: [cx5], options: { '--provider': 'claude' } }), { code: 2, out: '', err: 'pdd accounts import takes Codex folders only for now.\n' });
});

test('import and add upload only when a login server is set and --local is not given', async () => {
  const env = { HOME: freshHome(), PDD_ACCOUNTS_URL: 'https://accounts.synthetic.test' }, root = join(env.HOME, 'h');
  const calls = [], cloud = { async runCloudAccounts(action, input) { calls.push([action, input.name, input.home]); return { exitCode: 0, message: `Uploaded ${input.name}.` }; } };
  const a = await makeFolder(root, 'a', 'acct-a'), b = await makeFolder(root, 'b', 'acct-b');
  const first = await run('import', { env, operands: [a], ports: { accountsLogin: fakeLogin(), accountsCloud: cloud } });
  assert.deepEqual([first.code, first.out], [0, `Imported a from ${a} (login).\nUploaded a.\n`]);
  const local = await run('import', { env, operands: [b], options: { '--local': true }, ports: { accountsLogin: fakeLogin(), accountsCloud: cloud } });
  assert.equal(local.code, 0);
  assert.deepEqual(calls, [['upload', 'a', a]]);
  const missing = await run('import', { env: { ...env, HOME: freshHome() }, operands: [b], ports: { accountsLogin: fakeLogin(), accountsCloud: null } });
  assert.deepEqual([missing.code, missing.err], [2, 'pdd accounts import needs src/accounts-cloud.mjs, which this pdd does not have yet.\n']);
});

function fakeSpawn(behave) {
  const calls = [];
  return { calls, spawn(command, args, options) {
    calls.push({ command, args, home: options.env.CODEX_HOME, stdio: options.stdio });
    const child = new EventEmitter();
    queueMicrotask(async () => { child.emit('close', await behave(options.env.CODEX_HOME)); });
    return child;
  } };
}

test('add makes a private folder with the file store and runs only the fake Codex sign-in there', async () => {
  const env = { HOME: freshHome() }, signIn = fakeSpawn(async home => { await fs.writeFile(join(home, 'auth.json'), 'acct-new\n'); return 0; });
  const result = await run('add', { env, operands: ['cx7'], tty: true, ports: { accountsLogin: fakeLogin(), spawn: signIn.spawn } });
  const folder = join(env.HOME, '.pdd', 'codex', 'cx7');
  assert.equal(result.err, '');
  assert.equal(result.out, `Signing in to Codex for cx7 in ${folder}. Follow the Codex steps below.\nAdded cx7 (${folder}).\n`);
  assert.equal(result.code, 0);
  assert.deepEqual(signIn.calls, [{ command: 'codex', args: ['login', '--device-auth'], home: folder, stdio: 'inherit' }]);
  assert.equal((await fs.stat(folder)).mode & 0o777, 0o700);
  assert.equal(readFileSync(join(folder, 'config.toml'), 'utf8'), 'cli_auth_credentials_store = "file"\n');
  assert.equal((await fs.stat(join(folder, 'config.toml'))).mode & 0o777, 0o600);
  const row = (await readPool({ env })).logins[0];
  assert.deepEqual([row.name, row.home, row.source, row.reset], ['cx7', folder, 'add', 'never']);
  assert.deepEqual((await readLog({ env })).map(item => [item.action, item.login]), [['add', 'cx7']]);
});

test('add refuses without a person at a terminal, and removes its folder when the sign-in fails or repeats an account', async () => {
  const env = { HOME: freshHome() }, folder = join(env.HOME, '.pdd', 'codex', 'cx8');
  const none = fakeSpawn(async () => 0);
  assert.deepEqual(await run('add', { env, operands: ['cx8'], ports: { accountsLogin: fakeLogin(), spawn: none.spawn } }),
    { code: 2, out: '', err: 'pdd accounts add needs a person at a terminal: it runs the Codex sign-in.\n' });
  assert.equal(none.calls.length, 0);
  assert.equal(existsSync(folder), false);
  assert.deepEqual((await run('add', { env, operands: ['cx8'], options: { '--group': 'friends' }, tty: true })).code, 2);
  assert.deepEqual((await run('add', { env, operands: ['Bad'], tty: true, ports: { accountsLogin: fakeLogin() } })).err,
    'Bad is not a valid login name. Use a-z, 0-9, ., _ or - (at most 32).\n');

  const failed = await run('add', { env, operands: ['cx8'], tty: true, ports: { accountsLogin: fakeLogin(), spawn: fakeSpawn(async () => 1).spawn } });
  assert.deepEqual([failed.code, failed.err], [1, `The Codex sign-in did not finish. pdd removed ${folder}; nothing was added.\n`]);
  assert.equal(existsSync(folder), false);

  const home = await makeFolder(join(env.HOME, 'old'), 'cx1', 'acct-same');
  await run('import', { env, operands: [home], ports: { accountsLogin: fakeLogin() } });
  const twin = await run('add', { env, operands: ['cx8'], tty: true,
    ports: { accountsLogin: fakeLogin(), spawn: fakeSpawn(async dir => { await fs.writeFile(join(dir, 'auth.json'), 'acct-same\n'); return 0; }).spawn } });
  assert.deepEqual([twin.code, twin.err], [1, `This Codex account is in the pool as cx1. pdd removed ${folder}; nothing was added.\n`]);
  assert.equal(existsSync(folder), false);
  assert.deepEqual((await readPool({ env })).logins.map(row => row.name), ['cx1']);
  await fs.mkdir(folder, { recursive: true });
  assert.deepEqual((await run('add', { env, operands: ['cx8'], tty: true, ports: { accountsLogin: fakeLogin() } })).err,
    `${folder} exists. Use pdd accounts import ${folder}, or move it away first.\n`);
});

test('add runs a fake codex program with CODEX_HOME set to the new folder', async () => {
  const env = { HOME: freshHome(), PATH: process.env.PATH }, bin = join(env.HOME, 'bin');
  await fs.mkdir(bin);
  const codex = join(bin, 'codex');
  await fs.writeFile(codex, '#!/bin/sh\nprintf "%s\\n" "$*" > "$CODEX_HOME/args.txt"\nprintf "acct-fake\\n" > "$CODEX_HOME/auth.json"\n', { mode: 0o755 });
  const result = await run('add', { env, operands: ['cx9'], tty: true, ports: { accountsLogin: fakeLogin(), codexCommand: codex } });
  const folder = join(env.HOME, '.pdd', 'codex', 'cx9');
  assert.equal(result.code, 0, result.err);
  assert.equal(readFileSync(join(folder, 'args.txt'), 'utf8'), 'login --device-auth\n');
});

test('order shows the pool order and changes it with every form', async () => {
  const env = { HOME: freshHome() };
  await seed(env, ['a', 'b', 'c', 'd'].map((name, index) => ({ name, addedAt: `2026-11-0${index + 1}T00:00:00.000Z`, paused: name === 'c' })), { order: ['owner/shared'] });
  const show = await run('order', { env });
  assert.deepEqual(show, { code: 0, out: 'Pool order (steps use the first ready login):\n1  a\n2  b\n3  c  paused\n4  d\n', err: '' });
  const names = async () => (await readPool({ env })).order;
  assert.equal((await run('order', { env, operands: ['d', 'b'] })).out, 'New pool order:\n1  d\n2  b\n3  a\n4  c  paused\n');
  assert.deepEqual(await names(), ['d', 'b', 'a', 'c', 'owner/shared']);
  await run('order', { env, options: { '--first': 'c' } });
  assert.deepEqual(await names(), ['c', 'd', 'b', 'a', 'owner/shared']);
  await run('order', { env, options: { '--last': 'd' } });
  assert.deepEqual(await names(), ['c', 'b', 'a', 'd', 'owner/shared']);
  await run('order', { env, options: { '--after': ['c', 'a'] } });
  assert.deepEqual(await names(), ['b', 'a', 'c', 'd', 'owner/shared']);
  assert.deepEqual(await run('order', { env, options: { '--first': 'b' } }), { code: 0, out: 'Order unchanged.\n', err: '' });
  assert.deepEqual((await readLog({ env })).map(row => [row.action, row.login, row.detail]),
    [['order', null, 'd, b, a, c'], ['order', null, 'c, d, b, a'], ['order', null, 'c, b, a, d'], ['order', null, 'b, a, c, d']]);

  const refusals = [
    [{ operands: ['a'], options: { '--first': 'b' } }, 2, 'Use one of NAME..., --first NAME, --last NAME, --after NAME OTHER or --edit.'],
    [{ options: { '--after': ['a'] } }, 2, 'Use --after NAME OTHER: it moves NAME right after OTHER.'],
    [{ options: { '--after': ['a', 'a'] } }, 2, 'Use --after NAME OTHER: it moves NAME right after OTHER.'],
    [{ operands: ['a', 'b', 'a'] }, 2, 'a is named twice.'],
    [{ operands: ['ghost'] }, 1, 'No login named ghost.'],
    [{ options: { '--after': ['a', 'ghost'] } }, 1, 'No login named ghost.'],
    [{ options: { '--edit': true } }, 2, 'pdd accounts order --edit needs a person at a terminal.'],
    [{ options: { '--edit': true }, tty: true }, 2, 'Set VISUAL or EDITOR, or use pdd accounts order NAME...'],
  ];
  for (const [input, code, err] of refusals) assert.deepEqual(await run('order', { env, ...input }), { code, out: '', err: `${err}\n` });
  assert.deepEqual(await names(), ['b', 'a', 'c', 'd', 'owner/shared']);
});

test('order --edit opens the editor on the order file and saves the names it leaves', async () => {
  const env = { HOME: freshHome(), PATH: process.env.PATH }, editor = join(env.HOME, 'edit.sh'), seen = join(env.HOME, 'seen.txt');
  await seed(env, [{ name: 'a' }, { name: 'b' }, { name: 'c' }], { order: ['a', 'b', 'c'] });
  // The last argument is the file, as for an editor command with its own flag.
  await fs.writeFile(editor, `#!/bin/sh\nfor file; do :; done\ncp "$file" "${seen}"\nprintf '# kept comment\\n\\nc\\na\\n' > "$file"\n`, { mode: 0o755 });
  const result = await run('order', { env: { ...env, EDITOR: `${editor} --wait` }, options: { '--edit': true }, tty: true, ports: { tmpdir: env.HOME } });
  assert.deepEqual(result, { code: 0, out: 'New pool order:\n1  c\n2  a\n3  b\n', err: '' });
  assert.match(readFileSync(seen, 'utf8'), /^# .*\n# .*\na\nb\nc\n$/);
  assert.deepEqual((await fs.readdir(env.HOME)).filter(name => name.startsWith('pdd-accounts-order-')), [], 'the temp folder is removed');
  await fs.writeFile(editor, '#!/bin/sh\nexit 3\n', { mode: 0o755 });
  assert.deepEqual(await run('order', { env: { ...env, VISUAL: editor }, options: { '--edit': true }, tty: true }),
    { code: 1, out: '', err: 'The editor stopped with code 3. The order did not change.\n' });
});

test('pause and resume keep the place in the order', async () => {
  const env = { HOME: freshHome() };
  await seed(env, [{ name: 'a' }, { name: 'b' }], { order: ['a', 'b'] });
  assert.deepEqual(await run('pause', { env, operands: ['a'] }), { code: 0, out: 'Paused a. Steps skip it; it keeps its place in the order.\n', err: '' });
  assert.equal((await run('order', { env })).out, 'Pool order (steps use the first ready login):\n1  a  paused\n2  b\n');
  assert.deepEqual(await run('pause', { env, operands: ['a'] }), { code: 0, out: 'a is already paused.\n', err: '' });
  assert.deepEqual(await run('resume', { env, operands: ['a'] }), { code: 0, out: 'Resumed a.\n', err: '' });
  assert.deepEqual(await run('resume', { env, operands: ['a'] }), { code: 0, out: 'a is not paused.\n', err: '' });
  assert.deepEqual(await run('pause', { env, operands: ['ghost'] }), { code: 1, out: '', err: 'No login named ghost.\n' });
  assert.deepEqual((await readLog({ env })).map(row => [row.action, row.login]), [['pause', 'a'], ['resume', 'a']]);
});

test('set changes stop lines; the reset setting needs a person at a terminal and a typed yes', async () => {
  const env = { HOME: freshHome() };
  await seed(env, [{ name: 'work3' }]);
  const row = async () => (await readPool({ env })).logins[0];
  assert.deepEqual(await run('set', { env, operands: ['work3'] }), { code: 0, out: 'work3: stop lines week 97%, 5h 97%; reset never.\n', err: '' });
  assert.deepEqual(await run('set', { env, operands: ['work3'], options: { '--stop-week': '90', '--stop-5h': '95' } }),
    { code: 0, out: 'Saved work3: stop lines week 90%, 5h 95%; reset never.\n', err: '' });
  const refusal = 'Only a person at a terminal can change the reset setting. Run pdd accounts set work3 --reset auto in your own terminal.\n';
  assert.deepEqual(await run('set', { env, operands: ['work3'], options: { '--reset': 'auto', '--stop-week': '80' }, input: 'yes\n' }), { code: 2, out: '', err: refusal });
  assert.deepEqual(await run('set', { env: { ...env, PDD_AGENT: 'codex' }, operands: ['work3'], options: { '--reset': 'auto' }, tty: true, input: 'yes\n' }), { code: 2, out: '', err: refusal });
  const no = await run('set', { env, operands: ['work3'], options: { '--reset': 'auto' }, tty: true, input: 'y\n' });
  assert.deepEqual([no.code, no.err], [1, 'The reset setting did not change.\n']);
  assert.deepEqual([(await row()).reset, (await row()).stop], ['never', { week: 90, fiveHour: 95 }]);
  const yes = await run('set', { env, operands: ['work3'], options: { '--reset': 'auto' }, tty: true, input: 'yes\n' });
  assert.equal(yes.code, 0);
  assert.equal(yes.out, 'With auto, Autopilot may use a reset on work3 by itself when every login is out, at most one a day, and tells you.\n'
    + 'Type yes to set reset to auto for work3: Saved work3: stop lines week 90%, 5h 95%; reset auto.\n');
  assert.equal((await row()).reset, 'auto');
  assert.deepEqual((await readLog({ env })).map(item => [item.action, item.detail]), [['set', 'stop week 90, stop 5h 95'], ['set', 'reset auto']]);
});

test('remove forgets the row, never signs out, and keeps every folder that pdd did not make', async () => {
  const env = { HOME: freshHome() }, root = join(env.HOME, 'h');
  const imported = await makeFolder(root, 'cx5', 'acct-5'), made = await makeFolder(root, 'cx7', 'acct-7'), made2 = await makeFolder(root, 'cx8', 'acct-8');
  await seed(env, [{ name: 'cx5', home: imported }, { name: 'cx7', home: made, source: 'add' }, { name: 'cx8', home: made2, source: 'add' }], { order: ['cx7', 'cx5', 'cx8'] });
  const programs = [], ports = { spawn: (...args) => { programs.push(args); throw new Error('no program may run'); } };
  assert.deepEqual(await run('remove', { env, operands: ['cx5'], tty: true, input: 'y\n', ports }),
    { code: 0, out: `Removed cx5 from the pool. pdd did not sign out.\npdd kept ${imported} (pdd did not make it).\n`, err: '' });
  assert.equal(readFileSync(join(imported, 'auth.json'), 'utf8'), 'acct-5\n');
  assert.deepEqual(await run('remove', { env, operands: ['cx7'], ports }), { code: 0, out: `Removed cx7 from the pool. pdd did not sign out.\npdd kept ${made}.\n`, err: '' });
  assert.equal(existsSync(join(made, 'auth.json')), true);
  const asked = await run('remove', { env, operands: ['cx8'], tty: true, input: 'y\n', ports });
  assert.deepEqual(asked, { code: 0, out: `Delete ${made2} too? It holds the Codex login of cx8. [y/N] Removed cx8 from the pool. pdd did not sign out.\npdd deleted ${made2}.\n`, err: '' });
  assert.equal(existsSync(made2), false);
  assert.deepEqual(programs, []);
  const pool = await readPool({ env });
  assert.deepEqual([pool.logins, pool.order], [[], []]);
  assert.deepEqual((await readLog({ env })).map(row => [row.login, row.detail]), [['cx5', 'kept folder'], ['cx7', 'kept folder'], ['cx8', 'deleted folder']]);
  assert.deepEqual(await run('remove', { env, operands: ['cx5'] }), { code: 1, out: '', err: 'No login named cx5.\n' });
});

test('remove keeps an added folder when the person does not type y', async () => {
  const env = { HOME: freshHome() }, made = await makeFolder(join(env.HOME, 'h'), 'cx7', 'acct-7');
  await seed(env, [{ name: 'cx7', home: made, source: 'add' }]);
  const result = await run('remove', { env, operands: ['cx7'], tty: true, input: '\n' });
  assert.equal(result.out.endsWith(`pdd kept ${made}.\n`), true);
  assert.equal(existsSync(join(made, 'auth.json')), true);
});

test('home prints the folder and log shows the local changes', async () => {
  const env = { HOME: freshHome() };
  await seed(env, [{ name: 'cx5', home: '/synthetic/cx5' }]);
  assert.deepEqual(await run('home', { env, operands: ['cx5'] }), { code: 0, out: '/synthetic/cx5\n', err: '' });
  assert.deepEqual(await run('home', { env, operands: ['cx6'] }), { code: 1, out: '', err: 'No login named cx6.\n' });
  assert.deepEqual(await run('log', { env }), { code: 0, out: 'No changes in the local log yet.\n', err: '' });
  await run('pause', { env, operands: ['cx5'], ports: { now: () => NOW } });
  await run('set', { env, operands: ['cx5'], options: { '--stop-week': '90' } });
  const text = await run('log', { env, operands: ['cx5'] });
  assert.equal(text.code, 0);
  assert.match(text.out, /^Nov 11 14:58 PST {2}pause {2}cx5\n\w{3} \d+ \d\d:\d\d \w+ {2}set {2}cx5 {2}stop week 90\n$/);
  const json = JSON.parse((await run('log', { env, options: { '--json': true } })).out);
  assert.deepEqual(json.rows.map(row => [row.action, row.login]), [['pause', 'cx5'], ['set', 'cx5']]);
  assert.deepEqual(Object.keys(json.rows[0]), ['at', 'action', 'login', 'detail']);
});

test('login server forms and reset pass their words to the other modules', async () => {
  const env = { HOME: freshHome() }, calls = [];
  const cloud = { async runCloudAccounts(action, input) { calls.push([action, { ...input, env: undefined }]); return { exitCode: action === 'leave' ? 1 : 0, message: `${action} done` }; } };
  const share = await run('share', { env, operands: ['shared-200'], options: { '--with': 'ali, mehtab,' }, ports: { accountsCloud: cloud } });
  assert.deepEqual(share, { code: 0, out: 'share done\n', err: '' });
  assert.deepEqual((await run('leave', { env, operands: ['shared-200'], ports: { accountsCloud: cloud } })), { code: 1, out: '', err: 'leave done\n' });
  await run('group-create', { env, operands: ['friends'], options: { '--github': 'promptdriven/team' }, ports: { accountsCloud: cloud } });
  assert.deepEqual(calls, [['share', { name: 'shared-200', env: undefined, with: ['ali', 'mehtab'] }], ['leave', { name: 'shared-200', env: undefined }],
    ['group-create', { name: 'friends', env: undefined, github: 'promptdriven/team' }]]);
  assert.deepEqual(await run('unshare', { env, operands: ['x'], options: { '--with': ' , ' }, ports: { accountsCloud: cloud } }),
    { code: 2, out: '', err: 'Use pdd accounts unshare NAME --with USER,...\n' });
  for (const options of [{}, { '--with': 'ali', '--github': 'org' }])
    assert.deepEqual(await run('group-create', { env, operands: ['g'], options, ports: { accountsCloud: cloud } }),
      { code: 2, out: '', err: 'Use pdd accounts group create GROUP --with USER,... or --github ORG[/TEAM].\n' });
  const resets = [];
  const reset = await run('reset', { env, operands: ['work3'], ports: { accountsReset: { runReset: async input => { resets.push(input.name); return 0; } } } });
  assert.deepEqual([reset.code, resets], [0, ['work3']]);
});

test('a bad pool file gives its one line and exit 1, and stays as it was', async () => {
  const env = { HOME: freshHome() }, { configDir, poolFile } = poolPaths(env);
  await fs.mkdir(configDir, { recursive: true });
  await fs.writeFile(poolFile, '{ broken');
  const result = await run('pause', { env, operands: ['cx5'] });
  assert.deepEqual(result, { code: 1, out: '', err: `The pool file ${poolFile} is not valid: it is not valid JSON. pdd did not change it. Fix or move the file, then try again.\n` });
  assert.equal(readFileSync(poolFile, 'utf8'), '{ broken');
});
