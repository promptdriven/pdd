import test from 'node:test';
import assert from 'node:assert/strict';
import { EventEmitter } from 'node:events';
import { PassThrough } from 'node:stream';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { stepLogin, classifyAgentEnd, afterStep, startBinding, poolStatusLines } from '../src/autopilot-pool.mjs';
import { poolPaths, readLog, updatePool } from '../src/accounts-store.mjs';
import { loadUsage } from '../src/accounts-usage.mjs';

// The real store, usage and pick modules, a temp HOME, fake logins and a fake `codex app-server` (spawn port).
// Every secret below is made up for this test.
const MIN = 60_000, NOW = Date.UTC(2026, 10, 11, 14, 0), S = ms => Math.floor(ms / 1000);
const b64 = value => Buffer.from(JSON.stringify(value)).toString('base64url');
const jwt = payload => `${b64({ alg: 'none' })}.${b64(payload)}.fake-signature`;
const REFRESH = 'rt-fake-refresh-never-print';
const accountOf = name => `acct-fake-${name}`;
const accessOf = name => jwt({ exp: S(NOW) + 86_400, 'https://api.openai.com/auth': { chatgpt_account_id: accountOf(name) } });
const idOf = name => jwt({ email: `${name}.owner@example.test` });
const authFile = name => JSON.stringify({ auth_mode: 'chatgpt', tokens: { id_token: idOf(name), access_token: accessOf(name), refresh_token: REFRESH, account_id: accountOf(name) }, last_refresh: '2026-11-10T00:00:00Z' });
const reply = ({ week, fiveHour, weekReset = NOW + 3 * 1440 * MIN, fiveReset = NOW + 41 * MIN }) => ({ rateLimits: { planType: 'team',
  primary: { usedPercent: fiveHour, windowDurationMins: 300, resetsAt: S(fiveReset) }, secondary: { usedPercent: week, windowDurationMins: 10080, resetsAt: S(weekReset) } } });

function world(t, logins) {
  const home = mkdtempSync(join(tmpdir(), 'pdd-pool-int-'));
  t.after(() => rmSync(home, { recursive: true, force: true }));
  const env = { HOME: home, PATH: process.env.PATH ?? '/usr/bin:/bin' }, replies = new Map(), starts = [], names = [];
  // A fake codex app-server: it answers by the account of the access-only copy it was given.
  const spawn = (command, args, options) => {
    const auth = JSON.parse(readFileSync(join(options.env.CODEX_HOME, 'auth.json'), 'utf8'));
    const name = names.find(n => accountOf(n) === auth.tokens.account_id);
    starts.push({ name, args, refresh: auth.tokens.refresh_token, config: readFileSync(join(options.env.CODEX_HOME, 'config.toml'), 'utf8') });
    const child = new EventEmitter();
    child.stdin = new PassThrough(); child.stdout = new PassThrough(); child.stderr = new PassThrough();
    child.exitCode = null; child.signalCode = null;
    child.kill = () => { queueMicrotask(() => { child.exitCode = 0; child.emit('close', 0); }); return true; };
    child.stdin.on('data', bytes => {
      for (const line of bytes.toString().trim().split('\n')) {
        const row = JSON.parse(line);
        if (row.method === 'initialize') queueMicrotask(() => child.stdout.write(`${JSON.stringify({ id: 1, result: {} })}\n`));
        if (row.method === 'account/rateLimits/read') queueMicrotask(() => child.stdout.write(`${JSON.stringify({ id: 2, result: replies.get(name) })}\n`));
      }
    });
    return child;
  };
  const add = async (name, usage) => {
    const folder = join(home, '.pdd', 'codex', name);
    mkdirSync(folder, { recursive: true, mode: 0o700 });
    writeFileSync(join(folder, 'auth.json'), authFile(name), { mode: 0o600 });
    names.push(name); replies.set(name, reply(usage));
    await updatePool({ env }, pool => ({ ...pool, order: [...pool.order, name],
      logins: [...pool.logins, { name, provider: 'codex', home: folder, source: 'import', mode: 'local', paused: false, reset: 'never', stop: { week: 97, fiveHour: 97 }, addedAt: new Date(NOW).toISOString() }] }));
    return folder;
  };
  const files = () => {
    const paths = poolPaths(env), read = path => existsSync(path) ? readFileSync(path, 'utf8') : '';
    return [read(paths.poolFile), read(paths.usageFile), read(paths.logFile), read(join(paths.stateDir, 'autopilot-pool.json'))].join('\n');
  };
  const secrets = () => [REFRESH, ...names.flatMap(name => [accountOf(name), accessOf(name), idOf(name), `${name}.owner@example.test`])];
  return { home, env, add, replies, starts, files, secrets, ports: { modulePorts: { spawn }, timeZone: 'UTC' } };
}
const noSecret = (w, value, label) => { const text = typeof value === 'string' ? value : JSON.stringify(value); for (const secret of w.secrets()) assert.equal(text.includes(secret), false, `${label} shows no token, id or email`); };
const codexLog = message => [JSON.stringify({ type: 'thread.started', thread_id: 't1' }), JSON.stringify({ type: 'turn.failed', error: { message } })].join('\n');

test('P3 with the real pool: a limit moves the next step to the next login; all out pauses once; a new login wakes it', async t => {
  const w = world(t);
  const homes = { cx1: await w.add('cx1', { week: 98, fiveHour: 10 }), cx2: await w.add('cx2', { week: 63, fiveHour: 42 }) };

  // 1. Two logins, the first at its weekly stop line: the step gets the second, with no sign-in.
  const step = await stepLogin({ provider: 'codex', env: w.env, now: NOW }, w.ports);
  assert.equal(step.login.name, 'cx2');
  assert.deepEqual(step.env, { CODEX_HOME: homes.cx2 });
  assert.equal(step.line, 'Agent login: codex cx2 (week 63%, 5h 42%). Pool: 1 of 2 ready. Next free: cx1 at Nov 14 14:00 UTC.');
  assert.deepEqual(w.starts.map(s => [s.name, s.args.join(' '), s.refresh]), [['cx1', 'app-server --listen stdio://', ''], ['cx2', 'app-server --listen stdio://', '']],
    'each read used an access-only copy (no refresh token): nothing can refresh or sign in');
  assert.match(w.starts[0].config, /cli_auth_credentials_store = "file"/);
  const cache = await loadUsage({ env: w.env });
  assert.deepEqual([cache.cx1.week.usedPercent, cache.cx2.fiveHour.usedPercent, cache.cx2.readAt], [98, 42, NOW]);

  // 2. The step ends on a Codex usage limit: no strike, cx2 is marked limited, one log line names it.
  const end = classifyAgentEnd({ provider: 'codex', output: codexLog("You've hit your usage limit. To get more access now, send a request to your admin or try again at 4:41 PM."), exitCode: 1, now: NOW + MIN, timeZone: 'UTC' });
  assert.deepEqual(end, { kind: 'limit', until: Date.UTC(2026, 10, 11, 16, 41), message: 'usage limit' });
  const after = await afterStep({ login: step.login, end, env: w.env, now: NOW + MIN }, w.ports);
  assert.deepEqual([after.strike, after.mark, after.alert], [false, { name: 'cx2', until: Date.UTC(2026, 10, 11, 16, 41), reason: 'limit' }, null]);
  assert.equal(after.line, 'pdd-account: cx2 limited until 16:41 UTC (usage limit). The next step takes the next login.');
  const marked = await loadUsage({ env: w.env });
  assert.deepEqual([marked.cx2.limitedUntil, marked.cx2.limitReason, marked.cx1.week.usedPercent], [Date.UTC(2026, 10, 11, 16, 41), 'limit', 98], 'the mark keeps the other rows');
  assert.deepEqual((await readLog({ env: w.env })).map(row => [row.action, row.login, row.detail]), [['limited', 'cx2', 'limit until 2026-11-11T16:41:00.000Z']]);

  // 3. All out: one pause with the earliest reset and one alert; the next tick reads nothing and alerts nothing.
  const paused = await stepLogin({ provider: 'codex', env: w.env, now: NOW + 2 * MIN }, w.ports);
  assert.equal(paused.pause.reason, 'all-out');
  assert.deepEqual(paused.pause.earliest, { name: 'cx2', at: Date.UTC(2026, 10, 11, 16, 41) });
  assert.equal(paused.pause.wakeAt, Date.UTC(2026, 10, 11, 16, 41));
  assert.equal(paused.pause.line, 'Paused: no Codex login has quota now (2 at a limit). Earliest reset: cx2 at 16:41 UTC. Add a login (pdd accounts add NAME) and the pause ends at the next tick. Resets: off.');
  assert.equal(paused.pause.alert.text, paused.pause.line);
  assert.equal(w.starts.length, 2, 'fresh rows and a marked login need no read');
  const waiting = await stepLogin({ provider: 'codex', env: w.env, now: NOW + 10 * MIN }, w.ports);
  assert.deepEqual([waiting.pause.alert, waiting.pause.since, w.starts.length], [null, NOW + 2 * MIN, 2]);
  assert.deepEqual(await poolStatusLines({ provider: 'codex', env: w.env, now: NOW + 11 * MIN }, w.ports), [paused.pause.line]);

  // 4. A new login during the pause: the next tick wakes, reads the stale and the new rows, and takes it.
  const cx3 = await w.add('cx3', { week: 5, fiveHour: 5 });
  const woke = await stepLogin({ provider: 'codex', env: w.env, now: NOW + 12 * MIN }, w.ports);
  assert.equal(woke.login.name, 'cx3');
  assert.deepEqual(woke.env, { CODEX_HOME: cx3 });
  assert.equal(woke.recovered, 'Autopilot has a Codex login again: cx3. The pause ended.');
  assert.deepEqual(w.starts.slice(2).map(s => s.name), ['cx1', 'cx3'], 'cx1 was stale; the marked cx2 is not read');
  assert.deepEqual(await poolStatusLines({ provider: 'codex', env: w.env, now: NOW + 13 * MIN }, w.ports),
    ['Agent login: codex cx3 (week 5%, 5h 5%) since 14:12 UTC. Pool: 1 of 3 ready. Next free: cx2 at 16:41 UTC.']);
  assert.equal(w.starts.length, 4, 'status reads no usage');

  // 5. A limit end with no reset words: one real read gives the window's reset.
  w.replies.set('cx3', reply({ week: 20, fiveHour: 100, fiveReset: NOW + 50 * MIN }));
  const read = await afterStep({ login: woke.login, end: { kind: 'limit', until: null }, env: w.env, now: NOW + 14 * MIN }, w.ports);
  assert.deepEqual(read.mark, { name: 'cx3', until: NOW + 50 * MIN, reason: 'limit' });
  assert.equal(w.starts.at(-1).name, 'cx3');
  noSecret(w, [step, after, paused, waiting, woke, read], 'the results');
  noSecret(w, w.files(), 'the pool file, the usage cache, the log and the pool record');
});

test('P3 with the real pool: a pin, the start binding and a broken pool file', async t => {
  const w = world(t);
  const cx1 = await w.add('cx1', { week: 10, fiveHour: 10 });
  await w.add('cx2', { week: 10, fiveHour: 10 });
  const pinned = await stepLogin({ provider: 'codex', env: { ...w.env, CODEX_HOME: cx1 }, now: NOW }, w.ports);
  assert.deepEqual([pinned.pinned, pinned.reason, pinned.login?.name, w.starts.length], [true, 'env', 'cx1', 0]);
  assert.deepEqual(await startBinding({ provider: 'codex', env: w.env, saved: null }, w.ports),
    { agentPool: 'codex', home: null, line: 'Agent login: the codex pool (2 logins); each step takes the first login with quota.' });
  // The store refuses a pool file that does not parse and never changes it; no file text reaches the line.
  const { poolFile } = poolPaths(w.env);
  writeFileSync(poolFile, '{"logins": [ "secret-file-text-here"');
  const broken = await stepLogin({ provider: 'codex', env: w.env, now: NOW }, w.ports);
  assert.equal(broken.pause.reason, 'pool-error');
  assert.equal(broken.pause.line, `Paused: Autopilot cannot read the login pool file (The pool file ${poolFile} is not valid: it is not valid JSON. pdd did not change it. Fix or move the file, then try again.). Fix it, then the next tick goes on; no step starts until then.`);
  assert.equal(readFileSync(poolFile, 'utf8'), '{"logins": [ "secret-file-text-here"', 'the pool file is not changed');
  assert.ok(broken.pause.alert);
  // No absolute home: the store gives its own line, and no record can be written, so there is no alert.
  const homeless = await stepLogin({ provider: 'codex', env: { PATH: w.env.PATH }, now: NOW }, { ...w.ports, modulePorts: { ...w.ports.modulePorts, userInfo: () => ({ homedir: '' }) } });
  assert.equal(homeless.pause.line, 'Paused: Autopilot cannot read the login pool file (pdd accounts needs an absolute home folder; set HOME to an absolute path.). Fix it, then the next tick goes on; no step starts until then.');
  assert.equal(homeless.pause.alert, null);
});

// DESIGN D4: markLimited accepts needs-sign-in (60 minutes) and stale-copy (10 minutes). Until pool-usage ships that, the
// real usage module refuses these reasons; this test stays a todo so the gap stays visible.
test('P3 with the real pool: a sign-in end marks the login once and alerts once', { todo: 'accounts-usage: markLimited and the cache keep needs-sign-in and stale-copy (DESIGN D4)' }, async t => {
  const w = world(t);
  await w.add('cx3', { week: 10, fiveHour: 10 });
  const login = (await stepLogin({ provider: 'codex', env: w.env, now: NOW }, w.ports)).login;
  const end = classifyAgentEnd({ provider: 'codex', output: codexLog('Your access token could not be refreshed because your refresh token was already used. Please log out and sign in again.'), exitCode: 1, now: NOW });
  assert.equal(end.kind, 'needs-sign-in');
  const first = await afterStep({ login, end, env: w.env, now: NOW + MIN }, w.ports);
  assert.deepEqual(first.mark, { name: 'cx3', until: NOW + 61 * MIN, reason: 'needs-sign-in' });
  assert.equal(first.alert.text, 'Codex login cx3 needs a new sign-in. Autopilot skips it. Run: pdd accounts add cx3');
  assert.equal((await loadUsage({ env: w.env })).cx3.limitReason, 'needs-sign-in');
  assert.equal((await afterStep({ login, end, env: w.env, now: NOW + 2 * MIN }, w.ports)).alert, null, 'one alert per sign-in event');
  const copy = await afterStep({ login, end: { kind: 'stale-copy', until: null }, env: w.env, now: NOW + 3 * MIN }, w.ports);
  assert.deepEqual(copy.mark, { name: 'cx3', until: NOW + 13 * MIN, reason: 'stale-copy' });
});
