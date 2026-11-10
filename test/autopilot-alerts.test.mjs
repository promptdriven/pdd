import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { fork } from 'node:child_process';
import { once } from 'node:events';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, statSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import {isolatedCheckCapacity} from './helpers/check-machine.mjs';
import { alertStatusLine, runAutopilotAlerts } from '../src/autopilot-alerts.mjs';

// Synthetic webhook addresses. The fake HTTP port records requests; no test sends a real request.
const DISCORD = 'https://discord.com/api/webhooks/123456789012345678/SECRET-discord_token';
const SLACK = 'https://hooks.slack.com/services/T0000/B0000/SECRETslacktoken';
const BOT_TOKEN = 'MTMwMDAwMDAwMDAwMDAwMDAx.GbotA1.SECRETbot_token_value_0123456789';
const ROTATED_TOKEN = 'MTMwMDAwMDAwMDAwMDAwMDAy.GbotB2.SECRETrotated_token_9876543210';
const CHANNEL = '1300000000000000099';
const SECRETS = [DISCORD, SLACK, 'SECRET', 'discord_token', 'slacktoken', '123456789012345678', BOT_TOKEN, ROTATED_TOKEN, 'bot_token_value', 'rotated_token'];
const capture = () => ({ text: '', write(value) { this.text += value; } });
const echo = request => ({ status: 200, text: JSON.stringify({ id: '991', channel_id: '7', content: request.body.content }) });
const usage = { cause: 'Codex usage limit; resets 2026-11-06T18:00Z', tried: 'Paused issue 12 and kept other work going', need: 'Grant access to another signed-in account?' };

function setup(t) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-alerts-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const home = join(dir, 'home'), cwd = join(dir, 'repo');
  mkdirSync(home); mkdirSync(cwd);
  const f = { dir, home, cwd, requests: [], replies: [], outputs: [], time: Date.parse('2026-11-06T10:00:00Z') };
  f.ports = {
    stateRoot: join(home, 'state'), now: () => f.time, hostname: () => 'test-host',
    repository: async () => ({ nameWithOwner: 'owner/repo' }),
    http: async request => {
      f.requests.push(structuredClone(request));
      const reply = f.replies.shift();
      assert.ok(reply, 'the test planned a reply for every request');
      if (reply instanceof Error) throw reply;
      return typeof reply === 'function' ? reply(request) : reply;
    },
  };
  // Every XDG folder is set, so a runner's own XDG_CONFIG_HOME cannot point status at another config file.
  f.env = { HOME: home, XDG_CONFIG_HOME: join(home, '.config'), XDG_STATE_HOME: join(home, '.local', 'state'), PATH: process.env.PATH };
  f.pdd = async (argv, stdin = '') => {
    const stdout = capture(), stderr = capture();
    const exitCode = await runPdd(argv, { cwd, env: f.env, stdin, stdout, stderr, autopilotAlertsPorts: f.ports });
    f.outputs.push(stdout.text, stderr.text);
    return { exitCode, stdout: stdout.text, stderr: stderr.text };
  };
  f.alert = (issue, kind, fields, ...extra) => f.pdd(['autopilot', 'alert', '--issue', String(issue), '--kind', kind, '--input', '-', ...extra], JSON.stringify({code: `${issue}:${kind}`, ifNoAnswer: 'This run waits; other work continues.', ...fields}));
  f.config = join(home, '.config', 'pdd', 'autopilot-alerts.json');
  f.recordFile = () => join(f.ports.stateRoot, 'alerts', `${createHash('sha256').update('owner/repo').digest('hex').slice(0, 20)}.json`);
  f.record = () => JSON.parse(readFileSync(f.recordFile(), 'utf8'));
  // `pdd autopilot status` through the real launcher, with a saved repo state and no timer or Herdr.
  f.status = async () => {
    const id = createHash('sha256').update(cwd).digest('hex').slice(0, 20);
    mkdirSync(f.ports.stateRoot, { recursive: true });
    writeFileSync(join(f.ports.stateRoot, `${id}.json`), JSON.stringify({ repo: 'owner/repo', enabled: true, agent: { id: 'codex' } }));
    const stdout = capture(), stderr = capture();
    const exitCode = await runPdd(['autopilot', 'status'], { cwd, env: f.env, stdout, stderr, autopilotLauncherPorts: {
      checkCapacityPorts:isolatedCheckCapacity(dir), stateRoot: f.ports.stateRoot, timer: async () => false, herdr: async () => ({ running: false }), allocationCheck: async () => ({ state: 'ready', message: '' }),
      run: async command => { assert.equal(command, 'git', 'status runs only local git'); return { code: 0, stdout: `${cwd}\n`, stderr: '' }; },
    } });
    f.outputs.push(stdout.text, stderr.text);
    assert.equal(exitCode, 0, stderr.text);
    // Health has separate status coverage; keep these assertions scoped to alert delivery.
    const lines = stdout.text.trimEnd().split('\n');
    return [lines[0], ...lines.slice(1).filter(line => line.startsWith('Alerts:'))];
  };
  // The secret never reaches any output or local file other than the private destination (or no file at all for a token command).
  f.noSecret = ({ config = false } = {}) => {
    const files = readdirSync(home, { recursive: true }).map(name => join(home, name)).filter(path => statSync(path).isFile() && (config || path !== f.config));
    const texts = [...f.outputs, ...files.map(path => readFileSync(path, 'utf8'))];
    for (const text of texts) for (const secret of SECRETS) assert.ok(!text.includes(secret), `a secret part is visible: ${text}`);
  };
  return f;
}

// A fake Discord REST v10 API: it keeps posted messages so the readback is a real lookup.
function fakeDiscord(f) {
  const posted = new Map();
  f.discord = { me: 200, channel: 200, readback: 'same' };
  f.ports.http = async request => {
    f.requests.push(structuredClone(request));
    const url = new URL(request.url);
    const path = url.origin === 'https://discord.com' && url.pathname.startsWith('/api/v10/') ? url.pathname.slice('/api/v10'.length) + url.search : null;
    const reply = (status, value) => ({ status, text: JSON.stringify(value) });
    if (request.method === 'GET' && path === '/users/@me') return f.discord.me === 200 ? reply(200, { id: '42', username: 'PDD', bot: true }) : reply(f.discord.me, { message: 'no' });
    if (request.method === 'GET' && path === `/channels/${CHANNEL}`) return f.discord.channel === 200 ? reply(200, { id: CHANNEL, name: 'internal-alerts', type: 0 }) : reply(f.discord.channel, { message: 'no' });
    if (request.method === 'POST' && path === `/channels/${CHANNEL}/messages`) {
      const id = String(1300000000000000100n + BigInt(posted.size));
      posted.set(id, request.body.content);
      return reply(200, { id, channel_id: CHANNEL, content: request.body.content });
    }
    const message = path?.match(new RegExp(`^/channels/${CHANNEL}/messages/([0-9]+)$`))?.[1];
    // 'normalized' stores the text as a chat service may: LF line ends and no whitespace at line ends or at either end.
    const stored = text => f.discord.readback === 'same' ? text : f.discord.readback === 'normalized'
      ? text.replaceAll('\n', '  \r\n') + '  ' : 'edited by someone else';
    if (request.method === 'GET' && posted.has(message)) return reply(200, { id: message, content: stored(posted.get(message)) });
    return reply(404, { message: 'Unknown' });
  };
  f.route = request => `${request.method} ${request.url.slice('https://discord.com/api/v10'.length)}`;
}

test('alerts set saves a webhook from stdin outside the repository with private permissions and never prints it', async t => {
  const f = setup(t);
  const saved = await f.pdd(['autopilot', 'alerts', 'set'], `  ${DISCORD}\n`);
  assert.equal(saved.exitCode, 0, saved.stderr);
  assert.match(saved.stdout, /Discord/);
  assert.equal(statSync(f.config).mode & 0o777, 0o600);
  assert.equal(statSync(join(f.home, '.config', 'pdd')).mode & 0o777, 0o700);
  assert.deepEqual(JSON.parse(readFileSync(f.config, 'utf8')), { v: 1, service: 'discord', url: DISCORD });
  assert.deepEqual(readdirSync(f.cwd), [], 'nothing is written into the repository');

  const before = readFileSync(f.config, 'utf8');
  const argv = await f.pdd(['autopilot', 'alerts', 'set', SLACK]);
  assert.equal(argv.exitCode, 2, 'the URL is never accepted as an argument');
  // Only the parsed host counts: a Discord or Slack name in the path, the query or a longer host is another site.
  for (const bad of ['https://example.com/api/webhooks/1/abc', 'http://discord.com/api/webhooks/1/abc', 'https://discord.com/api/webhooks/1/SECRET extra', '',
    'https://evil.example/discord.com/api/webhooks/1/abc', 'https://discord.com.evil.example/api/webhooks/1/abc', 'https://evil.example/api/webhooks/1/abc?discord.com',
    'https://evil.example/hooks.slack.com/services/T000/B000/XXXX', 'https://hooks.slack.com.evil.example/services/T000/B000/XXXX']) {
    const refused = await f.pdd(['autopilot', 'alerts', 'set'], bad);
    assert.equal(refused.exitCode, 2, bad);
    assert.equal(refused.stdout, '', bad);
    if (bad) assert.equal(refused.stderr.indexOf(bad), -1, 'a refused value is not echoed');
    if (URL.canParse(bad)) assert.equal(refused.stderr.indexOf(new URL(bad).hostname), -1, 'a refused host is not echoed');
  }
  assert.equal(readFileSync(f.config, 'utf8'), before, 'a refused value saves nothing');
  assert.equal(f.requests.length, 0, 'set sends nothing');
  f.noSecret();
});


test('an empty or relative HOME never puts the secret or a record in the checkout: pdd uses the account home, or saves nothing', async t => {
  const f = setup(t);
  delete f.ports.stateRoot;
  const account = join(f.dir, 'account-home');
  let accountHome = account;
  f.ports.userInfo = () => { if (accountHome instanceof Error) throw accountHome; return { homedir: accountHome }; };
  // In the real CLI the env is the process env, and os.homedir() reads that same HOME; run inside the temporary checkout.
  const saved = { cwd: process.cwd(), HOME: process.env.HOME };
  t.after(() => { process.chdir(saved.cwd); if (saved.HOME === undefined) delete process.env.HOME; else process.env.HOME = saved.HOME; });
  process.chdir(f.cwd);
  const checkout = () => readdirSync(f.cwd, { recursive: true });
  const config = join(account, '.config', 'pdd', 'autopilot-alerts.json');
  const record = join(account, '.local', 'state', 'pdd', 'autopilot', 'alerts', `${createHash('sha256').update('owner/repo').digest('hex').slice(0, 20)}.json`);

  for (const HOME of ['', 'relhome']) {
    process.env.HOME = HOME;
    f.env = { HOME, XDG_CONFIG_HOME: 'relconfig', PATH: process.env.PATH };
    rmSync(account, { recursive: true, force: true }); mkdirSync(account);
    accountHome = account;
    const set = await f.pdd(['autopilot', 'alerts', 'set'], DISCORD);
    assert.equal(set.exitCode, 0, set.stderr);
    assert.deepEqual(checkout(), [], `HOME=${HOME}: set writes nothing in the checkout`);
    assert.deepEqual(JSON.parse(readFileSync(config, 'utf8')), { v: 1, service: 'discord', url: DISCORD }, `HOME=${HOME}: the account home holds it`);
    assert.equal(statSync(config).mode & 0o777, 0o600);
    f.replies.push(echo);
    assert.match((await f.alert(12, 'access', usage)).stdout, /confirmed/);
    assert.equal(statSync(record).mode & 0o777, 0o600, 'the record is in the account home too');
    assert.equal((await f.pdd(['autopilot', 'alerts', 'set', '--discord-channel', CHANNEL, '--token-command', 'true'])).exitCode, 0);
    assert.equal(JSON.parse(readFileSync(config, 'utf8')).tokenCommand, 'true');
    assert.equal((await f.pdd(['autopilot', 'alerts', 'clear'])).exitCode, 0);
    assert.equal(existsSync(config), false);
    assert.deepEqual(checkout(), [], `HOME=${HOME}: nothing is written in the checkout`);

    // No absolute home at all: every action refuses and saves, records and sends nothing.
    rmSync(account, { recursive: true, force: true });
    accountHome = HOME === '' ? '' : Object.assign(Error('no passwd entry'), { code: 'ENOENT' });
    const count = f.requests.length;
    for (const [argv, stdin, what] of [
      [['autopilot', 'alerts', 'set'], DISCORD, /Nothing was saved/],
      [['autopilot', 'alerts', 'set', '--discord-channel', CHANNEL], BOT_TOKEN, /Nothing was saved/],
      [['autopilot', 'alerts', 'set', '--discord-channel', CHANNEL, '--token-command', 'true'], '', /Nothing was saved/],
      [['autopilot', 'alerts', 'test'], '', /Nothing was sent/],
      [['autopilot', 'alerts', 'clear'], '', /Nothing was removed/],
      [['autopilot', 'alert', '--issue', '12', '--kind', 'usage-limit', '--input', '-'], JSON.stringify(usage), /Nothing was recorded or sent\. Continue other work/],
    ]) {
      const refused = await f.pdd(argv, stdin);
      assert.equal(refused.exitCode, 1, `HOME=${HOME}: ${argv.join(' ')}`);
      assert.match(refused.stderr, /need an absolute home folder; set HOME to an absolute path/);
      assert.match(refused.stderr, what);
    }
    assert.equal(f.requests.length, count, 'nothing is sent');
    assert.equal(existsSync(account), false, 'nothing is saved');
    assert.deepEqual(checkout(), [], `HOME=${HOME}: nothing is written in the checkout`);
    assert.equal(alertStatusLine({ repo: 'owner/repo', env: f.env }, { userInfo: f.ports.userInfo }), '', 'status reads nothing');
  }
  assert.deepEqual(readdirSync(f.home), [], 'the unused HOME folder stays empty');
  f.noSecret();
});


test('alerts test confirms a Discord message by readback; a missing readback is not a delivery', async t => {
  const f = setup(t);
  await f.pdd(['autopilot', 'alerts', 'set'], DISCORD);
  f.replies.push(echo);
  const ok = await f.pdd(['autopilot', 'alerts', 'test']);
  assert.equal(ok.exitCode, 0, ok.stderr);
  assert.match(ok.stdout, /delivered/i);
  const [request] = f.requests;
  assert.equal(new URL(request.url).searchParams.get('wait'), 'true', 'Discord returns the created message only with wait=true');
  assert.equal(request.url.replace(/\?wait=true$/, ''), DISCORD);
  assert.match(request.body.content, /PDD Autopilot test alert \(test-host\)/);
  assert.deepEqual(request.body.allowed_mentions, { parse: [] });

  for (const reply of [{ status: 204, text: '' }, { status: 200, text: JSON.stringify({ id: '5', content: 'another message' }) }, Object.assign(Error(`timeout ${DISCORD}`), { code: 'unknown' })]) {
    f.replies.push(reply);
    const unconfirmed = await f.pdd(['autopilot', 'alerts', 'test']);
    assert.equal(unconfirmed.exitCode, 1);
    assert.match(unconfirmed.stderr, /unconfirmed/);
  }
  assert.ok(!existsSync(join(f.ports.stateRoot, 'alerts')), 'a test message is not an alert record');
  f.noSecret();
});


test('Slack: an ok reply is delivered, an error reply fails with only its status and error word, and mentions are escaped', async t => {
  const f = setup(t);
  assert.match((await f.pdd(['autopilot', 'alerts', 'set'], SLACK)).stdout, /Slack/);
  f.replies.push({ status: 200, text: 'ok' });
  assert.equal((await f.pdd(['autopilot', 'alerts', 'test'])).exitCode, 0);
  assert.equal(f.requests[0].url, SLACK);
  assert.deepEqual(Object.keys(f.requests[0].body), ['text']);

  f.replies.push({ status: 404, text: 'no_service' });
  const failed = await f.pdd(['autopilot', 'alerts', 'test']);
  assert.equal(failed.exitCode, 1);
  assert.match(failed.stderr, /failed \(HTTP 404 no_service\)/);

  f.replies.push({ status: 200, text: 'ok' });
  const sent = await f.alert(30, 'access', { cause: 'Needs a paid plan', tried: 'Read <!channel> & the billing page', need: 'Approve spending' });
  assert.equal(sent.exitCode, 0, sent.stderr);
  assert.match(f.requests.at(-1).body.text, /Read &lt;!channel&gt; &amp; the billing page/);
  assert.equal(f.record().incidents['cause:30:access'].result, 'delivered');
  f.noSecret();
});


test('invalid alert input is refused with its problem named, and records and sends nothing', async t => {
  const f = setup(t);
  assert.equal((await f.pdd(['autopilot', 'alerts', 'set'], DISCORD)).exitCode, 0, 'a destination exists, so only validation stops a send');
  const alert = ['autopilot', 'alert', '--issue', '12', '--kind', 'usage-limit', '--input', '-'];
  const cases = [
    [['autopilot', 'alert', '--issue', '12', '--kind', 'usage-limit', '--input', 'file.json'], JSON.stringify(usage), /--input - with the alert JSON on stdin/],
    [['autopilot', 'alert', '--issue', 'twelve', '--kind', 'usage-limit', '--input', '-'], JSON.stringify(usage), /--issue N with a positive issue number/],
    [['autopilot', 'alert', '--issue', '0', '--kind', 'usage-limit', '--input', '-'], JSON.stringify(usage), /--issue N with a positive issue number/],
    [['autopilot', 'alert', '--kind', 'usage-limit', '--input', '-'], JSON.stringify(usage), /--issue N with a positive issue number/],
    [['autopilot', 'alert', '--issue', '12', '--input', '-'], JSON.stringify(usage), /--kind usage-limit\|resource\|interpreter\|interpreter-access\|access\|decision\|stuck\|test-suite\|long-running\|recovered/],
    [alert, 'not json', /JSON object on stdin with nonblank "cause", "tried", "need"\. Nothing was recorded/],
    [alert, '[]', /JSON object on stdin/],
    [alert, JSON.stringify({ cause: 'x', tried: 'y' }), /nonblank "cause", "tried", "need"/],
    [alert, JSON.stringify({ ...usage, need: '  ' }), /nonblank "cause", "tried", "need"/],
    [['autopilot', 'alert', '--issue', '12', '--kind', 'recovered', '--input', '-'], JSON.stringify({ cause: '' }), /nonblank "cause"\. Nothing was recorded/],
    [['autopilot', 'alert', '--issue', '12', '--kind', 'recovered', '--input', '-'], JSON.stringify({ cause: 'Quota reset', kind: 'progress' }), /"kind" in a recovery as one of usage-limit\|resource\|interpreter\|interpreter-access\|access\|decision\|stuck\|test-suite\|long-running,/],
  ];
  for (const [argv, stdin, problem] of cases) {
    const refused = await f.pdd(argv, stdin);
    assert.equal(refused.exitCode, 2, argv.join(' '));
    assert.match(refused.stderr, problem, argv.join(' '));
    assert.equal(refused.stdout, '');
  }
  assert.equal((await f.pdd(['autopilot', 'alert', '--issue', '12', '--kind', 'progress', '--input', '-'], JSON.stringify(usage))).exitCode, 2, 'the parser refuses an unknown kind');
  assert.equal(f.requests.length, 0);
  assert.equal(existsSync(f.recordFile()), false);
  f.noSecret();
});


test('alerts clear removes the destination, and test then reports that none is set', async t => {
  const f = setup(t);
  await f.pdd(['autopilot', 'alerts', 'set'], DISCORD);
  assert.equal((await f.pdd(['autopilot', 'alerts', 'clear'])).exitCode, 0);
  assert.equal(existsSync(f.config), false);
  assert.equal((await f.pdd(['autopilot', 'alerts', 'clear'])).exitCode, 0, 'clear is harmless when nothing is set');
  const tested = await f.pdd(['autopilot', 'alerts', 'test']);
  assert.equal(tested.exitCode, 1);
  assert.match(tested.stderr, /No alert destination/);
  assert.equal(f.requests.length, 0);
  f.noSecret();
});


test('a Discord bot with a stdin token: set saves it privately; test checks bot and channel, then posts with readback', async t => {
  const f = setup(t); fakeDiscord(f);
  const saved = await f.pdd(['autopilot', 'alerts', 'set', '--discord-channel', CHANNEL], `${BOT_TOKEN}\n`);
  assert.equal(saved.exitCode, 0, saved.stderr);
  assert.match(saved.stdout, new RegExp(`Discord bot for channel ${CHANNEL}`));
  assert.deepEqual(JSON.parse(readFileSync(f.config, 'utf8')), { v: 1, service: 'discord-bot', channel: CHANNEL, token: BOT_TOKEN });
  assert.equal(statSync(f.config).mode & 0o777, 0o600);

  const tested = await f.pdd(['autopilot', 'alerts', 'test']);
  assert.equal(tested.exitCode, 0, tested.stderr);
  assert.match(tested.stdout, /Discord bot PDD in #internal-alerts posted it and the readback matched/);
  assert.deepEqual(f.requests.map(f.route), ['GET /users/@me', `GET /channels/${CHANNEL}`, `POST /channels/${CHANNEL}/messages`,
    `GET /channels/${CHANNEL}/messages/1300000000000000100`]);
  for (const request of f.requests) {
    assert.equal(request.headers.authorization, `Bot ${BOT_TOKEN}`);
    assert.match(request.headers['user-agent'], /^PDD-Autopilot\/[^ ]+$/);
    assert.equal(request.body === undefined, request.method === 'GET', 'only the POST has a body');
  }
  const post = f.requests[2].body;
  assert.equal(post.flags, 4, 'link embeds are suppressed');
  assert.deepEqual(post.allowed_mentions, { parse: [] });
  assert.match(post.content, /^PDD Autopilot test alert \(test-host\)\.$/);

  const sent = await f.alert(12, 'access', usage);
  assert.equal(sent.exitCode, 0, sent.stderr);
  assert.match(sent.stdout, /confirmed/);
  assert.deepEqual(f.requests.slice(4).map(f.route), [`POST /channels/${CHANNEL}/messages`, `GET /channels/${CHANNEL}/messages/1300000000000000101`]);
  assert.match(f.requests[4].body.content, /^PDD Autopilot needs you: access\nIssue: https:\/\/github\.com\/owner\/repo\/issues\/12\n/);
  assert.equal(f.record().incidents['cause:12:access'].result, 'delivered');
  assert.equal((await f.status()).length, 1);
  f.noSecret();
});


test('a Discord bot readback mismatch is unconfirmed, shown in status and not sent again', async t => {
  const f = setup(t); fakeDiscord(f);
  await f.pdd(['autopilot', 'alerts', 'set', '--discord-channel', CHANNEL], BOT_TOKEN);
  f.discord.readback = 'changed';
  const sent = await f.alert(12, 'decision', { cause: 'No progress after the retry time', tried: 'Two repairs', need: 'Review the required check?' });
  assert.equal(sent.exitCode, 0, 'work continues');
  assert.match(sent.stdout, /delivery unconfirmed \(readback mismatch\)/);
  assert.equal(f.record().incidents['cause:12:decision'].result, 'unconfirmed');
  assert.match((await f.status())[1], /^Alerts: 1 open alert not delivered; last delivery unconfirmed \(readback mismatch\) for #12 decision/);
  const count = f.requests.length;
  assert.match((await f.alert(12, 'decision', { cause: 'No progress after the retry time', tried: 'Two repairs', need: 'Review the required check?' })).stdout, /nothing sent/);
  assert.equal(f.requests.length, count, 'an unconfirmed bot message may exist, so it is not posted again');
  const tested = await f.pdd(['autopilot', 'alerts', 'test']);
  assert.equal(tested.exitCode, 1);
  assert.match(tested.stderr, /Test alert unconfirmed \(readback mismatch\) for Discord bot PDD in #internal-alerts/);
  f.noSecret();
});


test('a Discord bot readback that changed only line ends or end spaces is delivered, and the result names the readback', async t => {
  const f = setup(t); fakeDiscord(f);
  await f.pdd(['autopilot', 'alerts', 'set', '--discord-channel', CHANNEL], BOT_TOKEN);
  f.discord.readback = 'normalized';
  const sent = await f.alert(12, 'decision', { cause: 'Line one  \r\nLine two\rLine three', tried: 'Two repairs', need: 'Review the required check?' });
  assert.equal(sent.stdout, 'Alert sent for #12 decision; the Discord bot readback confirmed it.\n');
  assert.match(f.requests.at(-2).body.content, /Ask: Review the required check\?/, 'the full ask is retained');
  assert.equal(f.record().incidents['cause:12:decision'].result, 'delivered');
  assert.equal((await f.status()).length, 1, 'no false unconfirmed alert in status');
  f.noSecret();
});


test('a bot token command runs at each send, the token never reaches disk or output, and a failing command sends nothing', async t => {
  const f = setup(t); fakeDiscord(f);
  // The fake secret store is outside HOME, like a real secret manager; the command is a plain local shell command.
  const store = join(f.dir, 'secret-store'), tokenFile = join(store, 'token');
  mkdirSync(store); writeFileSync(tokenFile, `${BOT_TOKEN}\n`);
  const saved = await f.pdd(['autopilot', 'alerts', 'set', '--discord-channel', CHANNEL, '--token-command', `cat '${tokenFile}'`], 'IGNORED-STDIN-VALUE');
  assert.equal(saved.exitCode, 0, saved.stderr);
  assert.match(saved.stdout, /stores no token/);
  assert.deepEqual(JSON.parse(readFileSync(f.config, 'utf8')), { v: 1, service: 'discord-bot', channel: CHANNEL, tokenCommand: `cat '${tokenFile}'` });
  assert.equal(statSync(f.config).mode & 0o777, 0o600);

  assert.match((await f.alert(12, 'access', usage)).stdout, /confirmed/);
  assert.equal(f.requests.at(-1).headers.authorization, `Bot ${BOT_TOKEN}`);
  writeFileSync(tokenFile, ROTATED_TOKEN);
  assert.match((await f.alert(13, 'access', { cause: 'Disk full', tried: 'Stopped new runs', need: 'Grant disk quota?' })).stdout, /confirmed/);
  assert.equal(f.requests.at(-1).headers.authorization, `Bot ${ROTATED_TOKEN}`, 'the command runs at send time, so a rotated token is used');
  assert.match((await f.pdd(['autopilot', 'alerts', 'test'])).stdout, /Discord bot PDD in #internal-alerts/);

  const count = f.requests.length;
  await f.pdd(['autopilot', 'alerts', 'set', '--discord-channel', CHANNEL, '--token-command', `cat '${tokenFile}'; cat '${tokenFile}' >&2; exit 3`]);
  const failed = await f.alert(14, 'access', { cause: 'Needs a paid plan', tried: 'Read the billing page', need: 'Approve spending' });
  assert.equal(failed.exitCode, 0, 'work continues');
  assert.match(failed.stdout, /delivery failed \(token command failed \(exit 3\)\)/);
  const tested = await f.pdd(['autopilot', 'alerts', 'test']);
  assert.equal(tested.exitCode, 1);
  assert.match(tested.stderr, /token command failed \(exit 3\)\. Its output is not shown/);
  await f.pdd(['autopilot', 'alerts', 'set', '--discord-channel', CHANNEL, '--token-command', 'true']);
  assert.match((await f.alert(15, 'decision', { cause: 'Two layouts', tried: 'Asked on the issue', need: 'Choose one layout?' })).stdout, /token command gave no token/);
  assert.equal(f.requests.length, count, 'no request is sent without a token');
  assert.match((await f.status())[1], /last delivery failed \(token command gave no token\) for #15 decision/);

  f.noSecret({ config: true });
});


test('a Discord bot check failure sends no message, and invalid bot settings save nothing', async t => {
  const f = setup(t); fakeDiscord(f);
  for (const [argv, stdin] of [
    [['autopilot', 'alerts', 'set', '--token-command', 'true'], ''],
    [['autopilot', 'alerts', 'set', '--discord-channel', 'internal-alerts'], BOT_TOKEN],
    [['autopilot', 'alerts', 'set', '--discord-channel', CHANNEL], '  '],
    [['autopilot', 'alerts', 'set', '--discord-channel', CHANNEL], 'short'],
    [['autopilot', 'alerts', 'test', '--discord-channel', CHANNEL], ''],
    [['autopilot', 'alerts', 'clear', '--token-command', 'true'], ''],
  ]) assert.equal((await f.pdd(argv, stdin)).exitCode, 2, argv.join(' '));
  assert.equal(existsSync(f.config), false);

  await f.pdd(['autopilot', 'alerts', 'set', '--discord-channel', CHANNEL], BOT_TOKEN);
  f.discord.me = 401;
  const badToken = await f.pdd(['autopilot', 'alerts', 'test']);
  assert.equal(badToken.exitCode, 1);
  assert.match(badToken.stderr, /Discord bot check failed \(HTTP 401\)/);
  f.discord.me = 200; f.discord.channel = 403;
  const noChannel = await f.pdd(['autopilot', 'alerts', 'test']);
  assert.equal(noChannel.exitCode, 1);
  assert.match(noChannel.stderr, new RegExp(`cannot read channel ${CHANNEL} \\(HTTP 403\\)`));
  assert.deepEqual(f.requests.map(f.route), ['GET /users/@me', 'GET /users/@me', `GET /channels/${CHANNEL}`], 'only read-only checks ran');
  f.noSecret();
});


test('alerts help exposes quiet review, digest cadence and separate destination rules', async t => {
  const f = setup(t);
  const reply = await f.pdd(['autopilot', 'alerts', '--help']);
  assert.equal(reply.exitCode, 0);
  for (const fact of ['cause', 'decision', 'recover', 'stuck', 'digest', 'repository', 'machine', '6 hours', '--destination', 'infrastructure'])
    assert.ok(reply.stdout.includes(fact), `alerts help must explain ${fact}`);
  assert.equal(f.requests.length, 0);
});


test('two native processes share incident custody and post the same alert once', { timeout: 10000 }, async t => {
  const f = setup(t);
  await f.pdd(['autopilot', 'alerts', 'set'], DISCORD);
  const script = join(f.dir, 'synthetic-alert-worker.mjs');
  writeFileSync(script, `
    import { runAutopilotAlerts } from ${JSON.stringify(new URL('../src/autopilot-alerts.mjs', import.meta.url).href)};
    import { acquireRunLock } from ${JSON.stringify(new URL('../src/workflow-runner.mjs', import.meta.url).href)};
    const result = await runAutopilotAlerts({ action: 'alert', cwd: ${JSON.stringify(f.cwd)}, env: process.env,
      issue: '41', kind: 'access', text: JSON.stringify({ code: 'required-check', cause: 'Required check unavailable', tried: 'Read checks', need: 'Restore check?', ifNoAnswer: 'Run waits; other work continues.' }) }, {
      stateRoot: ${JSON.stringify(f.ports.stateRoot)}, hostname: () => 'test-host', repository: async () => ({ nameWithOwner: 'owner/repo' }),
      recordLock: (...args) => { try { return acquireRunLock(...args); } catch (error) { process.send({ type: 'contended' }); throw error; } },
      http: async request => { process.send({ type: 'send' }); await new Promise(resolve => process.once('message', resolve));
        return { status: 200, text: JSON.stringify({ id: '991', content: request.body.content }) }; }
    });
    process.send({ type: 'done', exitCode: result.exitCode });
    process.disconnect();
  `);
  const start = () => {
    const child = fork(script, [], { env: f.env, execArgv: [], stdio: ['ignore', 'ignore', 'pipe', 'ipc'] });
    t.after(() => { if (child.exitCode === null) child.kill(); });
    const messages = [], queued = [], waiters = [];
    child.on('message', message => { messages.push(message); const waiting = waiters.shift(); if (waiting) waiting(message); else queued.push(message); });
    return { child, messages, ended: once(child, 'exit'), next: () => queued.length ? Promise.resolve(queued.shift()) : new Promise(resolve => waiters.push(resolve)) };
  };
  const first = start();
  assert.equal((await first.next()).type, 'send');
  const second = start();
  const competing = await second.next();
  assert.ok(['contended', 'send'].includes(competing.type));
  first.child.send({ release: true });
  if (competing.type === 'send') second.child.send({ release: true });
  assert.deepEqual(await first.ended, [0, null]);
  assert.deepEqual(await second.ended, [0, null]);
  assert.deepEqual([first, second].flatMap(worker => worker.messages.filter(m => m.type === 'done').map(m => m.exitCode)), [0, 0]);
  assert.equal([first, second].flatMap(worker => worker.messages).filter(m => m.type === 'send').length, 1,
    'separate processes must not both post the same open incident');
  assert.equal(Object.keys(f.record().incidents).length, 1);
  assert.deepEqual(f.record().log.map(row => row.action), ['alert', 'repeat']);
});

const MINUTE = 60_000, DAY = 24 * 60 * MINUTE;
const realAsk = {cause:'Disk available 3%',tried:'Read disk usage: available 3%',need:'Run pdd autopilot doctor?',paused:true};
async function persistent(f, issue, fields=realAsk) {
  await f.alert(issue,'resource',fields);f.time+=15*MINUTE;return f.alert(issue,'resource',fields);
}

test('restored: infrastructure set/test/clear, issue routing, recovery isolation and fallback',async t=>{
  const f=setup(t), selected=['--destination','infrastructure'];
  await f.pdd(['autopilot','alerts','set'],DISCORD);
  const configured=await f.pdd(['autopilot','alerts','set',...selected],SLACK);
  assert.equal(configured.exitCode,0);assert.match(configured.stdout,/--destination infrastructure/);
  const infra=join(f.home,'.config','pdd','autopilot-infrastructure-alerts.json');
  assert.equal(statSync(infra).mode&0o777,0o600);const ordinary=readFileSync(f.config,'utf8');
  f.replies.push({status:200,text:'ok'});await persistent(f,41);
  f.replies.push(echo);await f.alert(42,'decision',{cause:'Policy choice',tried:'Read policy',need:'Choose retention days?'});
  assert.ok(f.requests[0].url.startsWith(SLACK));assert.ok(f.requests[1].url.startsWith(DISCORD));
  f.time+=DAY;f.replies.push({status:200,text:'ok'},echo);
  await f.alert(41,'recovered',{cause:'Disk restored',kind:'resource',code:'41:resource'});
  await f.alert(42,'recovered',{cause:'Policy chosen',kind:'decision',code:'42:decision'});
  assert.ok(f.requests[2].url.startsWith(SLACK),'infrastructure recovery stays on infrastructure');
  assert.ok(f.requests[3].url.startsWith(DISCORD),'person recovery stays on ordinary destination');
  assert.deepEqual(f.record().incidents,{});
  const length=f.record().log.length;f.replies.push({status:200,text:'ok'});
  assert.equal((await f.pdd(['autopilot','alerts','test',...selected])).exitCode,0);
  assert.equal(f.record().log.length,length+1);assert.equal(f.record().log.at(-1).destination,'infrastructure');
  assert.equal((await f.pdd(['autopilot','alerts','clear',...selected])).exitCode,0);
  assert.equal(existsSync(infra),false);assert.equal(readFileSync(f.config,'utf8'),ordinary);
  f.replies.push(echo);await persistent(f,43);assert.ok(f.requests.at(-1).url.startsWith(DISCORD),'unset infrastructure falls back');
  assert.equal((await f.pdd(['autopilot','alerts','clear','--destination','unknown'])).exitCode,2);
  assert.equal(readFileSync(f.config,'utf8'),ordinary);f.noSecret();
});

test('restored: destination tests retain a concurrent alert save and isolate failures by route',async t=>{
  const f=setup(t);await f.pdd(['autopilot','alerts','set'],DISCORD);
  await f.pdd(['autopilot','alerts','set','--destination','infrastructure'],SLACK);
  const fields={cause:'Missing policy choice',tried:'Read policy',need:'Choose policy A?'};
  f.replies.push(echo);await f.alert(40,'decision',fields);
  let release,entered;const hold=new Promise(r=>{release=r;}),started=new Promise(r=>{entered=r;});
  f.replies.push(async request=>{entered();await hold;return echo(request);},echo);
  const sending=f.alert(41,'decision',fields);await started;
  const testing=f.pdd(['autopilot','alerts','test']);release();
  assert.deepEqual((await Promise.all([sending,testing])).map(r=>r.exitCode),[0,0]);
  assert.equal(Object.keys(f.record().incidents).length,2);assert.equal(f.record().log.at(-1).action,'test');
  f.replies.push({status:403,text:''});await persistent(f,42);
  let status=alertStatusLine({repo:'owner/repo',env:f.env},f.ports);assert.match(status,/--destination infrastructure/);
  f.replies.push(echo);await f.pdd(['autopilot','alerts','test']);
  status=alertStatusLine({repo:'owner/repo',env:f.env},f.ports);assert.match(status,/403/,'ordinary test cannot hide infrastructure failure');
  f.replies.push({status:200,text:'ok'});await f.pdd(['autopilot','alerts','test','--destination','infrastructure']);
  status=alertStatusLine({repo:'owner/repo',env:f.env},f.ports);
  assert.doesNotMatch(status,/403/);assert.match(status,/--destination infrastructure/,'open undelivered incident still shows');
  // Reverse the routes: a successful infrastructure test cannot hide an ordinary failure.
  f.replies.push({status:500,text:''});await f.alert(44,'decision',fields);
  f.replies.push({status:200,text:'ok'});await f.pdd(['autopilot','alerts','test','--destination','infrastructure']);
  status=alertStatusLine({repo:'owner/repo',env:f.env},f.ports);assert.match(status,/500/);
});

test('restored: saved machine identity survives hostname changes and ignores other repositories',async t=>{
  const f=setup(t);await f.pdd(['autopilot','alerts','set'],DISCORD);mkdirSync(f.ports.stateRoot,{recursive:true});
  for(const [name,repo,machine] of [['a','owner/other','other-machine'],['b','Owner/Repo','saved-machine']])
    writeFileSync(join(f.ports.stateRoot,`${name.repeat(20)}.json`),JSON.stringify({repo,machine}));
  f.ports.hostname=()=> 'renamed-host';f.replies.push(echo);
  await persistent(f,12,{...realAsk,code:'disk'});
  assert.equal(Object.values(f.record().incidents)[0].host,'saved-machine');
  f.ports.hostname=()=> 'renamed-again';await f.alert(13,'resource',{...realAsk,code:'disk'});
  assert.equal(f.requests.length,1);assert.equal(Object.keys(f.record().incidents).length,1);
  f.time+=DAY;f.replies.push(echo);await f.alert(13,'recovered',{cause:'Disk restored',kind:'resource',code:'disk'});
  assert.equal(f.requests.length,2);assert.deepEqual(f.record().incidents,{});f.noSecret();
});

test('restored: current checkout saved machine wins over sorted matching repository state',async t=>{
  const f=setup(t);await f.pdd(['autopilot','alerts','set'],DISCORD);mkdirSync(f.ports.stateRoot,{recursive:true});
  const id=createHash('sha256').update(f.cwd).digest('hex').slice(0,20);
  writeFileSync(join(f.ports.stateRoot,`${'0'.repeat(20)}.json`),JSON.stringify({repo:'owner/repo',machine:'machine-a'}));
  writeFileSync(join(f.ports.stateRoot,`${id}.json`),JSON.stringify({repo:'owner/repo',machine:'machine-b'}));
  f.replies.push(echo);await persistent(f,51);
  assert.equal(Object.values(f.record().incidents)[0].host,'machine-b');f.noSecret();
});

test('restored: failed digest status names digest without an invented issue',async t=>{
  const f=setup(t);await f.pdd(['autopilot','alerts','set'],DISCORD);f.replies.push({status:403,text:''});
  await runAutopilotAlerts({action:'digest',cwd:f.cwd,env:f.env,attention:[{number:41,category:'decision',need:'Choose policy A?'}]},f.ports);
  const status=alertStatusLine({repo:'owner/repo',env:f.env},f.ports);
  assert.match(status,/digest/);assert.match(status,/403/);assert.doesNotMatch(status,/#undefined/);
});
