import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, statSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';
import { alertStatusLine } from '../src/autopilot-alerts.mjs';

// Synthetic webhook addresses. The fake HTTP port records requests; no test sends a real request.
const DISCORD = 'https://discord.com/api/webhooks/123456789012345678/SECRET-discord_token';
const SLACK = 'https://hooks.slack.com/services/T0000/B0000/SECRETslacktoken';
const BOT_TOKEN = 'MTMwMDAwMDAwMDAwMDAwMDAx.GbotA1.SECRETbot_token_value_0123456789';
const ROTATED_TOKEN = 'MTMwMDAwMDAwMDAwMDAwMDAy.GbotB2.SECRETrotated_token_9876543210';
const CHANNEL = '1300000000000000099';
const SECRETS = [DISCORD, SLACK, 'SECRET', 'discord_token', 'slacktoken', '123456789012345678', BOT_TOKEN, ROTATED_TOKEN, 'bot_token_value', 'rotated_token'];
const capture = () => ({ text: '', write(value) { this.text += value; } });
const echo = request => ({ status: 200, text: JSON.stringify({ id: '991', channel_id: '7', content: request.body.content }) });
const usage = { cause: 'Codex usage limit; resets 2026-11-06T18:00Z', tried: 'Paused issue 12 and kept other work going', need: 'More quota or another signed-in account' };

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
  f.env = { HOME: home, PATH: process.env.PATH };
  f.pdd = async (argv, stdin = '') => {
    const stdout = capture(), stderr = capture();
    const exitCode = await runPdd(argv, { cwd, env: f.env, stdin, stdout, stderr, autopilotAlertsPorts: f.ports });
    f.outputs.push(stdout.text, stderr.text);
    return { exitCode, stdout: stdout.text, stderr: stderr.text };
  };
  f.alert = (issue, kind, fields, ...extra) => f.pdd(['autopilot', 'alert', '--issue', String(issue), '--kind', kind, '--input', '-', ...extra], JSON.stringify(fields));
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
      stateRoot: f.ports.stateRoot, timer: async () => false, herdr: async () => ({ running: false }),
      run: async command => { assert.equal(command, 'git', 'status runs only local git'); return { code: 0, stdout: `${cwd}\n`, stderr: '' }; },
    } });
    f.outputs.push(stdout.text, stderr.text);
    assert.equal(exitCode, 0, stderr.text);
    return stdout.text.trimEnd().split('\n');
  };
  // The secret never reaches any output or local file other than the private destination (or no file at all for a token command).
  f.noSecret = ({ config = false } = {}) => {
    const files = readdirSync(home, { recursive: true }).map(name => join(home, name)).filter(path => statSync(path).isFile() && (config || path !== f.config));
    const texts = [...f.outputs, ...files.map(path => readFileSync(path, 'utf8'))];
    for (const text of texts) for (const secret of SECRETS) assert.ok(!text.includes(secret), `a secret part is visible: ${text}`);
  };
  return f;
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
  for (const bad of ['https://example.com/api/webhooks/1/abc', 'http://discord.com/api/webhooks/1/abc', 'https://discord.com/api/webhooks/1/SECRET extra', '']) {
    const refused = await f.pdd(['autopilot', 'alerts', 'set'], bad);
    assert.equal(refused.exitCode, 2, bad);
    assert.ok(!refused.stderr.includes('example.com'), 'a refused value is not echoed');
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
    assert.match((await f.alert(12, 'usage-limit', usage)).stdout, /confirmed/);
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
  const sent = await f.alert(30, 'access', { cause: 'Needs <!channel> & a paid plan', tried: 'Read the billing page', need: 'Approve spending' });
  assert.equal(sent.exitCode, 0, sent.stderr);
  assert.match(f.requests.at(-1).body.text, /Needs &lt;!channel&gt; &amp; a paid plan/);
  assert.equal(f.record().incidents['30:access'].result, 'delivered');
  f.noSecret();
});

test('an alert names repo, issue link, cause, attempt and need, and a repeat without a material change sends nothing', async t => {
  const f = setup(t);
  await f.pdd(['autopilot', 'alerts', 'set'], DISCORD);
  f.replies.push(echo);
  const first = await f.alert(12, 'usage-limit', usage);
  assert.equal(first.exitCode, 0, first.stderr);
  assert.match(first.stdout, /#12 usage-limit/);
  assert.equal(f.requests.length, 1);
  assert.equal(f.requests[0].body.content, [
    'PDD Autopilot alert: usage-limit (test-host)', 'Repository: owner/repo', 'Issue: https://github.com/owner/repo/issues/12',
    `Cause: ${usage.cause}`, `Tried: ${usage.tried}`, `Needs: ${usage.need}`, 'Answer on the GitHub issue.'].join('\n'));

  const repeat = await f.alert(12, 'usage-limit', usage);
  assert.equal(repeat.exitCode, 0);
  assert.match(repeat.stdout, /nothing sent/);
  const reworded = await f.alert(12, 'usage-limit', { ...usage, tried: 'Paused it again' });
  assert.match(reworded.stdout, /nothing sent/, 'without --update new wording is not a material change');
  const sameUpdate = await f.alert(12, 'usage-limit', usage, '--update');
  assert.match(sameUpdate.stdout, /nothing sent/, '--update with unchanged fields sends nothing');
  assert.equal(f.requests.length, 1);

  f.replies.push(echo);
  const update = await f.alert(12, 'usage-limit', { ...usage, cause: 'Codex usage limit; reset moved to 2026-11-06T20:00Z' }, '--update');
  assert.equal(update.exitCode, 0);
  assert.equal(f.requests.length, 2);
  assert.match(f.requests[1].body.content, /^PDD Autopilot update: usage-limit \(test-host\)\n[^]*reset moved/);

  f.replies.push(echo);
  await f.alert(12, 'decision', { cause: 'Two layouts fit the Story', tried: 'Asked on the issue', need: 'Pick one layout' });
  assert.equal(f.requests.length, 3, 'another kind on the same issue is another incident');
  const actions = f.record().log.map(row => `${row.kind}:${row.action}:${row.result}`);
  assert.deepEqual(actions, ['usage-limit:alert:delivered', 'usage-limit:repeat:not-sent', 'usage-limit:repeat:not-sent', 'usage-limit:repeat:not-sent', 'usage-limit:update:delivered', 'decision:alert:delivered']);
  assert.equal(statSync(f.recordFile()).mode & 0o777, 0o600);
  assert.deepEqual((await f.status()).length, 1, 'delivered alerts add no status line');
  f.noSecret();
});

test('a failed delivery is recorded, does not stop work, shows in status, and the next call sends it again', async t => {
  const f = setup(t);
  await f.pdd(['autopilot', 'alerts', 'set'], DISCORD);
  f.replies.push({ status: 500, text: `{"message":"${DISCORD}"}` });
  const failed = await f.alert(12, 'usage-limit', usage);
  assert.equal(failed.exitCode, 0, 'work continues after a failed delivery');
  assert.match(failed.stdout, /delivery failed \(HTTP 500\)/);
  assert.match(failed.stdout, /pdd autopilot status/);
  assert.equal(f.record().incidents['usage-limit@test-host'].result, 'failed');

  const lines = await f.status();
  assert.equal(lines.length, 2);
  assert.match(lines[0], /^Autopilot enabled; .*owner\/repo/);
  assert.equal(lines[1], 'Alerts: 1 open alert not delivered; last delivery failed (HTTP 500) for #12 usage-limit at 2026-11-06T10:00:00.000Z; check with pdd autopilot alerts test.');

  f.time += 30 * 60 * 1000;
  f.replies.push(echo);
  const retried = await f.alert(12, 'usage-limit', usage);
  assert.equal(f.requests.length, 2, 'a failed alert is sent again on the next call');
  assert.match(retried.stdout, /confirmed/);
  assert.equal((await f.status()).length, 1, 'the status line ends after delivery');

  f.replies.push(Object.assign(Error(`connect ECONNREFUSED ${DISCORD}`), { code: 'unreached' }));
  const unreached = await f.alert(14, 'resource', { cause: 'Disk full on the runner', tried: 'Stopped new runs', need: 'Free disk space' });
  assert.match(unreached.stdout, /delivery failed \(not reached\)/);
  f.replies.push(Object.assign(Error('timeout'), { code: 'unknown' }));
  await f.alert(15, 'stuck', { cause: 'No progress after the retry time', tried: 'Two repairs', need: 'A person to look' });
  const again = await f.alert(15, 'stuck', { cause: 'No progress after the retry time', tried: 'Two repairs', need: 'A person to look' });
  assert.match(again.stdout, /nothing sent/, 'an unconfirmed alert may exist, so it is not sent again');
  assert.equal(f.requests.length, 4);
  assert.match((await f.status())[1], /^Alerts: 2 open alerts not delivered; last delivery unconfirmed \(no reply\) for #15 stuck/);
  f.noSecret();
});

test('without a destination an alert is recorded locally, work continues and status says how to set one', async t => {
  const f = setup(t);
  const result = await f.alert(12, 'usage-limit', usage);
  assert.equal(result.exitCode, 0);
  assert.match(result.stdout, /recorded on this machine/);
  assert.match(result.stdout, /pdd autopilot alerts set/);
  assert.equal(f.requests.length, 0);
  assert.deepEqual(f.record().incidents['usage-limit@test-host'].fields, usage);
  assert.equal(f.record().incidents['usage-limit@test-host'].result, 'not-configured');
  assert.equal((await f.status())[1], 'Alerts: 1 open alert not delivered; set one with pdd autopilot alerts set.');

  assert.match((await f.alert(12, 'usage-limit', usage)).stdout, /nothing sent/, 'no destination: a repeat adds no send');
  await f.pdd(['autopilot', 'alerts', 'set'], DISCORD);
  f.replies.push(echo);
  await f.alert(12, 'usage-limit', usage);
  assert.equal(f.requests.length, 1, 'once a destination exists, the recorded alert is sent');
  f.noSecret();
});

test('recovered closes the open alerts of the issue with one recovery message', async t => {
  const f = setup(t);
  await f.pdd(['autopilot', 'alerts', 'set'], DISCORD);
  f.replies.push(echo, echo, echo);
  await f.alert(12, 'usage-limit', usage);
  await f.alert(12, 'decision', { cause: 'Two layouts fit', tried: 'Asked on the issue', need: 'Pick one' });
  await f.alert(40, 'stuck', { cause: 'Other issue', tried: 'Waited', need: 'Look' });

  f.replies.push(echo);
  const recovered = await f.alert(12, 'recovered', { cause: 'Quota reset and the layout was chosen' });
  assert.equal(recovered.exitCode, 0, recovered.stderr);
  assert.equal(f.requests.at(-1).body.content, ['PDD Autopilot recovered: usage-limit, decision (test-host)', 'Repository: owner/repo',
    'Issue: https://github.com/owner/repo/issues/12', 'What changed: Quota reset and the layout was chosen'].join('\n'));
  assert.deepEqual(Object.keys(f.record().incidents), ['40:stuck'], 'only the issue named in the recovery closes');

  const count = f.requests.length;
  const none = await f.alert(12, 'recovered', { cause: 'Again' });
  assert.match(none.stdout, /nothing sent/);
  assert.equal(f.requests.length, count, 'a second recovery sends nothing');
  f.replies.push(echo);
  await f.alert(12, 'usage-limit', usage);
  assert.equal(f.requests.length, count + 1, 'a later alert opens a new incident');
  f.noSecret();
});

test('one usage limit that blocks five issues sends one alert; the issues join it, --update sends the list and recovered closes it', async t => {
  const f = setup(t);
  await f.pdd(['autopilot', 'alerts', 'set'], DISCORD);
  const links = issues => issues.map(n => `https://github.com/owner/repo/issues/${n}`).join(', ');
  f.replies.push(echo);
  assert.match((await f.alert(12, 'usage-limit', usage)).stdout, /Alert sent for #12 usage-limit; the webhook confirmed it/);
  for (const issue of [13, 14, 15, 16]) {
    const joined = await f.alert(issue, 'usage-limit', usage);
    assert.equal(joined.exitCode, 0);
    assert.match(joined.stdout, new RegExp(`Added #${issue} to the open usage-limit alert on this machine; nothing sent`));
  }
  assert.match((await f.alert(13, 'usage-limit', usage)).stdout, /already open; nothing sent/);
  assert.equal(f.requests.length, 1, 'one usage limit is one alert, not one per blocked issue');
  assert.deepEqual(f.record().incidents['usage-limit@test-host'].issues, [12, 13, 14, 15, 16]);

  f.replies.push(echo);
  assert.match((await f.alert(14, 'usage-limit', usage, '--update')).stdout, /Update sent for #12, #13, #14, #15, #16 usage-limit; the webhook confirmed it/);
  assert.equal(f.requests[1].body.content, ['PDD Autopilot update: usage-limit (test-host)', 'Repository: owner/repo', `Issues: ${links([12, 13, 14, 15, 16])}`,
    `Cause: ${usage.cause}`, `Tried: ${usage.tried}`, `Needs: ${usage.need}`, 'Answer on the GitHub issue.'].join('\n'));
  assert.match((await f.alert(15, 'usage-limit', usage, '--update')).stdout, /nothing sent/, 'the list was sent, so an unchanged --update sends nothing');

  const layout = { cause: 'Two layouts fit the Story', tried: 'Asked on the issue', need: 'Pick one layout' };
  f.replies.push(echo, echo);
  await f.alert(12, 'decision', layout);
  await f.alert(13, 'decision', layout);
  assert.equal(f.requests.length, 4, 'a decision stays one incident per issue');
  f.ports.hostname = () => 'other-host';
  f.replies.push(echo);
  await f.alert(12, 'usage-limit', usage);
  assert.match(f.requests[4].body.content, /^PDD Autopilot alert: usage-limit \(other-host\)\n/, 'another machine is another incident');
  f.ports.hostname = () => 'test-host';

  // A failed send is sent again by the next call from any affected issue, with the current list.
  const disk = { cause: 'Disk full on the runner', tried: 'Stopped new runs', need: 'Free disk space' };
  f.replies.push({ status: 503, text: '' });
  assert.match((await f.alert(20, 'resource', disk)).stdout, /delivery failed \(HTTP 503\)/);
  f.replies.push(echo);
  assert.match((await f.alert(21, 'resource', disk)).stdout, /Alert sent for #20, #21 resource; the webhook confirmed it/);
  assert.match(f.requests.at(-1).body.content, new RegExp(`\nIssues: ${links([20, 21]).replaceAll('.', '\\.')}\n`));
  for (let issue = 22; issue <= 31; issue += 1) await f.alert(issue, 'resource', disk);
  f.replies.push(echo);
  await f.alert(31, 'resource', disk, '--update');
  assert.match(f.requests.at(-1).body.content, new RegExp(`\nIssues: ${links([20, 21, 22, 23, 24, 25, 26, 27, 28, 29]).replaceAll('.', '\\.')} and 2 more\n`));

  const count = f.requests.length;
  f.replies.push(echo);
  const recovered = await f.alert(16, 'recovered', { cause: 'The usage limit reset', kind: 'usage-limit' });
  assert.equal(recovered.exitCode, 0, recovered.stderr);
  assert.equal(f.requests.length, count + 1, 'one recovery for the whole incident');
  assert.equal(f.requests.at(-1).body.content, ['PDD Autopilot recovered: usage-limit (test-host)', 'Repository: owner/repo',
    `Issues: ${links([12, 13, 14, 15, 16])}`, 'What changed: The usage limit reset'].join('\n'));
  assert.deepEqual(Object.keys(f.record().incidents).sort(), ['12:decision', '13:decision', 'resource@test-host', 'usage-limit@other-host']);
  assert.match((await f.alert(13, 'recovered', { cause: 'Again', kind: 'usage-limit' })).stdout, /No open alert of kind usage-limit for #13; nothing sent/);

  f.replies.push(echo);
  await f.alert(12, 'recovered', { cause: 'The layout was chosen' });
  assert.match(f.requests.at(-1).body.content, /^PDD Autopilot recovered: decision \(test-host\)\n[^]*\nIssue: https:\/\/github\.com\/owner\/repo\/issues\/12\n/);
  assert.deepEqual(Object.keys(f.record().incidents).sort(), ['13:decision', 'resource@test-host', 'usage-limit@other-host'],
    'without a kind, the issue\'s own incidents of this machine close');
  f.replies.push(echo);
  await f.alert(14, 'usage-limit', usage);
  assert.match(f.requests.at(-1).body.content, /^PDD Autopilot alert: usage-limit \(test-host\)\n[^]*\nIssue: https:\/\/github\.com\/owner\/repo\/issues\/14\n/, 'a later limit opens a new incident');
  f.noSecret();
});

test('an access or spending decision is one incident per issue: two decisions send two alerts, and a recovery closes only its own', async t => {
  const f = setup(t);
  await f.pdd(['autopilot', 'alerts', 'set'], DISCORD);
  const plan = { cause: 'Issue 70 needs a paid OpenAI plan', tried: 'Read the billing page', need: 'Approve 20 USD per month' };
  const dataset = { cause: 'Issue 71 needs the private dataset repo', tried: 'Cloned it with the run account', need: 'Grant read access' };
  f.replies.push(echo, echo);
  assert.match((await f.alert(70, 'access', plan)).stdout, /Alert sent for #70 access; the webhook confirmed it/);
  assert.match((await f.alert(71, 'access', dataset)).stdout, /Alert sent for #71 access; the webhook confirmed it/);
  assert.equal(f.requests.length, 2, 'a second, different decision is sent to the person');
  assert.equal(f.requests[1].body.content, ['PDD Autopilot alert: access (test-host)', 'Repository: owner/repo', 'Issue: https://github.com/owner/repo/issues/71',
    `Cause: ${dataset.cause}`, `Tried: ${dataset.tried}`, `Needs: ${dataset.need}`, 'Answer on the GitHub issue.'].join('\n'));
  assert.deepEqual(Object.keys(f.record().incidents).sort(), ['70:access', '71:access']);

  f.replies.push(echo);
  await f.alert(70, 'recovered', { cause: 'Spending approved', kind: 'access' });
  assert.equal(f.requests.at(-1).body.content, ['PDD Autopilot recovered: access (test-host)', 'Repository: owner/repo',
    'Issue: https://github.com/owner/repo/issues/70', 'What changed: Spending approved'].join('\n'));
  assert.deepEqual(Object.keys(f.record().incidents), ['71:access'], 'the other decision stays open');
  assert.match((await f.alert(71, 'access', dataset)).stdout, /Alert for #71 access is already open; nothing sent/);
  assert.equal(f.requests.length, 3);
  f.noSecret();
});

test('the machine in an incident is the coordinator\'s saved machine name, so a host rename finds the same incident', async t => {
  const f = setup(t);
  await f.pdd(['autopilot', 'alerts', 'set'], DISCORD);
  // Launcher states: one of another repository, then this repository's, with the machine name saved at its first start.
  mkdirSync(f.ports.stateRoot, { recursive: true });
  writeFileSync(join(f.ports.stateRoot, `${'a'.repeat(20)}.json`), JSON.stringify({ repo: 'owner/other', enabled: true, machine: 'other-repo-machine' }));
  writeFileSync(join(f.ports.stateRoot, `${'b'.repeat(20)}.json`), JSON.stringify({ repo: 'Owner/Repo', enabled: true, machine: 'saved-machine' }));
  f.ports.hostname = () => 'renamed-host-2';
  f.replies.push(echo);
  await f.alert(12, 'usage-limit', usage);
  assert.match(f.requests[0].body.content, /^PDD Autopilot alert: usage-limit \(saved-machine\)\n/);
  f.ports.hostname = () => 'renamed-host-3';
  assert.match((await f.alert(13, 'usage-limit', usage)).stdout, /Added #13 to the open usage-limit alert on this machine; nothing sent/);
  assert.equal(f.requests.length, 1, 'a host rename opens no new incident');
  f.replies.push(echo);
  await f.alert(13, 'recovered', { cause: 'The usage limit reset', kind: 'usage-limit' });
  assert.equal(f.requests[1].body.content, ['PDD Autopilot recovered: usage-limit (saved-machine)', 'Repository: owner/repo',
    'Issues: https://github.com/owner/repo/issues/12, https://github.com/owner/repo/issues/13', 'What changed: The usage limit reset'].join('\n'));
  assert.deepEqual(f.record().incidents, {}, 'the recovery closes the incident after the rename');
  f.noSecret();
});

test('a delivered alerts test ends the status line of an older failed recovery; an open undelivered alert still shows', async t => {
  const f = setup(t);
  await f.pdd(['autopilot', 'alerts', 'set'], DISCORD);
  f.replies.push(echo, { status: 500, text: '' });
  await f.alert(30, 'decision', { cause: 'Two layouts fit', tried: 'Asked on the issue', need: 'Pick one' });
  assert.match((await f.alert(30, 'recovered', { cause: 'The layout was chosen', kind: 'decision' })).stdout, /delivery failed \(HTTP 500\)/);
  assert.deepEqual(f.record().incidents, {}, 'the recovery closed the incident');
  assert.match((await f.status())[1], /^Alerts: last delivery failed \(HTTP 500\) for #30 decision at /);

  f.time += 60 * 1000;
  f.replies.push(echo);
  assert.equal((await f.pdd(['autopilot', 'alerts', 'test'])).exitCode, 0);
  assert.equal((await f.status()).length, 1, 'the delivered test is the newest send');
  assert.deepEqual(f.record().log.at(-1), { at: '2026-11-06T10:01:00.000Z', kind: 'test', action: 'test', result: 'delivered' });

  f.replies.push({ status: 500, text: '' });
  await f.alert(31, 'stuck', { cause: 'No progress', tried: 'Two repairs', need: 'A person to look' });
  f.replies.push(echo);
  await f.pdd(['autopilot', 'alerts', 'test']);
  assert.equal((await f.status())[1], 'Alerts: 1 open alert not delivered; check with pdd autopilot alerts test.');
  f.replies.push(echo);
  assert.match((await f.alert(31, 'stuck', { cause: 'No progress', tried: 'Two repairs', need: 'A person to look' })).stdout, /Alert sent for #31 stuck/);
  assert.equal((await f.status()).length, 1);
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
    [['autopilot', 'alert', '--issue', '12', '--input', '-'], JSON.stringify(usage), /--kind usage-limit\|resource\|runtime\|runtime-access\|access\|decision\|stuck\|recovered/],
    [alert, 'not json', /JSON object on stdin with nonblank "cause", "tried", "need"\. Nothing was recorded/],
    [alert, '[]', /JSON object on stdin/],
    [alert, JSON.stringify({ cause: 'x', tried: 'y' }), /nonblank "cause", "tried", "need"/],
    [alert, JSON.stringify({ ...usage, need: '  ' }), /nonblank "cause", "tried", "need"/],
    [['autopilot', 'alert', '--issue', '12', '--kind', 'recovered', '--input', '-'], JSON.stringify({ cause: '' }), /nonblank "cause"\. Nothing was recorded/],
    [['autopilot', 'alert', '--issue', '12', '--kind', 'recovered', '--input', '-'], JSON.stringify({ cause: 'Quota reset', kind: 'progress' }), /"kind" in a recovery as one of usage-limit\|resource\|runtime\|runtime-access\|access\|decision\|stuck/],
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

// A fake Discord REST v10 API: it keeps posted messages so the readback is a real lookup.
function fakeDiscord(f) {
  const posted = new Map();
  f.discord = { me: 200, channel: 200, readback: 'same' };
  f.ports.http = async request => {
    f.requests.push(structuredClone(request));
    const path = request.url.startsWith('https://discord.com/api/v10/') ? request.url.slice('https://discord.com/api/v10'.length) : null;
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
      ? text.replace(/\r\n?/g, '\n').replace(/[ \t]+$/gm, '').trim() : 'edited by someone else';
    if (request.method === 'GET' && posted.has(message)) return reply(200, { id: message, content: stored(posted.get(message)) });
    return reply(404, { message: 'Unknown' });
  };
  f.route = request => `${request.method} ${request.url.slice('https://discord.com/api/v10'.length)}`;
}

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
    assert.match(request.headers['user-agent'], /^DiscordBot \(https:\/\/github\.com\/promptdriven\/pdd, [^)]+\)$/);
    assert.equal(request.body === undefined, request.method === 'GET', 'only the POST has a body');
  }
  const post = f.requests[2].body;
  assert.equal(post.flags, 4, 'link embeds are suppressed');
  assert.deepEqual(post.allowed_mentions, { parse: [] });
  assert.match(post.content, /^PDD Autopilot test alert \(test-host\)\.$/);

  const sent = await f.alert(12, 'usage-limit', usage);
  assert.equal(sent.exitCode, 0, sent.stderr);
  assert.match(sent.stdout, /confirmed/);
  assert.deepEqual(f.requests.slice(4).map(f.route), [`POST /channels/${CHANNEL}/messages`, `GET /channels/${CHANNEL}/messages/1300000000000000101`]);
  assert.match(f.requests[4].body.content, /^PDD Autopilot alert: usage-limit \(test-host\)\nRepository: owner\/repo\nIssue: https:\/\/github\.com\/owner\/repo\/issues\/12\n/);
  assert.equal(f.record().incidents['usage-limit@test-host'].result, 'delivered');
  assert.equal((await f.status()).length, 1);
  f.noSecret();
});

test('a Discord bot readback mismatch is unconfirmed, shown in status and not sent again', async t => {
  const f = setup(t); fakeDiscord(f);
  await f.pdd(['autopilot', 'alerts', 'set', '--discord-channel', CHANNEL], BOT_TOKEN);
  f.discord.readback = 'changed';
  const sent = await f.alert(12, 'stuck', { cause: 'No progress after the retry time', tried: 'Two repairs', need: 'A person to look' });
  assert.equal(sent.exitCode, 0, 'work continues');
  assert.match(sent.stdout, /delivery unconfirmed \(readback mismatch\)/);
  assert.equal(f.record().incidents['12:stuck'].result, 'unconfirmed');
  assert.match((await f.status())[1], /^Alerts: 1 open alert not delivered; last delivery unconfirmed \(readback mismatch\) for #12 stuck/);
  const count = f.requests.length;
  assert.match((await f.alert(12, 'stuck', { cause: 'No progress after the retry time', tried: 'Two repairs', need: 'A person to look' })).stdout, /nothing sent/);
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
  const sent = await f.alert(12, 'stuck', { cause: 'Line one  \r\nLine two\rLine three', tried: 'Two repairs', need: 'A person to look' });
  assert.equal(sent.stdout, 'Alert sent for #12 stuck; the Discord bot readback confirmed it.\n');
  assert.match(f.requests.at(-2).body.content, /\nCause: Line one {2}\r\nLine two\rLine three\n/, 'the sent text is unchanged');
  assert.equal(f.record().incidents['12:stuck'].result, 'delivered');
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

  assert.match((await f.alert(12, 'usage-limit', usage)).stdout, /confirmed/);
  assert.equal(f.requests.at(-1).headers.authorization, `Bot ${BOT_TOKEN}`);
  writeFileSync(tokenFile, ROTATED_TOKEN);
  assert.match((await f.alert(13, 'resource', { cause: 'Disk full', tried: 'Stopped new runs', need: 'Free disk space' })).stdout, /confirmed/);
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
  assert.match((await f.alert(15, 'decision', { cause: 'Two layouts', tried: 'Asked on the issue', need: 'Pick one' })).stdout, /token command gave no token/);
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
