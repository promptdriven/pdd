import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, statSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { runPdd } from '../src/pdd-cli.mjs';

// Synthetic webhook addresses. The fake HTTP port records requests; no test sends a real request.
const DISCORD = 'https://discord.com/api/webhooks/123456789012345678/SECRET-discord_token';
const SLACK = 'https://hooks.slack.com/services/T0000/B0000/SECRETslacktoken';
const SECRETS = [DISCORD, SLACK, 'SECRET', 'discord_token', 'slacktoken', '123456789012345678'];
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
  // The webhook address never reaches any output, request record or local file other than the private destination.
  f.noSecret = () => {
    const files = readdirSync(home, { recursive: true }).map(name => join(home, name)).filter(path => statSync(path).isFile() && path !== f.config);
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
  assert.equal(f.record().incidents['12:usage-limit'].result, 'failed');

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
  assert.deepEqual(f.record().incidents['12:usage-limit'].fields, usage);
  assert.equal(f.record().incidents['12:usage-limit'].result, 'not-configured');
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

test('invalid alert input records and sends nothing', async t => {
  const f = setup(t);
  await f.pdd(['autopilot', 'alerts', 'set'], DISCORD);
  const cases = [
    ['autopilot', 'alert', '--issue', '12', '--kind', 'usage-limit', '--input', 'file.json'],
    ['autopilot', 'alert', '--issue', 'twelve', '--kind', 'usage-limit', '--input', '-'],
    ['autopilot', 'alert', '--kind', 'usage-limit', '--input', '-'],
    ['autopilot', 'alert', '--issue', '12', '--input', '-'],
    ['autopilot', 'alert', '--issue', '12', '--kind', 'progress', '--input', '-'],
  ];
  for (const argv of cases) assert.equal((await f.pdd(argv, JSON.stringify(usage))).exitCode, 2, argv.join(' '));
  for (const text of ['not json', '[]', JSON.stringify({ cause: 'x', tried: 'y' }), JSON.stringify({ ...usage, need: '  ' })])
    assert.equal((await f.pdd(['autopilot', 'alert', '--issue', '12', '--kind', 'usage-limit', '--input', '-'], text)).exitCode, 2, text);
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
