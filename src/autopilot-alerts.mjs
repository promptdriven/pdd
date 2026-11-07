// Generated from prompts/cli/autopilot-alerts.prompt.md (sha256: c1c0b328f2ca7a1e7e84d8332461cbb6732e4a3a8a634ec67a9976bc62fd5a72).
import * as nativeFs from 'node:fs';
import { createHash, randomUUID } from 'node:crypto';
import { execFile } from 'node:child_process';
import { hostname as osHostname, userInfo } from 'node:os';
import { dirname, isAbsolute, join } from 'node:path';
import { promisify } from 'node:util';

const execute = promisify(execFile);
export const ALERT_KINDS = Object.freeze(['usage-limit', 'resource', 'access', 'decision', 'stuck', 'long-running', 'recovered']);
// These incidents are shared by the whole machine: one incident per repository, machine and kind lists every affected issue.
// An access or spending decision belongs to its issue, like a product decision.
const MACHINE_KINDS = Object.freeze(['usage-limit', 'resource']);
const LOG_LIMIT = 200, TEXT_LIMIT = 1900, FIELD_LIMIT = 500, ISSUE_LIMIT = 10, TIMEOUT_MS = 10000, TOKEN_COMMAND_MS = 30000;
const SERVICE = { discord: 'Discord', slack: 'Slack', 'discord-bot': 'Discord bot' };
const DISCORD_API = 'https://discord.com/api/v10';
const SNOWFLAKE = /^[0-9]{17,20}$/, BOT_TOKEN = /^[A-Za-z0-9._-]{20,256}$/;
const VERSION = (() => { try { return JSON.parse(nativeFs.readFileSync(new URL('../package.json', import.meta.url), 'utf8')).version || '0'; } catch { return '0'; } })();
const USER_AGENT = `DiscordBot (https://github.com/promptdriven/pdd, ${VERSION})`;
const SENDS = ['delivered', 'failed', 'unconfirmed'];
// Errors that prove the request never reached the webhook server, so a later call may send again.
const UNREACHED = new Set(['ENOTFOUND', 'EAI_AGAIN', 'ECONNREFUSED', 'EHOSTUNREACH', 'ENETUNREACH', 'ERR_TLS_CERT_ALTNAME_INVALID',
  'CERT_HAS_EXPIRED', 'UNABLE_TO_VERIFY_LEAF_SIGNATURE', 'SELF_SIGNED_CERT_IN_CHAIN', 'DEPTH_ZERO_SELF_SIGNED_CERT']);
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const oneLine = value => String(value).replace(/[\x00-\x1f\x7f]+/g, ' ').trim();
// Defense in depth: no reply of this module may carry a webhook address or a bot token, even one that a bug let through.
const scrub = text => String(text).replace(/https?:\/\/\S*(?:webhooks|hooks\.slack\.com)\S*/gi, '[webhook]')
  .replace(/[A-Za-z0-9_-]{20,}\.[A-Za-z0-9_-]{4,}\.[A-Za-z0-9_-]{20,}/g, '[token]');
const done = (exitCode, message) => ({ exitCode, message: scrub(message) });
const repoName = value => typeof value === 'string' && /^[A-Za-z0-9][A-Za-z0-9-]*\/[A-Za-z0-9_.-]+$/.test(value);
const clip = (value, size) => value.length > size ? `${value.slice(0, size - 1)}…` : value;
// HOME counts only when it is absolute; else the account home from the OS (os.homedir() returns the same bad HOME).
// Without an absolute home, nothing is read or saved, so a secret or a record never lands in a checkout.
function homeFolder(env, ports) {
  if (isAbsolute(env.HOME ?? '')) return env.HOME;
  try { const value = (ports.userInfo ?? userInfo)().homedir; return typeof value === 'string' && isAbsolute(value) ? value : null; }
  catch { return null; }
}
const noHome = what => done(1, `Autopilot alerts need an absolute home folder; set HOME to an absolute path. ${what}`);
const configFile = (env, ports) => {
  if (isAbsolute(env.XDG_CONFIG_HOME ?? '')) return join(env.XDG_CONFIG_HOME, 'pdd', 'autopilot-alerts.json');
  const home = homeFolder(env, ports);
  return home ? join(home, '.config', 'pdd', 'autopilot-alerts.json') : null;
};
const stateRoot = (env, ports) => ports.stateRoot ?? (home => home && join(home, '.local', 'state', 'pdd', 'autopilot'))(homeFolder(env, ports));
const recordFile = (repo, env, ports) => {
  const root = stateRoot(env, ports);
  return root ? join(root, 'alerts', `${createHash('sha256').update(repo.toLowerCase()).digest('hex').slice(0, 20)}.json`) : null;
};
const STATE_FILE = /^[0-9a-f]{20}\.json$/;
const hostName = ports => oneLine((ports.hostname ?? osHostname)()) || 'unknown host';
// The launcher saves the coordinator's machine name once; a host name can change (macOS renames hosts), the saved name does not.
// This checkout's own state (the launcher's id for its Git top level) comes first, so machines that share one home keep their own incidents.
function machineName(fs, root, repo, ports, cwd) {
  try {
    const own = `${createHash('sha256').update(String(cwd)).digest('hex').slice(0, 20)}.json`;
    const names = fs.readdirSync(root).filter(name => STATE_FILE.test(name)).sort();
    for (const name of [...names.filter(name => name === own), ...names.filter(name => name !== own)]) {
      let state;
      try { state = JSON.parse(fs.readFileSync(join(root, name), 'utf8')); } catch { continue; }
      const saved = typeof state?.repo === 'string' && state.repo.toLowerCase() === repo.toLowerCase() && typeof state.machine === 'string' ? clip(oneLine(state.machine), 100) : '';
      if (saved) return saved;
    }
  } catch { /* No launcher state: use the host name. */ }
  return hostName(ports);
}

function writePrivate(fs, file, value) {
  fs.mkdirSync(dirname(file), { recursive: true, mode: 0o700 });
  const temp = `${file}.${randomUUID()}.tmp`;
  try { fs.writeFileSync(temp, JSON.stringify(value), { mode: 0o600, flag: 'wx' }); fs.chmodSync(temp, 0o600); fs.renameSync(temp, file); }
  finally { try { fs.unlinkSync(temp); } catch { /* Already renamed. */ } }
}

function webhook(text) {
  const value = String(text ?? '').trim();
  if (!value || /\s/.test(value)) return null;
  let url;
  try { url = new URL(value); } catch { return null; }
  if (url.protocol !== 'https:' || url.username || url.password || url.port) return null;
  if (['discord.com', 'discordapp.com', 'ptb.discord.com', 'canary.discord.com'].includes(url.hostname)
    && /^\/api\/(?:v\d+\/)?webhooks\/\d+\/[A-Za-z0-9_-]+\/?$/.test(url.pathname)) return { service: 'discord', url: url.href };
  if (url.hostname === 'hooks.slack.com' && /^\/services\/[A-Za-z0-9_-]+(?:\/[A-Za-z0-9_-]+)*\/?$/.test(url.pathname)) return { service: 'slack', url: url.href };
  return null;
}

// A missing, unreadable or invalid file counts as no destination; alerts are then recorded locally.
function readDestination(fs, env, ports) {
  const file = configFile(env, ports);
  if (!file) return null;
  try {
    const saved = JSON.parse(fs.readFileSync(file, 'utf8'));
    try { if ((fs.statSync(file).mode & 0o077) !== 0) fs.chmodSync(file, 0o600); } catch { /* Reading still works. */ }
    if (saved?.v === 1 && saved.service === 'discord-bot') return botDestination(saved);
    const parsed = saved?.v === 1 ? webhook(saved.url) : null;
    return parsed && parsed.service === saved.service ? parsed : null;
  } catch { return null; }
}

// A bot destination holds a channel and either a stored token or a token command, never both.
function botDestination(saved) {
  if (!SNOWFLAKE.test(String(saved.channel ?? ''))) return null;
  if (typeof saved.tokenCommand === 'string' && saved.tokenCommand.trim() && saved.token === undefined)
    return { service: 'discord-bot', channel: saved.channel, tokenCommand: saved.tokenCommand };
  if (typeof saved.token === 'string' && BOT_TOKEN.test(saved.token) && saved.tokenCommand === undefined)
    return { service: 'discord-bot', channel: saved.channel, token: saved.token };
  return null;
}

// Run the person's own command at send time; its output is the token and is never shown or saved.
async function nativeTokenCommand(command, { cwd }) {
  try { return (await execute('/bin/sh', ['-c', command], { cwd, encoding: 'utf8', timeout: TOKEN_COMMAND_MS, maxBuffer: 64 * 1024 })).stdout; }
  catch (error) { throw Object.assign(Error('token command failed'), { exitCode: Number.isInteger(error?.code) ? error.code : undefined }); }
}

async function botToken(destination, ports, cwd) {
  if (destination.token) return { token: destination.token };
  let output;
  try { output = await (ports.tokenCommand ?? nativeTokenCommand)(destination.tokenCommand, { cwd }); }
  catch (error) { return { error: `token command failed${Number.isInteger(error?.exitCode) ? ` (exit ${error.exitCode})` : ''}` }; }
  const token = String(output ?? '').trim();
  return BOT_TOKEN.test(token) ? { token } : { error: 'token command gave no token' };
}

async function nativeHttp({ method = 'POST', url, headers = {}, body }) {
  let response;
  try {
    response = await fetch(url, { method, headers: { ...(body === undefined ? {} : { 'content-type': 'application/json' }), ...headers },
      ...(body === undefined ? {} : { body: JSON.stringify(body) }), redirect: 'error', signal: AbortSignal.timeout(TIMEOUT_MS) });
  } catch (error) {
    const code = error?.cause?.code ?? error?.code;
    throw Object.assign(Error('webhook request failed'), { code: UNREACHED.has(code) ? 'unreached' : 'unknown' });
  }
  let text = '';
  try { text = await response.text(); } catch { /* A 2xx reply without a body has no readback. */ }
  return { status: response.status, text };
}

const success = status => Number.isInteger(status) && status >= 200 && status < 300;
// Compare text as a chat service may store it: LF line ends, no whitespace at a line end, and no whitespace at either end.
const normalized = text => text.replace(/\r\n?/g, '\n').split('\n').map(line => line.trimEnd()).join('\n').trim();
const sameText = (stored, sent) => typeof stored === 'string' && normalized(stored) === normalized(sent);
const parse = text => { try { return JSON.parse(text); } catch { return undefined; } };
const botRequest = (ports, token, method, path, body) => (ports.http ?? nativeHttp)({ method, url: `${DISCORD_API}${path}`,
  headers: { authorization: `Bot ${token}`, 'user-agent': USER_AGENT }, ...(body ? { body } : {}) });
async function botGet(ports, token, path) {
  let reply;
  try { reply = await botRequest(ports, token, 'GET', path); } catch { return { detail: 'no reply' }; }
  const status = Number(reply?.status), value = parse(reply?.text);
  if (!success(status)) return { detail: `HTTP ${Number.isInteger(status) ? status : 'unknown'}` };
  return object(value) ? { value } : { detail: 'unreadable reply' };
}

// POST the message with link embeds suppressed (flags 4), then GET it back: only matching content is a delivery.
async function botSend(destination, token, text, ports) {
  const channel = `/channels/${destination.channel}/messages`;
  let reply;
  try { reply = await botRequest(ports, token, 'POST', channel, { content: text, allowed_mentions: { parse: [] }, flags: 4 }); }
  catch (error) { return error?.code === 'unreached' ? { result: 'failed', detail: 'not reached' } : { result: 'unconfirmed', detail: 'no reply' }; }
  const status = Number(reply?.status), posted = parse(reply?.text);
  if (!success(status)) return { result: 'failed', detail: `HTTP ${Number.isInteger(status) ? status : 'unknown'}` };
  if (!/^[0-9]{1,25}$/.test(String(posted?.id ?? ''))) return { result: 'unconfirmed', detail: 'no message id' };
  const back = await botGet(ports, token, `${channel}/${posted.id}`);
  if (!back.value) return { result: 'unconfirmed', detail: `readback ${back.detail}` };
  return back.value.id === posted.id && sameText(back.value.content, text)
    ? { result: 'delivered' } : { result: 'unconfirmed', detail: 'readback mismatch' };
}

async function deliver(destination, text, ports, cwd) {
  if (destination.service === 'discord-bot') {
    const auth = await botToken(destination, ports, cwd);
    return auth.error ? { result: 'failed', detail: auth.error } : botSend(destination, auth.token, text, ports);
  }
  const discord = destination.service === 'discord';
  const body = discord ? { content: text, allowed_mentions: { parse: [] } }
    : { text: text.replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;') };
  let url = destination.url;
  if (discord) { const address = new URL(url); address.searchParams.set('wait', 'true'); url = address.href; }
  let reply;
  try { reply = await (ports.http ?? nativeHttp)({ url, body }); }
  catch (error) { return error?.code === 'unreached' ? { result: 'failed', detail: 'not reached' } : { result: 'unconfirmed', detail: 'no reply' }; }
  const status = Number(reply?.status), raw = typeof reply?.text === 'string' ? reply.text.trim() : '';
  if (!(Number.isInteger(status) && status >= 200 && status < 300)) {
    const word = !discord && /^[a-z_]{1,40}$/.test(raw) ? ` ${raw}` : '';
    return { result: 'failed', detail: `HTTP ${Number.isInteger(status) ? status : 'unknown'}${word}` };
  }
  if (!discord) return status === 200 && raw === 'ok' ? { result: 'delivered' } : { result: 'unconfirmed', detail: 'no readback' };
  let message;
  try { message = JSON.parse(raw); } catch { /* Checked below. */ }
  return typeof message?.id === 'string' && sameText(message.content, text)
    ? { result: 'delivered' } : { result: 'unconfirmed', detail: 'no readback' };
}

async function nativeRepository({ cwd }) {
  try {
    const { stdout } = await execute('gh', ['repo', 'view', '--json', 'nameWithOwner'], { cwd, encoding: 'utf8', timeout: TIMEOUT_MS });
    const name = JSON.parse(stdout).nameWithOwner;
    if (repoName(name)) return { nameWithOwner: name };
  } catch { /* Fall back to the origin remote. */ }
  try {
    const { stdout } = await execute('git', ['remote', 'get-url', 'origin'], { cwd, encoding: 'utf8', timeout: TIMEOUT_MS });
    const match = stdout.trim().match(/github\.com[/:]([A-Za-z0-9][A-Za-z0-9-]*)\/([A-Za-z0-9_.-]+?)(?:\.git)?\/?$/);
    if (match) return { nameWithOwner: `${match[1]}/${match[2]}` };
  } catch { /* No repository. */ }
  return null;
}

function readRecord(fs, file) {
  try {
    const record = JSON.parse(fs.readFileSync(file, 'utf8'));
    return record?.v === 1 && object(record.incidents) && Array.isArray(record.log) ? record : null;
  } catch { return null; }
}

const more = issues => (issues.length > ISSUE_LIMIT ? ` and ${issues.length - ISSUE_LIMIT} more` : '');
const issueLine = (repo, issues) => `${issues.length === 1 ? 'Issue' : 'Issues'}: ${issues.slice(0, ISSUE_LIMIT).map(n => `https://github.com/${repo}/issues/${n}`).join(', ')}${more(issues)}`;
const issueTags = issues => `${issues.slice(0, ISSUE_LIMIT).map(n => `#${n}`).join(', ')}${more(issues)}`;
const issuesOf = item => (Array.isArray(item?.issues) ? item.issues.filter(Number.isInteger) : []);

function alertText(heading, { kinds, host, repo, issues, fields }) {
  const lines = [`PDD Autopilot ${heading}: ${kinds.join(', ')} (${host})`, `Repository: ${repo}`, issueLine(repo, issues)];
  if (heading === 'recovered') lines.push(`What changed: ${clip(fields.cause, FIELD_LIMIT)}`);
  else lines.push(`Cause: ${clip(fields.cause, FIELD_LIMIT)}`, `Tried: ${clip(fields.tried, FIELD_LIMIT)}`, `Needs: ${clip(fields.need, FIELD_LIMIT)}`, 'Answer on the GitHub issue.');
  return clip(lines.join('\n'), TEXT_LIMIT);
}

function outcomeMessage(what, label, outcome, confirmer) {
  if (outcome.result === 'delivered') return `${what} sent for ${label}; ${confirmer} confirmed it.`;
  if (outcome.result === 'not-configured') return `${what} recorded on this machine for ${label}; no alert destination is set (pdd autopilot alerts set). Continue other work.`;
  const again = outcome.result === 'unconfirmed' ? ' It may have arrived, so it is not sent again.' : '';
  return `${what} recorded for ${label}; delivery ${outcome.result} (${outcome.detail}).${again} pdd autopilot status shows it. Continue other work.`;
}

async function sendAlert(input, ports, env, fs) {
  const issue = String(input.issue ?? '');
  if (!/^[1-9][0-9]{0,9}$/.test(issue)) return done(2, 'Use pdd autopilot alert --issue N with a positive issue number.');
  if (!ALERT_KINDS.includes(input.kind)) return done(2, `Use --kind ${ALERT_KINDS.join('|')}.`);
  const recovery = input.kind === 'recovered', names = recovery ? ['cause'] : ['cause', 'tried', 'need'];
  let fields;
  try { fields = JSON.parse(String(input.text ?? '')); } catch { /* Checked below. */ }
  if (!object(fields) || names.some(name => typeof fields[name] !== 'string' || !fields[name].trim()))
    return done(2, `Give a JSON object on stdin with nonblank ${names.map(name => `"${name}"`).join(', ')}. Nothing was recorded.`);
  // A recovery may name the one kind that ended; without it, every open incident of the issue ends.
  const target = recovery ? fields.kind : undefined;
  if (target !== undefined && (target === 'recovered' || !ALERT_KINDS.includes(target)))
    return done(2, `Give "kind" in a recovery as one of ${ALERT_KINDS.filter(kind => kind !== 'recovered').join('|')}, or leave it out. Nothing was recorded.`);
  const clean = Object.fromEntries(names.map(name => [name, fields[name].trim()]));
  if (!ports.stateRoot && !homeFolder(env, ports)) return noHome('Nothing was recorded or sent. Continue other work.');
  let repo;
  try { repo = (await (ports.repository ?? nativeRepository)({ cwd: input.cwd }))?.nameWithOwner; } catch { /* Checked below. */ }
  if (!repoName(repo)) return done(1, 'Autopilot alerts need a GitHub repository; run pdd autopilot alert in its checkout.');
  const file = recordFile(repo, env, ports), record = readRecord(fs, file) ?? { v: 1, repo, incidents: {}, log: [] };
  const at = new Date((ports.now ?? Date.now)()).toISOString(), host = machineName(fs, stateRoot(env, ports), repo, ports, input.cwd);
  const destination = readDestination(fs, env, ports), number = Number(issue);
  const confirmer = destination?.service === 'discord-bot' ? 'the Discord bot readback' : 'the webhook';
  const send = text => destination ? deliver(destination, text, ports, input.cwd) : { result: 'not-configured' };
  const log = (kind, action, outcome) => {
    record.log = [...record.log, { at, issue: number, kind, action, result: outcome.result, ...(outcome.detail ? { detail: outcome.detail } : {}) }].slice(-LOG_LIMIT);
  };
  const save = () => { try { writePrivate(fs, file, record); return true; } catch { return false; } };
  const unsaved = done(1, 'Cannot save the Autopilot alert record on this machine.');
  const machineKey = kind => `${kind}@${host}`;
  if (recovery) {
    // A machine incident of this host matches when it lists the issue, or when the recovery names its kind.
    const matches = (key, item) => object(item) && (target === undefined || item.kind === target) && (MACHINE_KINDS.includes(item.kind)
      ? key === machineKey(item.kind) && (target !== undefined || issuesOf(item).includes(number))
      : key === `${issue}:${item.kind}`);
    const keys = Object.keys(record.incidents).filter(key => matches(key, record.incidents[key]));
    if (!keys.length) {
      log(target ?? 'recovered', 'recovered', { result: 'not-sent' });
      return save() ? done(0, `No open alert ${target ? `of kind ${target} ` : ''}for #${issue}; nothing sent.`) : unsaved;
    }
    const kinds = keys.map(key => record.incidents[key].kind);
    const issues = [...new Set(keys.flatMap(key => issuesOf(record.incidents[key])))].sort((a, b) => a - b);
    const outcome = await send(alertText('recovered', { kinds, host, repo, issues: issues.length ? issues : [number], fields: clean }));
    for (const key of keys) delete record.incidents[key];
    log(kinds.join(','), 'recovered', outcome);
    return save() ? done(0, outcomeMessage('Recovery', `${kinds.join(', ')} (${issueTags(issues.length ? issues : [number])})`, outcome, confirmer)) : unsaved;
  }
  const machine = MACHINE_KINDS.includes(input.kind), key = machine ? machineKey(input.kind) : `${issue}:${input.kind}`;
  const open = object(record.incidents[key]) ? record.incidents[key] : null;
  const known = issuesOf(open), issues = [...new Set([...known, number])].sort((a, b) => a - b), listed = Array.isArray(open?.listed) ? open.listed : [];
  // A material change is new field text or an affected issue that no sent message has named yet.
  const changed = open && (names.some(name => open.fields?.[name] !== clean[name]) || issues.some(item => !listed.includes(item)));
  const action = !open ? 'alert' : input.update && changed ? 'update' : ['failed', 'not-configured'].includes(open.result) && destination ? 'retry' : 'repeat';
  const label = `${issueTags(issues)} ${input.kind}`;
  if (action === 'repeat') {
    const joined = !known.includes(number);
    if (joined) record.incidents[key] = { ...open, issues, updatedAt: at };
    log(input.kind, 'repeat', { result: 'not-sent' });
    if (!save()) return unsaved;
    return done(0, joined ? `Added #${issue} to the open ${input.kind} alert on this machine; nothing sent. Use --update to send the new issue list.`
      : `Alert for ${label} is already open; nothing sent. Use --update only for a material change.`);
  }
  const outcome = await send(alertText(action === 'update' ? 'update' : 'alert', { kinds: [input.kind], host, repo, issues, fields: clean }));
  record.incidents[key] = { kind: input.kind, issues, listed: issues, fields: clean, openedAt: open?.openedAt ?? at, updatedAt: at,
    result: outcome.result, ...(outcome.detail ? { detail: outcome.detail } : {}) };
  log(input.kind, action, outcome);
  return save() ? done(0, outcomeMessage(action === 'update' ? 'Update' : 'Alert', label, outcome, confirmer)) : unsaved;
}

export async function runAutopilotAlerts(input = {}, ports = {}) {
  const env = input.env ?? process.env, fs = ports.fs ?? nativeFs;
  try {
    if (input.action === 'alert') return await sendAlert(input, ports, env, fs);
    if (input.action === 'set' && (input.discordChannel !== undefined || input.tokenCommand !== undefined)) {
      const channel = String(input.discordChannel ?? ''), command = input.tokenCommand;
      if (!SNOWFLAKE.test(channel)) return done(2, 'Use --discord-channel with a Discord channel ID of 17 to 20 digits; --token-command needs it too. Nothing was saved.');
      if (command !== undefined && (typeof command !== 'string' || !command.trim() || command.length > 2000)) return done(2, 'Give --token-command one nonblank command. Nothing was saved.');
      const token = command === undefined ? String(input.text ?? '').trim() : undefined;
      if (command === undefined && !BOT_TOKEN.test(token)) return done(2, 'Give the Discord bot token on stdin, or use --token-command. Nothing was saved.');
      const file = configFile(env, ports);
      if (!file) return noHome('Nothing was saved.');
      try { writePrivate(fs, file, { v: 1, service: 'discord-bot', channel, ...(command === undefined ? { token } : { tokenCommand: command }) }); }
      catch { return done(1, 'Cannot save the alert destination; nothing was changed.'); }
      return done(0, command === undefined
        ? `Saved a Discord bot for channel ${channel} on this machine; the token is readable only by you. Run pdd autopilot alerts test.`
        : `Saved a Discord bot for channel ${channel} on this machine; pdd runs your token command at each send and stores no token. Run pdd autopilot alerts test.`);
    }
    if (input.action === 'set') {
      const parsed = webhook(input.text);
      if (!parsed) return done(2, 'Give one Discord or Slack incoming webhook URL (https) on stdin. Nothing was saved.');
      const file = configFile(env, ports);
      if (!file) return noHome('Nothing was saved.');
      try { writePrivate(fs, file, { v: 1, service: parsed.service, url: parsed.url }); }
      catch { return done(1, 'Cannot save the alert destination; nothing was changed.'); }
      return done(0, `Saved a ${SERVICE[parsed.service]} webhook for Autopilot alerts on this machine. Run pdd autopilot alerts test to send a test message.`);
    }
    if (input.action === 'test') {
      if (!configFile(env, ports)) return noHome('Nothing was sent.');
      const destination = readDestination(fs, env, ports);
      if (!destination) return done(1, 'No alert destination is set on this machine. Run pdd autopilot alerts set.');
      const text = `PDD Autopilot test alert (${hostName(ports)}).`, delivered = () => recordTest(fs, env, ports);
      if (destination.service === 'discord-bot') return await testBot(destination, text, input, ports, delivered);
      const outcome = await deliver(destination, text, ports, input.cwd), service = SERVICE[destination.service];
      if (outcome.result === 'delivered') { delivered(); return done(0, `Test alert delivered; ${service} confirmed the message.`); }
      if (outcome.result === 'failed') return done(1, `Test alert failed (${outcome.detail}). Check the ${service} webhook, then run pdd autopilot alerts set again.`);
      return done(1, `Test alert unconfirmed (${outcome.detail}). Look in the ${service} channel before you test again.`);
    }
    if (input.action === 'clear') {
      const file = configFile(env, ports);
      if (!file) return noHome('Nothing was removed.');
      try { fs.unlinkSync(file); }
      catch (error) {
        if (error?.code === 'ENOENT') return done(0, 'No alert destination was set on this machine.');
        return done(1, 'Cannot remove the alert destination.');
      }
      return done(0, 'Removed the Autopilot alert destination from this machine.');
    }
    return done(2, 'Use pdd autopilot alerts set|test|clear or pdd autopilot alert.');
  } catch { return done(1, 'The Autopilot alert command failed; nothing was printed about the webhook.'); }
}

// A delivered test is the newest send of each existing record, so status drops an older failed send (such as a closed recovery).
function recordTest(fs, env, ports) {
  const root = stateRoot(env, ports), at = new Date((ports.now ?? Date.now)()).toISOString();
  if (!root) return;
  let names = [];
  try { names = fs.readdirSync(join(root, 'alerts')).filter(name => STATE_FILE.test(name)); } catch { return; }
  for (const name of names) {
    const file = join(root, 'alerts', name), record = readRecord(fs, file);
    if (!record) continue;
    record.log = [...record.log, { at, kind: 'test', action: 'test', result: 'delivered' }].slice(-LOG_LIMIT);
    try { writePrivate(fs, file, record); } catch { /* The test message was still delivered. */ }
  }
}

// Read-only identity and channel checks first, then one test message with readback.
async function testBot(destination, text, input, ports, delivered) {
  const auth = await botToken(destination, ports, input.cwd);
  if (auth.error) return done(1, `Test alert not sent: the ${auth.error}. Its output is not shown.`);
  const me = await botGet(ports, auth.token, '/users/@me');
  if (!me.value) return done(1, `Discord bot check failed (${me.detail}); check the token. Nothing was sent.`);
  const channel = await botGet(ports, auth.token, `/channels/${destination.channel}`);
  const bot = clip(oneLine(me.value.username ?? 'unknown'), 100);
  if (!channel.value) return done(1, `Discord bot ${bot} cannot read channel ${destination.channel} (${channel.detail}). Nothing was sent.`);
  const where = `Discord bot ${bot} in #${clip(oneLine(channel.value.name ?? destination.channel), 100)}`;
  const outcome = await botSend(destination, auth.token, text, ports);
  if (outcome.result === 'delivered') { delivered(); return done(0, `Test alert delivered; ${where} posted it and the readback matched.`); }
  return done(1, `Test alert ${outcome.result} (${outcome.detail}) for ${where}.`);
}

// One short line for pdd autopilot status, from local files only; empty when nothing needs the person.
export function alertStatusLine({ repo, env = process.env } = {}, ports = {}) {
  try {
    if (!repoName(repo)) return '';
    const fs = ports.fs ?? nativeFs, file = recordFile(repo, env, ports), record = file && readRecord(fs, file);
    if (!record) return '';
    const open = Object.values(record.incidents).filter(item => object(item) && item.result !== 'delivered');
    const last = [...record.log].reverse().find(row => SENDS.includes(row?.result));
    const failed = last && last.result !== 'delivered' ? last : null;
    if (!open.length && !failed) return '';
    const parts = [];
    if (open.length) parts.push(`${open.length} open alert${open.length === 1 ? '' : 's'} not delivered`);
    if (failed) parts.push(`last delivery ${failed.result}${failed.detail ? ` (${failed.detail})` : ''} for #${failed.issue} ${failed.kind} at ${failed.at}`);
    const hint = readDestination(fs, env, ports) ? 'check with pdd autopilot alerts test' : 'set one with pdd autopilot alerts set';
    return scrub(oneLine(`Alerts: ${parts.join('; ')}; ${hint}.`));
  } catch { return ''; }
}
