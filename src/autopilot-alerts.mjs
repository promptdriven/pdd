// Generated from prompts/cli/autopilot-alerts.prompt.md (sha256: 568211909a50a5e6dacdcae1fdb1982e289898070745e7f419419688851cc898).
import * as nativeFs from 'node:fs';
import { createHash, randomUUID } from 'node:crypto';
import { execFile } from 'node:child_process';
import { homedir, hostname as osHostname } from 'node:os';
import { dirname, isAbsolute, join } from 'node:path';
import { promisify } from 'node:util';

const execute = promisify(execFile);
export const ALERT_KINDS = Object.freeze(['usage-limit', 'resource', 'access', 'decision', 'stuck', 'recovered']);
const LOG_LIMIT = 200, TEXT_LIMIT = 1900, FIELD_LIMIT = 500, TIMEOUT_MS = 10000, TOKEN_COMMAND_MS = 30000;
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
const home = env => (isAbsolute(env.HOME ?? '') ? env.HOME : homedir());

const configFile = env => join(isAbsolute(env.XDG_CONFIG_HOME ?? '') ? env.XDG_CONFIG_HOME : join(home(env), '.config'), 'pdd', 'autopilot-alerts.json');
const recordFile = (repo, env, ports) => join(ports.stateRoot ?? join(home(env), '.local', 'state', 'pdd', 'autopilot'), 'alerts',
  `${createHash('sha256').update(repo.toLowerCase()).digest('hex').slice(0, 20)}.json`);

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
function readDestination(fs, env) {
  const file = configFile(env);
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
  return back.value.id === posted.id && typeof back.value.content === 'string' && back.value.content.trim() === text.trim()
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
  return typeof message?.id === 'string' && typeof message.content === 'string' && message.content.trim() === text.trim()
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

function alertText(heading, { kinds, host, repo, issue, fields }) {
  const lines = [`PDD Autopilot ${heading}: ${kinds.join(', ')} (${host})`, `Repository: ${repo}`, `Issue: https://github.com/${repo}/issues/${issue}`];
  if (heading === 'recovered') lines.push(`What changed: ${clip(fields.cause, FIELD_LIMIT)}`);
  else lines.push(`Cause: ${clip(fields.cause, FIELD_LIMIT)}`, `Tried: ${clip(fields.tried, FIELD_LIMIT)}`, `Needs: ${clip(fields.need, FIELD_LIMIT)}`, 'Answer on the GitHub issue.');
  return clip(lines.join('\n'), TEXT_LIMIT);
}

function outcomeMessage(what, label, outcome) {
  if (outcome.result === 'delivered') return `${what} sent for ${label}; the webhook confirmed it.`;
  if (outcome.result === 'not-configured') return `${what} recorded on this machine for ${label}; no alert destination is set (pdd autopilot alerts set). Continue other work.`;
  const again = outcome.result === 'unconfirmed' ? ' It may have arrived, so it is not sent again.' : '';
  return `${what} recorded for ${label}; delivery ${outcome.result} (${outcome.detail}).${again} pdd autopilot status shows it. Continue other work.`;
}

async function sendAlert(input, ports, env, fs) {
  const issue = String(input.issue ?? '');
  if (!/^[1-9][0-9]{0,9}$/.test(issue)) return done(2, 'Use pdd autopilot alert --issue N with a positive issue number.');
  if (!ALERT_KINDS.includes(input.kind)) return done(2, `Use --kind ${ALERT_KINDS.join('|')}.`);
  const names = input.kind === 'recovered' ? ['cause'] : ['cause', 'tried', 'need'];
  let fields;
  try { fields = JSON.parse(String(input.text ?? '')); } catch { /* Checked below. */ }
  if (!object(fields) || names.some(name => typeof fields[name] !== 'string' || !fields[name].trim()))
    return done(2, `Give a JSON object on stdin with nonblank ${names.map(name => `"${name}"`).join(', ')}. Nothing was recorded.`);
  const clean = Object.fromEntries(names.map(name => [name, fields[name].trim()]));
  let repo;
  try { repo = (await (ports.repository ?? nativeRepository)({ cwd: input.cwd }))?.nameWithOwner; } catch { /* Checked below. */ }
  if (!repoName(repo)) return done(1, 'Autopilot alerts need a GitHub repository; run pdd autopilot alert in its checkout.');
  const file = recordFile(repo, env, ports), record = readRecord(fs, file) ?? { v: 1, repo, incidents: {}, log: [] };
  const at = new Date((ports.now ?? Date.now)()).toISOString(), host = oneLine((ports.hostname ?? osHostname)()) || 'unknown host';
  const destination = readDestination(fs, env), number = Number(issue);
  const send = text => destination ? deliver(destination, text, ports, input.cwd) : { result: 'not-configured' };
  const log = (kind, action, outcome) => {
    record.log = [...record.log, { at, issue: number, kind, action, result: outcome.result, ...(outcome.detail ? { detail: outcome.detail } : {}) }].slice(-LOG_LIMIT);
  };
  const save = () => { try { writePrivate(fs, file, record); return true; } catch { return false; } };
  const unsaved = done(1, 'Cannot save the Autopilot alert record on this machine.');
  if (input.kind === 'recovered') {
    const keys = Object.keys(record.incidents).filter(key => record.incidents[key]?.issue === number);
    if (!keys.length) {
      log('recovered', 'recovered', { result: 'not-sent' });
      return save() ? done(0, `No open alert for #${issue}; nothing sent.`) : unsaved;
    }
    const kinds = keys.map(key => record.incidents[key].kind);
    const outcome = await send(alertText('recovered', { kinds, host, repo, issue, fields: clean }));
    for (const key of keys) delete record.incidents[key];
    log(kinds.join(','), 'recovered', outcome);
    return save() ? done(0, outcomeMessage('Recovery', `#${issue} ${kinds.join(', ')}`, outcome)) : unsaved;
  }
  const key = `${issue}:${input.kind}`, open = object(record.incidents[key]) ? record.incidents[key] : null, label = `#${issue} ${input.kind}`;
  const changed = open && names.some(name => open.fields?.[name] !== clean[name]);
  const action = !open ? 'alert' : input.update && changed ? 'update' : ['failed', 'not-configured'].includes(open.result) && destination ? 'retry' : 'repeat';
  if (action === 'repeat') {
    log(input.kind, 'repeat', { result: 'not-sent' });
    return save() ? done(0, `Alert for ${label} is already open; nothing sent. Use --update only for a material change.`) : unsaved;
  }
  const outcome = await send(alertText(action === 'update' ? 'update' : 'alert', { kinds: [input.kind], host, repo, issue, fields: clean }));
  record.incidents[key] = { issue: number, kind: input.kind, fields: clean, openedAt: open?.openedAt ?? at, updatedAt: at,
    result: outcome.result, ...(outcome.detail ? { detail: outcome.detail } : {}) };
  log(input.kind, action, outcome);
  return save() ? done(0, outcomeMessage(action === 'update' ? 'Update' : 'Alert', label, outcome)) : unsaved;
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
      try { writePrivate(fs, configFile(env), { v: 1, service: 'discord-bot', channel, ...(command === undefined ? { token } : { tokenCommand: command }) }); }
      catch { return done(1, 'Cannot save the alert destination; nothing was changed.'); }
      return done(0, command === undefined
        ? `Saved a Discord bot for channel ${channel} on this machine; the token is readable only by you. Run pdd autopilot alerts test.`
        : `Saved a Discord bot for channel ${channel} on this machine; pdd runs your token command at each send and stores no token. Run pdd autopilot alerts test.`);
    }
    if (input.action === 'set') {
      const parsed = webhook(input.text);
      if (!parsed) return done(2, 'Give one Discord or Slack incoming webhook URL (https) on stdin. Nothing was saved.');
      try { writePrivate(fs, configFile(env), { v: 1, service: parsed.service, url: parsed.url }); }
      catch { return done(1, 'Cannot save the alert destination; nothing was changed.'); }
      return done(0, `Saved a ${SERVICE[parsed.service]} webhook for Autopilot alerts on this machine. Run pdd autopilot alerts test to send a test message.`);
    }
    if (input.action === 'test') {
      const destination = readDestination(fs, env);
      if (!destination) return done(1, 'No alert destination is set on this machine. Run pdd autopilot alerts set.');
      const host = oneLine((ports.hostname ?? osHostname)()) || 'unknown host', text = `PDD Autopilot test alert (${host}).`;
      if (destination.service === 'discord-bot') return await testBot(destination, text, input, ports);
      const outcome = await deliver(destination, text, ports, input.cwd), service = SERVICE[destination.service];
      if (outcome.result === 'delivered') return done(0, `Test alert delivered; ${service} confirmed the message.`);
      if (outcome.result === 'failed') return done(1, `Test alert failed (${outcome.detail}). Check the ${service} webhook, then run pdd autopilot alerts set again.`);
      return done(1, `Test alert unconfirmed (${outcome.detail}). Look in the ${service} channel before you test again.`);
    }
    if (input.action === 'clear') {
      try { fs.unlinkSync(configFile(env)); }
      catch (error) {
        if (error?.code === 'ENOENT') return done(0, 'No alert destination was set on this machine.');
        return done(1, 'Cannot remove the alert destination.');
      }
      return done(0, 'Removed the Autopilot alert destination from this machine.');
    }
    return done(2, 'Use pdd autopilot alerts set|test|clear or pdd autopilot alert.');
  } catch { return done(1, 'The Autopilot alert command failed; nothing was printed about the webhook.'); }
}

// Read-only identity and channel checks first, then one test message with readback.
async function testBot(destination, text, input, ports) {
  const auth = await botToken(destination, ports, input.cwd);
  if (auth.error) return done(1, `Test alert not sent: the ${auth.error}. Its output is not shown.`);
  const me = await botGet(ports, auth.token, '/users/@me');
  if (!me.value) return done(1, `Discord bot check failed (${me.detail}); check the token. Nothing was sent.`);
  const channel = await botGet(ports, auth.token, `/channels/${destination.channel}`);
  const bot = clip(oneLine(me.value.username ?? 'unknown'), 100);
  if (!channel.value) return done(1, `Discord bot ${bot} cannot read channel ${destination.channel} (${channel.detail}). Nothing was sent.`);
  const where = `Discord bot ${bot} in #${clip(oneLine(channel.value.name ?? destination.channel), 100)}`;
  const outcome = await botSend(destination, auth.token, text, ports);
  if (outcome.result === 'delivered') return done(0, `Test alert delivered; ${where} posted it and the readback matched.`);
  return done(1, `Test alert ${outcome.result} (${outcome.detail}) for ${where}.`);
}

// One short line for pdd autopilot status, from local files only; empty when nothing needs the person.
export function alertStatusLine({ repo, env = process.env } = {}, ports = {}) {
  try {
    if (!repoName(repo)) return '';
    const fs = ports.fs ?? nativeFs, record = readRecord(fs, recordFile(repo, env, ports));
    if (!record) return '';
    const open = Object.values(record.incidents).filter(item => object(item) && item.result !== 'delivered');
    const last = [...record.log].reverse().find(row => SENDS.includes(row?.result));
    const failed = last && last.result !== 'delivered' ? last : null;
    if (!open.length && !failed) return '';
    const parts = [];
    if (open.length) parts.push(`${open.length} open alert${open.length === 1 ? '' : 's'} not delivered`);
    if (failed) parts.push(`last delivery ${failed.result}${failed.detail ? ` (${failed.detail})` : ''} for #${failed.issue} ${failed.kind} at ${failed.at}`);
    const hint = readDestination(fs, env) ? 'check with pdd autopilot alerts test' : 'set one with pdd autopilot alerts set';
    return scrub(oneLine(`Alerts: ${parts.join('; ')}; ${hint}.`));
  } catch { return ''; }
}
