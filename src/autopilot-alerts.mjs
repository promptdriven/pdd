// Generated from prompts/cli/autopilot-alerts.prompt.md (sha256: d5de328f806f799d37278a5525ca4684215f9e0d38ad6b5152692df076525c67).
import * as nativeFs from 'node:fs';
import { createHash, randomUUID } from 'node:crypto';
import { execFile } from 'node:child_process';
import { hostname as osHostname, userInfo } from 'node:os';
import { dirname, isAbsolute, join } from 'node:path';
import { promisify } from 'node:util';
import { setTimeout as sleep } from 'node:timers/promises';
import { acquireRunLock } from './workflow-runner.mjs';

const execute = promisify(execFile);
export const ALERT_KINDS = Object.freeze(['usage-limit', 'resource', 'interpreter', 'interpreter-access', 'access', 'decision', 'stuck', 'test-suite', 'long-running', 'recovered']);
// These incidents are shared by the whole machine: one incident per repository, machine and kind lists every affected issue.
// An interpreter outage is one of them: the hosted PDD interpreter is down for every issue at once. So is interpreter-access:
// the interpreter health check of this machine cannot be read (its gh sign-in or PDD_RUNTIME_URL).
// An access or spending decision belongs to its issue, like a product decision.
const MACHINE_KINDS = Object.freeze(['usage-limit', 'resource', 'interpreter', 'interpreter-access']);
const LOG_LIMIT = 200, TEXT_LIMIT = 1900, ISSUE_LIMIT = 10, TIMEOUT_MS = 10000, TOKEN_COMMAND_MS = 30000;
const SERVICE = { discord: 'Discord', slack: 'Slack', 'discord-bot': 'Discord bot' };
const DISCORD_API = 'https://discord.com/api/v10';
const SNOWFLAKE = /^[0-9]{17,20}$/, BOT_TOKEN = /^[A-Za-z0-9._-]{20,256}$/;
const VERSION = (() => { try { return JSON.parse(nativeFs.readFileSync(new URL('../package.json', import.meta.url), 'utf8')).version || '0'; } catch { return '0'; } })();
const USER_AGENT = `PDD-Autopilot/${VERSION}`;
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
const configFile = (env, ports, destination = 'autopilot') => {
  const name = destination === 'infrastructure' ? 'autopilot-infrastructure-alerts.json' : 'autopilot-alerts.json';
  if (isAbsolute(env.XDG_CONFIG_HOME ?? '')) return join(env.XDG_CONFIG_HOME, 'pdd', name);
  const home = homeFolder(env, ports);
  return home ? join(home, '.config', 'pdd', name) : null;
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
function readDestination(fs, env, ports, destination = 'autopilot') {
  const file = configFile(env, ports, destination);
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
const issueLine = (repo, issues) => `${issues.length === 1 ? 'Issue' : 'Issues'}: ${issues.map(n => `https://github.com/${repo}/issues/${n}`).join(', ')}`;
const issueTags = issues => `${issues.slice(0, ISSUE_LIMIT).map(n => `#${n}`).join(', ')}${more(issues)}`;
const issuesOf = item => (Array.isArray(item?.issues) ? item.issues.filter(Number.isInteger) : []);

const MINUTE = 60000, HOUR = 60 * MINUTE, DAY = 24 * HOUR;
const CODE = /^[a-z0-9][a-z0-9_.:/-]{0,159}$/;
const PERSON_KINDS = ['decision', 'access'];
const issueIdentity = (repo, issue) => `${repo.toLowerCase()}:${issue}`;
const askIdentity = fields => JSON.stringify([fields.need, fields.owner ?? '']);
function clearAsk(need) {
  if (typeof need !== 'string' || !need.trim() || /[\r\n]/.test(need)) return false;
  const text = need.trim();
  if (/\bfyi\b|nothing to do|no human intervention|informational|no\s+(?:further\s+)?action|no\s+(?:(?:operator|human|person)\s+)?action|no\s+(?:action|operator|human)\s+(?:is\s+)?needed|no named blocker|identify the blocker/i.test(text)) return false;
  if (/(?:\b(?:and|then|also)\s+|[;,:—–]\s*|\s+-\s+)(?:(?:please|you)\s+)*(?:approve|choose|grant|provide|supply|sign|release|review|restore|renew|increase|allow|run|merge|resend|retry|pay|spend|pdd|gh|git)\b/i.test(text)) return false;
  if (/[.!]\s+\S/.test(text)) return false;
  const questions = (text.match(/\?/g) ?? []).length;
  return questions === 1 ? text.endsWith('?') && /\p{L}{2}/u.test(text) : questions === 0 &&
    /^(approve|choose|grant|provide|supply|sign|release|review|restore|renew|increase|allow|run)\b/i.test(text) &&
    !/[.!]\s+\S/.test(text);
}
function askText(kind, repo, issues, fields) {
  const need = scrub(fields.need);
  const lines = [`PDD Autopilot needs you: ${kind}`, issueLine(repo, issues), `Ask: ${need}`,
    `Tried: ${clip(scrub(oneLine(fields.tried)), 80)}`, `If no answer: ${clip(scrub(oneLine(fields.ifNoAnswer)), 80)}`];
  for (const [label, value] of [['Owner', fields.owner], ['Details', fields.details]]) {
    if (!value) continue;
    const line = `${label}: ${scrub(oneLine(value))}`;
    if ([...lines, line].join('\n').length <= 480) lines.push(line);
  }
  const text = lines.join('\n');
  return text.length <= 480 ? text : null;
}
function destinationIdentity(destination) {
  return createHash('sha256').update(`${destination.service}:${destination.channel ?? destination.url}`).digest('hex');
}
function readDelivery(fs, file) {
  let text;
  try { text = fs.readFileSync(file, 'utf8'); }
  catch (error) { if (error.code === 'ENOENT') return null; throw error; }
  const value = JSON.parse(text);
  if (value?.v !== 1 || !Array.isArray(value.sends) || !['issueSentAt','recoveredAt','digests','attention'].every(k => object(value[k])))
    throw Error('invalid delivery history');
  return value;
}
// Import only durable observations, never infer an old send from current prose.
function legacyDelivery(fs, directory, env, ports) {
  const history = {v:1, sends:[], issueSentAt:{}, recoveredAt:{}, digests:{}, attention:{}};
  const destination = readDestination(fs, env, ports), channel = destination && destinationIdentity(destination);
  const latest = (map, key, at) => { map[key] = Math.max(map[key] ?? -Infinity, at); };
  for (const name of fs.readdirSync(directory).filter(name => STATE_FILE.test(name))) {
    const saved = readRecord(fs, join(directory, name));
    if (!saved || !repoName(saved.repo)) continue;
    const host = machineName(fs, stateRoot(env, ports), saved.repo, ports);
    for (const row of saved.log) {
      const at = Date.parse(row?.at);
      if (!Number.isFinite(at) || row.action === 'test') continue;
      const identities = Number.isSafeInteger(row.issue) && row.issue > 0 ? [issueIdentity(saved.repo, row.issue)] : [];
      if (row.action === 'recovered') for (const id of identities) latest(history.recoveredAt, id, at);
      if (!SENDS.includes(row.result)) continue;
      for (const id of identities) latest(history.issueSentAt, id, at);
      history.sends.push({at, host:row.host ?? host, destination:channel, issues:identities});
      if (row.kind === 'digest' && channel && at > (history.digests[channel]?.at ?? -Infinity))
        history.digests[channel] = {at, result:row.result};
    }
  }
  return history;
}
// Reserve before I/O, under the shared lock. Failed and uncertain sends consume budgets too.
async function budgetedSend(destination, text, identities, context) {
  const {fs, history, historyFile, host, now, ports, cwd} = context;
  if (!destination) return {result:'not-configured'};
  history.sends = history.sends.filter(row => now - row.at < HOUR);
  if (history.sends.filter(row => row.host === host).length >= 6 ||
      identities.some(id => history.issueSentAt[id] !== undefined && now - history.issueSentAt[id] < DAY) ||
      !context.recovery && identities.some(id => history.recoveredAt[id] !== undefined && now - history.recoveredAt[id] < 2 * HOUR)) return {result:'not-sent'};
  history.sends.push({at:now, host, destination:destinationIdentity(destination), issues:identities});
  for (const id of identities) history.issueSentAt[id] = now;
  writePrivate(fs, historyFile, history);
  return deliver(destination, scrub(text), ports, cwd);
}

function outcomeMessage(what, label, outcome, confirmer) {
  if (outcome.result === 'delivered') return `${what} sent for ${label}; ${confirmer} confirmed it.`;
  if (outcome.result === 'not-configured') return `${what} recorded on this machine for ${label}; no alert destination is set (pdd autopilot alerts set). Continue other work.`;
  const again = outcome.result === 'unconfirmed' ? ' It may have arrived, so it is not sent again.' : '';
  return `${what} recorded for ${label}; delivery ${outcome.result} (${outcome.detail}).${again} pdd autopilot status shows it. Continue other work.`;
}

// Hold custody through delivery and atomic saves. Checkouts and repositories share one state-root lock.
async function withRecord(repo, env, ports, fs, action) {
  const file = recordFile(repo, env, ports);
  fs.mkdirSync(dirname(file), { recursive: true, mode: 0o700 });
  let release;
  for (let attempt = 0; attempt <= 1500; attempt++) {
    try { release = (ports.recordLock ?? acquireRunLock)(dirname(file), 'delivery.lock'); break; }
    catch (error) {
      if (error.code !== 'run_busy' || attempt === 1500) return done(1, 'Autopilot alert record is busy or unavailable; nothing sent.');
      await (ports.sleep ?? sleep)(20);
    }
  }
  try {
    const historyFile = join(dirname(file), 'delivery.json');
    return await action(file, readRecord(fs, file) ?? { v: 1, repo, incidents: {}, log: [] }, readDelivery(fs, historyFile) ?? legacyDelivery(fs, dirname(file), env, ports), historyFile);
  }
  finally { release(); }
}
const destinationFor = (fs, env, ports, kind) => MACHINE_KINDS.includes(kind)
  ? readDestination(fs, env, ports, 'infrastructure') ?? readDestination(fs, env, ports)
  : readDestination(fs, env, ports);

async function sendAlert(input, ports, env, fs) {
  const issue = String(input.issue ?? '');
  if (!/^[1-9][0-9]{0,9}$/.test(issue)) return done(2, 'Use pdd autopilot alert --issue N with a positive issue number.');
  if (!ALERT_KINDS.includes(input.kind)) return done(2, `Use --kind ${ALERT_KINDS.join('|')}.`);
  const recovery = input.kind === 'recovered', names = recovery ? ['cause'] : ['cause', 'tried', 'need'];
  let fields;
  try { fields = JSON.parse(String(input.text ?? '')); } catch { /* Checked below. */ }
  if (!object(fields) || names.some(name => typeof fields[name] !== 'string' || !fields[name].trim()))
    return done(2, `Give a JSON object on stdin with nonblank ${names.map(name => `"${name}"`).join(', ')}. Nothing was recorded.`);
  const target = recovery ? fields.kind : undefined;
  if (target !== undefined && (target === 'recovered' || !ALERT_KINDS.includes(target)))
    return done(2, `Give "kind" in a recovery as one of ${ALERT_KINDS.filter(kind => kind !== 'recovered').join('|')}, or leave it out. Nothing was recorded.`);
  const clean = Object.fromEntries(['cause','tried','need','code','ifNoAnswer','owner','details'].filter(k => typeof fields[k] === 'string').map(k => [k, scrub(fields[k].trim())]));
  if (!ports.stateRoot && !homeFolder(env, ports)) return noHome('Nothing was recorded or sent. Continue other work.');
  let repo;
  try { repo = (await (ports.repository ?? nativeRepository)({ cwd: input.cwd }))?.nameWithOwner; } catch { /* Checked below. */ }
  if (!repoName(repo)) return done(1, 'Autopilot alerts need a GitHub repository; run pdd autopilot alert in its checkout.');
  return withRecord(repo, env, ports, fs, async (file, record, history, historyFile) => {
    const now = (ports.now ?? Date.now)(), at = new Date(now).toISOString();
    const host = machineName(fs, stateRoot(env, ports), repo, ports, input.cwd), number = Number(issue);
    const context = {fs, history, historyFile, host, now, ports, cwd:input.cwd};
    const log = (kind, action, outcome, route = {}) => {
      record.log = [...record.log, {at, issue:number, kind, action, ...route, ...outcome}].slice(-LOG_LIMIT);
    };
    const save = () => { writePrivate(fs, historyFile, history); writePrivate(fs, file, record); };
    if (recovery) {
      const matches = Object.entries(record.incidents).filter(([, item]) => object(item) &&
        (!target || item.kind === target) && (!fields.code || item.code === fields.code) &&
        (!MACHINE_KINDS.includes(item.kind) || !item.host || item.host === host) &&
        (issuesOf(item).includes(number) || target && MACHINE_KINDS.includes(item.kind)));
      for (const [key, item] of matches) {
        const issues = issuesOf(item), ids = issues.map(n => issueIdentity(repo, n));
        let outcome = {result:'not-sent'};
        if (item.sentAt && now - Date.parse(item.sentAt) >= 15 * MINUTE &&
            (PERSON_KINDS.includes(item.kind) || MACHINE_KINDS.includes(item.kind))) {
          const text = `PDD Autopilot recovered: ${item.kind}\n${issueLine(repo, issues)}\nWhat changed: ${clip(scrub(oneLine(clean.cause)), 100)}`;
          if (text.length <= 480) outcome = await budgetedSend(destinationFor(fs, env, ports, item.kind), text, ids, {...context, recovery:true});
        }
        for (const id of ids) history.recoveredAt[id] = now;
        delete record.incidents[key];
        log(item.kind, 'recovered', outcome, item.destination ? {destination:item.destination} : {});
      }
      save();
      return done(0, `Recovery recorded for #${issue}; ${matches.length} open incident(s) closed.`);
    }
    const incomingMachine = MACHINE_KINDS.includes(input.kind), code = CODE.test(clean.code ?? '') ? clean.code : null;
    // A classification change on this host joins its existing cause, including legacy keys.
    const causeKeys = code ? Object.keys(record.incidents).filter(key => record.incidents[key]?.code === code) : [];
    const matchingKey = causeKeys.find(key => record.incidents[key].host === host) ??
      (!incomingMachine && causeKeys.find(key => !MACHINE_KINDS.includes(record.incidents[key].kind)));
    const key = matchingKey || (code ? `cause:${code}${incomingMachine ? `@${host}` : ''}` : incomingMachine ? `${input.kind}@${host}` : `${issue}:${input.kind}`);
    const open = object(record.incidents[key]) ? record.incidents[key] : null;
    const eligibleKind = kind => MACHINE_KINDS.includes(kind) || PERSON_KINDS.includes(kind);
    const incomingEligible = eligibleKind(input.kind);
    const kind = eligibleKind(open?.kind) ? open.kind : input.kind, machine = MACHINE_KINDS.includes(kind);
    const issues = [...new Set([...issuesOf(open), number, ...(Array.isArray(fields.issues) ? fields.issues.filter(n => Number.isSafeInteger(n) && n > 0 && n <= 9999999999) : [])])].sort((a,b) => a-b);
    const item = {...open, kind, code, host:open?.host ?? host, issues, listed:open?.listed ?? [], fields:!incomingEligible && eligibleKind(open?.kind) ? open.fields : clean,
      openedAt:open?.openedAt ?? at, updatedAt:at, result:open?.result ?? 'recorded',
      channel: destinationFor(fs, env, ports, kind) ? destinationIdentity(destinationFor(fs, env, ports, kind)) : null};
    if (machine && incomingMachine) {
      if (fields.paused !== true) { item.firstPausedAt = null; item.ticks = 0; item.lastTick = null; }
      else {
        const tick = String(fields.tick ?? now);
        item.firstPausedAt ??= at;
        if (item.lastTick !== tick) { item.ticks = (item.ticks ?? 0) + 1; item.lastTick = tick; }
      }
    }
    record.incidents[key] = item;
    const ids = issues.map(n => issueIdentity(repo, n));
    const hasAsk = clearAsk(fields.need) && Boolean(code && clean.ifNoAnswer);
    const persistent = !machine || item.ticks >= 2 && now - Date.parse(item.firstPausedAt) >= 15 * MINUTE;
    const quiet = ids.some(id => history.recoveredAt[id] !== undefined && now - history.recoveredAt[id] < 2 * HOUR);
    const changed = input.update && open?.asked !== askIdentity(clean);
    const canSend = !open?.asked || changed || ['failed','not-configured'].includes(open?.result);
    const text = hasAsk && askText(kind, repo, issues, clean);
    let outcome = {result:'not-sent'}, action = 'repeat';
    if (incomingEligible && persistent && !quiet && text && canSend) {
      const destination = destinationFor(fs, env, ports, kind);
      outcome = await budgetedSend(destination, text, ids, context);
      if (outcome.result !== 'not-sent') {
        item.result = outcome.result; item.asked = askIdentity(clean); item.listed = issues;
        if (outcome.detail) item.detail = outcome.detail; else delete item.detail;
        if (outcome.result === 'delivered') item.sentAt ??= at;
        if (machine && readDestination(fs, env, ports, 'infrastructure')) item.destination = 'infrastructure';
        action = open?.asked ? changed ? 'update' : 'retry' : 'alert';
      }
    }
    log(input.kind, action, outcome, item.destination ? {destination:item.destination} : {});
    save();
    if (outcome.result === 'not-sent') return done(0, `Alert recorded for ${issueTags(issues)} ${input.kind}; nothing sent (quiet-send rules).`);
    return done(0, outcomeMessage(action === 'update' ? 'Update' : 'Alert', `${issueTags(issues)} ${input.kind}`, outcome,
      destinationFor(fs, env, ports, input.kind)?.service === 'discord-bot' ? 'the Discord bot readback' : 'the webhook'));
  });
}

async function sendDigest(input, ports, env, fs) {
  if (!ports.stateRoot && !homeFolder(env, ports)) return noHome('Nothing was recorded or sent. Continue other work.');
  let repo;
  try { repo = (await (ports.repository ?? nativeRepository)({cwd:input.cwd}))?.nameWithOwner; } catch { /* No repository. */ }
  if (!repoName(repo)) return done(1, 'Autopilot digest needs a GitHub repository.');
  return withRecord(repo, env, ports, fs, async (file, record, history, historyFile) => {
    const now = (ports.now ?? Date.now)(), at = new Date(now).toISOString();
    const host = machineName(fs, stateRoot(env, ports), repo, ports, input.cwd);
    const destination = readDestination(fs, env, ports), channel = destination && destinationIdentity(destination);
    const rows = new Map(), add = (name, number, need) => {
      if (repoName(name) && Number.isSafeInteger(number) && number > 0 && clearAsk(need))
        rows.set(`${name.toLowerCase()}:${number}:${need.trim()}`, {repo:name.toLowerCase(), number, need:need.trim()});
    };
    history.attention[`${repo.toLowerCase()}@${host}`] = (Array.isArray(input.attention) ? input.attention : [])
      .filter(item => PERSON_KINDS.includes(item?.category) && clearAsk(item.need) && Number.isSafeInteger(item.number) && item.number > 0)
      .map(item => ({repo, number:item.number, need:scrub(item.need.trim()), channel}));
    for (const snapshot of Object.values(history.attention)) for (const item of snapshot)
      if (item.channel === channel) add(item.repo, item.number, item.need);
    const names = fs.readdirSync(dirname(file)).filter(name => STATE_FILE.test(name));
    for (const name of names) {
      const saved = readRecord(fs, join(dirname(file), name));
      if (!saved || !repoName(saved.repo)) continue;
      for (const item of Object.values(saved.incidents)) {
        if (!PERSON_KINDS.includes(item?.kind) || !CODE.test(item.code ?? '') || !item.fields?.ifNoAnswer || item.channel !== channel) continue;
        for (const number of issuesOf(item)) add(saved.repo, number, item.fields.need);
      }
    }
    const items = [...rows.values()].sort((a,b) => a.repo.localeCompare(b.repo) || a.number-b.number || a.need.localeCompare(b.need));
    const fingerprint = createHash('sha256').update(JSON.stringify(items)).digest('hex');
    const text = ['PDD Autopilot daily digest', ...items.map(item => `https://github.com/${item.repo}/issues/${item.number} — ${scrub(item.need)}`)].join('\n');
    const last = channel && history.digests[channel];
    if (!items.length || text.length > TEXT_LIMIT || last && (now - last.at < DAY || last.fingerprint === fingerprint)) {
      writePrivate(fs, historyFile, history);
      return done(0, 'Autopilot digest is empty, unchanged or not due; nothing sent.');
    }
    const ids = [...new Set(items.map(item => issueIdentity(item.repo, item.number)))];
    const outcome = await budgetedSend(destination, text, ids, {fs, history, historyFile, host, now, ports, cwd:input.cwd});
    if (channel && !['not-sent','not-configured'].includes(outcome.result)) history.digests[channel] = {at:now, fingerprint, ...outcome};
    record.log = [...record.log, {at, host, kind:'digest', action:'digest', ...outcome}].slice(-LOG_LIMIT);
    writePrivate(fs, historyFile, history); writePrivate(fs, file, record);
    return done(0, outcome.result === 'not-sent' ? 'Digest recorded; message budget reached; nothing sent.' :
      outcomeMessage('Digest', repo, outcome, destination?.service === 'discord-bot' ? 'the Discord bot readback' : 'the webhook'));
  });
}

// Explicit hook for the coordinator/core; workers leave their asks on the issue.
export function notifyAutopilotAsk(input = {}, ports = {}) {
  const {fields, ...rest} = input;
  return runAutopilotAlerts({...rest, action:'alert', text:JSON.stringify(fields)}, ports);
}

export async function runAutopilotAlerts(input = {}, ports = {}) {
  const env = input.env ?? process.env, fs = ports.fs ?? nativeFs;
  const suffix = input.destination === 'infrastructure' ? ' --destination infrastructure' : '';
  const testHint = `pdd autopilot alerts test${suffix}`, setHint = `pdd autopilot alerts set${suffix}`;
  try {
    if (input.destination !== undefined && (!['set', 'test', 'clear'].includes(input.action) || !['autopilot', 'infrastructure'].includes(input.destination)))
      return done(2, 'Use --destination autopilot|infrastructure with alerts set, test or clear.');
    if (input.action === 'digest') return await sendDigest(input, ports, env, fs);
    if (input.action === 'alert') return await sendAlert(input, ports, env, fs);
    if (input.action === 'set' && (input.discordChannel !== undefined || input.tokenCommand !== undefined)) {
      const channel = String(input.discordChannel ?? ''), command = input.tokenCommand;
      if (!SNOWFLAKE.test(channel)) return done(2, 'Use --discord-channel with a Discord channel ID of 17 to 20 digits; --token-command needs it too. Nothing was saved.');
      if (command !== undefined && (typeof command !== 'string' || !command.trim() || command.length > 2000)) return done(2, 'Give --token-command one nonblank command. Nothing was saved.');
      const token = command === undefined ? String(input.text ?? '').trim() : undefined;
      if (command === undefined && !BOT_TOKEN.test(token)) return done(2, 'Give the Discord bot token on stdin, or use --token-command. Nothing was saved.');
      const file = configFile(env, ports, input.destination);
      if (!file) return noHome('Nothing was saved.');
      try { writePrivate(fs, file, { v: 1, service: 'discord-bot', channel, ...(command === undefined ? { token } : { tokenCommand: command }) }); }
      catch { return done(1, 'Cannot save the alert destination; nothing was changed.'); }
      return done(0, command === undefined
        ? `Saved a Discord bot for channel ${channel} on this machine; the token is readable only by you. Run ${testHint}.`
        : `Saved a Discord bot for channel ${channel} on this machine; pdd runs your token command at each send and stores no token. Run ${testHint}.`);
    }
    if (input.action === 'set') {
      const parsed = webhook(input.text);
      if (!parsed) return done(2, 'Give one Discord or Slack incoming webhook URL (https) on stdin. Nothing was saved.');
      const file = configFile(env, ports, input.destination);
      if (!file) return noHome('Nothing was saved.');
      try { writePrivate(fs, file, { v: 1, service: parsed.service, url: parsed.url }); }
      catch { return done(1, 'Cannot save the alert destination; nothing was changed.'); }
      return done(0, `Saved a ${SERVICE[parsed.service]} webhook for Autopilot alerts on this machine. Run ${testHint} to send a test message.`);
    }
    if (input.action === 'test') {
      if (!configFile(env, ports, input.destination)) return noHome('Nothing was sent.');
      const destination = readDestination(fs, env, ports, input.destination);
      if (!destination) return done(1, `No alert destination is set on this machine. Run ${setHint}.`);
      const text = `PDD Autopilot test alert (${hostName(ports)}).`, delivered = () => recordTest(fs, env, ports, input.destination);
      if (destination.service === 'discord-bot') return await testBot(destination, text, input, ports, delivered);
      const outcome = await deliver(destination, text, ports, input.cwd), service = SERVICE[destination.service];
      if (outcome.result === 'delivered') { await delivered(); return done(0, `Test alert delivered; ${service} confirmed the message.`); }
      if (outcome.result === 'failed') return done(1, `Test alert failed (${outcome.detail}). Check the ${service} webhook, then run ${setHint} again.`);
      return done(1, `Test alert unconfirmed (${outcome.detail}). Look in the ${service} channel before you test again.`);
    }
    if (input.action === 'clear') {
      const file = configFile(env, ports, input.destination);
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
async function recordTest(fs, env, ports, destination) {
  const root = stateRoot(env, ports), at = new Date((ports.now ?? Date.now)()).toISOString();
  if (!root) return;
  let names = [];
  try { names = fs.readdirSync(join(root, 'alerts')).filter(name => STATE_FILE.test(name)); } catch { return; }
  for (const name of names) {
    const file = join(root, 'alerts', name), record = readRecord(fs, file);
    if (!record || !repoName(record.repo)) continue;
    try {
      await withRecord(record.repo, env, ports, fs, async (file, latest) => {
        latest.log = [...latest.log, { at, kind: 'test', action: 'test', result: 'delivered',
          ...(destination === 'infrastructure' ? { destination } : {}) }].slice(-LOG_LIMIT);
        writePrivate(fs, file, latest);
      });
    } catch { /* The test message was still delivered. */ }
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
  if (outcome.result === 'delivered') { await delivered(); return done(0, `Test alert delivered; ${where} posted it and the readback matched.`); }
  return done(1, `Test alert ${outcome.result} (${outcome.detail}) for ${where}.`);
}

// One short line for pdd autopilot status, from local files only; empty when nothing needs the person.
export function alertStatusLine({ repo, env = process.env } = {}, ports = {}) {
  try {
    if (!repoName(repo)) return '';
    const fs = ports.fs ?? nativeFs, file = recordFile(repo, env, ports), record = file && readRecord(fs, file);
    if (!record) return '';
    const open = Object.values(record.incidents).filter(item => object(item) && ['failed','unconfirmed','not-configured'].includes(item.result));
    const failed = ['autopilot', 'infrastructure'].map(destination => [...record.log].reverse()
      .find(row => SENDS.includes(row?.result) && (row.destination ?? 'autopilot') === destination))
      .filter(row => row && row.result !== 'delivered');
    if (!open.length && !failed.length) return '';
    const parts = [];
    if (open.length) parts.push(`${open.length} open alert${open.length === 1 ? '' : 's'} not delivered`);
    for (const row of failed) parts.push(`last delivery ${row.result}${row.detail ? ` (${row.detail})` : ''} for ${row.issue ? `#${row.issue} ` : ''}${row.kind} at ${row.at}`);
    const destinations = new Set([...open, ...failed].map(row => row.destination ?? 'autopilot'));
    const hints = [...destinations].map(destination => {
      const suffix = destination === 'infrastructure' ? ' --destination infrastructure' : '';
      return readDestination(fs, env, ports, destination) ? `check with pdd autopilot alerts test${suffix}` : `set one with pdd autopilot alerts set${suffix}`;
    });
    return scrub(oneLine(`Alerts: ${parts.join('; ')}; ${hints.join('; ')}.`));
  } catch { return ''; }
}
