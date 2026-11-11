// Generated from prompts/cli/github-calls.prompt.md (sha256: 1408163108cc4263bf6d47ffec18abefc2893dda8b984f0a16ccdb7c923dea6d).
import * as nativeFs from 'node:fs';
import { createHash, randomUUID } from 'node:crypto';
import { homedir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { recordCostGithub } from './cost-ledger.mjs';

export const GITHUB_PURPOSES = ['dependencies', 'claims', 'issues', 'pulls', 'writes', 'setup', 'other'];
export const GITHUB_SHARE = 30, GITHUB_FLOOR = 1000;
const HOUR = 60 * 60 * 1000, KEEP = 2 * HOUR, DEFAULT_LIMIT = 5000;
// The ETag cache keeps the entries used in the last day, at most this many and this size.
const ETAG_KEEP = 24 * HOUR, ETAG_ENTRIES = 5000, ETAG_BYTES = 32 * 1024 * 1024;
// gh api options that take a value. Every other word that starts with "-" is a flag.
const VALUE_OPTIONS = new Set(['-X', '--method', '-H', '--header', '-f', '--raw-field', '-F', '--field', '--input',
  '-q', '--jq', '-t', '--template', '--hostname', '--cache', '-p', '--preview']);
const FIELD_OPTIONS = new Set(['-f', '--raw-field', '-F', '--field', '--input']);
const REPOSITORY = /^[A-Za-z0-9][A-Za-z0-9_.-]*\/[A-Za-z0-9][A-Za-z0-9_.-]*$/;
const finite = value => typeof value === 'number' && Number.isFinite(value);
const hash = text => createHash('sha256').update(text).digest('hex').slice(0, 20);

// The REST or GraphQL route of one gh command. gh's own commands (pr, issue, repo, auth) use GraphQL.
export function githubCall(args = []) {
  const words = args.map(String);
  if (words[0] !== 'api') return { api: 'graphql', method: null, endpoint: '', conditional: false };
  let method, endpoint, fields = false, conditional = false;
  for (let at = 1; at < words.length; at++) {
    const word = words[at];
    if (VALUE_OPTIONS.has(word)) {
      const value = words[++at] ?? '';
      if (word === '-X' || word === '--method') method = value.toUpperCase();
      if ((word === '-H' || word === '--header') && /^if-none-match\s*:/i.test(value)) conditional = true;
      if (FIELD_OPTIONS.has(word)) fields = true;
    } else if (!word.startsWith('-') && endpoint === undefined) endpoint = word;
  }
  return { api: endpoint === 'graphql' ? 'graphql' : 'rest', method: method ?? (fields ? 'POST' : 'GET'), endpoint: endpoint ?? '', conditional };
}

// What a call is for, read from its arguments, when the caller names no purpose.
export function githubPurpose(args = []) {
  const words = args.map(String), call = githubCall(words);
  if (words[0] === 'auth' || words[0] === 'repo') return 'setup';
  if (words[0] === 'pr') return ['view', 'checks', 'list', 'status', 'diff'].includes(words[1]) ? 'pulls' : 'writes';
  if (words[0] === 'issue') return ['view', 'list', 'status'].includes(words[1]) ? 'issues' : 'writes';
  if (words[0] !== 'api') return 'other';
  if (call.api === 'graphql') return 'other';
  if (call.method !== 'GET') return 'writes';
  const path = call.endpoint.split('?')[0];
  if (/\/dependencies\/|\/timeline$|\/sub_issues/.test(path)) return 'dependencies';
  if (/\/issues\/comments\/[0-9]+$/.test(path)) return 'claims';
  if (/\/pulls(?:\/|$)|\/check-runs|\/check-suites|\/commits\/[^/]+\/status|\/statuses\//.test(path)) return 'pulls';
  if (/\/issues(?:\/|$)|\/collaborators(?:\/|$)/.test(path)) return 'issues';
  if (/^user$|^rate_limit$|^repos\/[^/]+\/[^/]+$|\/contents\/|\/labels(?:\/|$)|\/git\/ref/.test(path)) return 'setup';
  return 'other';
}

// The owner/name that one gh command reads or writes, lowercase, or null.
export function githubRepository(args = []) {
  const words = args.map(String), call = githubCall(words);
  const named = /^repos\/([^/?#]+\/[^/?#]+)/.exec(call.endpoint)?.[1];
  if (named && REPOSITORY.test(named)) return named.toLowerCase();
  for (let at = 0; at < words.length; at++) {
    if ((words[at] === '--repo' || words[at] === '-R') && REPOSITORY.test(words[at + 1] ?? '')) return words[at + 1].toLowerCase();
    const url = /^https:\/\/github\.com\/([^/]+\/[^/]+)\/(?:pull|issues)\/[0-9]+/.exec(words[at])?.[1];
    if (url && REPOSITORY.test(url)) return url.toLowerCase();
  }
  if (words[0] === 'repo' && words[1] === 'view' && REPOSITORY.test(words[2] ?? '')) return words[2].toLowerCase();
  return null;
}

// The status and the headers of a `gh api --include` reply. Null when the text has no HTTP status line.
export function githubReply(text) {
  const source = String(text ?? '');
  const status = /^HTTP\/\S+\s+([0-9]{3})/.exec(source)?.[1];
  if (!status) return null;
  const boundary = source.search(/\r?\n\r?\n/), head = boundary < 0 ? source : source.slice(0, boundary);
  const header = name => head.match(new RegExp(`^${name}:[ \\t]*(.*?)[ \\t]*\\r?$`, 'im'))?.[1];
  const number = name => { const value = header(name); return value === undefined || value === '' ? undefined : Number(value); };
  const remaining = number('x-ratelimit-remaining'), reset = number('x-ratelimit-reset');
  const rate = finite(remaining) ? { resource: header('x-ratelimit-resource') || 'core', remaining,
    ...(finite(number('x-ratelimit-limit')) ? { limit: number('x-ratelimit-limit') } : {}), ...(finite(reset) ? { resetAt: reset * 1000 } : {}) } : null;
  return { status: Number(status), etag: header('etag'), link: header('link'), rate, body: boundary < 0 ? '' : source.slice(boundary).trim() };
}

// One ledger entry for a finished gh call: its value or the error that it threw.
export function githubEntry(args, outcome, purpose, at) {
  const call = githubCall(args), reply = githubReply(outcome?.stdout);
  const status = reply?.status ?? (Number(/\bHTTP ([0-9]{3})\b/.exec(String(outcome?.stderr ?? ''))?.[1]) || null);
  return { at, api: call.api, purpose: GITHUB_PURPOSES.includes(purpose) ? purpose : githubPurpose(args), status,
    ...(call.conditional ? { conditional: true } : {}), ...(reply?.rate ?? {}) };
}

export const githubStateRoot = (env = process.env, stateRoot) => stateRoot ?? join(env?.HOME || homedir(), '.local', 'state', 'pdd', 'autopilot');
const ledgerFolder = root => join(root, 'github');

function readLines(fs, file) {
  let text;
  try { text = fs.readFileSync(file, 'utf8'); } catch { return []; }
  const entries = [];
  for (const line of text.split('\n')) {
    if (!line) continue;
    try { const entry = JSON.parse(line); if (entry && finite(entry.at) && typeof entry.purpose === 'string') entries.push(entry); } catch { /* A torn line is skipped. */ }
  }
  return entries;
}

// The local ledger of one repository on this machine: one JSON line for each call.
export function githubLedger({ root, repository, fs = nativeFs }) {
  const repo = String(repository).toLowerCase(), file = join(ledgerFolder(root), `${hash(repo)}.jsonl`);
  return {
    file, repository: repo,
    record(entry) {
      // Measurement never changes the call: a failed write is lost, the call result stays.
      try {
        fs.mkdirSync(dirname(file), { recursive: true, mode: 0o700 });
        fs.appendFileSync(file, `${JSON.stringify({ ...entry, repo })}\n`, { mode: 0o600 });
      } catch { /* best effort */ }
    },
    read: () => readLines(fs, file),
    // Keep the last 2 hours. A call that another process appends during the rewrite can be lost.
    compact(now) {
      try {
        const entries = readLines(fs, file);
        if (!entries.some(entry => entry.at <= now - KEEP)) return;
        const temp = `${file}.${randomUUID()}.tmp`;
        fs.writeFileSync(temp, entries.filter(entry => entry.at > now - KEEP).map(entry => `${JSON.stringify(entry)}\n`).join(''), { mode: 0o600 });
        fs.renameSync(temp, file);
      } catch { /* best effort */ }
    },
  };
}

// Every ledger on this machine, for the budget and the newest observed limit.
export function githubMachineEntries({ root, fs = nativeFs }) {
  let names = [];
  try { names = fs.readdirSync(ledgerFolder(root)).filter(name => /^[0-9a-f]{20}\.jsonl$/.test(name)); } catch { return []; }
  return names.flatMap(name => readLines(fs, join(ledgerFolder(root), name)));
}

// A gh runner that records each gh call in a ledger. options.purpose names the purpose of one call and
// options.repository its repository when the arguments do not name one; both are removed before the call runs.
// Other programs run unchanged.
export function countGithubCalls(exec, { ledger, purpose, now = Date.now } = {}) {
  return async (file, args, options = {}) => {
    const { purpose: named, repository, ...rest } = options ?? {};
    if (file !== 'gh' || !Array.isArray(args)) return exec(file, args, rest);
    let result, failure, failed = false;
    try { result = await exec(file, args, rest); } catch (error) { failure = error; failed = true; }
    try {
      const target = typeof ledger === 'function' ? ledger(args, repository) : ledger;
      target?.record(githubEntry(args, failed ? failure : result, named ?? purpose, now()));
    } catch { /* best effort */ }
    if (failed) throw failure;
    return result;
  };
}

// A counter for a pdd command outside the tick: the ledger of the repository that each call names, only when
// Autopilot already keeps a ledger for it on this machine. Other repositories, and test doubles of gh, write nothing.
// The folder is found at each call, so a later HOME applies.
export function nativeGithubCounter(exec, { env = process.env, stateRoot, purpose, fs = nativeFs, now = Date.now, costRun, costRecord = recordCostGithub } = {}) {
  const findCostRun = costRun ?? (async options => {
    if (typeof options.cwd !== 'string' || !fs.existsSync(join(options.cwd, '.git'))) return null;
    const result = await exec('git', ['rev-parse', '--path-format=absolute', '--git-common-dir'], { cwd: options.cwd });
    const folder = join(String(result.stdout).trim(), 'pdd', 'runs');
    let names; try { names = fs.readdirSync(folder); } catch { return null; }
    for (const name of names.filter(name => /^[1-9][0-9]*$/.test(name))) {
      try {
        const run = JSON.parse(fs.readFileSync(join(folder, name, 'status.json'), 'utf8'));
        if (run.root && resolve(run.root) === resolve(options.cwd)) return run.runDir;
      } catch {}
    }
    return null;
  });
  const countedExec = async (file, args, options = {}) => {
    let result, failure, failed = false;
    try { result = await exec(file, args, options); } catch (error) { failure = error; failed = true; }
    if (file === 'gh') {
      try { const runDir = await findCostRun(options); if (runDir) costRecord(runDir, { at: now() }, { fs }); } catch {}
    }
    if (failed) throw failure;
    return result;
  };
  return countGithubCalls(countedExec, { purpose, now, ledger: (args, named) => {
    const repository = githubRepository(args) ?? (typeof named === 'string' && REPOSITORY.test(named) ? named.toLowerCase() : null);
    if (!repository) return null;
    const ledger = githubLedger({ root: githubStateRoot(env, stateRoot), repository, fs });
    try { return fs.existsSync(ledger.file) ? ledger : null; } catch { return null; }
  } });
}

// Calls in the last hour, by purpose, and the newest limit that GitHub reported for each resource.
export function githubUsage(entries, now) {
  const recent = entries.filter(entry => entry.at > now - HOUR && entry.at <= now);
  const byPurpose = {}; let rest = 0, graphql = 0, counted = 0, conditional = 0, notModified = 0;
  for (const entry of recent) {
    byPurpose[entry.purpose] = (byPurpose[entry.purpose] ?? 0) + 1;
    if (entry.api === 'graphql') graphql++; else rest++;
    if (entry.conditional) { conditional++; if (entry.status === 304) notModified++; }
    // A 304 reply does not count against the REST limit.
    if (entry.api !== 'graphql' && entry.status !== 304) counted++;
  }
  const rate = {};
  for (const entry of entries) {
    if (typeof entry.resource !== 'string' || !finite(entry.remaining) || !finite(entry.resetAt) || entry.resetAt <= now || entry.at > now) continue;
    if (!rate[entry.resource] || entry.at >= rate[entry.resource].at) rate[entry.resource] = { remaining: entry.remaining, ...(finite(entry.limit) ? { limit: entry.limit } : {}), resetAt: entry.resetAt, at: entry.at };
  }
  return { calls: recent.length, rest, graphql, counted, conditional, notModified, byPurpose, rate };
}

// The share and the floor from the repository's Autopilot settings, else the defaults.
export function githubBudgetSettings(value) {
  const share = Number.isInteger(value?.share) && value.share >= 1 && value.share <= 100 ? value.share : GITHUB_SHARE;
  const floor = Number.isInteger(value?.floor) && value.floor >= 0 ? value.floor : GITHUB_FLOOR;
  return { share, floor };
}

// normal: work as usual. low: Autopilot on this machine used its share in the last hour.
// reserve: GitHub reported fewer than floor calls left; wait for the reset.
export function githubBudget({ usage, share = GITHUB_SHARE, floor = GITHUB_FLOOR }) {
  const core = usage.rate.core, limit = finite(core?.limit) ? core.limit : DEFAULT_LIMIT;
  const allowed = Math.floor(limit * share / 100), used = usage.counted;
  const short = ['core', 'graphql'].map(resource => ({ resource, ...usage.rate[resource] })).find(rate => finite(rate.remaining) && rate.remaining < floor);
  if (short) return { state: 'reserve', allowed, used, share, floor, resource: short.resource, remaining: short.remaining, resetAt: short.resetAt };
  return { state: used >= allowed ? 'low' : 'normal', allowed, used, share, floor };
}

const clock = at => new Date(at).toISOString().slice(11, 16) + 'Z';
// The one status line: calls in the last hour by purpose, 304 hits, the limit left and the budget state.
export function githubStatusLine({ usage, machine = usage, budget }) {
  const parts = GITHUB_PURPOSES.filter(name => usage.byPurpose[name]).map(name => `${name} ${usage.byPurpose[name]}`);
  const hits = usage.conditional ? `${usage.notModified} of ${usage.conditional} conditional reads were 304 (${Math.round(100 * usage.notModified / usage.conditional)}%)` : 'no conditional reads';
  const core = machine.rate.core;
  const left = core ? `REST limit ${core.remaining}${finite(core.limit) ? ` of ${core.limit}` : ''} left until ${clock(core.resetAt)}` : 'REST limit not seen in the last hour';
  // In reserve the budget part names its reason: the calls left and the floor.
  const reason = budget?.state === 'reserve' ? ` (${budget.remaining} ${budget.resource === 'graphql' ? 'GraphQL points' : 'REST calls'} left, below the floor of ${budget.floor})` : '';
  const plan = budget ? `; budget ${budget.state}${reason}: Autopilot on this machine used ${budget.used} of ${budget.allowed} (${budget.share}%)` : '';
  return `GitHub calls in the last hour: ${usage.calls}${usage.calls ? ` (${parts.join(', ')})` : ''}; ${hits}; ${left}${plan}.`;
}

// Saved ETags and bodies of GET replies, for conditional requests on the next read. A save merges with the file as
// it is then, so the tick and the pdd commands keep each other's entries: an entry stays while it was used in the
// last day, and the newest used entries stay within the count and size bounds.
export function githubEtagCache({ root, repository, fs = nativeFs, now = Date.now }) {
  const file = join(ledgerFolder(root), `${hash(String(repository).toLowerCase())}.etags.json`);
  let saved, used = new Map();
  const readFile = () => {
    try { const value = JSON.parse(fs.readFileSync(file, 'utf8')); return value && typeof value === 'object' && !Array.isArray(value) ? value : {}; } catch { return {}; }
  };
  const load = () => saved ??= readFile();
  const valid = entry => entry && typeof entry.etag === 'string' && typeof entry.body === 'string';
  return {
    file,
    get(endpoint) {
      const entry = used.get(endpoint) ?? load()[endpoint];
      if (!valid(entry)) return undefined;
      used.set(endpoint, { etag: entry.etag, body: entry.body, next: entry.next ?? '', at: now() });
      return entry;
    },
    set(endpoint, entry) { if (typeof entry?.etag === 'string' && entry.etag && typeof entry.body === 'string') used.set(endpoint, { etag: entry.etag, body: entry.body, next: entry.next ?? '', at: now() }); },
    save() {
      // A read that used no entry (it failed early) keeps the saved cache.
      if (!used.size) return;
      const at = now(), merged = Object.entries({ ...readFile(), ...Object.fromEntries(used) })
        .filter(([, entry]) => valid(entry) && finite(entry.at) && entry.at > at - ETAG_KEEP).sort((a, b) => b[1].at - a[1].at);
      const kept = {}; let size = 2;
      for (const [endpoint, entry] of merged.slice(0, ETAG_ENTRIES)) {
        size += Buffer.byteLength(JSON.stringify({ [endpoint]: entry })) - 2 + (size > 2 ? 1 : 0);
        if (size > ETAG_BYTES) break;
        kept[endpoint] = entry;
      }
      try {
        fs.mkdirSync(dirname(file), { recursive: true, mode: 0o700 });
        const temp = `${file}.${randomUUID()}.tmp`;
        fs.writeFileSync(temp, JSON.stringify(kept), { mode: 0o600 });
        fs.renameSync(temp, file);
      } catch { /* A lost cache only costs counted reads. */ }
      saved = kept; used = new Map();
    },
  };
}

// Below the floor, the non-safety reads of the tick and of pdd commands stop until the reset. Safety reads (claim
// checks, heartbeats, trust, readbacks after writes) and writes go on. The guard starts from the newest limit in the
// ledgers of this machine and follows the rate-limit headers of each later reply.
export function githubFloorGuard({ floor = GITHUB_FLOOR, entries = [], now = Date.now } = {}) {
  const rate = {}; let stopped = false;
  for (const [resource, value] of Object.entries(githubUsage(entries, now()).rate)) rate[resource] = { remaining: value.remaining, resetAt: value.resetAt };
  return {
    floor,
    // One reply of `gh api --include`, as githubReply reads it; a reply without rate-limit headers changes nothing.
    observe(reply) { const value = reply?.rate; if (value && finite(value.remaining)) rate[value.resource] = { remaining: value.remaining, resetAt: value.resetAt }; },
    blocked(resource = 'core') {
      const value = rate[resource];
      const low = !!value && value.remaining < floor && !(finite(value.resetAt) && value.resetAt <= now());
      if (low) stopped = true;
      return low;
    },
    get stopped() { return stopped; },
  };
}

// Every page of a list endpoint, with no --slurp (gh before 2.48 has no --slurp): each item is one line of JSON.
// `pick` is an optional jq projection of one item, for example '{tag_name, draft, published_at}'.
export const githubListArgs = (pick = '.') => ['--paginate', '--jq', `.[] | ${pick} | tojson`];
export function githubListItems(stdout) {
  // A line that is a whole JSON list (a gh or a double that ignored --jq) gives its items.
  return String(stdout ?? '').split('\n').filter(line => line.trim()).flatMap(line => { const value = JSON.parse(line); return Array.isArray(value) ? value : [value]; });
}

// GitHub's ETag covers only the body, and a 304 reply has no Link header. A full page without a next page keeps its
// body and its ETag when the list grows past it, so a conditional read would keep the saved "no next page" and miss
// the new items. Such a page is never read with its ETag.
export function githubFullLastPage(endpoint, items, next) {
  if (!Array.isArray(items) || next) return false;
  const query = String(endpoint ?? '').split('#', 1)[0].split('?')[1] ?? '';
  const asked = Number(new URLSearchParams(query).get('per_page'));
  return items.length >= (Number.isInteger(asked) && asked >= 1 ? Math.min(asked, 100) : 30);
}
