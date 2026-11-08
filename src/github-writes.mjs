// Implements prompts/cli/github-writes.prompt.md.
import * as nativeFs from 'node:fs';
import { createHash, randomUUID } from 'node:crypto';
import { hostname } from 'node:os';
import { join } from 'node:path';

const MINUTE = 60_000, HOUR = 60 * MINUTE, CLAIM_LIFE = 4 * HOUR;
const digest = text => createHash('sha256').update(text).digest('hex').slice(0, 20);
const option = (args, ...names) => {
  for (let i = 0; i < args.length; i++) for (const name of names) {
    if (args[i] === name) return args[i + 1];
    if (args[i].startsWith(`${name}=`)) return args[i].slice(name.length + 1);
    if (name.length === 2 && args[i].startsWith(name) && args[i].length > 2) return args[i].slice(2);
  }
};
const fail = (usage, retryAt = Date.now() + MINUTE) => Object.assign(Error(`GitHub writes deferred until ${new Date(retryAt).toISOString()}.`), { code: 'github_write_budget', retryAt, usage });

// Successful content can discuss limits. Only a response status or gh's failure
// diagnostic establishes a throttle; payload lines cannot supply HTTP headers.
export function githubWriteThrottle(outcome) {
  if (outcome?.code === 0) return null;
  const stdout = String(outcome?.stdout ?? ''), stderr = String(outcome?.stderr ?? '');
  const status = Number(/^HTTP\/\S+\s+([0-9]{3})\b/.exec(stdout)?.[1]);
  let head, report;
  if (status) {
    if (status !== 403 && status !== 429) return null;
    const boundary = stdout.search(/\r?\n\r?\n/);
    head = boundary < 0 ? stdout : stdout.slice(0, boundary);
    report = `${stdout}\n${stderr}`;
  } else {
    if (!/\bHTTP (?:403|429)\b/.test(stderr)) return null;
    head = stderr;
    report = stderr;
  }
  const retryAfter = /^retry-after:[ \t]*(.*?)[ \t]*\r?$/im.exec(head)?.[1];
  return retryAfter !== undefined || /secondary|abuse/i.test(report) ? { retryAfter } : null;
}

// Keep only GraphQL code. A # inside a quoted or block string is data, not
// a comment; it must never hide a later mutation operation from admission.
function graphqlCode(source) {
  let out = '';
  for (let i = 0; i < source.length;) {
    if (source[i] === '#') { while (i < source.length && source[i] !== '\n') i++; continue; }
    if (source[i] === '"') {
      const block = source.slice(i, i + 3) === '"""';
      i += block ? 3 : 1; let closed = false;
      while (i < source.length) {
        if (block && source[i] === '\\' && source.slice(i + 1, i + 4) === '"""') { i += 4; continue; }
        if (!block && source[i] === '\\') { i += 2; continue; }
        if (block ? source.slice(i, i + 3) === '"""' : source[i] === '"') { i += block ? 3 : 1; closed = true; break; }
        i++;
      }
      if (!closed) return null;
      out += ' "" '; continue;
    }
    out += source[i++];
  }
  return out.trim();
}

// Count top-level selected fields, including aliases and fields without input
// arguments. Count every mutation operation, regardless of operationName.
function graphqlFields(code) {
  const tokens=code.match(/[A-Za-z_]\w*|[{}():@]|\.\.\./g)??[];
  let depth=0, parens=0, fields=0, mutation=false;
  for(let i=0;i<tokens.length;i++) {
    const token=tokens[i];
    if(depth===0 && parens===0) { if(token==='mutation' || token==='Mutation' && tokens[i-1]==='on') mutation=true; else if(token==='query' || token==='fragment') mutation=false; }
    if(token==='(') {parens++;continue;}
    if(token===')') {parens--;continue;}
    if(token==='{') {depth++;continue;}
    if(token==='}') {depth--;continue;}
    if(mutation && depth===1 && parens===0 && /^[A-Za-z_]/.test(token) && tokens[i+1]!==':' && tokens[i-1]!=='@') fields++;
  }
  return Math.max(1,fields);
}

// Conservative reservations for opaque gh commands; raw API calls count each content request.
export function githubWriteCost(args, options = {}) {
  if (args[0] === 'api') {
    const method = (option(args, '-X', '--method') ?? (args.some(x => /^(?:--(?:input|field|raw-field)(?:=|$)|-[fF])/.test(x)) ? 'POST' : 'GET')).toUpperCase();
    const graphql = args.some(arg => arg === 'graphql' || /^https:\/\/[^/]+\/(?:[^?#]*\/)?graphql(?:[?#]|$)/i.test(arg));
    if (graphql) {
      let query = '';
      try { query = JSON.parse(options.input ?? '{}').query ?? ''; } catch { /* Unknown payload reserves one. */ }
      for (let i = 0; i < args.length; i++) { const field = args[i].replace(/^(?:--(?:raw-field|field)=|-[fF])/, ''); if (/^query=/.test(field)) query = field.slice(6); }
      const cleaned = graphqlCode(query);
      if (cleaned === null) return 1;
      if (/\bmutation\b/.test(cleaned) || cleaned.includes('...')) return graphqlFields(cleaned);
      if (/^(?:query\b|\{)/.test(cleaned)) return 0;
      return 1;
    }
    return ['GET', 'HEAD', 'OPTIONS'].includes(method) ? 0 : 1;
  }
  const [group, action] = args;
  if (['auth', 'repo'].includes(group) && (group === 'auth' || ['view', 'list'].includes(action))) return 0;
  if (['pr', 'issue'].includes(group) && ['view', 'list', 'status', 'checks', 'diff'].includes(action)) return 0;
  if (['label', 'release', 'run', 'workflow'].includes(group) && ['view', 'list', 'download', 'watch'].includes(action)) return 0;
  if (group === '--version' || args.includes('--help')) return 0;
  const labels = args.flatMap((x, i) => ['--add-label', '--remove-label', '--label', '-l'].includes(x) ? String(args[i + 1] ?? '').split(',').filter(Boolean) : []);
  // gh may look up/create labels and dispatch separate mutation requests.
  const extra = (args.includes('--comment') ? 1 : 0) + (args.includes('--delete-branch') ? 1 : 0);
  return Math.max(1, 1 + extra + 2 * labels.length + (['create', 'edit'].includes(action) ? 2 : 0));
}

// Lamport's choosing/ticket protocol, with one never-reused record per attempt.
// Recovery deletes only a dead process's unique record, never a shared sentinel
// that a replacement owner could have acquired. Contention defers rather than
// spinning inside synchronous admission.
export function githubWriteLock({ directory, fs = nativeFs }) {
  fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
  const name = `${process.pid}-${randomUUID()}`, own = join(directory, name);
  const busy = () => Object.assign(Error('GitHub write lock busy'), { code: 'github_write_lock_busy' });
  const records = () => fs.readdirSync(directory).flatMap(entry => {
    if (entry === name) return [];
    const pid = Number(/^(\d+)-[0-9a-f-]+$/.exec(entry)?.[1]);
    if (!Number.isSafeInteger(pid) || pid < 1) throw Error('Unreadable GitHub lock owner');
    try { process.kill(pid, 0); } catch (error) {
      if (error.code !== 'ESRCH') throw error;
      try { fs.unlinkSync(join(directory, entry)); } catch (e) { if (e.code !== 'ENOENT') throw e; }
      return [];
    }
    let text;
    try { text = fs.readFileSync(join(directory, entry), 'utf8'); } catch (e) { if (e.code === 'ENOENT') return []; throw e; }
    // Empty, partial or choosing records block until their live writer finishes.
    const ticket = /^\d+$/.test(text) ? Number(text) : 0;
    if (!Number.isSafeInteger(ticket)) throw Error('Invalid GitHub lock ticket');
    return [{ name: entry, ticket }];
  });
  let published = false;
  const release = () => { if (published) { fs.unlinkSync(own); published = false; } };
  try {
    fs.writeFileSync(own, '0', { flag: 'wx', mode: 0o600 }); published = true;
    const ticket = Math.max(0, ...records().map(row => row.ticket)) + 1;
    if (!Number.isSafeInteger(ticket)) throw Error('GitHub lock ticket exhausted');
    fs.writeFileSync(own, String(ticket));
    if (records().some(row => row.ticket === 0 || row.ticket < ticket || row.ticket === ticket && row.name < name)) throw busy();
    return release;
  } catch (error) { release(); throw error; }
}

export function githubWriteBudget({ root, identity = 'unknown', host = 'github.com', fs = nativeFs, now = Date.now, machine = hostname() }) {
  identity = String(identity || 'unknown').toLowerCase(); host = String(host).toLowerCase();
  const directory = join(root, 'github-writes'), file = join(directory, `${digest(`${host}/${identity}`)}.json`), lock = join(directory, `${digest(host)}.lock`);
  const cooldownPrefix = `cooldown-${digest(host)}-`;
  const cooldowns = () => {
    let names;
    try { names = fs.readdirSync(directory).filter(name => name.startsWith(cooldownPrefix) && name.endsWith('.json')); }
    catch (error) { if (error.code === 'ENOENT') return []; throw error; }
    return names.flatMap(name => {
      const path = join(directory, name); let row;
      try { row = JSON.parse(fs.readFileSync(path, 'utf8')); } catch (error) { if (error.code === 'ENOENT') return []; throw error; }
      if (row.host !== host || typeof row.identity !== 'string' || !row.identity || !Number.isFinite(row.retryAt)) throw Error('Invalid GitHub cooldown');
      return [{ ...row, path }];
    });
  };
  const empty = () => ({ identity, host, events: [], claims: {}, cooldown: 0 });
  const load = () => {
    let value;
    try { value = JSON.parse(fs.readFileSync(file, 'utf8')); } catch (error) { if (error.code === 'ENOENT') return empty(); throw error; }
    if (!Array.isArray(value.events) || !value.claims || typeof value.claims !== 'object' || !Number.isFinite(value.cooldown)
      || value.events.some(e => !Number.isFinite(e.at) || !Number.isSafeInteger(e.count) || e.count < 1)) throw Error('Invalid GitHub write state');
    return value;
  };
  const view = (value, count = 1) => {
    const at = now(), peers = new Set([machine]);
    let shared = {}, uncertain = [], cooldown = value.cooldown;
    for (const row of cooldowns()) if (identity === 'unknown' || row.identity === identity || row.identity === 'unknown') cooldown = Math.max(cooldown, row.retryAt);
    if (identity !== 'unknown') {
      try { const unknown = JSON.parse(fs.readFileSync(join(directory, `${digest(`${host}/unknown`)}.json`), 'utf8')); shared = unknown.claims; uncertain = unknown.events; cooldown = Math.max(cooldown, unknown.cooldown); }
      catch (error) { if (error.code !== 'ENOENT') throw error; }
    } else {
      let files = [];
      try { files = fs.readdirSync(directory).filter(name => /^[0-9a-f]{20}\.json$/.test(name)); } catch (error) { if (error.code !== 'ENOENT') throw error; }
      for (const name of files) {
        if (join(directory, name) === file) continue;
        const other = JSON.parse(fs.readFileSync(join(directory, name), 'utf8'));
        if (other.host !== host) continue;
        uncertain.push(...other.events); cooldown = Math.max(cooldown, other.cooldown);
        for (const [repository, claims] of Object.entries(other.claims)) shared[`${other.identity}/${repository}`] = claims;
      }
    }
    for (const claims of [...Object.values(shared), ...Object.values(value.claims)]) for (const c of claims) if (typeof c.machine === 'string' && c.seen > at - CLAIM_LIFE && c.seen <= at) peers.add(c.machine);
    const machines = peers.size, minuteLimit = Math.max(1, Math.floor(60 / machines)), hourLimit = Math.max(1, Math.floor(350 / machines));
    const events = [...uncertain, ...value.events].filter(e => e.at > at - HOUR && e.at <= at);
    const sum = rows => rows.reduce((n, e) => n + e.count, 0), minute = sum(events.filter(e => e.at > at - MINUTE)), hour = sum(events);
    const next = (window, limit) => {
      if (count > limit) return at + HOUR;
      const rows = events.filter(e => e.at > at - window).sort((a, b) => a.at - b.at);
      let used = sum(rows);
      for (const row of rows) { if (used + count <= limit) break; used -= row.count; if (used + count <= limit) return row.at + window; }
      return at;
    };
    const retryAt = Math.max(cooldown, next(MINUTE, minuteLimit), next(HOUR, hourLimit));
    return { identity, host, minute, hour, minuteLimit, hourLimit, machines, retryAt: retryAt > at ? retryAt : null, state: retryAt > at ? 'deferred' : 'normal' };
  };
  const update = action => {
    const temporary = `${lock}.${randomUUID()}`;
    let held = false;
    try {
      fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
      fs.writeFileSync(temporary, String(process.pid), { flag: 'wx', mode: 0o600 });
      try { fs.linkSync(temporary, lock); held = true; }
      catch (error) {
        if (error.code !== 'EEXIST') throw error;
        // Recoverers serialize through recoverable, uniquely owned attempts.
        const release = githubWriteLock({ directory: `${lock}.reap`, fs });
        try {
          // The previous owner may have released while recovery was acquired.
          let pid;
          try { pid = Number(fs.readFileSync(lock, 'utf8')); } catch (e) { if (e.code !== 'ENOENT') throw e; }
          if (pid !== undefined) {
            if (!Number.isSafeInteger(pid) || pid < 1) throw Error('Unreadable GitHub write lock');
            try { process.kill(pid, 0); } catch (dead) {
              if (dead.code !== 'ESRCH') throw dead;
              fs.unlinkSync(lock); pid = undefined;
            }
          }
          if (pid !== undefined) throw Error('GitHub write lock busy');
          // A normal acquirer can win this gap. EEXIST safely defers to it.
          fs.linkSync(temporary, lock); held = true;
        } finally { release(); }
      }
      const value = load(), result = action(value);
      value.events = value.events.filter(e => e.at > now() - HOUR);
      const saved = `${file}.${randomUUID()}.tmp`;
      try { fs.writeFileSync(saved, JSON.stringify(value), { flag: 'wx', mode: 0o600 }); fs.renameSync(saved, file); }
      finally { try { fs.unlinkSync(saved); } catch (e) { if (e.code !== 'ENOENT') throw e; } }
      return result;
    } catch (error) { if (error.code === 'github_write_budget') throw error; throw fail(undefined, now() + MINUTE); }
    finally {
      if (held) fs.unlinkSync(lock);
      try { fs.unlinkSync(temporary); } catch (e) { if (e.code !== 'ENOENT') throw e; }
    }
  };
  return {
    reserve(count) {
      if (!Number.isSafeInteger(count) || count < 0) throw fail(undefined, now() + MINUTE);
      if (!count) return this.usage();
      return update(value => {
        const usage = view(value, count);
        if (usage.retryAt) throw fail(usage, usage.retryAt);
        value.events.push({ at: now(), count });
        return view(value);
      });
    },
    usage() { try { if (fs.existsSync(lock)) throw Error('GitHub write lock present'); return view(load()); } catch { return { identity,host,minute:0,hour:0,minuteLimit:60,hourLimit:350,machines:1,state:'deferred',retryAt:now()+MINUTE,unavailable:true }; } },
    observeClaims(repository, claims) {
      return update(value => { value.claims[String(repository).toLowerCase()] = claims.filter(c => c.active === true && typeof c.machine === 'string' && c.machine)
        .map(c => ({ machine: c.machine, seen: Date.parse(c.lastSeen) })).filter(c => Number.isFinite(c.seen)); });
    },
    observe(outcome) {
      const throttle = githubWriteThrottle(outcome);
      if (!throttle) return;
      const retry = throttle.retryAfter;
      const delay = retry && /^\d+$/.test(retry) ? now() + Number(retry) * 1000 : Date.parse(retry);
      const retryAt = Number.isFinite(delay) && delay > now() ? delay : now() + MINUTE;
      // Immutable observations cannot overwrite a longer concurrent deadline,
      // and do not need the reservation lock held by another local process.
      fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
      const saved = join(directory, `${cooldownPrefix}${randomUUID()}.json`), temporary = `${saved}.tmp`;
      try { fs.writeFileSync(temporary, JSON.stringify({ host, identity, retryAt }), { flag: 'wx', mode: 0o600 }); fs.renameSync(temporary, saved); }
      finally { try { fs.unlinkSync(temporary); } catch (e) { if (e.code !== 'ENOENT') throw e; } }
      for (const row of cooldowns()) if (row.retryAt <= now()) try { fs.unlinkSync(row.path); } catch (e) { if (e.code !== 'ENOENT') throw e; }
    },
  };
}

export function githubWriteStatus(usage) {
  if (usage.unavailable) return `GitHub writes (${usage.host}/${usage.identity}): usage unavailable; deferred until ${new Date(usage.retryAt).toISOString()}.`;
  return `GitHub writes (${usage.host}/${usage.identity}): ${usage.minute}/${usage.minuteLimit} per minute; ${usage.hour}/${usage.hourLimit} per hour; ${usage.machines} machine(s); ${usage.state}${usage.retryAt ? ` until ${new Date(usage.retryAt).toISOString()}` : ''}.`;
}
