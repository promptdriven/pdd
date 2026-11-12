// Generated from prompts/cli/accounts-command.prompt.md (sha256: bf316b73d368ec6413d3e2992bd4d0de57ca6f437ce0273c03c43fce8d0732cb).
import { spawn as nodeSpawn } from 'node:child_process';
import * as nodeFs from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { basename, dirname, isAbsolute, join, resolve } from 'node:path';
import { PoolError, appendLog, orderedLogins, readLog, readPool, updatePool } from './accounts-store.mjs';

const NAME = /^[a-z0-9][a-z0-9._-]{0,31}$/;
const MODULES = { accountsLogin: 'accounts-login.mjs', accountsUsage: 'accounts-usage.mjs', accountsPick: 'accounts-pick.mjs',
  accountsCloud: 'accounts-cloud.mjs', accountsReset: 'accounts-reset.mjs' };
// The pick cannot use these logins until a person acts, so they get no place number in the list.
const NEEDS_PERSON = new Set(['paused', 'no-login', 'expired', 'needs-sign-in']);
const DEFAULT_STOP = Object.freeze({ week: 97, fiveHour: 97 });
const RESET_MEANING = {
  never: name => `With never, pdd never uses a reset on ${name}.`,
  ask: name => `With ask, pdd asks you before it uses a reset on ${name}.`,
  auto: name => `With auto, Autopilot may use a reset on ${name} by itself when every login is out, at most one a day, and tells you.`,
};

class Stop extends Error { constructor(exitCode, message) { super(message); this.exitCode = exitCode; } }
const stop = (exitCode, message) => { throw new Stop(exitCode, message); };
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
const finite = value => typeof value === 'number' && Number.isFinite(value);
const say = (stream, text) => stream.write(`${text}\n`);
const noLogin = name => new Stop(1, `No login named ${name}.`);
const badName = (name, hint) => `${name} is not a valid login name. Use ${hint}a-z, 0-9, ., _ or - (at most 32).`;
const nameInUse = (name, hint) => `The name ${name} is in use.${hint}`;

async function need(ctx, port, names) {
  let module = ctx.ports[port];
  if (module === undefined) {
    const url = new URL(`./${MODULES[port]}`, import.meta.url).href;
    try { module = await import(url); }
    catch (error) {
      // Only this module file missing means "not merged yet"; a broken module is a real error.
      if (error?.code !== 'ERR_MODULE_NOT_FOUND' || error.url !== url) throw error;
      module = null;
    }
  }
  if (!module || names.some(name => typeof module[name] !== 'function'))
    stop(2, `pdd accounts ${ctx.label} needs src/${MODULES[port]}, which this pdd does not have yet.`);
  return module;
}

const terminal = ctx => Boolean(ctx.stdin?.isTTY && ctx.stdout?.isTTY);
const serverUrl = (ctx, pool) => (typeof ctx.env.PDD_ACCOUNTS_URL === 'string' && ctx.env.PDD_ACCOUNTS_URL.trim())
  || (object(pool.server) && typeof pool.server.url === 'string' && pool.server.url) || null;
const find = (pool, name) => pool.logins.find(row => row.name === name);
// The one folder that add makes for a name; null without an absolute home.
const addFolder = (pool, env, name) => {
  const base = pool.homesDir ?? (isAbsolute(env.HOME ?? '') ? join(env.HOME, '.pdd') : null);
  return base && join(base, 'codex', name);
};
const log = (ctx, action, login, detail) => appendLog({ env: ctx.env }, { action, login, detail }, ctx.ports);

async function facts(module, home) {
  try { const value = await module.codexLoginFacts(home); return object(value) ? value : { state: 'unreadable' }; }
  catch { return { state: 'unreadable' }; }
}

function readLine(stdin) {
  return new Promise(done => {
    let text = '';
    const finish = () => { stdin.off?.('data', data); stdin.off?.('end', finish); stdin.off?.('close', finish); stdin.pause?.(); done(text.split('\n')[0]); };
    const data = chunk => { text += String(chunk); if (text.includes('\n')) finish(); };
    stdin.on('data', data); stdin.once('end', finish); stdin.once('close', finish);
    stdin.resume?.();
  });
}

function runProgram(ctx, command, args, env) {
  return new Promise(done => {
    let child;
    try { child = (ctx.ports.spawn ?? nodeSpawn)(command, args, { env, stdio: 'inherit' }); }
    catch { done(null); return; }
    child.once('error', () => done(null));
    child.once('close', code => done(code));
  });
}

function clock(ctx) {
  const format = new Intl.DateTimeFormat('en-US', { timeZone: ctx.timeZone, year: 'numeric', month: 'short', day: 'numeric',
    hour: '2-digit', minute: '2-digit', hourCycle: 'h23', timeZoneName: 'short' });
  const parts = ms => Object.fromEntries(format.formatToParts(new Date(ms)).map(part => [part.type, part.value]));
  const day = ms => { if (!finite(ms)) return '-'; const p = parts(ms); return `${p.month} ${p.day} ${p.hour}:${p.minute}`; };
  const zoned = ms => `${day(ms)} ${parts(ms).timeZoneName}`;
  const sameDay = (a, b) => { const x = parts(a), y = parts(b); return x.year === y.year && x.month === y.month && x.day === y.day; };
  const short = (ms, now) => { const p = parts(ms); return sameDay(ms, now) ? `${p.hour}:${p.minute} ${p.timeZoneName}` : zoned(ms); };
  return { day, zoned, short };
}

function usageMap(value, logins) {
  const rows = object(value) && value.rows !== undefined ? value.rows : value, map = new Map();
  if (Array.isArray(rows)) rows.forEach((row, index) => {
    const name = typeof row?.name === 'string' ? row.name : logins[index]?.name;
    if (name && object(row)) map.set(name, row);
  });
  else if (object(rows)) for (const [name, row] of Object.entries(rows)) if (object(row)) map.set(name, row);
  return map;
}

function table(rows) {
  const widths = rows[0].map((_, column) => Math.max(column === 0 ? 2 : 0, ...rows.map(row => row[column].length)));
  return rows.map(row => row.map((cell, column) => column === row.length - 1 ? cell : cell.padEnd(widths[column] + 2)).join('').trimEnd());
}

function stateText(reason, until, usage, time) {
  const at = finite(until) ? ` until ${time.day(until)}` : '';
  switch (reason) {
    case 'ready': return 'ready';
    case 'paused': return 'paused';
    case 'no-login': return 'no login';
    case 'expired': return 'access ended (this read never refreshes)';
    case 'needs-sign-in': return 'needs sign-in';
    case 'week': return `limited (week)${at}`;
    case 'five-hour': return `limited (5h)${at}`;
    case 'limited': return `${usage?.limitReason === 'credits' ? 'limited (credits)' : 'limited'}${at}`;
    case 'stale': return 'stale';
    default: {
      const note = typeof usage?.note === 'string' && usage.note.trim() ? ` (${usage.note.trim().slice(0, 80)})` : '';
      return `unknown${note}`;
    }
  }
}

const windowOf = value => object(value) && finite(value.usedPercent)
  ? { usedPercent: value.usedPercent, resetsAt: finite(value.resetsAt) ? value.resetsAt : null } : null;
const kindOf = (row, fact) => row.provider === 'claude' ? 'claude folder'
  : fact?.state === 'full' ? 'login' : fact?.state === 'access' ? 'access copy' : null;

function resetsLine(rows) {
  const settings = rows.map(row => row.reset ?? 'never');
  if (new Set(settings).size === 1) return `Resets: ${settings[0]} for every login.`;
  const parts = ['ask', 'auto'].filter(setting => settings.includes(setting))
    .map(setting => `${setting} for ${rows.filter(row => row.reset === setting).map(row => row.name).join(', ')}`);
  if (settings.includes('never')) parts.push('never for the others');
  return `Resets: ${parts.join('; ')}.`;
}

async function list(ctx) {
  const json = ctx.options['--json'] === true, cacheOnly = ctx.options['--no-read'] === true;
  const pool = await readPool({ env: ctx.env }, ctx.ports), rows = orderedLogins(pool);
  if (!rows.length) {
    say(ctx.stdout, json ? JSON.stringify({ mode: 'local', readAt: null, logins: [], next: null, ready: 0, total: 0, nextFree: null }, null, 2)
      : 'No logins on this machine yet. Run pdd accounts import PATH or pdd accounts add NAME.');
    return 0;
  }
  const login = await need(ctx, 'accountsLogin', ['codexLoginFacts']);
  const usageModule = await need(ctx, 'accountsUsage', [cacheOnly ? 'loadUsage' : 'readAllUsage']);
  const pick = await need(ctx, 'accountsPick', ['loginReadiness', 'poolSummary']);
  const now = ctx.now(), time = clock(ctx);
  const loginFacts = new Map();
  for (const row of rows) if (row.provider === 'codex') loginFacts.set(row.name, await facts(login, row.home));
  const usage = usageMap(cacheOnly ? await usageModule.loadUsage({ env: ctx.env }) : await usageModule.readAllUsage(rows, { env: ctx.env, now }), rows);
  const usageObject = Object.fromEntries(rows.filter(row => usage.has(row.name)).map(row => [row.name, usage.get(row.name)]));
  const shown = rows.map(row => {
    const use = usage.get(row.name) ?? null, fact = loginFacts.get(row.name) ?? null;
    const readiness = pick.loginReadiness(row, use, now) ?? {};
    const reason = typeof readiness.reason === 'string' ? readiness.reason : 'unknown';
    const until = finite(readiness.until) ? readiness.until : null;
    const access = finite(use?.accessExpiresAt) ? use.accessExpiresAt : finite(fact?.accessExpiresAt) ? fact.accessExpiresAt : null;
    return { row, use, reason, until, ready: readiness.ready === true, item: { position: row.position, name: row.name, provider: row.provider,
      kind: kindOf(row, fact), plan: typeof use?.plan === 'string' && use.plan ? use.plan : null, week: windowOf(use?.week), fiveHour: windowOf(use?.fiveHour),
      accessExpiresAt: access, state: stateText(reason, until, use, time), reason, until, paused: row.paused === true, reset: row.reset ?? 'never' } };
  });
  const summary = pick.poolSummary({ logins: rows, usage: usageObject, now }) ?? {};
  const next = typeof summary.next === 'string' ? summary.next : typeof summary.next?.name === 'string' ? summary.next.name : null;
  const ready = finite(summary.ready) ? summary.ready : shown.filter(entry => entry.ready).length;
  const total = finite(summary.total) ? summary.total : rows.length;
  const nextFree = object(summary.nextFree) && typeof summary.nextFree.name === 'string' && finite(summary.nextFree.at)
    ? { name: summary.nextFree.name, at: summary.nextFree.at } : null;
  const reads = [...usage.entries()].filter(([name]) => rows.some(row => row.name === name)).map(([, row]) => row.readAt).filter(finite);
  const readAt = reads.length ? Math.max(...reads) : null;
  if (json) {
    say(ctx.stdout, JSON.stringify({ mode: 'local', readAt, logins: shown.map(entry => entry.item), next, ready, total, nextFree }, null, 2));
    return 0;
  }
  const mode = serverUrl(ctx, pool) ? 'local logins only; this pdd does not list login server logins' : 'local mode, no login server';
  const read = readAt === null ? 'No usage read yet.' : `${cacheOnly ? 'Usage from the cache, read' : 'Usage read'} ${time.short(readAt, now)}.`;
  const percent = value => value ? `${Math.floor(value.usedPercent)}%` : '-';
  const cells = shown.map(({ item, reason }) => [NEEDS_PERSON.has(reason) ? '-' : String(item.position), item.name, item.kind ?? '-', item.plan ?? '-',
    percent(item.week), time.day(item.week?.resetsAt), percent(item.fiveHour), time.day(item.fiveHour?.resetsAt), time.day(item.accessExpiresAt), item.state]);
  const lines = [`Logins on this machine (${mode}). ${read} Read only: no refresh, nothing spent.`, '',
    ...table([['#', 'NAME', 'KIND', 'PLAN', 'WEEK', 'WEEK RESETS', '5H', '5H RESETS', 'ACCESS ENDS', 'STATE'], ...cells]), '',
    [next ? `Next step uses ${next}.` : 'No login is ready now.', `Ready: ${ready} of ${total}.`,
      ...(nextFree ? [`Next free: ${nextFree.name} at ${time.zoned(nextFree.at)}.`] : [])].join(' '), resetsLine(rows)];
  say(ctx.stdout, lines.join('\n'));
  return 0;
}

const newRow = (name, home, source, now) => ({ name, provider: 'codex', home, source, mode: 'local', paused: false, reset: 'never',
  stop: { ...DEFAULT_STOP }, addedAt: new Date(now).toISOString() });

async function accountKeys(login, pool) {
  const keys = new Map();
  for (const row of pool.logins) if (row.provider === 'codex') {
    const key = (await facts(login, row.home)).accountKey;
    if (typeof key === 'string' && key && !keys.has(key)) keys.set(key, row.name);
  }
  return keys;
}

async function linkTarget(fs, path) { try { return await fs.readlink(path); } catch { return 'an unknown place'; } }

// The pool rows were read outside the lock; a name or folder taken meanwhile refuses the whole change.
const addRows = rows => pool => {
  for (const row of rows) {
    if (find(pool, row.name)) stop(1, nameInUse(row.name, ''));
    const same = pool.logins.find(other => other.home === row.home);
    if (same) stop(1, `${row.home} is already in the pool as ${same.name}.`);
  }
  return { ...pool, logins: [...pool.logins, ...rows] };
};

async function upload(ctx, pool, rows) {
  if (!rows.length || ctx.options['--local'] === true || !serverUrl(ctx, pool)) return 0;
  const cloud = await need(ctx, 'accountsCloud', ['runCloudAccounts']);
  let code = 0;
  for (const row of rows) {
    const result = await cloud.runCloudAccounts('upload', { name: row.name, provider: row.provider, home: row.home, group: ctx.options['--group'], env: ctx.env });
    const replyCode = reply(ctx, result);
    code ||= replyCode;
  }
  return code;
}

async function importFolders(ctx) {
  if (ctx.options['--provider'] === 'claude') stop(2, 'pdd accounts import takes Codex folders only for now.');
  if (ctx.options['--name'] !== undefined && ctx.operands.length > 1) stop(2, 'Use --name with one PATH only.');
  const fs = ctx.fs, pool = await readPool({ env: ctx.env }, ctx.ports);
  const login = await need(ctx, 'accountsLogin', ['codexLoginFacts']);
  const keys = await accountKeys(login, pool), names = new Set(pool.logins.map(row => row.name));
  const real = async path => fs.realpath(path).catch(() => path);
  const homes = new Map();
  for (const row of pool.logins) homes.set(await real(row.home), row.name);
  const accepted = [], refused = [], now = ctx.now();
  for (const path of ctx.operands) {
    const home = resolve(ctx.cwd, path), refuse = text => refused.push(text);
    const info = await fs.lstat(home).catch(() => null);
    if (!info) { refuse(`No folder at ${home}.`); continue; }
    if (info.isSymbolicLink()) { refuse(`${home} is a link (to ${await linkTarget(fs, home)}). pdd imports only a folder with its own login file.`); continue; }
    if (!info.isDirectory()) { refuse(`${home} is not a folder.`); continue; }
    const file = join(home, 'auth.json'), fileInfo = await fs.lstat(file).catch(() => null);
    if (fileInfo?.isSymbolicLink()) { refuse(`${file} is a link (to ${await linkTarget(fs, file)}). pdd imports only a folder with its own login file.`); continue; }
    const fact = fileInfo ? await facts(login, home) : { state: 'none' };
    if (!['full', 'access', 'unreadable'].includes(fact.state)) { refuse(`No Codex login in ${home}. Use pdd accounts add NAME to sign in.`); continue; }
    if (fact.state === 'unreadable') { refuse(`pdd cannot read the Codex login in ${home}.`); continue; }
    const name = ctx.options['--name'] ?? basename(home);
    if (!NAME.test(name)) { refuse(badName(name, '--name NAME with ')); continue; }
    if (names.has(name)) { refuse(nameInUse(name, ' Use --name NAME.')); continue; }
    const realHome = await real(home);
    if (homes.has(realHome)) { refuse(`${home} is already in the pool as ${homes.get(realHome)}.`); continue; }
    if (typeof fact.accountKey === 'string' && fact.accountKey && keys.has(fact.accountKey)) {
      refuse(`${home} has the same Codex account as ${keys.get(fact.accountKey)}. pdd keeps one name for each account.`); continue;
    }
    names.add(name); homes.set(realHome, name);
    if (typeof fact.accountKey === 'string' && fact.accountKey) keys.set(fact.accountKey, name);
    accepted.push({ row: newRow(name, home, 'import', now), kind: fact.state === 'full' ? 'login' : 'access copy' });
  }
  let saved = pool;
  if (accepted.length) saved = await updatePool({ env: ctx.env }, addRows(accepted.map(entry => entry.row)), ctx.ports);
  for (const { row, kind } of accepted) {
    await log(ctx, 'import', row.name, `folder ${row.home}`);
    say(ctx.stdout, `Imported ${row.name} from ${row.home} (${kind}).`);
  }
  for (const text of refused) say(ctx.stderr, text);
  const code = await upload(ctx, saved, accepted.map(entry => entry.row));
  return code || (refused.length ? 1 : 0);
}

async function add(ctx) {
  const name = ctx.operands[0];
  if (ctx.options['--provider'] === 'claude') stop(2, 'pdd accounts add takes Codex logins only for now.');
  const pool = await readPool({ env: ctx.env }, ctx.ports);
  if (ctx.options['--group'] !== undefined && !serverUrl(ctx, pool)) stop(2, '--group needs the PDD login server. It is not set up on this machine.');
  if (!terminal(ctx)) stop(2, 'pdd accounts add needs a person at a terminal: it runs the Codex sign-in.');
  if (!NAME.test(name)) stop(1, badName(name, ''));
  if (find(pool, name)) stop(1, nameInUse(name, ''));
  const login = await need(ctx, 'accountsLogin', ['codexLoginFacts']);
  if (ctx.options['--local'] !== true && serverUrl(ctx, pool)) await need(ctx, 'accountsCloud', ['runCloudAccounts']);
  const fs = ctx.fs, folder = addFolder(pool, ctx.env, name) ?? stop(1, 'pdd accounts add needs an absolute home folder; set HOME to an absolute path.');
  const exists = `${folder} exists. Use pdd accounts import ${folder}, or move it away first.`;
  if (await fs.lstat(folder).catch(() => null)) stop(1, exists);
  await fs.mkdir(dirname(folder), { recursive: true, mode: 0o700 });
  try { await fs.mkdir(folder, { mode: 0o700 }); } catch (error) { if (error?.code === 'EEXIST') stop(1, exists); throw error; }
  const discard = async text => { await fs.rm(folder, { recursive: true, force: true }); stop(1, text); };
  let row;
  try {
    // The file store keeps the login in this folder, never in the system key store.
    await fs.writeFile(join(folder, 'config.toml'), 'cli_auth_credentials_store = "file"\n', { mode: 0o600, flag: 'wx' });
    say(ctx.stdout, `Signing in to Codex for ${name} in ${folder}. Follow the Codex steps below.`);
    const code = await runProgram(ctx, ctx.ports.codexCommand ?? 'codex', ['login', '--device-auth'], { ...ctx.env, CODEX_HOME: folder });
    const fact = await facts(login, folder);
    if (code !== 0 || fact.state !== 'full') await discard(`The Codex sign-in did not finish. pdd removed ${folder}; nothing was added.`);
    const owner = typeof fact.accountKey === 'string' && fact.accountKey ? (await accountKeys(login, pool)).get(fact.accountKey) : undefined;
    if (owner) await discard(`This Codex account is in the pool as ${owner}. pdd removed ${folder}; nothing was added.`);
    row = newRow(name, folder, 'add', ctx.now());
    await updatePool({ env: ctx.env }, addRows([row]), ctx.ports);
  } catch (error) {
    // pdd made this folder in this command; nothing was added, so nothing keeps it.
    await fs.rm(folder, { recursive: true, force: true }).catch(() => {});
    throw error;
  }
  await log(ctx, 'add', name, `folder ${folder}`);
  say(ctx.stdout, `Added ${name} (${folder}).`);
  return upload(ctx, await readPool({ env: ctx.env }, ctx.ports), [row]);
}

function moved(pool, move) {
  const names = orderedLogins(pool).map(row => row.name), known = new Set(names);
  for (const name of move.names) if (!known.has(name)) throw noLogin(name);
  const [name, other] = move.names, rest = names.filter(item => item !== name);
  if (move.kind === 'set') return [...move.names, ...names.filter(item => !move.names.includes(item))];
  if (move.kind === 'first') return [name, ...rest];
  if (move.kind === 'last') return [...rest, name];
  rest.splice(rest.indexOf(other) + 1, 0, name);
  return rest;
}

const orderLines = pool => orderedLogins(pool).map(row => `${row.position}  ${row.name}${row.paused ? '  paused' : ''}`);

async function editedNames(ctx, pool) {
  if (!terminal(ctx)) stop(2, 'pdd accounts order --edit needs a person at a terminal.');
  const editor = [ctx.env.VISUAL, ctx.env.EDITOR].find(value => typeof value === 'string' && value.trim());
  if (!editor) stop(2, 'Set VISUAL or EDITOR, or use pdd accounts order NAME...');
  const fs = ctx.fs, folder = await fs.mkdtemp(join(ctx.ports.tmpdir ?? tmpdir(), 'pdd-accounts-order-'));
  try {
    await fs.chmod(folder, 0o700);
    const file = join(folder, 'order.txt');
    await fs.writeFile(file, ['# Pool order: one login name per line. Steps use the first ready login.',
      '# Lines that start with # are skipped. A login that you leave out follows in its current order.',
      ...orderedLogins(pool).map(row => row.name), ''].join('\n'), { mode: 0o600, flag: 'wx' });
    const code = await runProgram(ctx, '/bin/sh', ['-c', `${editor} "$1"`, 'sh', file], ctx.env);
    if (code !== 0) stop(1, `The editor stopped with code ${code ?? 'unknown'}. The order did not change.`);
    return (await fs.readFile(file, 'utf8')).split('\n').map(line => line.trim()).filter(line => line && !line.startsWith('#'));
  } finally { await fs.rm(folder, { recursive: true, force: true }).catch(() => {}); }
}

async function order(ctx) {
  const { options, operands } = ctx;
  const chosen = [operands.length > 0, ...['--first', '--last', '--after', '--edit'].map(flag => options[flag] !== undefined)].filter(Boolean).length;
  if (chosen > 1) stop(2, 'Use one of NAME..., --first NAME, --last NAME, --after NAME OTHER or --edit.');
  const pool = await readPool({ env: ctx.env }, ctx.ports);
  if (!chosen) { say(ctx.stdout, ['Pool order (steps use the first ready login):', ...orderLines(pool)].join('\n')); return 0; }
  let move;
  if (options['--after'] !== undefined) {
    const names = [].concat(options['--after']);
    if (names.length !== 2 || names[0] === names[1]) stop(2, 'Use --after NAME OTHER: it moves NAME right after OTHER.');
    move = { kind: 'after', names };
  } else if (options['--first'] !== undefined) move = { kind: 'first', names: [options['--first']] };
  else if (options['--last'] !== undefined) move = { kind: 'last', names: [options['--last']] };
  else move = { kind: 'set', names: options['--edit'] ? await editedNames(ctx, pool) : [...operands] };
  const twice = move.names.find((name, index) => move.names.indexOf(name) !== index);
  if (twice) stop(2, `${twice} is named twice.`);
  const before = orderedLogins(pool).map(row => row.name), after = moved(pool, move);
  if (after.join('\n') === before.join('\n')) { say(ctx.stdout, 'Order unchanged.'); return 0; }
  const saved = await updatePool({ env: ctx.env }, fresh => {
    const names = moved(fresh, move), local = new Set(fresh.logins.map(row => row.name));
    const kept = fresh.order.filter((name, index) => !local.has(name) && fresh.order.indexOf(name) === index);
    return { ...fresh, order: [...names, ...kept] };
  }, ctx.ports);
  await log(ctx, 'order', null, orderedLogins(saved).map(row => row.name).join(', '));
  say(ctx.stdout, ['New pool order:', ...orderLines(saved)].join('\n'));
  return 0;
}

async function changeRow(ctx, name, change) {
  return updatePool({ env: ctx.env }, pool => {
    if (!find(pool, name)) throw noLogin(name);
    return { ...pool, logins: pool.logins.map(row => row.name === name ? change(row) : row) };
  }, ctx.ports);
}

async function pause(ctx, paused) {
  const name = ctx.operands[0], row = find(await readPool({ env: ctx.env }, ctx.ports), name);
  if (!row) throw noLogin(name);
  if (row.paused === paused) { say(ctx.stdout, paused ? `${name} is already paused.` : `${name} is not paused.`); return 0; }
  await changeRow(ctx, name, current => ({ ...current, paused }));
  await log(ctx, paused ? 'pause' : 'resume', name, '');
  say(ctx.stdout, paused ? `Paused ${name}. Steps skip it; it keeps its place in the order.` : `Resumed ${name}.`);
  return 0;
}

const settingsLine = row => `stop lines week ${row.stop?.week ?? DEFAULT_STOP.week}%, 5h ${row.stop?.fiveHour ?? DEFAULT_STOP.fiveHour}%; reset ${row.reset ?? 'never'}.`;

async function set(ctx) {
  const name = ctx.operands[0], row = find(await readPool({ env: ctx.env }, ctx.ports), name);
  if (!row) throw noLogin(name);
  const stopLines = { ...DEFAULT_STOP, ...row.stop }, wanted = { ...stopLines }, reset = ctx.options['--reset'] ?? row.reset;
  if (ctx.options['--stop-week'] !== undefined) wanted.week = Number(ctx.options['--stop-week']);
  if (ctx.options['--stop-5h'] !== undefined) wanted.fiveHour = Number(ctx.options['--stop-5h']);
  const changed = [...(wanted.week !== stopLines.week ? [`stop week ${wanted.week}`] : []),
    ...(wanted.fiveHour !== stopLines.fiveHour ? [`stop 5h ${wanted.fiveHour}`] : []), ...(reset !== row.reset ? [`reset ${reset}`] : [])];
  if (!changed.length) { say(ctx.stdout, `${name}: ${settingsLine(row)}`); return 0; }
  if (reset !== row.reset) {
    // A reset is the person's own resource; an agent with a terminal still must not choose it.
    if (!terminal(ctx) || (typeof ctx.env.PDD_AGENT === 'string' && ctx.env.PDD_AGENT.trim()))
      stop(2, `Only a person at a terminal can change the reset setting. Run pdd accounts set ${name} --reset ${reset} in your own terminal.`);
    ctx.stdout.write(`${RESET_MEANING[reset](name)}\nType yes to set reset to ${reset} for ${name}: `);
    if ((await readLine(ctx.stdin)).trim() !== 'yes') stop(1, 'The reset setting did not change.');
  }
  const saved = await changeRow(ctx, name, current => ({ ...current, stop: { ...current.stop, week: wanted.week, fiveHour: wanted.fiveHour }, reset }));
  await log(ctx, 'set', name, changed.join(', '));
  say(ctx.stdout, `Saved ${name}: ${settingsLine(find(saved, name))}`);
  return 0;
}

async function remove(ctx) {
  const name = ctx.operands[0], pool = await readPool({ env: ctx.env }, ctx.ports), row = find(pool, name);
  if (!row) throw noLogin(name);
  const folder = row.home, made = row.source === 'add' && folder === addFolder(pool, ctx.env, name);
  let wipe = false;
  if (made && terminal(ctx)) {
    ctx.stdout.write(`Delete ${folder} too? It holds the Codex login of ${name}. [y/N] `);
    wipe = ['y', 'yes'].includes((await readLine(ctx.stdin)).trim().toLowerCase());
  }
  await updatePool({ env: ctx.env }, pool => {
    if (!find(pool, name)) throw noLogin(name);
    return { ...pool, logins: pool.logins.filter(item => item.name !== name), order: pool.order.filter(item => item !== name) };
  }, ctx.ports);
  say(ctx.stdout, `Removed ${name} from the pool. pdd did not sign out.`);
  let detail = 'kept folder', code = 0;
  if (row.source !== 'add') say(ctx.stdout, `pdd kept ${folder} (pdd did not make it).`);
  else if (!wipe) say(ctx.stdout, `pdd kept ${folder}.`);
  else {
    const info = await ctx.fs.lstat(folder).catch(() => null);
    // Never follow a link: only the real folder that add made is deleted.
    if (info?.isDirectory() && !info.isSymbolicLink()) {
      try { await ctx.fs.rm(folder, { recursive: true }); detail = 'deleted folder'; say(ctx.stdout, `pdd deleted ${folder}.`); }
      catch { say(ctx.stderr, `pdd could not delete ${folder}.`); code = 1; }
    } else say(ctx.stdout, `pdd kept ${folder}.`);
  }
  await log(ctx, 'remove', name, detail);
  return code;
}

async function home(ctx) {
  const name = ctx.operands[0], row = find(await readPool({ env: ctx.env }, ctx.ports), name);
  if (!row) throw noLogin(name);
  say(ctx.stdout, row.home);
  return 0;
}

async function showLog(ctx) {
  const name = ctx.operands[0], json = ctx.options['--json'] === true, pool = await readPool({ env: ctx.env }, ctx.ports);
  const rows = await readLog({ env: ctx.env, name, limit: 100 }, ctx.ports), time = clock(ctx);
  if (json) say(ctx.stdout, JSON.stringify({ rows }, null, 2));
  else if (!rows.length) say(ctx.stdout, 'No changes in the local log yet.');
  else say(ctx.stdout, rows.map(row => `${time.zoned(Date.parse(row.at))}  ${row.action}  ${row.login ?? '-'}  ${row.detail}`.trimEnd()).join('\n'));
  if (!serverUrl(ctx, pool)) return 0;
  const cloud = await need(ctx, 'accountsCloud', ['runCloudAccounts']);
  return reply(ctx, await cloud.runCloudAccounts('log', { name, json, env: ctx.env }));
}

function reply(ctx, result) {
  const code = typeof result === 'number' ? result : result?.exitCode;
  if (!Number.isInteger(code) || code < 0 || code > 255) throw new Error(`Invalid reply for pdd accounts ${ctx.label}.`);
  if (typeof result?.message === 'string' && result.message.trim()) say(code === 0 ? ctx.stdout : ctx.stderr, result.message.replace(/\n$/, ''));
  return code;
}

const people = value => typeof value === 'string' ? value.split(',').map(item => item.trim()).filter(Boolean) : [];

async function cloudForm(ctx) {
  const action = ctx.action, name = ctx.operands[0], withNames = people(ctx.options['--with']);
  if (['share', 'unshare'].includes(action) && !withNames.length) stop(2, `Use pdd accounts ${action} NAME --with USER,...`);
  if (action === 'group-create' && (withNames.length > 0) === (ctx.options['--github'] !== undefined))
    stop(2, 'Use pdd accounts group create GROUP --with USER,... or --github ORG[/TEAM].');
  const cloud = await need(ctx, 'accountsCloud', ['runCloudAccounts']);
  const input = { name, env: ctx.env, ...(['share', 'unshare', 'group-create'].includes(action) && withNames.length ? { with: withNames } : {}),
    ...(action === 'group-create' && ctx.options['--github'] !== undefined ? { github: ctx.options['--github'] } : {}) };
  return reply(ctx, await cloud.runCloudAccounts(action, input));
}

async function reset(ctx) {
  const module = await need(ctx, 'accountsReset', ['runReset']);
  return reply(ctx, await module.runReset({ name: ctx.operands[0], env: ctx.env, stdin: ctx.stdin, stdout: ctx.stdout }));
}

const COMMANDS = { list, add, import: importFolders, order, pause: ctx => pause(ctx, true), resume: ctx => pause(ctx, false), set, remove, home,
  log: showLog, share: cloudForm, unshare: cloudForm, accept: cloudForm, leave: cloudForm, 'group-create': cloudForm, reset };

export async function runAccounts({ action, operands = [], options = {}, cwd = process.cwd(), env = process.env,
  stdin = process.stdin, stdout = process.stdout, stderr = process.stderr } = {}, ports = {}) {
  const ctx = { action, label: String(action).replace('-', ' '), operands: [...operands], options: { ...options }, cwd, env, stdin, stdout, stderr,
    ports, fs: ports.fs ?? nodeFs, now: ports.now ?? Date.now, timeZone: ports.timeZone ?? Intl.DateTimeFormat().resolvedOptions().timeZone };
  try {
    const command = Object.hasOwn(COMMANDS, action) ? COMMANDS[action] : stop(2, `Unsupported pdd accounts action ${action}. Run pdd accounts --help.`);
    return await command(ctx);
  } catch (error) {
    if (error instanceof Stop || error instanceof PoolError) { say(stderr, error.message); return error instanceof Stop ? error.exitCode : 1; }
    throw error;
  }
}
