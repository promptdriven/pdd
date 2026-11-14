// Generated from prompts/cli/setup-pairing.prompt.md (sha256: 5dc9e075b03a84ac9338405f3690e1b6fcfad6e0093712b6ff19d31a5e879407).
import { createPublicKey, randomBytes, verify } from 'node:crypto';
import { mkdirSync, readFileSync, writeFileSync, unlinkSync, lstatSync, rmSync, openSync, closeSync, renameSync, constants } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { setTimeout as delay } from 'node:timers/promises';
import { homedir } from 'node:os';

const ok = message => ({ exitCode: 0, message });
const fail = message => ({ exitCode: 1, message });
const root = env => join(env.XDG_STATE_HOME || join(env.HOME || homedir(), '.local', 'state'), 'pdd', 'pairing');
const read = (file, fallback) => { let fd; try { fd = openSync(file, constants.O_RDONLY | constants.O_NOFOLLOW); if (!lstatSync(file).isFile()) return fallback; return JSON.parse(readFileSync(fd, 'utf8')); } catch { return fallback; } finally { if (fd !== undefined) closeSync(fd); } };
const safeWrite = (file, data) => { try { if (!lstatSync(file).isFile()) throw Error('unsafe state'); } catch (e) { if (e.code !== 'ENOENT') throw e; } const temp = `${file}.${randomBytes(12).toString('hex')}.tmp`; const fd = openSync(temp, constants.O_WRONLY | constants.O_CREAT | constants.O_EXCL | constants.O_NOFOLLOW, 0o600); try { writeFileSync(fd, data); closeSync(fd); renameSync(temp, file); } catch (e) { try { closeSync(fd); } catch {} try { unlinkSync(temp); } catch {} throw e; } };
const jwk = k => k && typeof k === 'object' && Object.keys(k).sort().join(',') === 'crv,kty,x,y' && k.kty === 'EC' && k.crv === 'P-256' && /^[A-Za-z0-9_-]{43}$/.test(k.x) && /^[A-Za-z0-9_-]{43}$/.test(k.y);
const publicRecord = x => x && typeof x.login === 'string' && typeof x.keyId === 'string' && typeof x.deviceName === 'string' && jwk(x.publicKey) ? { login: x.login, keyId: x.keyId, deviceName: x.deviceName, publicKey: { kty: x.publicKey.kty, crv: x.publicKey.crv, x: x.publicKey.x, y: x.publicKey.y } } : null;
const records = file => { const data = read(file, []); return Array.isArray(data) ? data.map(publicRecord).filter(Boolean) : []; };
const sorted = x => Array.isArray(x) ? x.map(sorted) : x && typeof x === 'object' ? Object.fromEntries(Object.keys(x).sort().map(k => [k, sorted(x[k])])) : x;
function valid(offer, pending, now) {
  try {
    if (!pending || now >= Date.parse(pending.expiresAt) || !offer || Object.keys(offer).sort().join(',') !== 'code,deviceName,keyId,login,publicKey,signature,v' || offer.v !== 1 || !['login','code','keyId','deviceName','signature'].every(k => typeof offer[k] === 'string' && offer[k].length > 0) || offer.login !== pending.login || offer.code !== pending.code || !jwk(offer.publicKey) || !/^[A-Za-z0-9_-]+$/.test(offer.signature)) return false;
    const { signature, ...body } = offer, sig = Buffer.from(signature, 'base64url');
    return sig.length === 64 && verify('sha256', Buffer.from(JSON.stringify(sorted(body))), { key: createPublicKey({ key: offer.publicKey, format: 'jwk' }), dsaEncoding: 'ieee-p1363' }, sig);
  } catch { return false; }
}
const now = ports => (ports.now ?? Date.now)();
function pendingAt(dir, ports) { const p = read(join(dir, 'pending.json'), null); return p && typeof p.id === 'string' && /^[a-f0-9]{32}$/.test(p.id) && typeof p.login === 'string' && typeof p.code === 'string' && typeof p.expiresAt === 'string' && now(ports) < Date.parse(p.expiresAt) ? p : null; }
async function ask(question, ports, signal) {
  ports.stdout?.write(question);
  if (ports.confirm) return /^(y|yes)$/i.test(String(await ports.confirm(question)).trim());
  const { lineReader } = await import('./prompt-approve.mjs');
  if (signal?.aborted) return false;
  const reader = lineReader(ports.stdin ?? process.stdin);
  const close = () => reader.close();
  signal?.addEventListener('abort', close, { once: true });
  try { return /^(y|yes)$/i.test((await reader.ask()).trim()); } finally { signal?.removeEventListener('abort', close); reader.close(); }
}
export async function pairStatus({ env }, ports = {}) {
  const dir = root(env), p = pendingAt(dir, ports);
  return ok(JSON.stringify({ pending: p ? { login: p.login, code: p.code, expiresAt: p.expiresAt } : null, paired: records(join(dir, 'keys.json')) }));
}
export async function pairOffer({ env, messageFile }, ports = {}) {
  try {
    const dir = root(env), p = pendingAt(dir, ports), offer = JSON.parse(readFileSync(messageFile, 'utf8'));
    if (!valid(offer, p, now(ports))) return fail('Invalid or expired phone offer.');
    writeFileSync(join(dir, `offer-${p.id}.json`), JSON.stringify(offer), { flag: 'wx', mode: 0o600 });
    return ok('Offer delivered.');
  } catch { return fail('Phone offer could not be delivered.'); }
}
export async function runSetupPairing({ cwd, env, code, interactive }, ports = {}) {
  if (!interactive) return ok('');
  if (code === undefined && !await ask('Pair a phone? [y/N] ', ports)) return ok('');
  const login = ports.login ? await ports.login({ cwd, env }) : spawnSync('gh', ['api', 'user', '--jq', '.login'], { cwd, env, encoding: 'utf8', stdio: ['ignore','pipe','ignore'] }).stdout?.trim();
  if (!login) return fail('GitHub login is unavailable for pairing.');
  const dir = root(env), keysFile = join(dir, 'keys.json');
  if (code === undefined && records(keysFile).some(x => x.login === login)) return ok('');
  const random = ports.random ?? (n => randomBytes(n));
  code ??= random(4).toString('hex').toUpperCase();
  let locked = false, id, cancelResolve, timer;
  const controller = new AbortController();
  const cancelled = new Promise(resolve => { cancelResolve = resolve; });
  const cancel = () => { controller.abort(); cancelResolve(false); };
  const onInterrupt = () => cancel();
  process.on('SIGINT', onInterrupt);
  try {
    const parent = join(dir, '..');
    mkdirSync(parent, { recursive: true, mode: 0o700 });
    if (!lstatSync(parent).isDirectory()) throw Error('unsafe state directory');
    mkdirSync(dir, { recursive: true, mode: 0o700 });
    if (!lstatSync(dir).isDirectory()) throw Error('unsafe state directory');
    mkdirSync(join(dir, 'lock'), { mode: 0o700 }); locked = true;
    id = random(16).toString('hex');
    const p = { id, login, code, expiresAt: new Date(now(ports) + 600000).toISOString() };
    safeWrite(join(dir, 'pending.json'), JSON.stringify(p));
    timer = (ports.setTimer ?? setTimeout)(cancel, Math.max(0, Date.parse(p.expiresAt) - now(ports)));
    ports.stdout?.write(`Pairing code: ${code} (expires in 10 minutes)\n`);
    const offerFile = join(dir, `offer-${id}.json`);
    let offer;
    while (!controller.signal.aborted && now(ports) < Date.parse(p.expiresAt)) {
      offer = read(offerFile, null);
      if (offer) break;
      await Promise.race([ports.wait ? ports.wait({ pending: p, offerFile }) : delay(250), cancelled]);
    }
    if (controller.signal.aborted || !valid(offer, p, now(ports))) return fail('Phone offer expired or invalid.');
    if (!await Promise.race([ask(`Does your phone show ${code}? [y/N] `, ports, controller.signal), cancelled])) return fail('Phone pairing declined or interrupted.');
    if (controller.signal.aborted || !valid(offer, p, now(ports))) return fail('Phone offer expired or invalid.');
    const keys = records(keysFile), existing = keys.find(x => x.login === login && x.keyId === offer.keyId);
    if (existing && JSON.stringify(sorted(existing.publicKey)) !== JSON.stringify(sorted(offer.publicKey))) return fail('Phone key ID already belongs to another key.');
    if (!existing) keys.push(publicRecord(offer));
    safeWrite(keysFile, JSON.stringify(keys));
    return ok(`Paired: ${offer.deviceName} (key ${offer.keyId})`);
  } catch { return fail('Phone pairing could not start or complete.'); }
  finally { if (timer !== undefined) (ports.clearTimer ?? clearTimeout)(timer); controller.abort(); process.removeListener('SIGINT', onInterrupt); if (locked) { try { const p = read(join(dir, 'pending.json'), null); if (p?.id === id) unlinkSync(join(dir, 'pending.json')); } catch {} try { unlinkSync(join(dir, `offer-${id}.json`)); } catch {} rmSync(join(dir, 'lock'), { recursive: true, force: true }); } }
}
