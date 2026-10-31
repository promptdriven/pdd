// Generated from prompts/cli/approval-policy.prompt.md (sha256: 710d65f2f6451d4904bce7c2b7f7a8cc96cddbf37527a55baec3ce23eccb305d).
import * as nativeFs from 'node:fs';
import { join } from 'node:path';
import { randomUUID } from 'node:crypto';
import { hostname } from 'node:os';
import { StringDecoder } from 'node:string_decoder';
const object = value => value !== null && typeof value === 'object' && !Array.isArray(value);
export function readApprovalPolicy({ root }, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  let text;
  try { text = fs.readFileSync(join(root, 'pdd.json'), 'utf8'); }
  catch (error) { if (error.code === 'ENOENT') return { strictApprovals: false }; throw Error('Cannot read pdd.json.'); }
  let config;
  try { config = JSON.parse(text); } catch { throw Error('Invalid JSON in pdd.json.'); }
  if (!object(config) || Object.hasOwn(config, 'strict_approvals') && typeof config.strict_approvals !== 'boolean') throw Error('pdd.json must be an object with boolean strict_approvals.');
  return { strictApprovals: config.strict_approvals ?? false };
}
export async function readSaidWords(said, ports = {}) {
  if (typeof said !== 'string') throw Error('--said requires nonblank words.');
  let words = said;
  if (said === '-') {
    const decoder = new StringDecoder('utf8');
    words = '';
    try {
      for await (const chunk of ports.stdin ?? process.stdin) words += typeof chunk === 'string' ? chunk : decoder.write(chunk);
      words += decoder.end();
    } catch { throw Error('Cannot read --said words from stdin.'); }
  }
  if (!words.trim()) throw Error('--said requires nonblank words.');
  return words;
}
export function approvalActor(env = process.env) {
  for (const key of ['CODEX_THREAD_ID', 'CLAUDECODE', 'PDD_AGENT_SESSION']) if (typeof env[key] === 'string' && env[key].length) return { kind: 'agent', id: `${key}=${env[key]}` };
  return { kind: 'terminal', id: env.USER || env.LOGNAME || 'unknown' };
}
function validEvidence(e) {
  return object(e) && (!Object.hasOwn(e, 'id') || typeof e.id === 'string' && e.id.length > 0) && ['said','terminal','chat'].includes(e.route) && object(e.actor) && ['agent','terminal'].includes(e.actor.kind) && typeof e.actor.id === 'string' && Number.isSafeInteger(e.at) && (e.words === null || typeof e.words === 'string') && Array.isArray(e.prompts) && e.prompts.every(p => object(p) && typeof p.path === 'string' && /^[a-f0-9]{64}$/.test(p.proseSha256));
}
export function readPromptApprovals({ commonDir }, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  let text;
  try { text = fs.readFileSync(join(commonDir, 'pdd', 'approvals.json'), 'utf8'); }
  catch (error) { if (error.code === 'ENOENT') return []; throw Error('Cannot read pdd/approvals.json.'); }
  let journal;
  try { journal = JSON.parse(text); } catch { throw Error('Invalid pdd/approvals.json.'); }
  if (!object(journal) || journal.v !== 1 || !Array.isArray(journal.approvals) || !journal.approvals.every(validEvidence)) throw Error('Invalid pdd/approvals.json.');
  return journal.approvals;
}
function ownerAlive(pid, ports) {
  if (ports.processIdentity) {
    try { return ports.processIdentity(pid)?.alive; } catch { return undefined; }
  }
  try {
    process.kill(pid, 0);
    return true;
  } catch (error) { return error.code === 'ESRCH' ? false : undefined; }
}
function claimJournal(lock, fs, ports) {
  const host = typeof ports.hostname === 'function' ? ports.hostname() : ports.hostname ?? hostname();
  const owner = { pid: ports.ownerPid ?? process.pid, hostname: host, token: randomUUID() };
  const busy = () => Object.assign(Error('pdd/approvals.json is busy; retry approval.'), { code: 'approval_busy' });
  if (!Number.isInteger(owner.pid) || owner.pid < 1 || typeof host !== 'string' || !host) throw Error('Cannot identify approval lock owner.');
  let created = false;
  try { fs.mkdirSync(lock, { mode: 0o700 }); created = true; } catch (error) { if (error.code !== 'EEXIST') throw error; }
  const observed = fs.lstatSync(lock);
  if (!observed.isDirectory()) throw busy();
  const names = fs.readdirSync(lock);
  // An old empty lock has no verifiable owner and must be preserved.
  if (!created && !names.length) throw busy();
  const leaf = join(lock, `owner-${owner.token}.json`), temporary = `${lock}.${owner.token}.tmp`, bytes = JSON.stringify(owner);
  try { fs.writeFileSync(temporary, bytes, { flag: 'wx', mode: 0o600 }); fs.renameSync(temporary, leaf); }
  finally { try { fs.unlinkSync(temporary); } catch {} }
  const release = () => {
    try { if (fs.readFileSync(leaf, 'utf8') === bytes) fs.unlinkSync(leaf); } catch {}
    try {
      const current = fs.lstatSync(lock);
      if (current.dev === observed.dev && current.ino === observed.ino) fs.rmdirSync(lock);
    } catch { /* A concurrent claim or a replacement owner keeps its lock. */ }
  };
  try {
    for (const name of fs.readdirSync(lock)) {
      if (name === `owner-${owner.token}.json`) continue;
      const otherPath = join(lock, name);
      let text, other;
      try { text = fs.readFileSync(otherPath, 'utf8'); other = JSON.parse(text); }
      catch (error) { if (error.code === 'ENOENT') continue; throw busy(); }
      if (!object(other) || !Number.isInteger(other.pid) || other.pid < 1 || typeof other.hostname !== 'string' || !other.hostname ||
          typeof other.token !== 'string' || name !== `owner-${other.token}.json` || other.hostname !== host || ownerAlive(other.pid, ports) !== false) throw busy();
      try { if (fs.readFileSync(otherPath, 'utf8') === text) fs.unlinkSync(otherPath); }
      catch (error) { if (error.code !== 'ENOENT') throw error; }
    }
    return release;
  } catch (error) { release(); throw error; }
}
export async function recordPromptApproval({ commonDir, evidence }, ports = {}) {
  if (!validEvidence(evidence)) throw Error('Invalid approval evidence.');
  const fs = ports.fs ?? nativeFs, dir = join(commonDir, 'pdd'), lock = join(dir, 'approvals.lock');
  fs.mkdirSync(dir, { recursive: true, mode: 0o700 });
  let release;
  for (let attempt = 0; attempt < 500; attempt++) {
    try { release = claimJournal(lock, fs, ports); break; }
    catch (error) { if (error.code !== 'approval_busy' || attempt === 499) throw error; await new Promise(done => setTimeout(done, 10)); }
  }
  const temporary = join(dir, `.approvals.${randomUUID()}.tmp`);
  try {
    const approvals = readPromptApprovals({ commonDir }, ports);
    fs.writeFileSync(temporary, JSON.stringify({ v: 1, approvals: [...approvals, evidence] }, null, 2) + '\n', { mode: 0o600 });
    fs.renameSync(temporary, join(dir, 'approvals.json'));
  } finally {
    try { fs.unlinkSync(temporary); } catch { /* Already renamed or never written. */ }
    release();
  }
}
